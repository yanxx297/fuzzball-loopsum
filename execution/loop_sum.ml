(* 
 This file contains most code implementing the loop summarization algorithm
 descried in Automatic Partial Loop Summarization in Dynamic Test Generation
 (ISSTA'11.)
 Our implementation are different with the original paper in several ways:
 - The original algorithm is based on concolic execution, while our 
 implementation is pure symbolic.
*)

module DS = Set.Make (Int64);;
module V = Vine;;

exception LoopsumNotReady

open Exec_options;;
open Frag_simplify;;
open Exec_exceptions;;

(* Split a jmp condition to (lhs, rhs, op)*)
(* b := the in loop side of the cjmp (true/false) *)
(* TODO: add support to more operations*)
let split_cond e b if_expr_temp =
  let rec split e b = 
    (let msg = "Check loop cond" in
       (match e with
          (* je/jne *)
          | V.BinOp(V.EQ, lhs, (V.Constant(_) as rhs)) ->
              (if !opt_trace_loopsum then
                 Printf.eprintf "%s (je/jne):\n%s\n" msg (V.exp_to_string e);
               if b then (Some lhs, Some rhs, V.EQ) else (Some lhs, Some rhs, V.NEQ))
          (* jl/jge*)
          | V.BinOp(V.SLT, (V.BinOp(V.PLUS, _, _) as lhs), (V.Constant(_) as rhs)) ->
              (if !opt_trace_loopsum then
                 Printf.eprintf "%s (jl/jge):\n%s\n" msg (V.exp_to_string e);
               if b then (Some lhs, Some rhs, V.SLT) else (Some rhs, Some lhs, V.SLE))
          (* jg/jle *)
          | V.BinOp(V.BITOR, V.BinOp(V.SLT, _, _), V.BinOp(V.EQ, lhs, rhs))
          | V.BinOp(V.SLE, lhs, rhs) ->
              (if !opt_trace_loopsum then
                 Printf.eprintf "%s (jg/jle):\n%s\n" msg (V.exp_to_string e);
               if b then (Some lhs, Some rhs, V.SLE) else (Some rhs, Some lhs, V.SLT))
          (* js/jns *)
          | V.Cast(V.CAST_HIGH, V.REG_1, V.BinOp(V.PLUS, lhs, rhs)) ->
              (if !opt_trace_loopsum then
                 Printf.eprintf "%s (js/jns):\n%s\n" msg (V.exp_to_string e);
               if b then (Some lhs, Some (V.UnOp(V.NEG, rhs)), V.SLT) 
               else (Some (V.UnOp(V.NEG, rhs)), Some lhs, V.SLE))
          (* jae/jb *)
          | V.BinOp(V.LT, (V.Constant(_) as lhs), rhs)
          | V.BinOp(V.LT, lhs, (V.Constant(_) as rhs)) ->
              (if !opt_trace_loopsum then
                 Printf.eprintf "%s (jae/jb):\n%s\n" msg (V.exp_to_string e);
               if b then (Some lhs, Some rhs, V.LT) else (Some rhs, Some lhs, V.LE))
          (* ja/jbe *)
          | V.BinOp(V.BITOR, V.BinOp(V.LT, _, _), V.BinOp(V.EQ, lhs, rhs)) ->
              (if !opt_trace_loopsum then
                 Printf.eprintf "%s (ja/jbe):\n%s\n" msg (V.exp_to_string e);
               if b then (Some lhs, Some rhs, V.LE) else (Some rhs, Some lhs, V.LT))
          | V.Lval(V.Temp(var)) -> 
              (if_expr_temp var (fun e' -> split e' b) 
                 ((None: V.exp option), (None: V.exp option), V.NEQ) 
                 (fun (v: V.var) -> 
                    let msg = 
                      Printf.sprintf "Fail to unfold %s\n" (V.exp_to_string e)
                    in ignore(failwith msg)))
          (* Unwrap temps when they are part of the expression*)
          | V.BinOp(V.LT, V.Lval(V.Temp(var)), c)
          | V.BinOp(V.LT, c, V.Lval(V.Temp(var))) ->
              (if_expr_temp var (fun e' -> split (V.BinOp(V.LT, c, e')) b) 
                 ((None: V.exp option), (None: V.exp option), V.NEQ) 
                 (fun (v: V.var) -> 
                    let msg = 
                      Printf.sprintf "Fail to unfold %s\n" (V.exp_to_string e)
                    in failwith msg))
          | V.BinOp(V.BITOR, V.Lval(V.Temp(var)), (V.BinOp(V.EQ, _, _) as cond)) ->
              (if_expr_temp var (fun e' -> split (V.BinOp(V.BITOR, e', cond)) b) 
                 ((None: V.exp option), (None: V.exp option), V.NEQ) 
                 (fun (v: V.var) -> 
                    let msg = 
                      Printf.sprintf "Fail to unfold %s\n" (V.exp_to_string e)
                    in failwith msg))
          | V.Ite(e', _, _) -> (Printf.eprintf "Split ite %s to %s" (V.exp_to_string e) (V.exp_to_string e'); split e' b)
          (* Ignore this expr if it's True or False *)
          | V.Constant(V.Int(V.REG_1, b)) -> 
              (Printf.eprintf "%s %Ld\n" msg b;
                (None, None, V.NEQ))
          | _ -> 
              Printf.eprintf "split_cond currently doesn't support this condition(%B): %s\n" b (V.exp_to_string e);
              (None, None, V.NEQ)
       ))
  in
    split e (not b)


let print_set set = 
  Printf.eprintf "Set = {";
  DS.iter (fun d -> Printf.eprintf "0x%08Lx, " d) set;
  Printf.eprintf "}\n"

(* Minimum negative value*)    
(* MINUS 1 to get max positive value*)
let min_signed ty =
  match ty with
    | V.REG_1 -> (0x1L)
    | V.REG_8 -> (0x80L)
    | V.REG_16 -> (0x8000L)
    | V.REG_32 -> (0x80000000L)
    | V.REG_64 -> (0x8000000000000000L)
    | _  -> failwith "Illegal type\n" 

let max_unsigned ty = 
  match ty with
    | V.REG_1 -> (0x1L)
    | V.REG_8 -> (0xffL)
    | V.REG_16 -> (0xffffL)
    | V.REG_32 -> (0xffffffffL)
    | V.REG_64 -> (0xffffffffffffffffL)
    | _  -> failwith "Illegal type\n" 

class simple_node id = object(self)
  val mutable domin = DS.singleton id
  val mutable domin_snap = DS.singleton id

  method add_domin dom = domin <- (DS.add dom domin)

  method get_domin = domin 

  method set_domin domin' = domin <- domin'

  method update_domin update = domin <- DS.union domin update

  method make_snap = 
    domin_snap <- DS.empty;
    DS.iter (fun d -> domin_snap <- DS.add d domin_snap) domin

  method reset_snap = 
    domin <- DS.empty;
    DS.iter (fun d -> domin <- DS.add d domin) domin_snap
end

(*Simple graph that contains some basic operations and automatic dominator computation*)
class simple_graph (h: int64) = object(self)
  val head = h
  val mutable nodes = Hashtbl.create 100
  val successor = Hashtbl.create 100
  val predecessor = Hashtbl.create 100

  (*NOTE: what's the purpose to have domin and full_domin?*)
  val mutable domin = DS.empty
  val mutable full_dom = DS.empty

  method private dom_size dom = 
    let s = DS.cardinal dom in
      (*Printf.eprintf "dom size: %d\n" s;*)
      s

  method private eip_to_node eip = try Hashtbl.find nodes eip with Not_found -> None

  method private eip_to_set eip = 
    let node = self#eip_to_node eip in
      match node with
        | None -> DS.empty
        | Some n -> n#get_domin

  (* Compute dominators set*)
  method dom_comp id = 
    domin <- full_dom;
    let inter_set pred_id set = 
      let pred_set = self#eip_to_set pred_id in
        DS.inter pred_set set;
    in
    let pred_id_list = self#pred id in
      List.iter (fun pid -> domin <- inter_set pid domin) pred_id_list;
      domin <- DS.add id domin; 
      let node = self#eip_to_node id in
        (match node with 
          | Some n -> n#update_domin domin
          | None -> ());
        domin <- DS.empty

  method add_node id = 
    let node = new simple_node id in
      Hashtbl.replace nodes id (Some node);
      full_dom <- DS.add id full_dom;
      if !opt_trace_loop_detailed then
        Printf.eprintf "Add %Lx to graph %Lx\n" id head

  method add_edge tail head =
    let add_nodup tbl a b =
      let l = Hashtbl.find_all tbl a in
        if not (List.mem b l) then Hashtbl.add tbl a b
    in
    if not (Hashtbl.mem nodes tail) then 
      self#add_node tail;
    add_nodup successor tail head;
    add_nodup predecessor head tail;
    if not (Hashtbl.mem nodes head) then 
      (self#add_node head;
       self#dom_comp head)
    else
      self#dom_comp head
(*       Printf.eprintf "Node 0x%Lx already in list, don't compute dom\n" head *)

  method pred n = 
    Hashtbl.find_all predecessor n

  (*return whether d dominate x*)
  method is_dom x d = 
    let dom = self#eip_to_set x in
    let res = DS.mem d dom in
      if !opt_trace_loop_detailed then
        if res = true then Printf.eprintf "0x%08Lx dominate 0x%08Lx\n" d x
        else Printf.eprintf "0x%08Lx does not dominate 0x%08Lx\n" d x;
      res

  method reset =
    domin <- DS.empty;
    let reset_node e n = 
      match n with
        | Some node -> node#set_domin DS.empty
        | None -> ()
    in
      Hashtbl.iter reset_node nodes;

  method make_snap =
    Hashtbl.iter (fun _ n -> 
                    match n with
                      | Some node -> node#make_snap
                      | None -> ()
    ) nodes

  method reset_snap =
    let reset_node e n = 
      match n with
        | Some node -> node#reset_snap
        | None -> ()
    in
      Hashtbl.iter reset_node nodes;

end

class loop_record tail head g= object(self)
  val mutable iter = 1
  val mutable iter_snap = 1
  (* A loop record is identified by the dest of the backedge *)
  val id = head
  val loop_body = Hashtbl.create 100

  (* List of in-loop branch conditions and the associated prog slices *)
  (* This list is shared among all summaries in the same lss*)
  (* bt := (eip -> (cond, slice))*)
  val bt = Hashtbl.create 10

  (* List of in-loop branch decisions made in current Path *)
  (* each bdt is associated with one loopsum *)
  (* bdt := (eip -> decision(bool))*)
  val mutable bdt = Hashtbl.create 10
  val mutable snap_bdt = Hashtbl.create 10

  method private bdt_cmp bdt bdt' = 
    if not (Hashtbl.length bdt == Hashtbl.length bdt') then false
    else
      let res = ref true in
        Hashtbl.iter (fun (eip:int64) d ->
                        match (Hashtbl.find_opt bdt' eip) with
                          | Some d' -> if not d = d' then res := false
                          | None -> res := false
        ) bdt;
        !res

  method add_bd eip b =
    Hashtbl.replace bdt eip b

  method add_slice (eip:int64) (cond: V.exp) (slice: V.stmt list) = 
    Hashtbl.replace bt eip (cond, slice)

  method find_slice eip = 
    match (Hashtbl.find_opt bt eip) with
      | Some s -> true
      | None -> false

  (* Status about applying loopsum*)
  (* None: haven't tried to apply loopsum *)
  (* Some false : has checked this loop but no feasible loopsum, either *) 
  (*              because non of them work for current path or there is *)
  (*              no loopsum*)
  (* Some true : a loopsum has been applied to this loop*)
  val mutable loopsum_status = None
  val mutable loopsum_status_snap = None
                              
  method get_status = loopsum_status
 
  method set_status opt = (
    if !opt_trace_loopsum_detailed then
      Printf.eprintf "set use_loopsum to %s\n" 
        (match opt with
           | Some b -> Printf.sprintf "%B" b
           | None -> "None");
    loopsum_status <- opt)

  method update_loopsum = 
    loopsum_status <- None

  method inc_iter = 
    iter <- (iter + 1);
    if !opt_trace_loop then (
      Printf.eprintf "----------------------------------------------------------------------------\n";
      Printf.eprintf "iter [+1] : %d\n" iter)

  method get_iter = iter

  (* Inductive variable table (IVT) = (offset, V_0, V, V', dV)*)
  (* offset:= addr offset from stack pointer *)
  (* NOTE: add ty to this table instead of intering it on demand?*)
  val mutable ivt = []
  val iv_cond_t = Hashtbl.create 10

  (* Return true if ivt and ivt' are identical *)
  (* For the IVTs of the same loopsum, there should be exactly the same number*)
  (* of IVs, added in exactly the same order*)
  method private ivt_cmp ivt ivt' =
    if not (List.length ivt = List.length ivt') then false
    else
      let res = ref true in
        List.iteri (fun i iv ->
                      let (_, v, _, _, dv) = iv  
                      and (_, v', _, _, dv') = List.nth ivt' i in
                        if not (v = v' && dv = dv') then res := false
        ) ivt;
        !res

  method private ivt_search off = 
    let res = ref None in
    let loop ((offset, v0, v, v', dv_opt) as iv) = (
      if off = offset then res := Some iv
    ) in 
      List.iter loop ivt;
      !res

  method is_iv_cond cond = 
    let res = Hashtbl.mem iv_cond_t cond in
      res

  (* At the end of each loop iteration, check each iv and clean ivt if *)
  (* - any iv is changed by a different dV from previous, OR*)
  (* - any iv is not changed in current iter *)      
  method update_ivt simplify check =
    let simplify_cond exp = 
      (let rec is_cond e = 
         (match e with
            | V.BinOp(op, exp1, exp2) -> 
                (match op with                
                   | (V.EQ | V.NEQ | V.SLT | V.SLE | V.LT | V.LE) -> true
                   | _ -> ((is_cond exp1)&&(is_cond exp2)))
            | _ -> (false)) 
       in
         if is_cond exp then simplify V.REG_1 exp else exp)
    in
    let simplify_typecheck exp =
      let typ = Vine_typecheck.infer_type_fast exp in
        simplify typ exp
    in
    let rec check_ivt l =
      match l with
        | iv::l' ->
            (let (offset, v0, v, v', dv_opt) = iv in
               if iter = 2 then (offset, v0, v', v', dv_opt)::(check_ivt l')
               else if check (V.BinOp(V.EQ, v', v)) then check_ivt l'
               else
                 let dv' = simplify_typecheck (V.BinOp(V.MINUS, v', v)) in
                   match dv_opt with
                     | None -> 
                         (offset, simplify_typecheck (V.BinOp(V.MINUS, v0, dv')), v', v', Some dv')::(check_ivt l')
                     | Some dv -> 
                         (*NOTE: should check validity instead of satisfiability?*)
                         (let cond = V.BinOp(V.EQ, dv, dv') in
                            (match (simplify_cond cond) with
                               | V.Constant(V.Int(V.REG_1, 1L)) -> 
                                   (offset, v0, v', v', Some dv')::(check_ivt l')
                               | V.Constant(V.Int(V.REG_1, 0L)) -> check_ivt l'
                               | _ ->
                                   (if check cond then
                                      (Hashtbl.replace iv_cond_t cond ();
                                       (offset, v0, v', v', Some dv')::(check_ivt l'))
                                    else check_ivt l'))))
        | [] -> []
    in
    let ivt' = check_ivt ivt in
      if (List.length ivt') < (List.length ivt) then ivt <- []
      else ivt <- ivt'

  method get_ivt = ivt

  method in_loop eip = 
    let res = Hashtbl.mem loop_body eip in
      if !opt_trace_loop_detailed then
        (match res with
           | true -> (Printf.eprintf "0x%08Lx is in the loop <0x%08Lx>\n" eip id)
           | false  -> (Printf.eprintf "0x%08Lx is not in the loop <0x%08Lx>\n" eip id));
      res


  (* FIXME: consider the situation that a variable is updated mutiple times in the same loop iteration*)
  method add_iv (offset: int64) (exp: V.exp) =
    let replace_iv (offset, v0, v, v', dv) = 
      (let rec loop l =
         (match l with
            | iv::l' -> (
                let (offset', _, _, _, _) = iv in
                  if offset' = offset then [(offset, v0, v, v', dv)] @ l' 
                  else [iv] @ (loop l'))
            | [] -> [])
       in
         ivt <- loop ivt)
    in
    match (self#ivt_search offset) with
      | Some iv -> 
          let (offset, v0, v, v', dv) = iv in
            if not (v' = exp) then replace_iv (offset, v0, v, exp, dv)
      | None -> 
          if iter = 2 then 
            (Printf.eprintf "Add new iv with offset = %Lx\n" offset;
             ivt <- ivt @ [(offset, exp, exp, exp, None)])

  (*Guard table: (eip, op, ty, D0_e, D, dD, b, exit_eip)*)
  (*D0_e: the code exp of the jump condition's location*)
  (*D: the actual distance of current iteration, updated at each new occurence of the same loop*)
  (*EC: the expected execution count*)
  (*b: denotes which side of the cjmp branch is in the loop*)
  val mutable gt = []

  method private gt_cmp gt gt' =
    if not (List.length gt = List.length gt') then false
    else
      let res = ref true in
        List.iteri (fun i g ->
                      let (eip, _, _, _, _, _, _, _) = g 
                      and (eip', _, _, _, _, _, _, _) = List.nth gt' i in
                        if not (eip = eip') then res := false
        ) gt;
        !res

  method private gt_search gt eip = 
    let rec check_gt l eip =
      (match l with
         | h::l' ->
             (let (eip', _, _, _, _, _, _, _) = h in
                if eip' = eip then Some h
                else check_gt l' eip
             )
         | [] -> None)
    in
      check_gt gt eip

  (* Given an eip, check whether it is the eip of an existing guard *)
  method private is_known_guard geip gt = 
    let res = ref false in
      List.iter (fun (eip, _, _, _, _, _, _, _) ->
                   if eip = geip then res := true
      ) gt;
      !res

  method private compute_distance_from_scratch g check eval_cond simplify if_expr_temp =
    let (_, op, ty, d0_e, _, _, b, _) = g in
    let e = eval_cond d0_e in
    match (split_cond e b if_expr_temp) with
      | (Some lhs, Some rhs, _) -> 
          self#compute_distance op ty lhs rhs check simplify
      | _ -> None

  (* Formulas to compute EC (expected count)*)
  (* EC = (D+dD+1)/dD if integer overflow not happen *)
  (* EC = (D-1)/dD + 1 if iof happens*)
  (* D is unsigned and dD should be positive *)
  method private ec var check = 
    let (op, ty, d, dd) = var in
      if check (V.BinOp(V.LT, V.BinOp(V.PLUS, d, dd), d)) then
        V.BinOp(V.PLUS, V.BinOp(V.DIVIDE, V.BinOp(
          V.MINUS, d, V.Constant(V.Int(ty, 1L))), dd), V.Constant(V.Int(ty, 1L)))
      else
        V.BinOp(V.DIVIDE, V.BinOp(V.MINUS, V.BinOp(V.PLUS, d, dd), V.Constant(V.Int(ty, 1L))), dd)

  (* Compute expected loop count from a certain guard*)
  (* D and dD should not be 0, otherwise current path never enter/exit the loop *)
  method private compute_ec g check eval_cond simplify if_expr_temp =
    let (_, op, ty, d0_e, _, dd_opt, b, _) = g in
    let e = eval_cond d0_e in
    match (split_cond e b if_expr_temp) with
    | (Some lhs, Some rhs, _) ->
        (let d = (match self#compute_distance op ty lhs rhs check simplify with
                    | Some d -> 
                        assert(check (V.BinOp(V.NEQ, V.Constant(V.Int(ty, 0L)), d))); d
                    | None -> failwith "Cannot compute D")
         in
         let dd = (match dd_opt with
                     | Some dd -> 
                         assert(check (V.BinOp(V.NEQ, V.Constant(V.Int(ty, 0L)), dd))); dd
                     | None -> failwith "Cannot compute Dd")
         in
         (* Check integer overflow by checking whether D and dD are both *)
         (* positive/negative, and compute EC with modified D and dD accordingly*)
         let d_cond = V.BinOp(V.SLT, V.Constant(V.Int(ty, 0L)), d) in
         let dd_cond = V.BinOp(V.SLT, V.Constant(V.Int(ty, 0L)), dd) in
         let res = 
           (match op with
              | V.SLE | V.SLT ->
                  (match (check d_cond, check dd_cond) with
                     | (true, false) -> self#ec (op, ty, d, V.UnOp(V.NEG, dd)) check 
                     | (false, true) -> self#ec (op, ty, V.UnOp(V.NEG, d), dd) check
                     | (true, true) -> 
                         self#ec (op, ty, V.BinOp(V.PLUS, 
                                                  V.BinOp(V.MINUS, 
                                                          V.Constant(V.Int(ty, Int64.sub (min_signed ty) 1L)), lhs), 
                                                  dd), dd) check
                     | (false, false) -> 
                         self#ec (op, ty, V.BinOp(V.MINUS, 
                                                  V.BinOp(V.MINUS, 
                                                          V.Constant(V.Int(ty, min_signed ty)), lhs), 
                                                  dd), V.UnOp(V.NEG, dd)) check)
              | V.LE | V.LT ->
                  (match (check d_cond, check dd_cond) with
                     | (true, false) -> self#ec (op, ty, d, V.UnOp(V.NEG, dd)) check
                     | (false, true) -> self#ec (op, ty, V.UnOp(V.NEG, d), dd) check
                     | (true, true) -> 
                         self#ec (op, ty, V.BinOp(V.PLUS, 
                                                  V.BinOp(V.MINUS, 
                                                          V.Constant(V.Int(ty, max_unsigned ty)), lhs), dd), dd) check
                     | (false, false) -> self#ec (op, ty, V.BinOp(V.MINUS, lhs, dd), dd) check)
              | V.EQ ->
                  (match (check d_cond, check dd_cond) with
                     | (true, false) -> self#ec (op, ty, d, V.UnOp(V.NEG, dd)) check
                     | (false, true) -> self#ec (op, ty, V.UnOp(V.NEG, d), dd) check
                     | (true, true) ->
                         self#ec (op, ty, V.BinOp(V.MINUS, rhs, lhs), dd) check
                     | (false, false) -> self#ec (op, ty, d, V.UnOp(V.NEG, dd)) check
                  )
              | _ -> failwith "invalid guard operation")
         in
           (match (check d_cond, check dd_cond) with
              | (true, false) -> (d_cond, V.UnOp(V.NOT, dd_cond), res) 
              | (false, true) -> (V.UnOp(V.NOT, d_cond), dd_cond, res)
              | (true, true) -> (d_cond, dd_cond, res)
              | (false, false) -> 
                  (V.UnOp(V.NOT, d_cond), V.UnOp(V.NOT, dd_cond), res)))
    | _ -> 
        (Printf.eprintf "Unable to split %s\n" (V.exp_to_string e);
         raise Not_found)

  (* Given lhs, rhs and op, compute a distance (D)*)
  (* loop_cond := if true, stay in the loop*) 
  (* iof_cond = lhs>0 && rhs<0 && lhs-rhs<lhs; if true, integer overflow happens*)
  (* when computing D*)
  (* TODO: handle IOF*)
  method private compute_distance op ty lhs rhs check simplify =
    let msg = ref "" in
    let res = 
      (match op with
         | V.SLE -> 
             (let loop_cond = V.BinOp(V.SLT, rhs, lhs) in
              let iof_cond = 
                V.BinOp(V.BITAND, 
                        V.BinOp(V.BITAND, 
                                V.BinOp(V.SLT, rhs, V.Constant(V.Int(ty, 0L))), 
                                V.BinOp(V.SLT, V.Constant(V.Int(ty, 0L)), lhs)), 
                        V.BinOp(V.SLT, V.BinOp(V.MINUS, lhs, rhs), lhs)) 
              in 
                msg := !msg ^ (Printf.sprintf "loop_cond %s\n" (V.exp_to_string (simplify V.REG_1 loop_cond)));
                msg := !msg ^ (Printf.sprintf "iof_cond %s\n" (V.exp_to_string (simplify V.REG_1 iof_cond)));
                if not (check loop_cond) || check iof_cond then None
                else Some (V.BinOp(V.MINUS, lhs, rhs)))
         | V.SLT -> 
             (let loop_cond = V.BinOp(V.SLE, rhs, lhs) in
              let iof_cond = 
                V.BinOp(V.BITAND, 
                        V.BinOp(V.BITAND, 
                                V.BinOp(V.SLT, rhs, V.Constant(V.Int(ty, 0L))), 
                                V.BinOp(V.SLT, V.Constant(V.Int(ty, 0L)), lhs)), 
                        V.BinOp(V.SLT, V.BinOp(V.MINUS, lhs, rhs), lhs)) 
              in 
                msg := !msg ^ (Printf.sprintf "loop_cond %s\n" (V.exp_to_string (simplify V.REG_1 loop_cond)));
                msg := !msg ^ (Printf.sprintf "iof_cond %s\n" (V.exp_to_string (simplify V.REG_1 iof_cond)));
                if not (check loop_cond) || check iof_cond then None
                else Some (V.BinOp(V.MINUS, lhs, rhs)))
         | V.LE -> 
             (let cond = V.BinOp(V.LT, rhs, lhs) in
                if not (check cond) then None
                else Some (V.BinOp(V.MINUS, lhs, rhs)))
         | V.LT -> 
             (let cond = V.BinOp(V.LE, rhs, lhs) in
                if not (check cond) then None
                else Some (V.BinOp(V.MINUS, lhs, rhs))) 
         | V.EQ -> 
             Some (V.BinOp(V.MINUS, lhs, rhs))
         | _  -> None)
    in
      if !opt_trace_loopsum_detailed then Printf.eprintf "%s" !msg;
      res

  (* Add or update a guard table entry*)
  method add_g g' check simplify =
    let (eip, op, ty, d0_e, lhs, rhs, b, eeip) = g' in
      if !opt_trace_loopsum_detailed then
        Printf.eprintf "At iter %d, check cjmp at %08Lx, op = %s\n" iter eip (V.binop_to_string op);
      (match self#gt_search gt eip with
         | Some g -> 
             (let (_, _, _, _, d_opt, dd_opt, _, _) = g in
              let d_opt' = self#compute_distance op ty lhs rhs check simplify in
                (match (d_opt, d_opt', dd_opt) with
                   | (Some d, Some d', Some dd) ->
                       (let dd' = V.BinOp(V.MINUS, d', d) in
                          if check (V.BinOp(V.EQ, dd, dd')) then
                            self#replace_g (eip, op, ty, d0_e, Some d', Some dd', b, eip)
                          else Printf.eprintf "Guard at 0x%Lx not inductive\n" eip)
                   | (Some d, Some d', None) ->
                       (let dd' = V.BinOp(V.MINUS, d', d) in
                          self#replace_g (eip, op, ty, d0_e, Some d', Some dd', b, eip))
                   | (_, _, None) -> Printf.eprintf "fail to compute D\n"
                   | _ -> ()))
         | None -> 
             (if iter = 2 then
                (let d_opt = self#compute_distance op ty lhs rhs check simplify in
                   match d_opt with
                     | Some d ->
                         (gt <- gt @ [eip, op, ty, d0_e, d_opt, None, b, eeip];
                          if !opt_trace_loopsum_detailed then                     
                            Printf.eprintf "Add new guard at 0x%08Lx, D0 =  %s\n" eip (V.exp_to_string d))
                     | None -> ())))

  method private print_ivt ivt = 
    Printf.eprintf "* Inductive Variables Table [%d]\n" (List.length ivt);
    List.iteri (fun i (offset, v0, v, v', dv) ->
                  Printf.eprintf "[%d]\tmem[sp+%Lx] = %s " i offset (V.exp_to_string v0);
                  match dv with
                    | Some d -> Printf.eprintf "\t(+ %s)\n" (V.exp_to_string d)
                    | None -> Printf.eprintf "\t [dV N/A]\n"
    ) ivt

  method private print_gt gt =
    Printf.eprintf "* Guard Table [%d]\n" (List.length gt);
    List.iteri (fun i (eip, _, _, d0_e, _, _, _, eeip) ->
                  Printf.eprintf "[%d]\t0x%Lx\t%s\t0x%Lx\n" i eip (V.exp_to_string d0_e) eeip
    ) gt

  method private print_bdt bdt = 
    Printf.eprintf "* Branch Decisions[%d]:\n" (Hashtbl.length bdt);
    Hashtbl.iter (fun eip b ->
                    Printf.eprintf "0x%Lx\t%B\n" eip b
    ) bdt

  method get_gt = gt

  method private replace_g (eip, op, ty, d0_e, d, dd, b, eeip) = 
    let rec loop l =
      match l with
        | g::l' -> (
            let (e, _, _, _, _, _, _, _) = g in
              if e = eip then [(eip, op, ty, d0_e, d, dd, b, eeip)] @ l'
              else[g] @ (loop l'))
        | [] -> []
    in
      gt <- loop gt

  method get_head = id

  method add_insn (eip:int64) = 
    Hashtbl.replace loop_body eip ()

  (* loopsum set (lss) = (ivt, gt, bdt, geip)*)
  (* geip := the guard to leave from*)
  (* bdt := in-loop branch decision *)
  val mutable lss = []

  method get_lss = lss

  method set_lss s = lss <- s

  (* Return true if new loopsum n already exist in lss *)
  method private check_dup_lss n = 
    let rec check_dup l n = 
      (match l with
         | h::rest ->
             (let (ivt, gt, bdt, geip) = h
              and (ivt', gt', bdt', geip') = n in
                if (geip = geip' 
                    && (self#bdt_cmp bdt bdt')
                    && (self#ivt_cmp ivt ivt') 
                    && (self#gt_cmp gt gt')) 
                then true
                else check_dup rest n)
         | [] -> false)
    in
      check_dup lss n

  method private print_lss =
    Printf.eprintf "lss length %d\n" (List.length lss);
    List.iteri (fun i (ivt, gt, bdt, geip) ->
                  Printf.eprintf "lss[%d]:\n" i;
                  self#print_ivt ivt;
                  self#print_gt gt;
                  self#print_bdt bdt;
                  Printf.eprintf "Leave from 0x%Lx\n" geip
    ) lss

  (* Save current (ivt, gt, bdt, geip) to a new lss if valid*)
  (* Call this function when exiting a loop *)
  (* TODO: should also check invalid GT ?*)
  method save_lss geip =
    if not (self#is_known_guard geip gt) then
      Printf.eprintf "No lss saved since %Lx is not a guard\n" geip
    else
      let all_valid = ref true in
        List.iter (fun iv ->
                     let (_, _, _, _, dv) = iv in
                       if dv = None then all_valid := false 
        ) ivt;
        if not !all_valid then
          Printf.eprintf "No lss saved since some IV invalid\n"
        else if (self#check_dup_lss (ivt, gt, bdt, geip)) then 
          Printf.eprintf "lss already exist, ignore\n"
        else
          lss <- lss @ [(ivt, gt, Hashtbl.copy bdt, geip)];
        self#print_lss

  method private compute_precond loopsum check eval_cond simplify if_expr_temp (run_slice: V.stmt list -> unit) =
    let (_, gt, bdt, geip) = loopsum in
    let min_g_opt = self#gt_search gt geip in 
      match min_g_opt with
        | Some min_g ->
            (let (d_cond, dd_cond, min_ec) = 
               self#compute_ec min_g check eval_cond simplify if_expr_temp 
             in
             (* Construct the condition that Guard_i is the one with minimum EC*)
             let min_ec_cond geip gt =
               let res = ref (V.Constant(V.Int(V.REG_1, 1L))) in
               let after_min = ref false in
                 List.iter (fun g ->
                              let (eip, _, _, _, _, _, _, _) = g in
                                if not (eip = geip) then
                                  (let (_, _, ec) = self#compute_ec g check eval_cond simplify if_expr_temp in
                                     if !after_min then
                                       res := V.BinOp(V.BITAND, !res, V.BinOp(V.SLE, min_ec, ec))
                                     else
                                       res := V.BinOp(V.BITAND, !res, V.BinOp(V.SLT, min_ec, ec))
                                  )
                                else after_min := true
                 ) gt;
                 Printf.eprintf "min_ec_cond = %s\n" (V.exp_to_string !res);
                 !res
             in
             let branch_cond bdt =                
               (let res = ref (V.Constant(V.Int(V.REG_1, 1L))) in
                  Hashtbl.iter (fun eip d ->
                                  match Hashtbl.find_opt bt eip with
                                    | Some (cond, slice) -> 
                                        (run_slice slice;
                                         if d then 
                                           res := V.BinOp(V.BITAND, !res, eval_cond cond)
                                         else res := V.BinOp(V.BITAND, !res, eval_cond (V.UnOp(V.NOT, cond))))
                                    | None -> ()
                  ) bdt;
                  !res)
             in
               (* Run the prog slice of each in-loop branch and eval*)
               Printf.eprintf "branch_cond: %s\n" (V.exp_to_string (branch_cond bdt));
               V.BinOp(V.BITAND, 
                       V.BinOp(V.BITAND, 
                               V.BinOp(V.BITAND, d_cond, dd_cond), 
                               (branch_cond bdt)), 
                       (min_ec_cond geip gt)))
        | _ -> failwith ""

  method compute_loop_body tail head (g:simple_graph) = 
    let rec inc_loopbody eip = 
      if not (eip = head) then 
        (self#add_insn eip;
         let pred = g#pred eip in
           if !opt_trace_loop_detailed then
             (Printf.eprintf "pred %Lx { " eip;
              List.iter (fun addr ->
                           Printf.eprintf "%Lx, " addr) pred;
              Printf.eprintf "}\n");
           List.iter inc_loopbody pred)
    in
      inc_loopbody tail;
      self#add_insn tail;
      self#add_insn head;
      if !opt_trace_loop then
        (Printf.eprintf "Compute loopbody (%Lx -> %Lx) size: %d\n" 
           tail head (Hashtbl.length loop_body);
         let msg = ref "" in
           Hashtbl.iter (fun eip _ ->
                           msg := !msg ^ (Printf.sprintf "%Lx " eip)
           ) loop_body;
           Printf.eprintf "{%s}\n" !msg)

  (* Check whether any existing loop summarization that can fit current
   condition and return the updated values and addrs of IVs.
   NOTE: the update itself implemented in sym_region_frag_machine.ml*)
  (*TODO: loopsum preconds should be add to path cond*)
  method check_loopsum eip check (add_pc: V.exp -> unit) simplify load_iv eval_cond if_expr_temp
            try_ext (random_bit:bool) (is_all_seen: int -> bool) (cur_ident: int) 
            get_t_child get_f_child (add_node: int -> unit) run_slice = 
    let trans_func (_ : bool) = V.Unknown("unused") in
    let try_func (_ : bool) (_ : V.exp) = true in
    let non_try_func (_ : bool) = () in
    let both_fail_func (b : bool) = b in
    let true_bit () = true in
    let false_bit () = false in
    let rec get_precond l cur =
      match l with
        | h::rest -> 
            (if cur = -1 || not (is_all_seen (get_t_child cur)) then
               let precond = self#compute_precond h check eval_cond simplify if_expr_temp run_slice in
                 V.BinOp(V.BITOR, precond, (get_precond rest (get_f_child cur)))
             else 
               get_precond rest (get_f_child cur)
            ) 
        | [] -> V.Constant(V.Int(V.REG_1, 0L))
    in
    let use_loopsum () =
      (add_node cur_ident;
       let cond = 
         (try 
            get_precond lss (get_t_child cur_ident)
          with
            | Not_found -> V.Constant(V.Int(V.REG_1, 0L)))
       in
       let b = 
         (if check cond then (add_pc cond; true)
          (* TODO: uncomment the code bellow to enable random decision*)
          (* and call add_pc accordingly*)
          (*
           (Printf.eprintf "It is possible to use loopsum\n";
           let rand = random_bit in 
           Printf.eprintf "random: %B\n" rand;
           rand)
           *)
          else (add_pc (V.UnOp(V.NOT, cond)); false))
       in
         if b then 
           (let b =  try_ext trans_func try_func non_try_func true_bit both_fail_func 0x0 in
              Printf.eprintf "Decide to use loopsum (%B)\n" b)
         else 
           (let b = try_ext trans_func try_func non_try_func false_bit both_fail_func 0x0 in
              Printf.eprintf "Decide not to use loopsum (%B)\n" b);
         b)
    in
    let compute_iv_update loopsum = 
      let (ivt, gt, geip) = loopsum in
      let g_opt = self#gt_search gt geip in
        match g_opt with
          | None -> failwith ""
          | Some g ->
              (let (_, _, _, _, _, _, _, eeip) = g in
               let (_, _, ec) = self#compute_ec g check eval_cond simplify if_expr_temp in 
               let vt = List.map (fun (offset, v, _, _, dv_opt) ->
                                    let ty = Vine_typecheck.infer_type_fast v in
                                    let v0 = load_iv offset ty in
                                      match dv_opt with
                                        | Some dv -> 
                                            (offset, simplify ty (V.BinOp(V.PLUS, v0, V.BinOp(V.TIMES, ec, dv))))
                                        | None -> failwith ""
               ) ivt in 
                 (vt, eeip))
    in
    let choose_loopsum l =
      let feasibles = ref [] in
      let rec get_feasible id l conds = 
        Printf.eprintf "conds[%d]:%s\n" id (V.exp_to_string (simplify V.REG_1 conds));
        (match l with
           | h::rest ->
               (let (ivt, gt, _, geip) = h in
                let precond = self#compute_precond h check eval_cond simplify if_expr_temp run_slice in
                  Printf.eprintf "Precond[%d]: %s\n" id (V.exp_to_string precond);
                  if check (V.BinOp(V.BITAND, precond, conds)) then
                    (Printf.eprintf "lss[%d] is feasible\n" id;
                      feasibles := (V.BinOp(V.BITAND, precond, conds), 
                                  id, ivt, gt, geip)::!feasibles)
                  else Printf.eprintf "lss[%d] is infeasible\n" id;
                  get_feasible (id+1) rest (V.BinOp(V.BITAND, conds, V.UnOp(V.NOT, precond))))
           | [] -> ())
      in
        get_feasible 0 l (V.Constant(V.Int(V.REG_1, 1L)));
        let all = List.length !feasibles in
          if all <= 0 then failwith "Inconsistency between use_loopsum and choose_loopsum\n";
          let n = Random.int all in
          let (loopsum_cond, id, ivt, gt, geip) = (List.nth !feasibles n) in
          let (vt, eeip) = compute_iv_update (ivt, gt, geip) in
            add_pc loopsum_cond;
            (n, id, vt, eeip)
    in
    (*TODO: modify this method so that try_ext code = lss id*)
    let extend_with_loopsum l id =
      let rec extend l level =
        match l with
          | h::rest -> 
              (if level < id then
                 (ignore(try_ext trans_func try_func non_try_func false_bit both_fail_func level);
                  extend rest (level+1)
                 )
               else if level = id then
                 ignore(try_ext trans_func try_func non_try_func true_bit both_fail_func level)
               else failwith ""
              )
          | [] -> ()
      in
        extend l 1
    in
      if not (self#get_iter = 2) then ([], 0L)
      else
        (match loopsum_status with
           (*NOTE: should also extend useLoopsum node for Some ture/false status? *)
           | Some true -> 
               Printf.eprintf "Loopsum has been applied in 0x%Lx\n" eip; ([], 0L)
           | Some false -> 
               Printf.eprintf "Loop has been checked but no loopsum applies in 0x%Lx\n" eip; ([], 0L)
           | None -> 
               (if use_loopsum () then
                  (loopsum_status <- Some true;
                   let (n, id, vt, eeip) =  choose_loopsum lss in
                     Printf.eprintf "Choose loopsum[%d]\n" id;
                     extend_with_loopsum lss (n+1);
                     (vt, eeip))
                else 
                  (loopsum_status <- Some false;
                   ([], 0L))))

  (* Print loopsum status when exiting a loop*)
  method finish_loop = 
    if !opt_trace_loopsum then
      (self#print_gt gt;
       self#print_ivt ivt;
       self#print_bdt bdt)
       

  method reset =
    iter <- 0;
    loopsum_status <- None;
    ivt <- [];
    gt <- [];

  method make_snap =
    snap_bdt <- bdt;    
    iter_snap <- iter;
    loopsum_status_snap <- loopsum_status

  method reset_snap =
    bdt <- snap_bdt;
    iter <- iter_snap;
    loopsum_status <- loopsum_status_snap

  initializer 
    self#compute_loop_body tail head g;

end

(*Manage a simpe_graph and the corresponding loop stack*)
(*Automatic loop detection*)
class dynamic_cfg (eip : int64) = object(self)
  val g = new simple_graph eip
  val mutable current_node = -1L
  val mutable current_node_snap = -1L

  (* The eip of the 1st instruction in the procedure *)
  val head = eip

  method get_head = head

  (* To handle nested loops, track the current loop with a stack *)
  (* Each element is the id of a loop *)
  val mutable loopstack = Stack.create ()
  val mutable loopstack_snap = Stack.create ()

  (* A full List of loops in current subroutine*)
  (* Hashtbl loop head -> loop record *)
  val mutable looplist = Hashtbl.create 10	
                         
  (* Check the all_seen status of loops on current path *)
  (* If all the true subtrees of loopsums and the false subtree of useLoopsum*) 
  (* are all_seen, then mark the false side of last loopsum to all_seen*)
  method mark_extra_all_seen (loop_enter_nodes: (int * loop_record) list)  
                           mark_all_seen (is_all_seen: int -> bool) get_t_child
                           get_f_child =
    let rec subtree_all_seen node =
      Printf.eprintf "subtree_all_seen(%d)\n" node;
      if not (((get_t_child node) = -1) || (is_all_seen (get_t_child node))) then -1
      else if not ((get_f_child node) = -1) then 
        subtree_all_seen (get_f_child node)
      else
        node
         
    in
      if !opt_trace_loopsum then
        Printf.eprintf "Current path covered %d loop(s)\n" (List.length loop_enter_nodes);
      List.iter (fun (node, loop) ->
                   if is_all_seen (get_f_child node) then
                     (let n = subtree_all_seen (get_t_child node) in
                        Printf.eprintf "Try to mark all_seen, node %d\n" n;
                        if n >= 0 then mark_all_seen n)
      ) loop_enter_nodes

  method get_loop_head = 
    let loop = self#get_current_loop in
      match loop with
        | None -> -1L
        | Some l -> l#get_head

  method get_iter = 
    let loop = self#get_current_loop in
      match loop with
        | None -> 0
        | Some l -> l#get_iter

  method update_ivt simplify check = 
    let loop = self#get_current_loop in
      match loop with
        | None -> ()
        | Some l -> l#update_ivt simplify check

  method add_iv addr exp =
    let loop = self#get_current_loop in
      match loop with
        | None -> ()
        | Some l  -> l#add_iv addr exp

  method is_iv_cond cond=
    let loop = self#get_current_loop in
      match loop with
        | None -> false
        | Some l  -> l#is_iv_cond cond

  method add_g g check simplify =
    let loop = self#get_current_loop in
      match loop with
        | None -> ()
        | Some l  -> l#add_g g check simplify 

  method add_bd eip b = 
    let loop = self#get_current_loop in
      match loop with
        | None -> ()
        | Some l  -> l#add_bd eip b

  method add_slice eip cond slice = 
    let loop = self#get_current_loop in
      match loop with
        | None -> ()
        | Some l  -> l#add_slice eip cond slice

  method find_slice eip = 
    let loop = self#get_current_loop in
      match loop with
        | None -> false
        | Some l  -> l#find_slice eip

  method private is_parent lp lc = 
    let head = lc#get_head in
      Printf.eprintf "head: 0x%08Lx\n" head;
      if (lp#in_loop head) then true else false

  method private get_current_loop =
    if Stack.is_empty loopstack then None 
    else (		
      let current_loop = Stack.top loopstack in
      let loop = Hashtbl.find looplist current_loop in Some loop 
    )

  (* Return bool * bool: whether enter a loop * whether enter a different loop*)	
  method private enter_loop src dest =
    let msg = ref "" in
    let is_backedge t h = g#is_dom t h in 
    let current_head = 
      (match (self#get_current_loop) with
         | None -> -1L
         | Some loop -> loop#get_head)
    in
      if Hashtbl.mem looplist dest then 
        (if !opt_trace_loop then 
           msg := !msg ^ (Printf.sprintf "Find loop in looplist, head = 0x%08Lx\n" dest);
         let l = Hashtbl.find looplist dest in
           l#compute_loop_body src dest g;
           (true, true, Some l, !msg))
      else if current_head = dest then 
        (if !opt_trace_loop then
           msg := !msg ^ (Printf.sprintf "Stay in the same loop, head = %Lx\n" dest);
         let l = self#get_current_loop in
           (true, false, l, !msg))
      else if is_backedge src dest then 
        (if !opt_trace_loop then
           msg := !msg ^ (Printf.sprintf "Find backedge 0x%Lx --> 0x%Lx\n" src dest);
         let loop = new loop_record src dest g in
           (true, true, Some loop, !msg)
        )
      else (false, false, None, "")

  method private exit_loop eip = 
    let loop = self#get_current_loop in
      match loop with 
        | None -> (None, false)
        | Some l -> (loop, not (l#in_loop eip))

  method in_loop eip = 
    let loop = self#get_current_loop in
      match loop with
        | None -> false
        | Some l -> l#in_loop eip

  method is_loop_head eip = Hashtbl.mem looplist eip 

  method check_loopsum eip check add_pc simplify load_iv eval_cond if_expr_temp
                              try_ext random_bit is_all_seen cur_ident get_t_child
                              get_f_child add_loopsum_node run_slice = 
    let trans_func (_ : bool) = V.Unknown("unused") in
    let try_func (_ : bool) (_ : V.exp) = true in
    let non_try_func (_ : bool) = () in
    let both_fail_func (b : bool) = b in
    let loop = self#get_current_loop in
      match loop with
        | Some l -> 
            (let add_node ident = add_loopsum_node ident l in 
               l#check_loopsum eip check add_pc simplify load_iv eval_cond if_expr_temp
                 try_ext random_bit is_all_seen cur_ident get_t_child get_f_child 
                 add_node run_slice)
        | None -> 
            ignore(try_ext trans_func try_func non_try_func (fun() -> false) both_fail_func 0xffff);
            ([], 0L)

  (* NOTE: maybe rewrite this method with new structure, merge enter_loop and *)
  (* exit_loop, and add new loop to looplist*)
  method add_node (eip:int64) =
    let res =
      (if current_node = -1L then
         (g#add_node eip; NotInLoop)
       else
         (g#add_edge current_node eip;
          match (self#enter_loop current_node eip) with
            (* Enter the same loop*)
            | (true, false, loop, msg) -> 
                (match loop with
                   | Some l -> 
                       (l#inc_iter; 
                        if !opt_trace_loop then Printf.eprintf "%s" msg;
                        EnterLoop)
                   | None -> ErrLoop)
            (* Enter a different loop *)
            | (true, true, loop, msg) -> 
                (Stack.push eip loopstack;
                 match loop with
                   | Some lp -> 
                       (lp#inc_iter;
                        if not (Hashtbl.mem looplist eip) then Hashtbl.add looplist eip lp;
                        if !opt_trace_loop then 
                          Printf.eprintf "Enter loop from %Lx -> %Lx\n%s" 
                            current_node eip msg;
                        if !opt_trace_loop_detailed then 
                          Printf.eprintf "Add head = %Lx to looplist\n" eip;
                          Printf.eprintf "At iter %d, there are %d loop(s) in list\n" 
                            lp#get_iter (Hashtbl.length looplist);
                        EnterLoop)
                   | None -> ErrLoop)	
            | (_, in_loop, _, msg) ->
                (match self#exit_loop eip with
                   (* Exit loop *)
                   | (Some l, true) ->
                       (if !opt_trace_loop && (l#get_iter > 0) then 
                          Printf.eprintf "%sEnd loop %Lx on %d-th iter\n" 
                            msg (l#get_head) (l#get_iter);
                        if (l#get_status != Some true) 
                        && (self#get_iter > 2) then
                          (l#save_lss current_node;
                           l#finish_loop);
                        l#reset;
                        ExitLoop)
                   | _ -> if in_loop then InLoop else NotInLoop)))
    in
      current_node <- eip;
      res

  method private count_loop = 
    let count = Stack.length loopstack in
      Printf.eprintf "Current dcfg (0x%08Lx) have %d loops in active\n" head count

  method reset = 
    if !opt_trace_loopsum_detailed then
      Printf.eprintf "Reset dcfg starts with %Lx\n" head;
    g#reset; 
    current_node <- -1L;

  method make_snap =
    if !opt_trace_loopsum_detailed then
      Printf.eprintf "make_snap dcfg starts with %Lx\n" head;
    g#make_snap;
    Hashtbl.iter (fun _ l -> l#make_snap) looplist;
    current_node_snap <- current_node;
    loopstack_snap <- Stack.copy loopstack

  method reset_snap =
    if !opt_trace_loopsum_detailed then
      Printf.eprintf "Reset_snap dcfg starts with %Lx\n" head;
    g#reset_snap;
    current_node <- current_node_snap;
    loopstack <- Stack.copy loopstack_snap;
    let func hd l = 
      if (l#in_loop current_node) then 
          (Stack.push hd loopstack;
           l#reset_snap
          )
    in
      Hashtbl.iter func looplist  

end
