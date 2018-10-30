class simple_graph : int64 -> object
  method add_node : int64 -> unit
  method add_edge : int64 -> int64 -> unit
  method dom_comp : int64 -> unit
  method pred : int64 -> int64 list
  method is_dom : int64 -> int64 -> bool
  method reset : unit
  method make_snap : unit
  method reset_snap : unit
end

class loop_record : int64 -> int64 -> simple_graph -> object
  method in_loop : int64 -> bool
  method get_head : int64
  method inc_iter : unit
  method get_iter : int
  method add_iv : int64 -> Vine.exp -> unit
  method clean_ivt : unit
  method reset : unit
  method get_ivt : (int64 * Vine.exp * Vine.exp * Vine.exp * Vine.exp option) list
  method renew_ivt : (Vine.exp -> Vine.exp) -> (Vine.exp -> bool) -> bool option
  method is_iv_cond : Vine.exp -> bool
  method add_g : int64 -> Vine.exp -> Vine.exp -> Vine.binop_type -> Vine.typ -> (Vine.typ -> Vine.exp -> Vine.exp) -> (Vine.exp -> bool) -> int64 -> unit
  method clean_gt : unit
  method get_gt : (int64 * Vine.exp option * Vine.binop_type * Vine.typ * Vine.exp option * Vine.exp option * Vine.exp option * Vine.exp option * int64) list
  method is_gt_cond : Vine.exp -> bool
  method print_ec : unit
  method print_ivt : unit
  method get_heur : bool
  method compute_lss : int64 -> ((int64 * Vine.exp) list -> unit) -> unit
  method get_lss: (Vine.exp * (Vine.exp * (int64 * Vine.exp) list * int64) list) list
  method add_insn : int64 -> unit
  method get_loop_body : (int64, unit) Hashtbl.t
  method add_bd : int64 -> Vine.exp -> int64 -> unit
  method check_bt : int64 -> (Vine.exp * int64) option
  method clean_bt : unit
  method get_status : bool option
  method set_status : bool option -> unit
  method update_loopsum : unit
end

class dynamic_cfg : int64 -> object
  method add_node : int64 -> ((int64 * Vine.exp) list -> unit) -> Exec_options.loop_stat
  method get_current_loop : loop_record option
  method reset : unit
  method in_loop : int64 -> bool
  method get_head : int64
  method get_loop_head : int64
  method get_iter : int
  method add_iv : int64 -> Vine.exp -> unit
  method clean_ivt : unit
  method renew_ivt : (Vine.exp -> Vine.exp) -> (Vine.exp -> bool) -> bool option
  method is_iv_cond : Vine.exp -> bool
  method add_g : int64 -> Vine.exp -> Vine.exp -> Vine.binop_type -> Vine.typ -> (Vine.typ -> Vine.exp -> Vine.exp) -> (Vine.exp -> bool) -> int64 -> unit
  method clean_gt : unit
  method is_gt_cond : Vine.exp -> bool
  method make_snap : unit
  method reset_snap : unit
  method use_heur : bool
  method check_loopsum : int64 ->
    (Vine.exp -> bool) ->
    (Vine.typ -> Vine.exp -> Vine.exp) ->
    ((bool -> Vine.exp) ->
      (bool -> Vine.exp -> bool) ->
      (bool -> unit) ->
      (unit -> bool) -> (bool -> bool) -> bool) ->
    (int64 * Vine.exp) list * int64
  method get_lss: (Vine.exp * (Vine.exp * (int64 * Vine.exp) list * int64) list) list
  method add_bd : int64 -> Vine.exp -> int64 -> unit
  method check_bt : int64 -> (Vine.exp * int64) option
end
