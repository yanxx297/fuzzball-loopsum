(*
  Copyright (C) BitBlaze, 2009-2010. All rights reserved.
*)

module V = Vine;;

open Exec_domain;;
open Exec_exceptions;;
open Exec_utils;;
open Exec_options;;
open Frag_simplify;;
open Fragment_machine;;
open Sym_path_frag_machine;;
open Sym_region_frag_machine;;
open Exec_run_common;;
open Exec_runloop;;
open Exec_stats;;

let loop_w_stats count fn =
  let iter = ref 0L and
      start_wtime = Unix.gettimeofday () and
      start_ctime = Sys.time () in
    (try
       while (match count with
		| None -> true
		| Some i -> !iter < i)
       do
	 iter := Int64.add !iter 1L;
	 let old_wtime = Unix.gettimeofday () and
             old_ctime = Sys.time () in
	   if !opt_trace_iterations then 
	     Printf.printf "Iteration %Ld:\n" !iter;
	   fn !iter;
	   if !opt_time_stats then
	     ((let ctime = Sys.time() in
		 Printf.printf "CPU time %f sec, %f total\n"
		   (ctime -. old_ctime) (ctime -. start_ctime));
	      (let wtime = Unix.gettimeofday() in
		 Printf.printf "Wall time %f sec, %f total\n"
		   (wtime -. old_wtime) (wtime -. start_wtime)));
	   flush stdout
       done
     with
	 LastIteration -> ());
    if !opt_gc_stats then
      Gc.full_major () (* for the benefit of leak checking *)

let last_dt_print_time = ref 0.0

let print_tree fm =
  let now = Unix.gettimeofday () in
  let interval = match !opt_save_decision_tree_interval with
    | Some i -> i | None -> failwith "missing interval in print_tree" in
    if now -. !last_dt_print_time > interval then
      let chan = open_out "fuzz.tree" in
	fm#print_tree chan;
	close_out chan;
	last_dt_print_time := Unix.gettimeofday ()

let periodic_stats fm at_end force = 
  if !opt_save_decision_tree_interval <> None || force then
    print_tree fm;
  if !opt_gc_stats || force then
    check_memory_usage fm trans_cache;
  if !opt_gc_stats || force then
    Gc.print_stat stdout;
  if (!opt_solver_stats && at_end) || force then
    (Printf.printf "Solver returned satisfiable %Ld time(s)\n" !solver_sats;
     Printf.printf "Solver returned unsatisfiable %Ld time(s)\n"
       !solver_unsats;
     Printf.printf "Solver failed %Ld time(s)\n" !solver_fails)

let fuzz start_eip fuzz_start_eip end_eips
    (fm : fragment_machine) asmir_gamma symbolic_init =
  if !opt_trace_setup then
    (Printf.printf "Initial registers:\n";
     fm#print_x86_regs);
  flush stdout;
  (if start_eip <> fuzz_start_eip then
     (if !opt_trace_setup then Printf.printf "Pre-fuzzing execution...\n";
      flush stdout;
      runloop fm start_eip asmir_gamma (fun a -> a = fuzz_start_eip)));
  fm#start_symbolic;
  if !opt_trace_setup then
    (Printf.printf "Setting up symbolic values:\n"; flush stdout);
  symbolic_init ();
  fm#make_snap ();
  if !opt_trace_setup then
    (Printf.printf "Took snapshot\n"; flush stdout);
  Sys.set_signal  Sys.sighup
    (Sys.Signal_handle(fun _ -> raise (Signal "HUP")));
  Sys.set_signal  Sys.sigint
    (Sys.Signal_handle(fun _ -> raise (Signal "INT")));
  Sys.set_signal Sys.sigterm
    (Sys.Signal_handle(fun _ -> raise (Signal "TERM")));
  Sys.set_signal Sys.sigquit
    (Sys.Signal_handle(fun _ -> raise (Signal "QUIT")));
  Sys.set_signal Sys.sigusr1
    (Sys.Signal_handle(fun _ -> raise (Signal "USR1")));
  Sys.set_signal Sys.sigusr2
    (Sys.Signal_handle(fun _ -> periodic_stats fm false true));
  (try
     (try
	loop_w_stats !opt_num_paths
	  (fun iter ->
	     let old_tcs = Hashtbl.length trans_cache in
	     let stop str = if !opt_trace_stopping then
	       Printf.printf "Stopping %s\n" str
	     in
	       fm#set_iter_seed (Int64.to_int iter);
	       (try
		  runloop fm fuzz_start_eip asmir_gamma
		    (fun a -> List.mem a end_eips);
		with
		  | SimulatedExit(_) -> stop "when program called exit()"
		  | KnownPath -> stop "on previously-explored path"
		      (* KnownPath currently shouldn't happen *)
		  | DeepPath -> stop "on too-deep path"
		  | SymbolicJump -> stop "at symbolic jump"
		  | NullDereference -> stop "at null deref"
		  | JumpToNull -> stop "at jump to null"
		  | DivideByZero -> stop "at division by zero"
		  | TooManyIterations -> stop "after too many loop iterations"
		  | UnhandledTrap -> stop "at trap"
		  | IllegalInstruction -> stop "at bad instruction"
		  | UnhandledSysCall(s) ->
		      Printf.printf "[trans_eval WARNING]: %s\n%!" s;
		      stop "at unhandled system call"
		  | SymbolicSyscall -> stop "at symbolic system call"
		  | ReachedMeasurePoint -> stop "at measurement point"
		  | ReachedInfluenceBound -> stop "at influence bound"
		  | DisqualifiedPath -> stop "on disqualified path"
		  | BranchLimit -> stop "on branch limit"
		  | SolverFailure when !opt_nonfatal_solver
		      -> stop "on solver failure"
		  | Signal("USR1") -> stop "on SIGUSR1"
		  (* | NotConcrete(_) -> () (* shouldn't happen *)
		     | Simplify_failure(_) -> () (* shouldn't happen *)*)
	       ); 
	       if !opt_coverage_stats && 
		 (Hashtbl.length trans_cache - old_tcs > 0) then
		   Printf.printf "Coverage increased to %d on %Ld\n"
		     (Hashtbl.length trans_cache) iter;
	       periodic_stats fm false false;
	       if not fm#finish_path then raise LastIteration;
	       if !opt_concrete_path then raise LastIteration;
	       fm#reset ()
	  );
      with
	| LastIteration -> ()
	| Signal("QUIT") -> Printf.printf "Caught SIGQUIT\n");
     fm#after_exploration
   with
     | Signal(("INT"|"HUP"|"TERM") as s) -> Printf.printf "Caught SIG%s\n" s
    (*
     | e -> Printf.printf "Caught fatal error %s\n" (Printexc.to_string e);
	 Printexc.print_backtrace stderr *) );
  periodic_stats fm true false
