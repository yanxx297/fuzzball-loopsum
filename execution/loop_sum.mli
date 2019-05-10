val split_cond : Vine.exp -> bool ->
  (Vine.var ->
     (Vine.exp -> Vine.exp option * Vine.exp option * Vine.binop_type) ->
     Vine.exp option * Vine.exp option * Vine.binop_type ->
     (Vine.var -> unit) -> Vine.exp option * Vine.exp option * Vine.binop_type) ->
  Vine.exp option * Vine.exp option * Vine.binop_type

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
  method reset : unit
  method make_snap : unit
  method reset_snap : unit
  method get_ivt : (int64 * Vine.exp * Vine.exp * Vine.exp * Vine.exp option) list
  method update_ivt : (Vine.exp -> Vine.exp) -> (Vine.exp -> bool) -> unit
  method is_iv_cond : Vine.exp -> bool
  method add_g : int64 * Vine.binop_type * Vine.typ * Vine.exp * Vine.exp * Vine.exp * bool * int64 ->
    (Vine.exp -> bool) -> (Vine.typ -> Vine.exp -> Vine.exp) -> unit
  method get_gt : (int64 * Vine.binop_type * Vine.typ * Vine.exp * Vine.exp option *
                   Vine.exp option * bool * int64) list                                                                  
  method print_gt : unit
  method print_ivt : unit
  method get_lss: ((int64 * Vine.exp * Vine.exp * Vine.exp * Vine.exp option) list *
                   (int64 * Vine.binop_type * Vine.typ * Vine.exp * Vine.exp option *
                    Vine.exp option * bool * int64)
                     list * int64) list                                                                  
  method set_lss: ((int64 * Vine.exp * Vine.exp * Vine.exp * Vine.exp option) list *
                   (int64 * Vine.binop_type * Vine.typ * Vine.exp * Vine.exp option *
                    Vine.exp option * bool * int64)
                     list * int64) list -> unit
  method save_lss : int64 -> unit
  method add_insn : int64 -> unit
  method add_bd : int64 -> Vine.exp -> int64 -> unit
  method check_bt : int64 -> (Vine.exp * int64) option
  method get_status : bool option
  method set_status : bool option -> unit
  method update_loopsum : unit
  method check_loopsum : int64 ->
    (Vine.exp -> bool) ->
    (Vine.exp -> unit) ->
    (Vine.typ -> Vine.exp -> Vine.exp) ->
    (int64 -> Vine.typ -> Vine.exp) ->
    (Vine.exp -> Vine.exp) ->
    (Vine.var ->
       (Vine.exp -> Vine.exp option * Vine.exp option * Vine.binop_type) ->
       Vine.exp option * Vine.exp option * Vine.binop_type ->
       (Vine.var -> unit) -> Vine.exp option * Vine.exp option * Vine.binop_type) ->
    ((bool -> Vine.exp) ->
      (bool -> Vine.exp -> bool) ->
      (bool -> unit) -> (unit -> bool) -> (bool -> bool) -> int -> bool) ->
    bool ->
    (int -> bool) ->
    int -> (int -> int) -> (int -> int) -> (int -> unit) -> 
    (int64 * Vine.exp) list * int64  
  method finish_loop : unit
end

class dynamic_cfg : int64 -> object
  method add_node : int64 -> Exec_options.loop_stat
  method reset : unit
  method in_loop : int64 -> bool
  method is_loop_head : int64 -> bool
  method get_head : int64
  method get_loop_head : int64
  method get_iter : int
  method add_iv : int64 -> Vine.exp -> unit
  method update_ivt : (Vine.exp -> Vine.exp) -> (Vine.exp -> bool) -> unit
  method is_iv_cond : Vine.exp -> bool
  method add_g : int64 * Vine.binop_type * Vine.typ * Vine.exp * Vine.exp * Vine.exp * bool * int64 ->
    (Vine.exp -> bool) -> (Vine.typ -> Vine.exp -> Vine.exp) -> unit
  method make_snap : unit
  method reset_snap : unit
  method check_loopsum : int64 ->
    (Vine.exp -> bool) ->
    (Vine.exp -> unit) ->
    (Vine.typ -> Vine.exp -> Vine.exp) ->
    (int64 -> Vine.typ -> Vine.exp) ->
    (Vine.exp -> Vine.exp) ->
    (Vine.var ->
       (Vine.exp -> Vine.exp option * Vine.exp option * Vine.binop_type) ->
       Vine.exp option * Vine.exp option * Vine.binop_type ->
       (Vine.var -> unit) -> Vine.exp option * Vine.exp option * Vine.binop_type) ->
    ((bool -> Vine.exp) ->
      (bool -> Vine.exp -> bool) ->
      (bool -> unit) -> (unit -> bool) -> (bool -> bool) -> int -> bool) ->
    bool ->
    (int -> bool) ->
    int -> (int -> int) -> (int -> int) -> (int -> loop_record -> unit) -> 
    (int64 * Vine.exp) list * int64  
  method add_bd : int64 -> Vine.exp -> int64 -> unit
  method check_bt : int64 -> (Vine.exp * int64) option
  method mark_extra_all_seen : (int * loop_record) list -> (int -> unit) ->
    (int -> bool) -> (int -> int) -> (int -> int) -> unit
end
