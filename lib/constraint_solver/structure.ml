open! Import

module type S = Mlsus_unifier.Structure.S

module Former = struct
  type 'a t =
    | App of 'a * 'a
    | Spine of 'a list
    | Head of Type_head.t
  [@@deriving sexp]

  type 'a ctx = unit

  exception Cannot_merge

  let iter t ~f =
    match t with
    | App (t1, t2) ->
      f t1;
      f t2
    | Spine ts -> List.iter ts ~f
    | Head _ -> ()
  ;;

  let map t ~f =
    match t with
    | App (t1, t2) -> App (f t1, f t2)
    | Spine ts -> Spine (List.map ts ~f)
    | Head hd -> Head hd
  ;;

  let copy t ~f = map t ~f

  let fold t ~f ~init =
    match t with
    | App (t1, t2) -> f t2 (f t1 init)
    | Spine ts -> List.fold_right ts ~f ~init
    | Head _ -> init
  ;;

  let merge ~ctx:() ~create:_ ~unify ~type1:_ ~type2:_ t1 t2 =
    match t1, t2 with
    | App (t11, t12), App (t21, t22) ->
      unify t11 t21;
      unify t12 t22;
      t1
    | Spine ts1, Spine ts2 ->
      (match List.iter2 ts1 ts2 ~f:unify with
       | Ok () -> t1
       | Unequal_lengths -> raise Cannot_merge)
    | Head hd1, Head hd2 when Type_head.(hd1 = hd2) -> t1
    | _ -> raise Cannot_merge
  ;;
end

module Rigid (S : S) = struct
  type 'a t =
    | Rigid_var
    | Structure of 'a S.t
  [@@deriving sexp_of]

  type 'a ctx = 'a S.ctx

  exception Cannot_merge = S.Cannot_merge

  let iter t ~f =
    match t with
    | Rigid_var -> ()
    | Structure s -> S.iter s ~f
  ;;

  let copy t ~f =
    match t with
    | Rigid_var -> Rigid_var
    | Structure s -> Structure (S.copy s ~f)
  ;;

  let fold t ~f ~init =
    match t with
    | Rigid_var -> init
    | Structure s -> S.fold s ~f ~init
  ;;

  let merge ~ctx ~create ~unify ~type1 ~type2 t1 t2 =
    match t1, t2 with
    | Rigid_var, _ | _, Rigid_var -> raise Cannot_merge
    | Structure s1, Structure s2 ->
      Structure
        (S.merge ~ctx ~create:(fun s -> create (Structure s)) ~unify ~type1 ~type2 s1 s2)
  ;;
end

module Suspended_first_order (S : S) = struct
  module Var = struct
    type 'a t =
      | Empty
      | Empty_one_or_more_handlers of 'a handler list
    [@@deriving sexp_of]

    and 'a handler =
      { run : 'a S.t -> unit
      ; default : unit -> unit (** [default ()] is used to fill the variable (or fail) *)
      }
    [@@deriving sexp_of]

    let merge t1 t2 =
      match t1, t2 with
      | Empty, Empty -> t1
      | Empty, Empty_one_or_more_handlers _ -> t2
      | Empty_one_or_more_handlers _, Empty -> t1
      | Empty_one_or_more_handlers handlers1, Empty_one_or_more_handlers handlers2 ->
        Empty_one_or_more_handlers (handlers1 @ handlers2)
    ;;

    let add_handler t handler =
      match t with
      | Empty -> Empty_one_or_more_handlers [ handler ]
      | Empty_one_or_more_handlers handlers ->
        Empty_one_or_more_handlers (handler :: handlers)
    ;;

    let fill t s ~schedule_handler =
      match t with
      | Empty -> ()
      | Empty_one_or_more_handlers handlers -> List.iter handlers ~f:(schedule_handler s)
    ;;
  end

  type 'a t =
    | Var of 'a Var.t
    | Structure of 'a S.t
  [@@deriving sexp_of]

  exception Cannot_merge = S.Cannot_merge

  type 'a ctx =
    { schedule_handler : 'a S.t -> 'a Var.handler -> unit
    ; super : 'a S.ctx
    }

  let iter t ~f =
    match t with
    | Var _ -> ()
    | Structure s -> S.iter s ~f
  ;;

  let fold t ~f ~init =
    match t with
    | Var _ -> init
    | Structure s -> S.fold s ~f ~init
  ;;

  let copy t ~f =
    match t with
    | Var _ -> Var Empty
    | Structure s -> Structure (S.copy s ~f)
  ;;

  let merge ~ctx ~create ~unify ~type1 ~type2 t1 t2 =
    match t1, t2 with
    | Var var1, Var var2 -> Var (Var.merge var1 var2)
    | Structure s, Var var | Var var, Structure s ->
      Var.fill var s ~schedule_handler:ctx.schedule_handler;
      Structure s
    | Structure s1, Structure s2 ->
      Structure
        (S.merge
           ~ctx:ctx.super
           ~create:(fun s -> create (Structure s))
           ~unify
           ~type1
           ~type2
           s1
           s2)
  ;;
end
