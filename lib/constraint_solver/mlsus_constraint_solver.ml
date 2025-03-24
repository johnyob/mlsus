open! Import

module Error : sig
  type t = Solver.Error.t =
    | Unsatisfiable of Mlsus_error.t
    | Unbound_type_var of Constraint.Type.Var.t
    | Unbound_var of Constraint.Var.t
    | Cannot_unify of Decoded_type.t * Decoded_type.t
    | Cannot_resume_suspended_generic
    | Cannot_resume_match_due_to_cycle
  [@@deriving sexp]
end =
  Solver.Error

let solve = Solver.solve
