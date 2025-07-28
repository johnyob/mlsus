open Core
open Mlsus_constraint
module C = Constraint
module Principal_shape = Mlsus_constraint_solver.For_testing.Principal_shape

let%quick_test _ =
  fun (type_scheme :
        (C.Type_scheme.t
        [@generator C.Quickcheckable.Type_scheme.quickcheck_generator]
        [@shrinker C.Quickcheckable.Type_scheme.quickcheck_shrinker])) ->
  let _, poly_shape = Principal_shape.poly_shape_decomposition_of_scheme type_scheme in
  Principal_shape.Poly.invariant poly_shape
;;
