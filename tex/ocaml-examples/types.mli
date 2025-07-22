type 'a one = { x : 'a; y : int; }
type two = { x : int; z : int; }
val one : int one
val app : ('a -> 'b) -> 'a -> 'b
val rev_app : 'a -> ('a -> 'b) -> 'b
