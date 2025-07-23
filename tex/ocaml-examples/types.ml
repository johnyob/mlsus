type 'a one = {x : 'a; y : int}
type two = {x : int; z : int}
let one = { x = 1; y = 2}
let app f x = f x
let rev_app x f = f x
