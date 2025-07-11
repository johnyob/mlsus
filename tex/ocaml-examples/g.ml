open Types
let _ =
  let g (f : 'a one -> int) : int = f {x = 1; y = 1} in g (fun r -> r.x)
