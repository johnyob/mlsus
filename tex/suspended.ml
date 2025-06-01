module type Dir = sig                                                    
  type 'a one = {x : 'a}
  type two = {x : int; y : int}
end

module type Inv = sig                                                    
  type two = {x : int; y : int}
  type 'a one = {x : 'a}
end

module E1 (Env : Dir) = struct
  open Env
  let e_1 r = r.x
end

module E2 (Env : Dir) = struct
  open Env
  let e_2 = let r = {x = 1; y = 2} in r.x
end

module F3 (Env : Dir) = struct
  open Env
  let e_3 = (fun r -> r.x) {x = 1}
end

module F4 (Env : Dir) = struct
  open Env
  let e_4 = (fun r -> r.x) @@ {x = 1}
end

module F5 (Env : Dir) = struct
  open Env
  let e_5 = {x = 1}  |> (fun r -> r.x)
end

module E6 (Env : Dir) = struct
  open Env
  let e_6 r = (r.y,  r.x)
  let e_6 r = (r.x,  r.y)
end

module F6 (Env : Inv) = struct
  open Env
  let e_6 r = (r.y,  r.x)
  let e_6 r = (r.x,  r.y)
end

module F7 (Env : Dir) = struct
  open Env
  let e_7 r = (r.x : bool)
end

module F8 (Env : Dir) = struct
  open Env
  let e_7 r = r.x.x
end

module E9 (Env : Dir) = struct
  open Env
  let e_9 =
    let g : ('a one -> int) -> int = fun f -> f {x = 1} in
    g (fun r -> r.x) 
end

module type Fields = sig
  type three = {x : int; y : int}
  type four  = {y : int; z : int}
  type five  = {x : int; z : int}
  type m = L | M
  type n = L
end

module F10 (Env : Fields) = struct
  open Env
  let e10 = fun r -> let x = r.x in x + r.y
end
