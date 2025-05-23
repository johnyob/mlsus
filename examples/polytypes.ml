let id = fun x -> x;;
let pid = [ id : 'a. 'a -> 'a ];;

let see_pid = (fun x -> (@[x], @[x])) pid;;
let see_pid_check = forall (type 'a 'b) -> (see_pid : ('a -> 'a) * ('b -> 'b));;
