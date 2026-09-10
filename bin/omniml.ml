open Core
open Omniml_main
open Omniml_log

let open_with_lexbuf ~f filename () =
  Omniml_error.handle_uncaught ~exit:true
  @@ fun () ->
  let in_ =
    try In_channel.create filename with
    | Sys_error _ -> Omniml_error.(raise @@ file_not_found filename)
  in
  protect
    ~f:(fun () ->
      let lexbuf = Lexing.from_channel in_ in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      f lexbuf)
    ~finally:(fun () -> In_channel.close in_)
;;

module Params = struct
  open Command.Spec

  let dump_ast =
    flag "-dump-ast" no_arg ~doc:"Dumps the parsed program (formatted as a sexp)."
  ;;

  let dump_constraint =
    flag
      "-dump-constraint"
      no_arg
      ~doc:"Dumps the generated constraint (formatted as a sexp)."
  ;;

  let no_stdlib =
    flag "-no-stdlib" no_arg ~doc:"Disables the inclusion of the standard library"
  ;;

  let include_stdlib = Command.Param.(no_stdlib >>| fun no_stdlib -> not no_stdlib)

  let fflag ~name ~feature ~default =
    let fname = "-f" ^ name in
    let fno_name = "-fno-" ^ name in
    let default_doc = if default then "Enabled" else "Disabled" in
    let f =
      flag
        ~full_flag_required:()
        fname
        no_arg
        ~doc:(Fmt.str "Enables the %s feature. %s by default." feature default_doc)
    in
    let fno =
      flag
        ~full_flag_required:()
        fno_name
        no_arg
        ~doc:(Fmt.str "Disables the %s feature. %s by default." feature default_doc)
    in
    Command.Param.map3 f fno args ~f:(fun f fno args ->
      match f, fno with
      | true, true ->
        (* When both flags are passed, the last flag wins *)
        List.fold args ~init:false ~f:(fun result -> function
          | name when String.(fname = name) -> true
          | name when String.(fno_name = name) -> false
          | _ -> result)
      | true, false -> true
      | false, true -> false
      | false, false ->
        (* Enabled by default *)
        default)
  ;;

  let ffcp = fflag ~name:"fcp" ~feature:"first class polymorphism" ~default:true
  let frec_types = fflag ~name:"rec-types" ~feature:"recursive types" ~default:false
  let fdefaulting = fflag ~name:"defaulting" ~feature:"defaulting" ~default:false
end

module Command = struct
  let lex =
    Command.basic_spec
      ~summary:"Lexes [filename] and prints the tokens."
      Command.Spec.(empty +> anon ("filename" %: string))
      (open_with_lexbuf ~f:lex_and_print)
  ;;

  let parse =
    Command.basic_spec
      ~summary:"Parses [filename] and prints the program (formatted as a sexp)."
      Command.Spec.(empty +> anon ("filename" %: string))
      (open_with_lexbuf ~f:parse_and_print)
  ;;

  let constraint_gen =
    Command.basic_spec
      ~summary:
        "Parses [filename] and prints the generated constraint (formatted as a sexp)."
      Command.Spec.(
        empty
        +> anon ("filename" %: string)
        +> Params.dump_ast
        +> Params.include_stdlib
        +> Params.ffcp)
      (fun filename dump_ast include_stdlib ffcp ->
         let options =
           Omniml_options.(
             empty
             |> with_ ~option:Dump_ast ~enabled:dump_ast
             |> with_ ~option:Include_stdlib ~enabled:include_stdlib
             |> with_ ~option:First_class_polymorphism ~enabled:ffcp)
         in
         open_with_lexbuf ~f:(constraint_gen_and_print ~options) filename)
  ;;

  let type_check =
    Command.basic_spec
      ~summary:"Type checks [filename]."
      Command.Spec.(
        empty
        +> anon ("filename" %: string)
        +> Params.dump_ast
        +> Params.dump_constraint
        +> Params.include_stdlib
        +> Params.ffcp
        +> Params.frec_types
        +> Params.fdefaulting
        +> Global.set_level_via_param ()
        +> Global.set_trace_file_via_param ())
      (fun filename
        dump_ast
        dump_constraint
        include_stdlib
        ffcp
        frec_types
        fdefaulting
        ()
        () ->
         let options =
           let fdefaulting = fdefaulting || ffcp in
           Omniml_options.(
             empty
             |> with_ ~option:Dump_ast ~enabled:dump_ast
             |> with_ ~option:Dump_constraint ~enabled:dump_constraint
             |> with_ ~option:Include_stdlib ~enabled:include_stdlib
             |> with_ ~option:First_class_polymorphism ~enabled:ffcp
             |> with_ ~option:Recursive_types ~enabled:frec_types
             |> with_ ~option:Defaulting ~enabled:fdefaulting)
         in
         open_with_lexbuf filename ~f:(fun lexbuf ->
           let source = `File filename in
           type_check_and_print ~source ~options lexbuf))
  ;;

  let v =
    Command.group
      ~summary:"omniml"
      [ "lex", lex
      ; "parse", parse
      ; "constraint-gen", constraint_gen
      ; "type-check", type_check
      ]
  ;;

  let is_command = function
    (* OmniML commands *)
    | "lex" | "parse" | "constraint-gen" | "type-check" -> true
    (* Built-in commands from [Command] *)
    | "help"
    | "-help"
    | "--help"
    | "version"
    | "-version"
    | "--version"
    | "-build-info"
    | "--build-info" -> true
    | _ -> false
  ;;
end

let () =
  let argv =
    match Sys.get_argv () |> Array.to_list with
    | program :: (arg :: _ as args) when Command.is_command arg -> program :: args
    | program :: args -> program :: "type-check" :: args
    | [] -> assert false
  in
  Command_unix.run ~argv Command.v
;;
