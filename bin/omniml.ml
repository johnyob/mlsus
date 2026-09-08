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

  let disable_stdlib =
    flag "-disable-stdlib" no_arg ~doc:"Disables the inclusion of the standard library"
  ;;

  let ffcp =
    flag
      ~full_flag_required:()
      "-ffcp"
      no_arg
      ~doc:"Enables the first class polymorphism feature. Enabled by default."
  ;;

  let fno_fcp =
    flag
      ~full_flag_required:()
      "-fno-fcp"
      no_arg
      ~doc:"Disables the first class polymorphism feature."
  ;;

  let fcp =
    Command.Param.map3 ffcp fno_fcp args ~f:(fun ffcp fno_fcp args ->
      match ffcp, fno_fcp with
      | true, true ->
        (* When both flags are passed, the last flag wins *)
        List.fold args ~init:false ~f:(fun with_fcp -> function
          | "-ffcp" -> true
          | "-fno-fcp" -> false
          | _ -> with_fcp)
      | true, false -> true
      | false, true -> false
      | false, false ->
        (* Enabled by default *)
        true)
  ;;

  let defaulting =
    flag
      "-defaulting"
      (optional Omniml_main.Options.Defaulting.arg_type)
      ~doc:"STRATEGY Defaulting strategy. Disabled by default, enabled with -ffcp"
  ;;
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
        +> Params.disable_stdlib
        +> Params.fcp)
      (fun filename dump_ast without_stdlib with_fcp ->
         open_with_lexbuf
           ~f:
             (constraint_gen_and_print
                ~dump_ast
                ~with_stdlib:(not without_stdlib)
                ~with_fcp)
           filename)
  ;;

  let type_check =
    Command.basic_spec
      ~summary:"Type checks [filename]."
      Command.Spec.(
        empty
        +> anon ("filename" %: string)
        +> Params.dump_ast
        +> Params.dump_constraint
        +> Params.disable_stdlib
        +> Params.fcp
        +> Params.defaulting
        +> Global.set_level_via_param ()
        +> Global.set_trace_file_via_param ())
      (fun filename dump_ast dump_constraint without_stdlib with_fcp defaulting () () ->
         let defaulting =
           Option.value defaulting ~default:(if with_fcp then Unary else Disabled)
         in
         open_with_lexbuf filename ~f:(fun lexbuf ->
           let source = `File filename in
           type_check_and_print
             ~source
             ~dump_ast
             ~dump_constraint
             ~with_stdlib:(not without_stdlib)
             ~with_fcp
             ~defaulting
             lexbuf))
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
