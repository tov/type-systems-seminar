open Core

let warn s =
  Out_channel.output_string Out_channel.stderr s;
  Out_channel.flush Out_channel.stderr

let rec read () =
  try
    print_string "> ";
    Out_channel.flush stdout;
    Some (Parser.expr_of_sexp (Sexp.input_sexp In_channel.stdin))
  with
  | End_of_file -> None
  | Parser.Bad_syntax(exp, got) ->
      warn "Syntax error: expecting ";
      warn exp;
      warn ", got:\n";
      Sexp.output_hum_indent 2 Out_channel.stderr got;
      warn "\n";
      read ()

let rec repl () =
  match read () with
  | None -> ()
  | Some e ->
      let v = Eval.eval Env.empty e in
      print_string ("-> " ^ Eval.string_of_value v ^ "\n");
      repl ()

