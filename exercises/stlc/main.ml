let e = Env.empty
let e' = Env.extend e "a" 8

let t = Parser.type_of_string "(-> int int (* int int))"

let _ = print_string (Printer.type_to_string t)
