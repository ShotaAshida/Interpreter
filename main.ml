open Syntax
open Eval
open Typing

let rec checker x y = match y with
                    DeclDecl(x1, e1, e2) -> if x = x1 then true else checker x e2
                  | Decl(x1, e) -> if x = x1 then true else false
                  | _ -> raise (Failure " checker ")

let rec read_eval_print env tyenv=
  print_string "# ";
  flush stdout;
  try
  let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
  (*追加 Ex3.3.2 *)
  let rec repeat env1 tyenv1 x = 
    let (ty, newtyenv) = ty_decl tyenv1 x in
    let (id, newenv, v, expr2) = eval_decl env1 x in
    match expr2 with 
            Nothing -> Printf.printf "val %s : " id;
                      pp_ty ty;
                      print_string " = ";
                      pp_val v;
                      print_newline();
                      read_eval_print newenv newtyenv
          | Decl( x1, e ) -> if checker id expr2 
                            then
                            repeat newenv newtyenv expr2
                            else
                            Printf.printf "val %s : " id;
                            pp_ty ty;
                            print_string " = ";
                            pp_val v;
                            print_newline();
                            repeat newenv newtyenv expr2
          | DeclDecl( x1, e1, e2 ) -> if checker id expr2 
                                    then
                                    repeat newenv newtyenv expr2
                                    else
                                    Printf.printf "val %s : " id;
                                    pp_ty ty;
                                    print_string " = ";
                                    pp_val v;
                                    print_newline();
                                    repeat newenv newtyenv expr2
          |_ -> raise (Failure "ohohoho")
  in repeat env tyenv decl
  with  Typing.Error s -> print_string (s ^ "\n") ; read_eval_print env tyenv
      | Eval.Error s -> print_string (s ^ "\n") ; read_eval_print env tyenv
      | Parser.Error -> print_string ("Parser Error" ^ "\n") ; read_eval_print env tyenv
      | Failure s -> print_string(s ^ "\n") ; read_eval_print env tyenv
      | _ -> print_string("何かしらのエラー\n") ; read_eval_print env tyenv


let initial_env =
Environment.extend "iv" (IntV 4)
  (Environment.extend "iii" (IntV 3)
    (Environment.extend "ii" (IntV 2)
      (Environment.extend "i" (IntV 1)
        (Environment.extend "v" (IntV 5)
           (Environment.extend "x" (IntV 10) Environment.empty)))))

let initial_tyenv =
  Environment.extend "iv" (TyScheme([], TyInt))
    (Environment.extend "iii" (TyScheme([], TyInt))
      (Environment.extend "ii" (TyScheme([], TyInt))
        (Environment.extend "i" (TyScheme([], TyInt))
          (Environment.extend "v" (TyScheme([], TyInt))
            (Environment.extend "x" (TyScheme([], TyInt)) Environment.empty)))))

let _ = read_eval_print initial_env initial_tyenv