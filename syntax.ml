(* ML interpreter / type reconstruction *)
type id = string

type tyvar = int

type binOp = | Equal | Plus | Minus | Mult | Lt | And | Or | Cons

type ty = TyInt | TyBool | TyVar of tyvar | TyFun of ty * ty

type tysc = TyScheme of tyvar list * ty

let tysc_of_ty ty = TyScheme ([], ty)

let rec freevar_tysc tysc = let tyvars, ty = tysc in
                            match ty with
                                  TyVar x -> if MySet.member ty tyvars then MySet.empty
                                                else MySet.singleton x
                                | TyFun(x, y) -> let tyx = freevar_tysc (tyvars, x) in
                                                    let tyy = freevar_tysc (tyvars, y) in
                                                    MySet.union tyx tyy
                                | _ -> MySet.empty

let rec pp_ty = function  TyInt -> print_string "int"
                    | TyBool -> print_string "bool"
                    | TyVar x -> print_string ("'a" ^ string_of_int x) 
                    | TyFun (x, y) -> print_string "(" ; pp_ty x ; print_string " -> ";  pp_ty y ; print_string ")"

let fresh_tyvar = let counter = ref 0 in 
                    let body () = 
                        let v = !counter in
                            counter := v + 1 ; v in body


let rec freevar_ty = function
                          TyVar x -> MySet.singleton x
                        | TyFun (x, y) -> let tyx = freevar_ty x in
                                            let tyy = freevar_ty y in
                                                MySet.union tyx tyy
                        | _ -> MySet.empty

type exp =
    Var of id
  | ILit of int 
  | BLit of bool
  | BinOp of binOp * exp * exp
  | IfExp of exp * exp * exp
  | LetExp of id * exp * exp
  | FunExp of id * exp 
  | AppExp of exp * exp 
  | LetRecExp of id * id * exp * exp (*追加*)

type program =
    Exp of exp
    | Decl of id * exp
    | RecDecl of id * id * exp (*追加*)
    | DeclDecl of id * exp * program (*追加 Ex3.3.2*)
    | Nothing 