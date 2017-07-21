open Syntax
exception Error of string
let err s = raise (Error s)

(* Type Environment *)
type tyenv = ty Environment.t

type subst = (tyvar * ty) list

let rec subst_type a b = match b with
                        TyVar c ->
                        (match a with
                          [] -> b
                          | x :: rest -> let (d, e) = x in if d = c then TyVar e else subst_type rest b )
                      | TyFun (f, g) -> TyFun ( subst_type a f, subst_type a g )
                      | _ -> b





let ty_prim op ty1 ty2 = match op with
    Plus -> (match ty1, ty2 with
                 TyInt, TyInt -> TyInt
               | _ -> err ("Argument must be of integer: +"))
  | Minus -> (match ty1, ty2 with
                  TyInt, TyInt -> TyInt
                |  _ -> err ("Argument must be of integer: +"))
  | Mult -> (match ty1, ty2 with
                  TyInt, TyInt -> TyInt
                |  _ -> err ("Argument must be of integer: +"))
  | Lt -> (match ty1, ty2 with
                  TyInt, TyInt -> TyBool
                |  _ -> err ("Argument must be of integer: +"))
  | Equal -> (match ty1, ty2 with
                  TyInt, TyInt -> TyInt
                |  _ -> err ("Argument must be of integer: +"))
  | And -> (match ty1, ty2 with
                  TyBool, TyBool -> TyBool
                | _ -> err ("Argument must be of boolean: +"))
  | Or -> (match ty1, ty2 with
                  TyBool, TyBool -> TyBool
                | _ -> err ("Argument must be of boolean: +"))
  | Cons -> err "ty_prim Not Implemented!"


let rec ty_exp tyenv = function
    Var x ->
      (try Environment.lookup x tyenv with
          Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit _ -> TyInt
  | BLit _ -> TyBool
  | BinOp (op, exp1, exp2) ->
      let tyarg1 = ty_exp tyenv exp1 in
      let tyarg2 = ty_exp tyenv exp2 in
        ty_prim op tyarg1 tyarg2
  | IfExp (exp1, exp2, exp3) ->
      let tyarg0 = ty_exp tyenv exp1 in
      if tyarg0 = TyBool then
      (let tyarg1 = ty_exp tyenv exp2 in
      let tyarg2 = ty_exp tyenv exp3 in
        if tyarg1 = tyarg2 then tyarg1 else err("ifExp Not Implemented!"))
      else err ("Not Bool") 
  | LetExp (id, exp1, exp2) -> let tyarg = ty_exp tyenv exp1 in
  						                  ty_exp (Environment.extend id tyarg tyenv) exp2
  | _ -> err ("ty_exp Not Implemented!")

let ty_decl tyenv = function
    Exp e -> (ty_exp tyenv e, tyenv)
  | Decl (x, e) -> let v = ty_exp tyenv e in (v, Environment.extend x v tyenv)
  | _ -> err ("ty_decl Not Implemented!")