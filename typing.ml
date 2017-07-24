open Syntax
exception Error of string
let err s = raise (Error s)

(* Type Environment *)
type tyenv = tysc Environment.t

type subst = (tyvar * ty) list

let rec subst_type a b = match b with
                        TyVar c ->
                          (match a with
                              [] -> b
                            | (d, e) :: rest -> if d = c then subst_type a e else subst_type rest b )
                      | TyFun (f, g) -> TyFun ( subst_type a f, subst_type a g )
                      | _ -> b

let rec eqs_of_subst s = match s with
                          [] -> []
                        | (a, b) :: rest -> (TyVar a, b) :: (eqs_of_subst rest)

let rec subst_eqs s eqs = match eqs with
                          [] -> [] 
                        | (a, b) :: rest -> (subst_type s a, subst_type s b) :: (subst_eqs s rest)


(* let rec freevar_tysc tysc = let tyvars, ty = tysc in
                            match ty with
                                  TyVar x -> if MySet.member ty tyvars then MySet.empty
                                                else MySet.singleton x
                                | TyFun(x, y) -> let tyx = freevar_tysc (tyvars, x) in
                                                    let tyy = freevar_tysc (tyvars, y) in
                                                    MySet.union tyx tyy
                                | _ -> MySet.empty *)



let rec freevar_tyenv (tyenv :tysc Environment.t) = let f v a = 
                                                      (match v with
                                                          TyScheme(tyvars, _) -> MySet.union (MySet.from_list tyvars) a
                                                        | _ -> err("Error of freevar_tyenv\n")) in
                                                    Environment.fold_right f tyenv (MySet.empty)

let closure ty tyenv subst =
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
        (fun id -> freevar_ty (subst_type subst (TyVar id)))
        fv_tyenv') in
  let ids = MySet.diff (freevar_ty ty) fv_tyenv in
    TyScheme (MySet.to_list ids, ty)

let rec unify a = 
  match a with
      [] -> []
    | x :: rest -> 
        match x with 
            (TyInt , TyInt) -> unify rest
          | (TyBool, TyBool) -> unify rest
          | (TyVar tyvar, TyInt) -> [ (tyvar, TyInt) ] @ unify ( subst_eqs [(tyvar, TyInt)] rest )
          | (TyVar tyvar, TyBool) -> [ (tyvar, TyBool) ] @ unify ( subst_eqs [(tyvar, TyBool)] rest )
             | (TyVar tyvar, TyFun(b, c)) -> let varlist = freevar_ty (TyFun (b, c)) in
                                      if MySet.member tyvar varlist then err("can't unify") 
                                       else  [(tyvar, TyFun(b, c))] @ unify ( subst_eqs [(tyvar, TyFun(b, c))] rest )    
          | (TyInt, TyVar tyvar) -> [ (tyvar, TyInt) ] @ unify ( subst_eqs [(tyvar, TyInt)] rest )
          | (TyBool, TyVar tyvar) -> [ (tyvar, TyBool) ] @ unify ( subst_eqs [(tyvar, TyBool)] rest )
          | (TyFun(a, b), TyVar tyvar) -> let varlist = freevar_ty (TyFun (a, b)) in
                                      if MySet.member tyvar varlist then err("can't unify") 
                                      else  [ (tyvar, TyFun(a,b)) ] @ unify ( subst_eqs [(tyvar, TyFun(a,b))] rest )
          | (TyFun (x1, y1), TyFun (x2, y2)) -> unify( [(x1, x2) ; (y1, y2)] @ rest)
          | (TyVar tyvar, TyVar b) -> if (tyvar = b) then unify rest else
                                  [ (tyvar, TyVar b) ] @ unify ( subst_eqs [(tyvar, TyVar b)] rest ) 
          | (_, _) -> err ("can't unify")


let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt )
  | Minus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt )
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt )
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool )
  | Equal -> ([(ty1, TyInt); (ty2, TyInt)], TyBool )
  | And -> ([(ty1, TyBool); (ty2, TyBool)] , TyBool)
  | Or -> ([(ty1, TyBool); (ty2, TyBool)] , TyBool)
  | Cons -> err "ty_prim Not Implemented!"

let rec ty_exp tyenv = function
    Var x ->
      (try 
       let TyScheme (vars, ty) = Environment.lookup x tyenv in
        let s = List.map (fun id -> (id, TyVar (fresh_tyvar ())))
          vars in  ([], subst_type s ty)
        with Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit _ -> ([], TyInt)
  | BLit _ -> ([], TyBool)
  | BinOp (op, exp1, exp2) ->
      let (s1,ty1) = ty_exp tyenv exp1 in
      let (s2,ty2) = ty_exp tyenv exp2 in
      let (eqs3, ty) = ty_prim op ty1 ty2 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 in
      let s3 = unify eqs in (s3, subst_type s3 ty)
  | IfExp (exp1, exp2, exp3) ->
      let (s1, ty1) = ty_exp tyenv exp1 in
      let (s2, ty2) = ty_exp tyenv exp2 in
      let (s3, ty3) = ty_exp tyenv exp3 in
      let eqs1 = eqs_of_subst s1 in
      let eqs2 = eqs_of_subst s2 in
      let eqs3 = eqs_of_subst s3 in
      let eqs = eqs1 @ eqs2 @ eqs3 @ [(ty2, ty3) ; (ty1, TyBool)] in
      let s4 = unify eqs in (s4, subst_type s4 ty2)


  | LetExp (id, exp1, exp2) ->  let (a, b) = ty_exp tyenv exp1 in
                                let tysc = closure b tyenv a in
                                let (c, d) = ty_exp (Environment.extend id tysc tyenv) exp2 in
                                  let s = unify( eqs_of_subst (c @ a) ) in (s, subst_type s d )

  | FunExp (id, exp) -> 
    let domty = 
      let newvar = fresh_tyvar () in
                  TyVar newvar in
      let s, ranty =
        ty_exp (Environment.extend id (TyScheme( [], domty )) tyenv) exp in
        (s, TyFun (subst_type s domty, ranty))

  | AppExp (exp1, exp2) ->  let (s1, ty1) = ty_exp tyenv exp1 in
                            let (s2, ty2) = ty_exp tyenv exp2 in
                            let eqs1 = eqs_of_subst s1 in
                            let eqs2 = eqs_of_subst s2 in
                            let midty1 = TyVar (fresh_tyvar()) in
                            let midty2 = TyVar (fresh_tyvar()) in
                            let eqs = eqs1 @ eqs2 @ [ (TyFun (midty1, midty2) , ty1) ; (midty1, ty2) ] in
                            let s3 = unify eqs in (s3, subst_type s3 midty2)

  | _ -> err ("ty_exp Not Implemented!")

let ty_decl tyenv = function
    Exp e -> let (_, v) = ty_exp tyenv e in (v, tyenv)
  | Decl (x, e) -> let (subst, v) = ty_exp tyenv e in
                    let tysc = closure v tyenv subst in (v, Environment.extend x tysc tyenv)
  | DeclDecl (id, e1, e2) -> let (subst, v) = ty_exp tyenv e1 in
                                let tysc = closure v tyenv subst in (v, Environment.extend id tysc tyenv)
  | _ -> err ("ty_decl Not Implemented!")