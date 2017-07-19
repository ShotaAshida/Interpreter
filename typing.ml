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
                          | (d, e) :: rest -> if d = c then e else subst_type rest b )
                      | TyFun (f, g) -> TyFun ( subst_type a f, subst_type a g )
                      | _ -> b

let rec eqs_of_subst s = match s with
                          [] -> []
                        | (a, b) :: rest -> (TyVar a, b) :: (eqs_of_subst rest)

let rec subst_eqs s eqs = match eqs with 
                          [] -> [] 
                        | (a, b) :: rest -> (subst_type s a, subst_type s b) :: (subst_eqs s rest)

let rec unify a = match a with
                      [] -> []
                    | x :: rest -> match x with 
                                            (TyInt , TyInt) -> unify rest
                                          | (TyBool, TyBool) -> unify rest
                                          | (TyVar a, TyInt) -> unify ( subst_eqs [(a, TyInt)] rest ) @ [ (a, TyInt) ]
                                          | (TyVar a, TyBool) -> unify ( subst_eqs [(a, TyBool)] rest ) @ [ (a, TyBool) ]
                                          | (TyVar a, TyFun(b, c)) -> let varlist = freevar_ty (TyFun (b, c)) in
                                                                      if MySet.member a varlist then err("can't unify") 
                                                                      else unify ( subst_eqs [(a, TyFun(b, c))] rest ) @ [(a, TyFun(b, c))]
                                          | (TyInt, TyVar a) -> unify ( subst_eqs [(a, TyInt)] rest ) @ [ (a, TyInt) ]
                                          | (TyBool, TyVar a) -> unify ( subst_eqs [(a, TyBool)] rest ) @ [ (a, TyBool) ]
                                          | (TyFun(a, b), TyVar c) -> let varlist = freevar_ty (TyFun (a, b)) in
                                                                      if MySet.member c varlist then err("can't unify") 
                                                                      else unify ( subst_eqs [(c, TyFun(a,b))] rest ) @ [ (c, TyFun(a,b)) ]
                                          | (TyFun (x1, y1), TyFun (x2, y2)) -> unify( (x1 , x2) :: (y1 ,y2) :: rest )
                                          | (TyVar a, TyVar b) -> unify ( subst_eqs [(a, TyVar b)] rest ) @ [ (a, TyVar b) ]
                                          | (_, _) -> []






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
      (try ([], Environment.lookup x tyenv) with
          Environment.Not_bound -> err ("variable not bound: " ^ x))
  | ILit _ -> ([], TyInt)
  | BLit _ -> ([], TyBool)
  | BinOp (op, exp1, exp2) ->
      let (s1,ty1) = ty_exp tyenv exp1 in
      let (s2,ty2) = ty_exp tyenv exp2 in      
      let (eqs3, ty) = ty_prim op ty1 ty2 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 in
      let s3 = unify eqs in (s3, subst_type s3 ty)
  | IfExp (exp1, exp2, exp3) ->
      (match ty_exp tyenv exp1 with
          (sub1, TyBool) ->
                          let (s1, ty1) = ty_exp tyenv exp2 in
                          let (s2, ty2) = ty_exp tyenv exp3 in
                          let s3 = (eqs_of_subst s1) @ (eqs_of_subst s2) in
                          let eqs1 = unify s3 in
                          let ty3 = subst_type eqs1 ty1 in
                          let ty4 = subst_type eqs1 ty2 in
                              (match ty3, ty4 with
                                  TyInt, TyInt -> ( eqs1, ty3 )
                                | TyBool, TyBool -> (eqs1, ty3)
                                | TyVar p, TyVar q -> let eqs2 = unify ( eqs_of_subst ((q, TyVar p) :: eqs1) )
                                                        in (eqs2, subst_type eqs2 ty3)
                                | TyInt, TyVar p -> let eqs2 = unify ( eqs_of_subst ((p, TyInt) :: eqs1) )
                                                        in (eqs2, TyInt)
                                | TyBool, TyVar p -> let eqs2 = unify ( eqs_of_subst ((p, TyBool) :: eqs1) )
                                                        in (eqs2, TyBool)
                                | TyFun(a, b), TyVar p -> let eqs2 = unify ( eqs_of_subst ((p, ty3) :: eqs1) )
                                                        in (eqs2, ty3)
                                | TyVar p, TyInt -> let eqs2 = unify ( eqs_of_subst ((p, ty4) :: eqs1) )
                                                        in (eqs2, ty4)
                                | TyVar p, TyBool -> let eqs2 = unify ( eqs_of_subst ((p, ty4) :: eqs1) )
                                                        in (eqs2, ty4)
                                | TyVar p, TyFun (a, b) -> let eqs2 = unify ( eqs_of_subst ((p, ty4) :: eqs1) )
                                                        in (eqs2, ty4)
                                | TyFun (a, b), TyFun (c, d) -> let eqs3 = unify ((a, c) :: (b, d) :: s3) in
                                                                  (eqs3, ty3)

                                | _, _ -> err("エラーだよ")
                              )
        | (sub1, TyVar a) ->
                              let s = eqs_of_subst (( a, TyBool ):: sub1) in
                              let (s1, ty1) = ty_exp tyenv exp2 in
                              let (s2, ty2) = ty_exp tyenv exp3 in
                              let s3 = (eqs_of_subst s1) @ (eqs_of_subst s2) @ s in
                              let eqs1 = unify s3 in
                              let ty3 = subst_type eqs1 ty1 in
                              let ty4 = subst_type eqs1 ty2 in
                                  (match ty3, ty4 with
                                      TyInt, TyInt -> ( eqs1, ty3 )
                                    | TyBool, TyBool -> (eqs1, ty3)
                                    | TyVar p, TyVar q -> let eqs2 = unify ( eqs_of_subst ((q, TyVar p) :: eqs1) )
                                                            in (eqs2, subst_type eqs2 ty3)
                                    | TyInt, TyVar p -> let eqs2 = unify ( eqs_of_subst ((p, TyInt) :: eqs1) )
                                                            in (eqs2, TyInt)
                                    | TyBool, TyVar p -> let eqs2 = unify ( eqs_of_subst ((p, TyBool) :: eqs1) )
                                                            in (eqs2, TyBool)
                                    | TyFun(a, b), TyVar p -> let eqs2 = unify ( eqs_of_subst ((p, ty3) :: eqs1) )
                                                            in (eqs2, ty3)
                                    | TyVar p, TyInt -> let eqs2 = unify ( eqs_of_subst ((p, ty4) :: eqs1) )
                                                            in (eqs2, ty4)
                                    | TyVar p, TyBool -> let eqs2 = unify ( eqs_of_subst ((p, ty4) :: eqs1) )
                                                            in (eqs2, ty4)
                                    | TyVar p, TyFun (a, b) -> let eqs2 = unify ( eqs_of_subst ((p, ty4) :: eqs1) )
                                                            in (eqs2, ty4)
                                    | TyFun (a, b), TyFun (c, d) -> let eqs3 = unify ((b, d) :: (a, c) :: (b, d) :: s3) in
                                                                      (eqs3, subst_type eqs3 ty3)
                                    | _, _ -> err("エラーだよ")
                                    )
        | (_,_) -> err("ifExp Not Implemented!3")
      )

  | LetExp (id, exp1, exp2) -> let (a, b) = (ty_exp tyenv exp1) in
                                  let (c, d) = ty_exp (Environment.extend id b tyenv) exp2 in
                                    let s = unify( eqs_of_subst (c @ a) ) in
                                    (s, subst_type s d )



  | FunExp (id, exp) -> 
    let domty = TyVar (fresh_tyvar ()) in
    let s, ranty =
      ty_exp (Environment.extend id domty tyenv) exp in
       (s, TyFun (subst_type s domty, ranty))
  | AppExp (exp1, exp2) ->  let (s1, ty1) = ty_exp tyenv exp1 in
                            let (s2, ty2) = ty_exp tyenv exp2 in
                            let s3 = unify (eqs_of_subst (s1 @ s2) ) in
                            let ty3 = subst_type s3 ty1 in
                            let ty4 = subst_type s3 ty2 in
                            (match ty3, ty4 with
                                TyFun (TyInt, b) , TyInt -> ( s3, b )
                              | TyFun (TyBool, b) , TyBool -> ( s3, b )
                              | TyFun (TyVar a, b) , c -> let d = unify (eqs_of_subst ((a, c) :: s3) ) in (d, subst_type d b)
                              | TyFun (TyFun (a, b), c), d -> let e = unify ( (TyFun (a,b), d) :: eqs_of_subst s3) in (e, subst_type e c)
                              | TyVar a, TyVar b -> let c = fresh_tyvar () in
                                                    let d = unify (eqs_of_subst (( a, TyFun (TyVar b,  TyVar c) ):: s3)) in
                                                      ( d , subst_type d (TyVar c) )
                              | TyVar a, TyFun (c, d) -> let p = fresh_tyvar() in
                                                                      let q = unify (eqs_of_subst ((a, TyFun (TyFun (c, d), TyVar p)) :: s3)) in
                                                                        ( q , subst_type q (TyVar p) )
                              | TyVar a, TyBool -> let p = fresh_tyvar() in
                                                    let q = unify (eqs_of_subst ( (a, TyFun (TyBool, TyVar p)) :: s3)) in
                                                      (q, subst_type q (TyVar p))

                              | TyVar a, TyInt -> let p = fresh_tyvar() in
                                                  let q = unify (eqs_of_subst ((a, TyFun (TyInt , TyVar p)) :: s3)) in
                                                    (q, subst_type q (TyVar p))
                              | _, _ -> err ("AppExpEror") 
                              )
  | _ -> err ("ty_exp Not Implemented!")

let ty_decl tyenv = function
    Exp e -> let (_, v) = ty_exp tyenv e in (v, tyenv)
  | Decl (x, e) -> let (_, v) = ty_exp tyenv e in (v, Environment.extend x v tyenv)
  | _ -> err ("ty_decl Not Implemented!")