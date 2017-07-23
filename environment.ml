type 'a t = (Syntax.id * 'a) list

exception Not_bound

let empty = []
let extend x v env = (x,v)::env

let rec lookup x env = 
  try List.assoc x env with Not_found -> raise Not_bound

let rec map f = function
    [] -> []
  | (id, v)::rest -> (id, f v) :: map f rest

let rec fold_right f env a =
  match env with
      [] -> a
    | (_, v)::rest -> f v (fold_right f rest a)

let rec get_var tyenv = match tyenv with
                            [] -> MySet.empty
                          | (_, v) :: rest -> let (tyvars, ty) = v in MySet.union (MySet.singleton ty) (get_var rest)
