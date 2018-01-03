open Set

module StringSet = Set.Make(String)

(* TODO faire un module locally nameless *)

type ty =
  | TBool
  | TArrow of ty * ty

(* locally nameless lambda term *)
type term =
  | Bvar of int
  | Fvar of string
  | Abs  of ty * term
  | App  of term * term
  | True
  | False

(* opening of bound variable to free variable, can be implemented with opening function below *) (* TODO use types ? *)
let varopening x term =
  let rec varopening_h k x = function
    | Bvar i       -> if i = k then Fvar x else Bvar i
    | Fvar y       -> Fvar y
    | Abs (ty, t)  -> Abs (ty, (varopening_h (k+1) x t))
    | App (t1, t2) -> App ((varopening_h k x t1), (varopening_h k x t2))
    | t            -> t
  in
  varopening_h 0 x term

(* opening of bound variable to term *) (* TODO use types ? *)
let opening t term =
  let rec opening_h k tu = function
    | Bvar i       -> if i = k then tu else Bvar i
    | Fvar y       -> Fvar y
    | Abs (ty, t)  -> Abs (ty, (opening_h (k+1) tu t))
    | App (t1, t2) -> App ((opening_h k tu t1), (opening_h k tu t2))
    | t            -> t
  in
  opening_h 0 t term

(* closing of free variable *) (* TODO use types ? *)
let closing x term =
  let rec closing_h k x = function
    | Bvar i       -> Bvar i
    | Fvar y       -> if x = y then Bvar k else Fvar y
    | Abs (ty, t)  -> Abs (ty, (closing_h (k+1) x t))
    | App (t1, t2) -> App ((closing_h k x t1), (closing_h k x t2))
    | t            -> t
  in
  closing_h 0 x term

(* check valid term *) (* TODO use types ? *)
let check_locally_closed term =
  let rec check_locally_closed_h k = function
    | Bvar i       -> i < k
    | Fvar y       -> true
    | Abs (ty, t)  -> check_locally_closed_h (k+1) t
    | App (t1, t2) -> (check_locally_closed_h k t1) && (check_locally_closed_h k t2)
    | t            -> true (* constant ?? *)
  in
  check_locally_closed_h 0 term

(* set of free_vars *) (* TODO use types ? *)
let rec free_vars = function
  | Bvar i       -> StringSet.empty
  | Fvar y       -> StringSet.singleton y
  | Abs (ty, t)  -> free_vars t
  | App (t1, t2) -> StringSet.union (free_vars t1) (free_vars t2)
  | t            -> StringSet.empty

(* substitute the free variable vs with term ts *)
let rec substitute_fv vs ts = function
  | Bvar i       -> Bvar i
  | Fvar y       -> if vs = y then ts else Fvar y
  | Abs (ty, t)  -> Abs (ty, (substitute_fv vs ts t))
  | App (t1, t2) -> App ((substitute_fv vs ts t1), (substitute_fv vs ts t2))
  | t            -> t

(* new free name *)
let gensym =
  let i = ref 0 in
  incr i;
  "fvar"^(string_of_int !i)

let rec string_of_term = function
  | Bvar i       -> ("b"^(string_of_int i))
  | Fvar y       -> ("f"^y)
  | Abs (ty, t)  -> "λ.("^(string_of_term t)^")"
  | App (t1, t2) -> "("^(string_of_term t1)^")("^(string_of_term t2)^")"
  | True         -> "True"
  | False        -> "False"

let print term = print_string (string_of_term term)

exception No_Reduction

let b_reduce = function (* TODO use types ? *)
  | App (Abs (ty, t), u) -> opening u t
  | _ -> raise No_Reduction

(* EVALUATION : CALL BY VALUE *)

let is_value = function
  | Abs _ | Fvar _ | Bvar _ -> true (* Bvar ????? *)
  | _ -> false

let rec eval_cbv t =
  match t with
  | App (t1, t2) ->
    let cv1 = eval_cbv t1 in
    let cv2 = eval_cbv t2 in
    (try 
       b_reduce (App (cv1, cv2))
     with No_Reduction ->
       (print_string ("no reduc : "^(string_of_term (App(cv1,cv2)))));
       App(cv1, cv2))
  | _ -> t

let rec eval_big_cbv t =
  let et = eval_cbv t in
  if et = t then
     t
  else
    eval_big_cbv et

let test =
  App (Abs (TBool, (Bvar 0)), Fvar "lol")

(* TODO typed test *)
(*
let test2 = 
  App(
    Abs(
      App( Abs(Bvar 0), Bvar 0 )
    ),
    App( Abs( Bvar 0 ), Abs( Bvar 0) ) )
*)
let _ = print test; print_string "\n"; print (eval_cbv test); print_string "\n"

(*let _ = print test2; print_string "\n"; print (eval_big_cbv test2)*)
