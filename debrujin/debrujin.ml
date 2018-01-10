type name = string

let eq_name n1 n2 = (n1 = n2)

type term =
    | Var  of int
    | XVar of name
    | Abs  of term
    | App  of term * term

let rec height (t : term) (n : int) =
  match t with
    | Var(_) -> n
    | XVar(_) -> n
    | Abs(t) -> height t (n+1)
    | App(t1, t2) -> max (height t1 n) (height t2 n)

                   
let rec lift (t : term) (i : int) =
  match t with
    | Var(n) -> if n > i then Var(n+1) else t
    | XVar(_) -> t
    | Abs(t) -> Abs(lift t (i+1))
    | App(t1, t2) -> App((lift t1 i), (lift t2 i))

let lift_plus (t : term) = lift t 0

let rec subst (a: term) (b: term) (n: int) =
  match a with
    | Var(m) -> if m > n then Var(n-1)
      else (if n = m then b else Var(m))
    | XVar(_) -> a
    | Abs(t1) -> Abs(subst t1 (lift_plus b) (n+1))
    | App(t1, t2) -> App((subst t1 b n), (subst t2 b n))

let beta_red (t: term) =
  match t with
  | App(Abs(a), b) -> subst a b 1
  | _ -> t


