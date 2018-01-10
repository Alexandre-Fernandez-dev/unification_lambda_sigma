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

let rec free_var (t : term) (i : int) =
  match t with
    | Var(m) -> if m > i then 1 else 0
    | XVar(_) -> 0
    | Abs(t1) -> free_var t1 (i+1)
    | App(t1, t2) -> (free_var t1 i) + (free_var t2 i)

(*------------------------------ lsgima --------------------------------*)

type s_subst =
  | Yvar of name
  | Id
  | Shift
  | Cons of s_term * s_subst
  | Comp of s_subst * s_subst
and s_term =
  | S_One
  | S_Xvar of name
  | S_App of s_term * s_term
  | S_Abs of s_term
  | S_Tsub of s_term * s_subst

let rec s_shift_n (n : int) =
  match n with
  | 0 -> Id
  | 1 -> Shift
  | n -> Comp(Shift, s_shift_n (n-1))

let rec precooking (l_t : term) (n : int) : s_term =
  match l_t with
    | Var(k) -> S_Tsub (S_One, s_shift_n (k-1)) (* Var k *)
    | XVar(nam) -> S_Tsub (S_Xvar(nam), s_shift_n (n))
    | Abs(t1) -> S_Abs(precooking t1 (n+1))
    | App(t1, t2) -> S_App((precooking t1 n), (precooking t2 n))
