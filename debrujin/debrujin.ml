type name = string

let eq_name n1 n2 = (n1 = n2)

(* types *)
type ty =
  | K of name
  | Arrow of ty * ty

(* new type generator *)
let gen_type =
  let v = ref 0 in
  incr v;
  K (string_of_int !v)

let rec eq_typ t1 t2 =
  match t1, t2 with
  | K (n1), K (n2) -> eq_name n1 n2
  | Arrow (ty11, ty12), Arrow (ty21, ty22) ->
    eq_typ ty11 ty21 && eq_typ ty12 ty22
  | _ -> false

(* typing context *)
type context = ty list

let get_type_c i c = List.nth c (i-1)

(* lambda terms *)
type term =
  | Var  of int
  | XVar of name
  | Abs  of ty * term
  | App  of term * term

(* lambda height *)
let rec height (t : term) (n : int) =
  match t with
  | Var(_) -> n
  | XVar(_) -> n
  | Abs(ty, t) -> height t (n+1)
  | App(t1, t2) -> max (height t1 n) (height t2 n)

let rec lift (t : term) (i : int) =
  match t with
  | Var(n) -> if n > i then Var(n+1) else t
  | XVar(_) -> t
  | Abs(ty, t) -> Abs(ty, lift t (i+1))
  | App(t1, t2) -> App((lift t1 i), (lift t2 i))

(* lift (up arrow) operation : increments free de brujin indices *)
let lift_plus (t : term) = lift t 0

(* substitution for beta reduction *)
let rec subst (a: term) (b: term) (n: int) =
  match a with
  | Var(m) -> if m > n then Var(n-1)
    else (if n = m then b else Var(m))
  | XVar(_) -> a
  | Abs(ty, t1) -> Abs(ty, subst t1 (lift_plus b) (n+1))
  | App(t1, t2) -> App((subst t1 b n), (subst t2 b n))

(* beta reduction *)
let beta_red (t: term) =
  match t with
  | App(Abs(ty, a), b) -> subst a b 1
  | _ -> t

(* count free variables *)
let rec free_var (t : term) (i : int) =
  match t with
  | Var(m) -> if m > i then 1 else 0
  | XVar(_) -> 0
  | Abs(ty, t1) -> free_var t1 (i+1)
  | App(t1, t2) -> (free_var t1 i) + (free_var t2 i)

(*------------------------------ lsgima --------------------------------*)

(* lambda sigma substitutions and terms *)
type s_subst =
  (*| Yvar of name *)
  | Id
  | Shift
  | Cons of s_term * s_subst
  | Comp of s_subst * s_subst
and s_term =
  | S_One
  | S_Xvar of name
  | S_App of s_term * s_term
  | S_Abs of ty * s_term
  | S_Tsub of s_term * s_subst

(* n number : One lifted (n-1) times *)
let rec s_shift_n (n : int) =
  match n with
  | 0 -> Id
  | 1 -> Shift
  | n -> Comp(Shift, s_shift_n (n-1))

(* lambda terms to lambda sigma terms *)
let rec precooking (l_t : term) (n : int) : s_term =
  match l_t with
  | Var(k) -> S_Tsub (S_One, s_shift_n (k-1)) (* Var k *)
  | XVar(nam) -> S_Tsub (S_Xvar(nam), s_shift_n (n))
  | Abs(ty, t1) -> S_Abs(ty, precooking t1 (n+1))
  | App(t1, t2) -> S_App((precooking t1 n), (precooking t2 n))

exception No_unshift

(* for eta : need to reverse shift operation *)
let rec unshift_s (t : s_term) = (* not sure what i am doing here *)
  match t with
  | S_One          -> raise No_unshift
  | S_Xvar (n)     -> S_Xvar (n)
  | S_App (t1, t2) -> S_App (unshift_s t1, unshift_s t2)
  | S_Abs (ty, t)  -> S_Abs (ty, unshift_s t)
  | S_Tsub (t, s)  -> S_Tsub (t, (unshift_sub_s s))
and unshift_sub_s (s : s_subst) =
  match s with
  | Id            -> Id
  | Shift         -> Id
  | Cons (t, s)   -> Cons (t, s)
  | Comp (s1, s2) -> if s2 = Shift
                     then s1
                     else unshift_sub_s s2

(* check if term is a de brujin indice *)
let rec is_number t =
  match t with
  | S_One         -> true
  | S_Tsub (t, s) -> if s = Shift
                     then is_number t
                     else if t = S_One
                          then is_shift_n s
                          else false
  | _ -> false
and is_shift_n s =
  match s with
  | Shift         -> true
  | Comp (s1, s2) -> (is_shift_n s1) && (is_shift_n s2)
  | _ -> false

let add_option_i o1 i =
  match o1 with
  | Some (n) -> Some (n+i)
  | None -> None

let add_option o1 o2 =
  match o1,o2 with
  | Some (n1), Some (n2) -> Some (n1+n2)
  | _ -> None

(* get the integer corresponding to a term representing a de brujin indice *)
let rec get_number t =
  match t with
  | S_One         -> Some(1)
  | S_Tsub (t, s) -> if s = Shift
                     then add_option_i (get_number t) 1
                     else if t = S_One
                          then add_option_i (count_shift s) 1
                          else None
  | _ -> None
and count_shift s =
  match s with
  | Shift         -> Some(1)
  | Comp (s1, s2) -> add_option (count_shift s1) (count_shift s2)
  | _ -> None

(* pretty print *)
let rec print_sigma_term t =
  match t with
  | S_One          -> print_string "1"
  | S_Xvar (n)     -> print_string n
  | S_Abs (ty, t)  -> print_string "λ.( "; print_sigma_term t;
                      print_string " )"
  | S_App (t1, t2) -> print_string "( "; print_sigma_term t1;
                      print_string " ";
                      print_sigma_term t2; print_string " )"
  | S_Tsub (t1, s) -> let o_i = get_number t in
                      match o_i with
                        | None ->
                          print_string "( ";
                          print_sigma_term t1; print_string " [ ";
                          print_sigma_subst s; print_string " ] )"
                        | Some (i) ->
                          print_int i
and print_sigma_subst s =
  match s with
  | Id             -> print_string "id"
  | Shift          -> print_string "↑"
  | Cons (t1, s2)  -> print_sigma_term t1;
                      print_string "."; print_sigma_subst s2
  | Comp (s1, s2)  -> print_sigma_subst s1;
                      print_string "∘"; print_sigma_subst s2

(* reduction rules *)
let beta_red_s (t: s_term) =
  match t with
  | S_App (S_Abs (ty, a), b) -> S_Tsub (a, Cons (b, Id))
  | _ -> t

let app_red_s (t: s_term) =
  match t with
  | S_Tsub (S_App (a,b), s) -> S_App (S_Tsub (a,s), S_Tsub (b,s))
  | _ -> t

let varcons_red_s (t: s_term) =
  match t with
  | S_Tsub (S_One, Cons (a,b)) -> a
  | _ -> t

let id_red_s (t: s_term) =
  match t with
  | S_Tsub (a, Id) -> a
  | _ -> t

let abs_red_s (t: s_term) =
  match t with
  | S_Tsub (S_Abs (ty, a), s) -> S_Abs (ty, S_Tsub (a, Cons (S_One, Comp (s, Shift))))
  | _ -> t

let clos_red_s (t: s_term) =
  match t with
  | S_Tsub (S_Tsub (a,s),t) -> S_Tsub (a, Comp (s,t))
  | _ -> t

let idl_red_s (s: s_subst) =
  match s with
  | Comp (Id, s1) -> s1
  | _ -> s

let shiftcons_red_s (s: s_subst) =
  match s with
  | Comp (Shift, Cons (a,s1)) -> s1
  | _ -> s

let assenv_red_s (s: s_subst) =
  match s with
  | Comp (Comp (s1, s2), s3) -> Comp (s1, Comp (s2,s3))
  | _ -> s

let mapenv_red_s (s: s_subst) =
  match s with
  | Comp (Cons (a,s1),t) -> Cons (S_Tsub (a,t), Comp (s1,t))
  | _ -> s

let idr_red_s (s: s_subst) =
  match s with
  | Comp (s1, Id) -> s1
  | _ -> s

let varshift_red_s (s: s_subst) =
  match s with
  | Cons (S_One, Shift) -> Id
  | _ -> s

let scons_red_s (s: s_subst) =
  match s with
  | Cons (S_Tsub (S_One, s1), Comp (Shift, s2)) -> if s1 = s2 then s1 else s
  | _ -> s

let eta_red_s (t: s_term) =
  match t with
  | S_Abs (ty, S_App(a, S_One)) -> unshift_s a
  | _ -> t

(* All reduction rules for terms *)
let reduce_term_s (t : s_term) =
  match t with
  | S_Tsub (S_App (a,b), s) -> S_App (S_Tsub (a,s), S_Tsub (b,s))
  | S_Tsub (S_One, Cons (a,b)) -> a
  | S_Tsub (a, Id) -> a
  | S_Tsub (S_Abs (ty, a), s) -> S_Abs (ty, S_Tsub (a, Cons (S_One, Comp (s, Shift))))
  | S_Tsub (S_Tsub (a,s),t) -> S_Tsub (a, Comp (s,t))
  | _ -> t

(* All reduction rules for subst *)
let reduce_subst_s (s : s_subst) =
  match s with
  | Comp (Id, s1) -> s1
  | Comp (Shift, Cons (a,s1)) -> s1
  | Comp (Comp (s1, s2), s3) -> Comp (s1, Comp (s2,s3))
  | Comp (Cons (a,s1),t) -> Cons (S_Tsub (a,t), Comp (s1,t))
  | Comp (s1, Id) -> s1
  | Cons (S_One, Shift) -> Id
  | Cons (S_Tsub (S_One, s1), Comp (Shift, s2)) -> if s1 = s2 then s1 else s
  | _ -> s

(* Attempt to leftmost outermost application of function on lambda sigma *)
let rec transform_term (t : s_term) (f : s_term -> s_term) (g : s_subst -> s_subst) : s_term =
  let transformed_term = f t in
  match transformed_term with
    | S_One          -> S_One
    | S_Xvar (n)     -> S_Xvar (n)
    | S_Abs (ty, t)  -> S_Abs (ty, transform_term t f g)
    | S_App (t1, t2) -> let leftmost = transform_term t1 f g in
                        if leftmost = t1
                        then S_App (t1, transform_term t2 f g)
                        else S_App (transform_term leftmost f g, t2)
    | S_Tsub (t1, s) -> S_Tsub (transform_term t1 f g, transform_subst s f g)
and transform_subst (s : s_subst) (f : s_term -> s_term) (g : s_subst -> s_subst) : s_subst =
  let transformed_subst = g s in
  match transformed_subst with
    | Id            -> Id
    | Shift         -> Shift
    | Cons (t1, s2) -> Cons (transform_term t1 f g, transform_subst s2 f g)
    | Comp (s1, s2) -> let leftmost = transform_subst s1 f g in
                       if leftmost = s1
                       then Comp (s1, transform_subst s2 f g)
                       else Comp (transform_subst leftmost f g, s2)

(* normalisation with lambda calculus *)
let rec normalise_beta_eta (t : s_term) =
  let reduced = transform_term t (beta_red_s) (fun x -> x) in
  let reduced = transform_term reduced (eta_red_s) (fun x -> x) in
  if reduced <> t then
    normalise_beta_eta reduced
  else
    reduced

(* term and subst rewriting for sigma calculus *)
let rec normalise_sigma (t : s_term) =
    let reduced = transform_term t reduce_term_s reduce_subst_s in
    if reduced <> t then
      normalise_sigma reduced
    else
      reduced

(* normalisation for lambda sigma calculus *)
let rec normalise_lambda_sigma (t : s_term) =
  let reduced = normalise_beta_eta t in
  let reduced = normalise_sigma reduced in
  let reduced = normalise_beta_eta reduced in
  if reduced <> t then
    normalise_lambda_sigma reduced
  else
    reduced

let two = S_Tsub (S_One, Shift)

let three = S_Tsub (two, Shift)

let four = S_Tsub (three, Shift)

let test = S_App (three, S_Tsub (S_App ( four, S_Xvar ("H1") ), Cons (S_One, Id ) ) )

let () = print_sigma_term test; print_string "\n"; print_sigma_term (normalise_lambda_sigma test)

(* number of arrow in a type *)
let rec length_type (t : ty) =
  match t with
  | K(n) -> 1
  | Arrow(t1, t2) -> length_type t1 + length_type t2
(* FIXME : maybe wrong for getting "toplevel" arrow chain size, cf. number of Ai for long normal form p. 19 dowek1 *)

exception No_inference

let rec type_check_inf c t_term =
  match t_term with
  | S_One -> get_type_c 1 c
  | S_Xvar(n) -> K(n) (* FIXME : Not really sure about this one, should be an unique type Tx AND an unique context Cx, cf. dowek1 p18*)
  | S_Abs(ty_abs, te_abs) ->
    type_check_inf (ty_abs::c) te_abs
  | S_App(a, b) -> let ty_A = type_check_inf c b in
    let ty_arr = type_check_inf c a in
    (match ty_arr with
     | Arrow(ty_A2, ty_B) -> if eq_typ ty_A ty_A2 then ty_B else raise No_inference
     | _ -> raise No_inference)
  | S_Tsub(t, s) -> let c_s = type_check_cont c s in
    type_check_inf c_s t 
and type_check_cont c t_sub =
  match t_sub with
  (*| Yvar(n)      -> *) (* TODO : Do not remember why this variant was added. Removed for the moment *)
  | Id           -> c
  | Shift        -> (match c with
      | []     -> raise No_inference
      | hd::tl -> tl)
  | Cons(t, s)   -> let c_s = type_check_cont c s in
    let ty_t = type_check_inf c t in
    ty_t::c_s
  | Comp(s1, s2) -> let c_s2 = type_check_cont c s2 in
    type_check_cont c_s2 s1 


(* eta long normal form *)
(* auxialiary function to get the last type before the returning type of a type *)
(* the first element of the returning pair is the type you wan't and the second is the type without the result that you get *) 
let rec get_before_last_type (typ : ty) : (ty*ty) =
  match typ with
  | K n -> failwith "TODO make a good comment to say it's not possible :p"
  | Arrow (ty1,K n) -> (ty1, K n)
  | Arrow (ty1,ty2) -> let (ret1,ret2) =  get_before_last_type ty2 in
                       (ret1,Arrow (ty1,ret2))
                       
(* dans cette fonction on considère que l'on appel avec un terme qui à est déja sous normale forme 
c'est pour ça par exemple quand dans le cas de S_Tsub on ne traite que le cas où le terme de gauche est une variable existentielle *)
let rec eta_long_normal_form (t : s_term) (typ : ty): s_term =
  match t with
  | S_One | S_Xvar _ -> t
  | S_App (t1,t2) -> let (ty,rest) = get_before_last_type typ in
                     let left = (match t1 with
                       | S_One -> S_Tsub (S_One,(s_shift_n 2))
                       | S_Tsub(S_One,s1) -> S_Tsub(S_One,Comp(Shift,s1))
                       | S_Tsub(S_Xvar n,s1) -> failwith "aussi"
                       | _ -> failwith "eta_long_normal_form can't happend you should be in normal form") in
                     let right = eta_long_normal_form (normalise_lambda_sigma (S_Tsub(t2,(s_shift_n 1)))) rest in 
                     S_Abs(left,right)
  | S_Abs (ty1,t1) ->
     S_Abs(ty1,eta_long_normal_form t1 )
  | S_Tsub (t1,s1) -> (match t1 with
                       | S_Xvar n -> failwith "celle la on vas la faire"
                       | _ -> failwith "eta_long_normal_form can't happend")
                        
                                       
