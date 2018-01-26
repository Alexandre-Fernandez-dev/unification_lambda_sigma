type terminal =
| Success
| Failure

type equationsys =
| Eq of s_term * s_term
| SysEq of equationsys * equationsys
| NotAnEq

type simplresult = 
| Term of terminal
| Sys of equationsys

let rec extract_head ( t1 : s_term ) : s_term =
	match t1 with
	| S_Abs (ty, t) -> extract_head (t)
	| S_App (t2, t3) -> t2
	| _ -> t1

let rec is_rigid_rigid ( t1 : s_term ) ( t2 : s_term ) : bool =
	if (is_number(extract_head (t1))&&is_number(extract_head (t2))) then true else false

let rec is_flexible_rigid ( t1 : s_term ) ( t2 : s_term ) : bool =
	if ((!is_number(extract_head (t1))&&is_number(extract_head (t2)))||(!is_number(extract_head (t1))&&is_number(extract_head (t2)))) then true else false

let rec is_flexible_flexible ( t1 : s_term ) ( t2 : s_term ) : bool =
	if (!is_number(extract_head (t1))&&!is_number(extract_head (t2))) then true else false

let rec contains_rigid_rigid (s : equationsys) : boolean =
	match s with
	| Eq (t1, t2) -> is_rigid_rigid (t1, t2)
	| SysEq (s1, s2) -> contains_rigid_rigid (s1) || cotains_rigid_rigid (s2)

let rec contains_flexible_rigid (s : equationsys) : boolean =
	match s with
	| Eq (t1, t2) -> is_flexible_rigid (t1, t2)
	| SysEq (s1, s2) -> contains_flexible_rigid (s1) || cotains_flexible_rigid (s2)

let rec contains_flexible_flexible (s : equationsys) : boolean =
	match s with
	| Eq (t1, t2) -> is_flexible_flexible (t1, t2)
	| SysEq (s1, s2) -> contains_flexible_flexible (s1) || cotains_rigid_rigid (s2)

let rec get_rigid_rigid (s : equationsys) : equationsys =
	match s with
	| Eq (t1, t2) -> if is_rigid_rigid (t1, t2) then Eq(t1,t2) else NotAnEq
	| SysEq (s1, s2) -> if contains_rigid_rigid (s1) then get_rigid_rigid (s1) else if contains_rigid_rigid(s2) then get_rigid_rigid (s2) else NotAnEq
	|NotAnEq -> NotAnEq

let rec get_flexible_rigid (s : equationsys) : equationsys =
	match s with
	| Eq (t1, t2) -> if is_flexible_rigid (t1, t2) then Eq(t1,t2) else NotAnEq
	| SysEq (s1, s2) -> if contains_flexible_rigid (s1) then get_flexible_rigid (s1) else if contains_flexible_rigid(s2) then get_flexible_rigid (s2) else NotAnEq
	|NotAnEq -> NotAnEq

let rec get_flexible_flexible (s : equationsys) : equationsys =
	match s with
	| Eq (t1, t2) -> if is_flexible_flexible (t1, t2) then Eq(t1,t2) else NotAnEq
	| SysEq (s1, s2) -> if contains_flexible_flexible (s1) then get_flexible_flexible (s1) else if contains_flexible_flexible(s2) then get_flexible_flexible (s2) else NotAnEq
	|NotAnEq -> NotAnEq


let rec delete_from_sys (s1 : equationsys) (s2 : equationsys) : equationsys =
	match s1 with
	| NotAnEq -> s2
	| Eq(t1, t2) -> match s2 with
			| Eq (t3, t4) -> if t1 = t3 then if t2 = t4 then NotAnEq else s2 else s2
			| SysEq (s3, s4) -> SysEq(delete_from_sys (s1, s3), delete_from_sys (s1, s4))
			| NotAnEq -> NotAnEq
	|SysEq (s5, s6) -> delete_from_sys(s5,delete_from_sys(s6, s2))

let rec apply_lambda (s: equationsys) (ty: ty) : equationsys =
	match s with
	| NotAnEq -> NotAnEq
	| Eq (t1, t2) -> Eq (S_Abs(ty,t1), S_Abs(ty,t2))
	| SysEq(s1, s2) -> SysEq(apply_lambda(s1, ty), apply_lambda(s2, ty))

let rec get_new_eq (s: equationsys)(t:s_term) : equationsys =
	match s with
		| NotAnEq -> NotAnEq
		| Eq (t1, t2) -> match t1 with
						| S_Abs (ty1, t3) -> match t2 with
											| S_Abs (ty2, t4) -> apply_lambda(get_new_eq (Eq(t3,t4), t)  ,ty)
											| _ -> Eq (t3,t4)
						| S_App (t3, t4) -> match t2 with
											| S_App (t5, t6) -> if t3 == t then get_new_eq (Eq (t4, t6), t) else SysEq(Eq(t3,t5), get_new_eq (Eq(t4,t6)))
											| _-> Eq(t1,t2)
						| _ -> Eq(t1,t2)

let rec count_lambda (t: s_term): int =
	match t with
		| S_Abs (ty, t1) -> 1 + count_lambda (t1)
		| _ -> 0

let rec huet_simpl ( s: equationsys ) : simplresult = 
	if  contains_rigid_rigid (s) then
		match get_rigid_rigid (s) with
		| Eq (t1, t2) -> if get_number (extract_head(t1)) != get_number (extract_head(t2)) then Failure else
			huet_simpl(Sys_Eq(delete_from_sys(Eq(t1,t2), s), get_new_eq(Eq(t1,t2), extract_head(t1))))
		| _ -> Failure
	else
		if contains_flexible_rigid (s) then s else Success

let rec huet_imitation (s:equationsys) : s_subst =
	if contains_flexible_rigid(s) then
		match get_flexible_rigid(s) with
			| Eq(t1,t2) -> match extract_head (s1) with
							| S_XVar -> match extract_head (s2) with
										| S_One -> if (1 > count_lambda (t2)) then Id else
										| S_Tsub (t, sub) -> if is_number Tsub(t, sub) then else
			| _ -> Id
	else Id
		
