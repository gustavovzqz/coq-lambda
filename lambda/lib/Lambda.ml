open Datatypes
open String

type l_type =
| LT_nat
| LT_bool
| LT_arrow of l_type * l_type

type term =
| TM_var of char list
| TM_app of term * term
| TM_abs of char list * l_type * term
| TM_true
| TM_false
| TM_nat of nat
| TM_if of term * term * term
| TM_iszero
| TM_succ
| TM_pred

(** val nat_to_string : nat -> char list **)

let rec nat_to_string = function
| O -> '0'::[]
| S m -> append ('S'::(' '::[])) (nat_to_string m)

(** val type_to_string : l_type -> char list **)

let rec type_to_string = function
| LT_nat -> 'n'::('a'::('t'::[]))
| LT_bool -> 'b'::('o'::('o'::('l'::[])))
| LT_arrow (ty1, ty2) ->
  let s1 =
    match ty1 with
    | LT_arrow (_, _) ->
      append ('('::[]) (append (type_to_string ty1) (')'::[]))
    | _ -> type_to_string ty1
  in
  let s2 = type_to_string ty2 in
  append s1 (append (' '::('-'::('>'::(' '::[])))) s2)

(** val term_to_string : term -> char list **)

let rec term_to_string = function
| TM_var x -> x
| TM_app (t1, t2) ->
  append ('('::[])
    (append (term_to_string t1)
      (append (' '::[]) (append (term_to_string t2) (')'::[]))))
| TM_abs (x, l, t0) ->
  append ('('::[])
    (append ('f'::('u'::('n'::(' '::[]))))
      (append x
        (append (' '::(':'::(' '::[])))
          (append (type_to_string l)
            (append (' '::('='::('>'::(' '::[]))))
              (append (term_to_string t0) (')'::[])))))))
| TM_true -> 't'::('r'::('u'::('e'::[])))
| TM_false -> 'f'::('a'::('l'::('s'::('e'::[]))))
| TM_nat n -> nat_to_string n
| TM_if (t1, t2, t3) ->
  append ('i'::('f'::(' '::[])))
    (append (term_to_string t1)
      (append (' '::('t'::('h'::('e'::('n'::(' '::[]))))))
        (append (term_to_string t2)
          (append (' '::('e'::('l'::('s'::('e'::(' '::[]))))))
            (term_to_string t3)))))
| TM_iszero -> 'i'::('s'::('z'::('e'::('r'::('o'::[])))))
| TM_succ -> 's'::('u'::('c'::('c'::[])))
| TM_pred -> 'p'::('r'::('e'::('d'::[])))

type context = (char list * l_type) list

(** val find : char list -> context -> l_type option **)

let rec find s = function
| [] -> None
| p :: t -> let (key, h) = p in if eqb key s then Some h else find s t

(** val eq_l_type : l_type -> l_type -> bool **)

let rec eq_l_type ty1 ty2 =
  match ty1 with
  | LT_nat -> (match ty2 with
               | LT_nat -> true
               | _ -> false)
  | LT_bool -> (match ty2 with
                | LT_bool -> true
                | _ -> false)
  | LT_arrow (ty1a, ty1b) ->
    (match ty2 with
     | LT_arrow (ty2a, ty2b) ->
       (&&) (eq_l_type ty1a ty2a) (eq_l_type ty1b ty2b)
     | _ -> false)

(** val get_type : context -> term -> l_type option **)

let rec get_type c = function
| TM_var x -> find x c
| TM_app (t1, t2) ->
  (match get_type c t1 with
   | Some l ->
     (match l with
      | LT_arrow (ty1, ty2) ->
        (match get_type c t2 with
         | Some ty1' -> if eq_l_type ty1 ty1' then Some ty2 else None
         | None -> None)
      | _ -> None)
   | None -> None)
| TM_abs (x, l, t') ->
  (match get_type ((x, l) :: c) t' with
   | Some ty -> Some (LT_arrow (l, ty))
   | None -> None)
| TM_true -> Some LT_bool
| TM_false -> Some LT_bool
| TM_nat _ -> Some LT_nat
| TM_if (t1, t2, t3) ->
  (match get_type c t1 with
   | Some l ->
     (match l with
      | LT_bool ->
        (match get_type c t2 with
         | Some ty2 ->
           (match get_type c t3 with
            | Some ty3 -> if eq_l_type ty2 ty3 then Some ty2 else None
            | None -> None)
         | None -> None)
      | _ -> None)
   | None -> None)
| TM_iszero -> Some (LT_arrow (LT_nat, LT_bool))
| _ -> Some (LT_arrow (LT_nat, LT_nat))
