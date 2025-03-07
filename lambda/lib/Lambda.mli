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

val nat_to_string : nat -> char list

val type_to_string : l_type -> char list

val term_to_string : term -> char list

type context = (char list * l_type) list

val find : char list -> context -> l_type option

val eq_l_type : l_type -> l_type -> bool

val get_type : context -> term -> l_type option
