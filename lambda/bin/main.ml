open Lambda

let string_of_list list = String.of_seq (List.to_seq list)

let print_term_type term = 
  let typel = get_type [] term in 
  let s = string_of_list (term_to_string term) in 
  print_string (s ^ " : ");

  match typel with 
  | Some t -> print_endline (string_of_list (type_to_string t))
  | None -> print_endline "Termo mal tipado!"


let () = 
  print_term_type TM_true;
  print_term_type TM_false;
  print_term_type (TM_nat (S (S O)));
  print_term_type TM_succ;
  print_term_type TM_pred;
  print_term_type TM_iszero;
  print_term_type (TM_app (TM_succ, TM_nat (S O)));
  print_term_type (TM_app (TM_pred, TM_nat (S O)));
  print_term_type (TM_app (TM_iszero, TM_nat O));
  print_term_type (TM_abs (['x'], LT_nat, TM_var ['x']));
  print_term_type (TM_abs (['x'], LT_nat, TM_app (TM_succ, TM_var ['x'])));
  print_term_type (TM_app (TM_abs (['x'], LT_nat, TM_var ['x']), TM_nat (S O)));
  print_term_type (TM_app (TM_abs (['x'], LT_nat, TM_app (TM_succ, TM_var ['x'])), TM_nat (S O)));
  print_term_type (TM_if (TM_true, TM_nat (S O), TM_nat O));
  print_term_type (TM_if (TM_false, TM_nat (S O), TM_nat O));
  print_term_type (TM_if (TM_app (TM_iszero, TM_nat O), TM_nat (S O), TM_nat O));
  print_term_type (TM_app (TM_true, TM_nat (S O)));
  print_term_type (TM_if (TM_nat (S O), TM_nat O, TM_nat (S (S O))));
  print_term_type (TM_app (TM_abs (['x'], LT_nat, TM_var ['x']), TM_true));
