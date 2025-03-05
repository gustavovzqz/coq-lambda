open Lambda

let string_of_list (l : char list) : string =
  String.of_seq (List.to_seq l)

let () = 
  match (get_type []  TM_pred) with
  | Some t -> print_endline (string_of_list (type_to_string t))
  | None -> ()

