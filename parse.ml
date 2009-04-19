(* ex: se sts=3 sw=3 expandtab: *)

type pnode =
   VSym of string | VStr of string | VNum of int | VList of pnode list

let rec show_pt = function
   | VSym s -> s
   | VStr s -> "\"" ^ s ^ "\""
   | VNum n -> string_of_int n
   | VList l -> "(" ^ String.concat " " (List.map show_pt l) ^ ")"

(* Parse source into AST *)
let parse s =
   let e = String.length s in
   let rec get p =
      match s.[p] with
      | '"' -> get_str (p + 1) (p + 1)
      | '0' .. '9' -> let p, v = get_sym p p in p, VNum (int_of_string v)
      | '(' -> let p, l = get_list ')' (p + 1) [] in p, VList l
      | '{' -> let p, l = get_list '}' (p + 1) [] in p, VList (VSym "{}" :: l)
      | '.' -> let p, v = get (p + 1) in p, VList [VSym "quote"; v]
      | _   -> let p, v = get_sym p (p + 1) in p, VSym v
   and get_str b p =
      if p >= e then
         raise (Failure "Unexpected end of string");
      if s.[p] = '"' then
         p + 1, VStr (String.sub s b (p - b))
      else get_str b (p + 1)
   and get_sym b p =
      match if p >= e then ' ' else s.[p] with
      | '\000' .. ' ' | '(' | ')' | '{' | '}' | '.' | '"' | ':' | ';' | '|' ->
         p, String.sub s b (p - b)
      | _ -> get_sym b (p + 1)
   and get_list ec p l =
      if p >= e then
         raise (Failure "Unexpected end of list");
      match s.[p] with
      | '\000' .. ' ' -> get_list ec (p + 1) l
      | c when c = ec -> p + 1, List.rev l
      | _ -> let p, v = get p in get_list ec p (v :: l)
   and top_list p l =
      if p >= e then
         match l with
         | [a] -> a
         | _ -> VList (List.rev l)
      else
         match s.[p] with
         | ')' -> raise (Failure "Unexpected )")
         | '\000' .. ' ' -> top_list (p + 1) l
         | _ -> let p, v = get p in top_list p (v :: l)
   in top_list 0 []
