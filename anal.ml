(* ex: se sts=3 sw=3 expandtab: *)

#load "parse.cmo"
#load "exprparse.cmo"

open Parse
open Exprparse
open Printf

type join_type = Multi | Choice
type tval = Nil | Val of pnode | Var of int | Join of tjoin
   | Fun of tval * tval | Apply of tval * tval
and tjoin = { join_type: join_type; joined: tval array }

let show_join_type = function
   | Multi -> " | "
   | Choice -> " # "

let allow_log = ref true
let log s = if !allow_log then print_endline s

let var_counter = ref 0

let mkvar () =
   var_counter := !var_counter + 1;
   Var !var_counter

let rec show = function
   | Nil -> "."
   | Val v -> "." ^ show_pt v
   | Var v -> "%" ^ string_of_int v
   | Fun (a, r) -> "(" ^ show a ^ " -> " ^ show r ^ ")"
   | Apply (f, a) -> "(" ^ show f ^ " $ " ^ show a ^ ")"
   | Join j ->
      "(" ^ String.concat (show_join_type j.join_type)
                          (Array.to_list (Array.map show j.joined)) ^ ")"

let array_of_hash h =
   Array.of_list (Hashtbl.fold (fun k _ l -> k :: l) h [])

exception Mismatch of (tval * tval)

let map_nodups all f a =
   let l = Array.length a in
   if l == 0 then a else
   let res = Array.create l a.(0) and c = ref 0 and h = Hashtbl.create l in
   for i = 0 to l - 1 do
      try
         let v = f a.(i) in
         if not (Hashtbl.mem h v) then
            (res.(!c) <- v; c := !c + 1; Hashtbl.add h v ())
      with Mismatch e ->
         if all || !c == 0 && i = l - 1 then
            raise (Mismatch e)
   done;
   Array.sub res 0 !c

let map_join all f j =
   match map_nodups all f j.joined with
   | [|t|] -> t
   | a -> Join { join_type = j.join_type; joined = a }

let first_join f {joined = fs} =
   let last = Array.length fs - 1 in
   let rec find i =
      try f fs.(i) with Mismatch e ->
         if i = last then
            raise (Mismatch e);
         find (i + 1) in find 0

let is_var = function
   | Var _ -> true
   | _ -> false

(* reduces type trees using abstract interpretation *)
let rec reduce (ctx : (int * tval) list) t =
   let r = match t with
   | Var id as t ->
      (try List.assoc id ctx with Not_found -> t)
   | Apply (f, a) ->
      reduce_apply ctx (reduce ctx a) (reduce ctx f)
   | Fun (a, r) -> Fun (a, reduce ctx r)
   | Join j -> map_join true (reduce ctx) j
   | t -> t in
   if !allow_log && t <> r then
      log ("REDUCED " ^ show t ^ " INTO " ^ show r);
   r
and reduce_apply ctx a = function
   | Fun (Var arg, body) ->
      reduce ((arg, a) :: ctx) body
   | Fun ((Val _) as arg, body) ->
      let apply a = flow ctx (a, arg); reduce ctx body in
      (* In case of join try all variants *)
      (match a with
      | Join j -> map_join (j.join_type = Choice) apply j
      | _ -> apply a)
   | Fun (arg, _) ->
      failwith ("Bad argument: " ^ show arg)
   | Join ({join_type = Choice} as j) ->
      map_join true (reduce_apply ctx a) j
   | Join j when not (is_var a) ->
      first_join (reduce_apply ctx a) j
   | Val _ as f ->
      raise (Mismatch (f, Fun (a, mkvar ())))
   | f -> Apply (f, a)
and flow ctx = function
   | Val x, Val y when x = y -> ()
   | Var x, t -> ()
   | x -> raise (Mismatch x)

type op = ApplyOp | Op of string | BindOp of string

let op_prio = function
   | ApplyOp ->  1, Infix, ToRight
   | Op "|"  ->  3, Listfix, ToLeft 
   | BindOp _ -> 9, PreInfix 9, ToLeft
   | Op ";"  -> 10, Listfix, ToLeft
   | Op _    ->  5, Postfix, ToLeft

let op_eq a b =
   match a, b with
   | BindOp _, BindOp _ -> true
   | _ -> a = b

(* Converts source tree into type tree *)
let rec type_tree (ctx : (string * tval) list) = function
   | VSym s ->
      (try List.assoc s ctx with Not_found ->
         raise (Failure ("Unbound " ^ s)))
   | VList [VSym "quote"; v] -> Val v
   | VList (VSym "{}" :: l) ->
      let rec scan al = function
         | VSym ":" :: body ->
            let rec mkfun ctx = function
               | VSym arg :: rest ->
                  let argt = mkvar () in
                  Fun (argt, mkfun ((arg, argt) :: ctx) rest)
               | arg :: rest ->
                  Fun (type_tree ctx arg, mkfun ctx rest)
               | [] -> type_tree ctx (VList body)
            in mkfun ctx (List.rev al)
         | a :: r -> scan (a :: al) r
         | [] -> Fun (mkvar (), type_tree ctx (VList l))
      in scan [] l
   | VList expr ->
      let p = new expr_parser op_prio ~op_eq:op_eq ApplyOp in
      let rec add = function
         | VSym s :: VSym "=" :: rest ->
            p#add_op (BindOp s); add rest
         | VSym s as sym :: rest ->
            (match s.[0] with
            | 'A' .. 'Z' | 'a' .. 'z' | '_' | '?' | '{' -> p#add sym
            | _ -> p#add_op (Op s));
            add rest
         | token :: rest ->
            p#add token; add rest
         | [] -> () in
      add expr;
      op_expr ctx p#result
   | src -> Val src
and op_expr ctx = function
   | OpNode op ->
      (match op.op with
      | ApplyOp ->
         Apply (op_expr ctx op.left, op_expr ctx op.right)
      | Op "|" ->
         Join { join_type = Multi;
                joined = Array.map (op_expr ctx)
                                   (Array.of_list (node_list op)) }
      | Op ";" ->
         let rec seq ctx = function
            | OpNode ({op = BindOp name; right = bind}) :: rest ->
               seq ((name, op_expr ctx bind) :: ctx) rest
            | [expr] -> op_expr ctx expr
            | expr :: rest ->
               let _ = op_expr ctx expr in seq ctx rest
            | [] -> failwith "WTF[]"
         in seq ctx (node_list op)
      | Op s ->
         Apply (type_tree ctx (VSym s), op_expr ctx op.right)
      | BindOp s ->
         failwith "Bind not expected")
   | OtherNode v -> type_tree ctx v
   | _ -> failwith "WTF"

let catch_err action =
   try
      action ()
   with
      | Failure s ->
         printf "Error: %s\n" s;
      | Mismatch (a, b) ->
         printf "Type mismatch: %s <> %s\n" (show a) (show b)
;;

if Array.length Sys.argv <= 1 then begin
   try
      allow_log := false;
      while true do
         catch_err (function _ ->
            var_counter := 0;
            let t = type_tree [] (parse (read_line ())) in
            print_endline (show (reduce [] t));
            flush stdout)
      done
   with End_of_file -> ()
end else catch_err (function _ ->
   let pt = parse Sys.argv.(1) in
   log (show_pt pt);
   let t = type_tree [] pt in
   let tr = reduce [] t in
   log (show tr))
