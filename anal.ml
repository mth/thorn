(* ex: se sts=3 sw=3 expandtab: *)

#load "parse.cmo"
#load "exprparse.cmo"

open Parse
open Exprparse
open Printf

type join_type = Multi | Choice
type tval = Val of pnode | Var of int | Join of tjoin
   | Fun of int * tval * tval_free | Apply of tval_free * tval_free
and tval_free = tval * int
and tjoin = {join_type: join_type; joined: tval_free array}

let level_no_var = 100000000

let show_join_type = function
   | Multi -> " | "
   | Choice -> " # "

let allow_log = ref true
let log_indent = ref ""
let log s = if !allow_log then print_endline (!log_indent ^ s)
let log' s f =
   log s;
   let old = !log_indent in
   log_indent := old ^ ".";
   let res = f () in
   log_indent := old;
   res

let var_counter = ref 0

let mkvar () =
   var_counter := !var_counter + 1;
   Var !var_counter

let (%) f g x = f (g x)

let rec show = function
   | Val v -> "." ^ show_pt v
   | Var v -> "%" ^ string_of_int v
   | Fun (l, a, (r, _)) ->
      sprintf "(%s -> %s)" (show a) (show r)
   | Apply ((f, _), (a, _)) ->
      sprintf "(%s $ %s)" (show f) (show a)
   | Join j ->
      "(" ^ String.concat (show_join_type j.join_type)
                         (Array.to_list (Array.map (show % fst) j.joined)) ^ ")"

let array_of_hash h =
   Array.of_list (Hashtbl.fold (fun k _ l -> k :: l) h [])

exception Mismatch of (tval * tval)

let map_nodups all f a =
   let l = Array.length a in
   let res = Array.create l a.(0) and c = ref 0 and h = Hashtbl.create l in
   let level = ref level_no_var in
   for i = 0 to l - 1 do
      try
         let (_, level') as v = f a.(i) in
         if not (Hashtbl.mem h v) then
           (res.(!c) <- v;
            c := !c + 1;
            Hashtbl.add h v ();
            if level' < !level then
               level := level')
      with Mismatch e ->
         if all || !c == 0 && i = l - 1 then
            raise (Mismatch e)
   done;
   Array.sub res 0 !c, !level

let map_join all f j =
   match map_nodups all f j.joined with
   | [|t|], _ -> t
   | a, level -> Join {join_type = j.join_type; joined = a}, level

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

let rec reduce fun_level (ctx: (int * tval) list) = function
   (* reduce is done only when the expression contains
      free variables (level < fun_level) to eliminate those *)
   | t, level when level < fun_level ->
      let old_indent = !log_indent in
      if String.length old_indent >= 16 then
         failwith "recursion too deep";
      log_indent := old_indent ^ " ";
      let r = match t with
      | Var id ->
         log (sprintf "var %%%d" id);
        (try
            let t = List.assoc id ctx in
            t, level_no_var
         with Not_found ->
            failwith (sprintf "Missing %%%d" id))
      | Apply (f, a) ->
         log (sprintf "Apply(%d) %s $ %s"
                      fun_level (show (fst f)) (show (fst a)));
         let (_, fl) as f = reduce fun_level ctx f 
         and (arg, al) as a = reduce fun_level ctx a in
         if fl > fun_level && al > fun_level then
            beta_reduce ctx arg f (* no free vars, get rid of the Apply *)
         else
            Apply (f, a), min fl al
      | Fun (f_level, a, r) ->
         log (sprintf "reduce_fun %d (%d < %d) %s -> %s"
               f_level level fun_level (show a) (show (fst r)));
         let (_, level) as r = reduce f_level ctx r in
         log (sprintf "Fun (%d, %s, %s) %d"
                      f_level (show a) (show (fst r)) level);
         Fun (f_level, a, r), if level >= f_level then level_no_var else level
      | Join j ->
         log (sprintf "reduce join: %s, %d" (show t) level);
         map_join true (reduce fun_level ctx) j
      | Val _ -> t, level
      in log_indent := old_indent;
      if !allow_log then
         log (sprintf " REDUCED %s INTO %s, %d"
              (show t) (show (fst r)) (snd r));
      r
   | t ->
      log (sprintf " no reduce !(%d < %d) %s"
                   (snd t) fun_level (show (fst t)));
      t
and beta_reduce (ctx: (int * tval) list) arg func =
   match fst func with
   | Fun (level, Var id, body) ->
      log ("apply_var " ^ string_of_int level ^ " " ^ show arg);
      reduce (level + 1) ((id, arg) :: ctx) body
   | Fun (level, (Val _ as arg'), body) ->
      log "apply_const";
      let level = level + 1 in
      (* In case of join try all variants *)
      (match arg with
      | Join j ->
         let apply (a, _) = flow (a, arg'); reduce level ctx body in
         map_join (j.join_type = Choice) apply j
      | _ ->
         flow (arg, arg');
         reduce level ctx body)
   | Join ({join_type = Choice} as j) ->
      log "apply_choice";
      map_join true (beta_reduce ctx arg) j
   | Join j ->
      log "apply_multi";
      first_join (beta_reduce ctx arg) j
   | f ->
      log "not a function";
      raise (Mismatch (f, Fun (0, arg, (Var 0, 0))))
and flow = function
   | Val x, Val y when x = y -> ()
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

type ctx = {level: int; scope: (string * tval_free) list}

let fun_of ctx name arg body_of node =
   let l = ctx.level + 1 in
   let s = if name = "" then ctx.scope else (name, (arg, l)) :: ctx.scope in
   let (_, level) as body = body_of {level = l; scope = s} node in
   Fun (l, arg, body), if level >= l then level_no_var else level

(* Converts source tree into type tree *)
let rec type_tree (ctx : ctx) = function
   | VSym s ->
      (try List.assoc s ctx.scope with Not_found ->
         raise (Failure ("Unbound " ^ s)))
   | VList [VSym "quote"; v] -> Val v, level_no_var
   | VList (VSym "{}" :: l) ->
      let rec scan al = function
         | VSym ":" :: body ->
            let rec mkfun ctx = function
               | VSym arg :: rest ->
                  fun_of ctx arg (mkvar ()) mkfun rest
               | arg :: rest ->
                  fun_of ctx "" (fst (type_tree ctx arg)) mkfun rest
               | [] -> type_tree ctx (VList body)
            in mkfun ctx (List.rev al)
         | a :: r -> scan (a :: al) r
         | [] -> fun_of ctx "" (mkvar ()) type_tree (VList l)
      in scan [] l
   | VList expr ->
      let p = new expr_parser op_prio ~op_eq:op_eq ApplyOp in
      let rec add = function
         | VSym s :: VSym "=" :: rest ->
            p#add_op (BindOp s); add rest
         | VSym s as sym :: rest ->
            (* TODO: being an operator should be decided by declaration *)
            (match s.[0] with
            | 'A' .. 'Z' | 'a' .. 'z' | '_' | '?' | '{' -> p#add sym
            | _ -> p#add_op (Op s));
            add rest
         | token :: rest ->
            p#add token; add rest
         | [] -> () in
      add expr;
      op_expr ctx p#result
   | src -> Val src, level_no_var
and op_expr ctx = function
   | OpNode op ->
      (match op.op with
      | ApplyOp ->
         apply ctx (op_expr ctx op.left) (op_expr ctx op.right)
      | Op "|" ->
         let j = Array.map (op_expr ctx) (Array.of_list (node_list op)) in
         Join {join_type = Multi; joined = j},
         Array.fold_left min level_no_var (Array.map snd j)
      | Op ";" ->
         let rec seq ctx = function
            | OpNode ({op = BindOp name; right = bind}) :: rest ->
               let var = mkvar () in
               let scope = (name, (var, ctx.level)) :: ctx.scope in
               let value = op_expr {level = ctx.level; scope = scope} bind in
               apply ctx (fun_of ctx name var seq rest) value
            | [expr] -> op_expr ctx expr
            | expr :: rest ->
               let _ = op_expr ctx expr in seq ctx rest
            | [] -> failwith "WTF[]"
         in seq ctx (node_list op)
      | Op s ->
         apply ctx (type_tree ctx (VSym s)) (op_expr ctx op.right)
      | BindOp s ->
         failwith "Bind not expected")
   | OtherNode v -> type_tree ctx v
   | _ -> failwith "WTF"
and apply ctx ((ft, fl) as f) ((at, al) as a) =
   log (sprintf "apply %d: %s $ %s" ctx.level (show ft) (show at));
   let level = min fl al in
   if level > ctx.level then beta_reduce [] at f else Apply (f, a), level

let catch_err action =
   try
      action ()
   with
      | Failure s ->
         printf "Error: %s\n" s;
      | Mismatch (a, b) ->
         printf "Type mismatch: %s <> %s\n" (show a) (show b)

let type_tree' node =
   let empty_ctx = {level = 1; scope = []} in
   let t = type_tree empty_ctx node in
   log "tree created";
   (*fst (reduce (empty_ctx.level + 1) [] t)*)
   fst t

;;
if Array.length Sys.argv <= 1 then begin
   try
      allow_log := false;
      while true do
         catch_err (function _ ->
            var_counter := 0;
            let t = type_tree' (parse (read_line ())) in
            print_endline (show t);
            flush stdout)
      done
   with End_of_file -> ()
end else catch_err (function _ ->
   let pt = parse Sys.argv.(1) in
   log (show_pt pt);
   let t = type_tree' pt in
   log (show t))
