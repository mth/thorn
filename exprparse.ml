(* ex: se sw=3 sts=3 expandtab: *)

(*  Priority based expression parser.

    Copyright (C) 2005,2006,2007 Madis Janson

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

type op_fix = Prefix | PreInfix of int | Infix | Listfix | Postfix
type op_direction = ToLeft | ToRight

type ('a, 'b) tmp_op = {
   prio: int;
   op: 'a;
   fix: op_fix;
   mutable left: ('a, 'b) op_node;
   mutable right: ('a, 'b) op_node;
   mutable parent: ('a, 'b) op_node
} and ('a, 'b) op_node = OpNode of ('a, 'b) tmp_op
                       | ListNode of ('a, 'b) op_node list
                       | OtherNode of 'b | NoNode

let no_op_str _ = "?"

(* op_prio is a function for determining operator properties.
   apply_op is a operator used between concative values. *)
class ['a, 'b] expr_parser (op_prio: 'a -> (int * op_fix * op_direction))
                           ?(op_eq: 'a -> 'a -> bool = (=))
                           ?(op_str: 'a -> string = no_op_str)
                           (apply_op: 'a) = object(self)
   val mutable last_op = true
   val mutable cur =
      { prio = 0; op = apply_op; fix = Infix; (* just some fix *)
        left = NoNode; right = NoNode; parent = NoNode }
   val mutable root = None

   initializer root <- Some cur

   method private insert (op: 'a) prio fix t =
      if fix <> Listfix
            || (match t.right with
               | OpNode n when op_eq n.op op -> cur <- n; false
               | _ -> true) then begin
         let node = {
            prio = prio;
            op = op;
            fix = fix;
            left = if fix = Listfix then ListNode [] else NoNode;
            right = t.right; (* steal parents last arg *)
            parent = OpNode t
         } in
         t.right <- OpNode node; (* and make self to be parents last arg *)
         (match node.right with
         | OpNode o -> o.parent <- t.right
         | _ -> ());
         cur <- node
      end

   method private add_unary_prefix (op: 'a) prio =
      if not last_op then
         self#add_apply;
      let t = {
         prio = prio;
         op = op;
         fix = Prefix;
         left = NoNode;
         right = NoNode;
         parent = OpNode cur
      } in last_op <- false;
      cur.left <- cur.right;
      cur.right <- OpNode t;
(*      print_endline ("add_unary_prefix " ^ op_str op ^ " " ^
                     string_of_int prio ^ " -> " ^ op_str cur.op ^ " " ^
                     string_of_int cur.prio); *)
      cur <- t;
      true

   method private add_apply =
      if cur.fix = Postfix then
         match cur.parent with
         | OpNode t -> self#insert apply_op cur.prio Infix t
         | _ -> raise (Failure "shit2!")
      else self#add_op apply_op

   (* Pushes operator into the parser automata. *)
   method add_op (op: 'a) =
      let prio, fix, dir = op_prio op in
      let is_op =
         match fix with
         | Prefix -> self#add_unary_prefix op prio
         | PreInfix prio when last_op || cur.fix = Postfix ->
            self#add_unary_prefix op prio
         | _ ->
            let rec find_parent n =
               (*print_endline ("find_parent n.prio = " ^
                  string_of_int n.prio ^ "; prio = " ^
                  string_of_int prio);*)
               if (n.prio > prio || n.prio = prio && dir = ToLeft)
                  && n.fix <> Postfix then n
               else match n.parent with
               | OpNode t -> find_parent t
               | NoNode -> n
               | _ -> raise (Failure "shit!")
            in self#insert op prio fix (find_parent cur);
            fix <> Postfix
      in if last_op then
         raise (Failure "You shall not stack operators...");
      last_op <- is_op(*;
      print_endline (" -> " ^ op_str cur.op ^
         if last_op then "<LO>" else "");*)

   (* Pushes value node into the parser automata. *)
   method add (n: 'b) =
      if not last_op then
         self#add_apply;
      last_op <- false;
      (match cur.left with
      | ListNode a -> cur.left <- ListNode(cur.right :: a)
      | _ -> cur.left <- cur.right);
      cur.right <- OtherNode n (*;
      print_endline (" | add_simple -> " ^ op_str cur.op)*)

   (* Retrieves parse tree. *)
   method result =
      match root with
      | Some node -> node.right
      | _ -> NoNode
end

let node_list op =
   match op.left with
   | ListNode l ->
      (match op.right with
      | NoNode -> List.rev l
      | n -> List.rev (n :: l))
   | _ -> 
      match op.right with
      | NoNode -> [ op.left ]
      | _ -> [ op.left; op.right ]

