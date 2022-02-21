(*FIX WORKS IN THIS ONE*)
open Ast

(** Variable set. Based on OCaml standard library Set. *)
module VarSet = Set.Make (String)

(* Helper function for parsing an expression. Useful for testing. *)
let parse (s: string) : Ast.expr =
  Parser.main Scanner.token (Lexing.from_string s)
(*******************************************************************|
|**********************   Interpreter   ****************************|
|*******************************************************************|
|*******************************************************************)

(* Exception indicating that evaluation is stuck *)
exception Stuck of string

(* Raises an exception indicating that evaluation got stuck. *)
let im_stuck msg = raise (Stuck msg)

(* Raises an exception for things that need to be implemented
 * in this assignment *)
let todo () = failwith "TODO"

(* Helper function to check that an expression is a value, otherwise raises a
   Stuck exception. *)
let assert_value e =
  if is_value e then () else im_stuck (string_of_expr e ^ " is not a value")

(** Computes the set of free variables in the given expression *)
let rec free_vars (e : expr) : VarSet.t =
  match e with
  | NumLit c -> VarSet.empty
  | Binop (t1,op,t2) -> VarSet.union (free_vars t1) (free_vars t2)
  | IfThenElse (t1,t2,t3) -> VarSet.union (VarSet.union (free_vars t1) (free_vars t2)) (free_vars t3)
  | ListNil -> VarSet.empty
  | ListCons (t1,t2) -> VarSet.union (free_vars t1) (free_vars t2)
  | ListHead t1 -> (free_vars t1)
  | ListTail t1 -> (free_vars t1)
  | ListIsNil t1 -> (free_vars t1)
  | Var u -> VarSet.singleton u
  | App (t1, t2) -> VarSet.union (free_vars t1) (free_vars t2)
  | Lambda (u, t') -> VarSet.diff (free_vars t') (VarSet.singleton u)
  | LetBind (u,t1,t2) -> VarSet.union (free_vars t1) (free_vars (Lambda(u,t2)))
  | Fix t1 -> (free_vars t1)
  | _ -> im_stuck "free_vars did not match any expr"

 let print_set s = 
     VarSet.iter print_endline s
(*begin (print_endline "origName:"); (print_endline x); (print_endline "FV Set:"); (print_set fv); (print_endline "newName:"); (print_endline newName);*)
let rec renaming (x: string) (fv: VarSet.t) (counter: int) : string =
  let newName = x ^ (string_of_int counter) in 
  if (VarSet.mem newName fv) then renaming x fv (counter + 1) else newName

(** Performs the substitution [x -> e1]e2 *)
let rec subst (x : string) (e1 : expr) (e2 : expr) : expr =
  match e2 with
  | NumLit c -> e2
  | Binop (t1,op,t2) -> Binop ((subst x e1 t1), op, (subst x e1 t2))
  | IfThenElse (t1,t2,t3) -> IfThenElse ((subst x e1 t1), (subst x e1 t2), (subst x e1 t3))
  | ListNil -> e2
  | ListCons (t1,t2) -> ListCons ((subst x e1 t1), (subst x e1 t2))
  | ListHead t1 -> ListHead (subst x e1 t1)
  | ListTail t1 -> ListTail (subst x e1 t1)
  | ListIsNil t1 -> ListIsNil (subst x e1 t1)
  | Var u -> if u = x then e1 else e2
  | App (t1, t2) -> App ((subst x e1 t1), (subst x e1 t2))
  | Lambda (u, t') -> 
    if u != x 
    then 
      (
       if (VarSet.mem u (free_vars e1)) 
       then let rename = renaming u (VarSet.union (free_vars e1) (free_vars t')) 0 in 
          Lambda(rename,(subst x e1 (subst u (Var rename) t'))) 
       else Lambda (u, (subst x e1 t'))
      ) 
    else Lambda (u, t')
  | LetBind (u,t1,t2) -> let substApp = subst x e1 (App (Lambda(u,t2),t1)) in 
    (match substApp with
     | App (Lambda(u',t2'), t1') -> LetBind(u',t1',t2'))
  | Fix t1 -> Fix (subst x e1 t1)
  | _ -> im_stuck "subst did not match any expr"

(*| LetBind (u,t1,t2) -> if u != x then (if (VarSet.mem u (free_vars e1)) then let rename = renaming u (VarSet.union (free_vars e1) (free_vars t2)) in LetBind (rename, (subst x e1 (subst u (Var rename) t1)), (subst x e1 (subst u (Var rename) t2))) else LetBind (u, (subst x e1 t1), (subst x e1 t2))) else e2*)
(** Evaluates e. You need to copy over your
   implementation of homework 3. *)
let rec eval (e : expr) : expr =
  try
    match e with
    (* Things you need to implement *)
    | NumLit n -> NumLit n
    | Binop (e1, op, e2) -> let t1 = assert_value (eval e1) in let t2 = assert_value (eval e2) in 
      (match (eval e1), op, (eval e2) with 
        | NumLit e1', Add, NumLit e2' -> NumLit (e1' + e2') 
        | NumLit e1', Sub, NumLit e2' -> NumLit (e1' - e2')  
        | NumLit e1', Mul, NumLit e2' -> NumLit (e1' * e2')  
        | NumLit e1', Gt, NumLit e2' -> if e1' > e2' then NumLit 1 else NumLit 0
        | NumLit e1', Lt, NumLit e2' -> if e1' < e2' then NumLit 1 else NumLit 0
        | NumLit e1', And, NumLit e2' -> if (e1' != 0) && (e2' != 0) then NumLit 1 else NumLit 0
        | NumLit e1', Or, NumLit e2' -> if (e1' != 0) || (e2' != 0) then NumLit 1 else NumLit 0 
        | NumLit e1', Eq, NumLit e2' -> if e1' = e2' then NumLit 1 else NumLit 0
        | _-> im_stuck "one of the arguments are not of type NumLit"
      )
    | IfThenElse (e1, e2, e3) -> let t1 = assert_value (eval e1) in
      (match (eval e1) with
        | NumLit 0 -> let t2 = assert_value (eval e3) in (eval e3)
        | NumLit _ -> let t3 = assert_value (eval e2) in (eval e2)
        | _ -> im_stuck "e1 is not a NumLit"
      ) 
    | ListNil -> ListNil
    | ListCons (e1, e2) -> let t1 = assert_value (eval e1) in let t2 = assert_value (eval e2) in ListCons ((eval e1), (eval e2))
    | ListHead e -> let t1 = assert_value (eval e) in
      (match (eval e) with
       | ListCons (e1, e2) -> let t1 = assert_value (eval e1) in let t2 = assert_value (eval e2) in (eval e1)
       | _ -> im_stuck "argument is not a ListCons"
      )
    | ListTail e -> let t1 = assert_value (eval e) in
      (match (eval e) with
       | ListCons (e1, e2) ->  let t1 = assert_value (eval e1) in let t2 = assert_value (eval e2) in (eval e2)
       | _ -> im_stuck "argument is not a ListCons"
      )
    | ListIsNil e -> let t1 = assert_value (eval e) in 
      (match (eval e) with 
       | ListNil -> NumLit 1
       | ListCons (_, _) -> NumLit 0
       | _ -> im_stuck "argument is not of List type"
      ) 
    | Var str -> im_stuck "lonely var decl"
    | LetBind (x,e1,e2) -> let v1 = (eval e1) in assert_value v1; let v2 = eval (subst x v1 e2) in assert_value v2; v2
    | Lambda (str, e) -> Lambda (str, e)
    | App (e1, e2) -> let t1 = assert_value (eval e1) in 
      (match (eval e1) with
       | Lambda (x, e1') -> let v = (eval e2) in assert_value v; let v' = (eval (subst x v e1')) in assert_value v'; v'
       | _ -> im_stuck "first argument is not a lambda abstraction"
      )
    | Fix e1 -> let t1 = assert_value (eval e1) in
      (match (eval e1) with
       | Lambda (f, e') -> let v = eval (subst f (Fix (Lambda (f,e'))) e') in let t2 = assert_value v in v
       | _ -> im_stuck "e is not a lambda abstraction"
      )
    | _ -> im_stuck "Not an Expression"
  with
  | Stuck msg -> im_stuck (msg ^ "\nin expression " ^ string_of_expr e)
  ;;