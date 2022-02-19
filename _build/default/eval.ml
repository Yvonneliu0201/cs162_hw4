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
  failwith "TODO: homework" ;;

(** Performs the substitution [x -> e1]e2 *)
let rec subst (x : string) (e1 : expr) (e2 : expr) : expr =
  match e2 with
  | Var u -> if u != x then e1 else e2
  | NumLit c -> NumLit c
  | App (t1, t2) -> App ((subst x e1 t1), (subst x e1 t2))
  | Lambda (u, t') -> if u != x then (if (VarSet.mem u (free_vars e1)) then im_stuck "alpha renaming" else Lambda (u, (subst x e1 t'))) else e2
  | _ -> im_stuck "subst did not match to Var|App|Lambda"

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
    | Var str -> Var str
    | LetBind (str,e1,e2) -> let t1 = assert_value (eval e1) in let subAssert = assert_value ( eval (subst str (eval e1) e2) ) in eval (subst str (eval e1) e2)
    | Lambda (str, e) -> Lambda (str, e)
    | App (e1, e2) -> let t1 = assert_value (eval e1) in 
      (match (eval e1) with
       | Lambda (x, e1') -> let t2 = assert_value (eval e2) in let subAssert = assert_value(eval (subst x (eval e2) e1')) in eval (subst x (eval e2) e1')
       | _ -> im_stuck "first argument is not a lambda abstraction"
      )
    | Fix e -> let t1 = assert_value (eval e) in
      (match (eval e) with
       | Lambda (f, e') -> let v = eval (subst f (Fix (Lambda (f,e'))) e') in let t2 = assert_value v in v
       | _ -> im_stuck "e is not a lambda abstraction"
      )
    | _ -> im_stuck "Not an Expression"
  with
  | Stuck msg -> im_stuck (msg ^ "\nin expression " ^ string_of_expr e)
  ;;