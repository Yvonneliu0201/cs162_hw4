open Ast
open Eval

(* Unit test utilities *)

let texpr = Alcotest.testable (fun ppf -> fun e -> Fmt.pf ppf "%s" (string_of_expr e)) (=) ;;

(* Helper function to parse an expression *)
let parse (s: string) : Ast.expr =
  Parser.main Scanner.token (Lexing.from_string s)

(* Helper function to check evaluation of an expression *)
let check_eval e expected () =
  let v =
    try eval e with
    | Stuck msg -> failwith ("Got stuck!\n" ^ msg)
  in
    Alcotest.(check' texpr) ~msg:"eval" ~expected:expected ~actual:v

(* Helper function to check evaluation of an expression (given a string of the expression) *)
let check_eval_s s expected () =
  check_eval (parse s) expected ()

(* Helper function to check that evaluation gets stuck *)
let check_stuck s () =
  try
    let v = eval (parse s) in
    Alcotest.fail ("evaluated to " ^ string_of_expr v)
  with
  | Stuck _ -> ()
;;

let open Alcotest in
(* Test that an expression (as a string) evaluates to the expected expression *)
let test_e s exp = test_case s `Quick (check_eval_s s exp) in
(* Test that an expression gets stuck *)
let test_stuck s = test_case s `Quick (check_stuck s) in
(* Test suite *)
run "lambda-plus" [
  "eval", [
    test_e "5" (NumLit(5)) ;
    test_e "(lambda x. x) 2" (NumLit(2)) ;
    test_e "(lambda x. x + x) 5" (NumLit(10)) ;
    test_e "lambda x. let y = 2 in y" (Lambda("x",LetBind("y",NumLit(2),Var("y")))) ;
    test_e "(lambda x. (let y = 2 in y+y)) 3" (NumLit(4)) ;
    test_e "(lambda x. (let x = 1 in let y = 2 in x + y) + x) 5" (NumLit(8)) ;
    
    (*Nested Apps and LetBinds*)
    test_e "(lambda x. lambda x. x) 5" (Lambda ("x", Var("x"))) ;
    test_e "(lambda x. (lambda x. x) 2) 1" (NumLit(2)) ;
    test_e "(lambda x. (let x = 1 in x)) 2" (NumLit(1)) ;
    test_e "(lambda x. (let x = 1 in x) + x) 2" (NumLit(3)) ;

    (*alpha renaming*)
    test_e "(lambda x, y. x y) (lambda x. y)" (Lambda("y0",App(Lambda("x",Var("y")),Var("y0")))) ;
    test_e "(lambda x, y. x y y0) (lambda x. y)" (Lambda("y1",App(App(Lambda("x",Var("y")),Var("y1")),Var("y0"))));
    test_e "(lambda f, y. let y0 = 5 in y) (lambda x. y)" (Lambda("y0",LetBind("y00",NumLit(5),Var("y0"))));
    test_e "(lambda z. lambda y. let x = 5 in z) (lambda y. x)" (Lambda ("y",LetBind("x0",NumLit(5),Lambda("y",Var("x")))));
    test_e "(lambda x, y. x y) (lambda x. y)" (Lambda("y0",App(Lambda("x",Var("y")),Var("y0"))));
    
    (*FIX expr*)
    test_e "let f = lambda x. x * 2 in f 3" (NumLit(6)) ;
    test_e "fun f with m = if m > 1 then m * (f (m - 1)) else 1 in f 6" (NumLit(720)) ;
  ];
  "stuck", [
    test_stuck "1 > Nil" ;
  ]
]

(*
    test_e "(lambda z. lambda y. let x = 5 in z) (lambda y. x)" (Lambda("x",Var("x"))) ;
*)