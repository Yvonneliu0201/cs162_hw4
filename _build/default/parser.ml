type token =
  | EOF
  | FUN
  | GT
  | EQ
  | LT
  | LPAREN
  | RPAREN
  | DOT
  | COMMA
  | TRUE
  | FALSE
  | AND
  | OR
  | LET
  | IN
  | IF
  | THEN
  | ELSE
  | WITH
  | LAMBDA
  | NIL
  | CONS
  | HEAD
  | TAIL
  | ISNIL
  | TYINT
  | TYLIST
  | THINARROW
  | COLON
  | LBRACK
  | RBRACK
  | PLUS
  | SUB
  | TIMES
  | APP
  | NUMBER of (int)
  | ID of (string)

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Ast
let mk_lambdas (xs : string list) (e : expr) =
  let f x e' = Lambda (x, e') in
  List.fold_right f xs e
let syntax_error () =
  let start_pos = Parsing.rhs_start_pos 1 in
  let end_pos = Parsing.rhs_end_pos 1 in
  let sl = start_pos.pos_lnum
  and sc = start_pos.pos_cnum - start_pos.pos_bol
  and el = end_pos.pos_lnum
  and ec = end_pos.pos_cnum - end_pos.pos_bol in
  failwith (Printf.sprintf "Syntax error: %d.%d-%d.%d" sl sc el ec)
# 56 "parser.ml"
let yytransl_const = [|
    0 (* EOF *);
  257 (* FUN *);
  258 (* GT *);
  259 (* EQ *);
  260 (* LT *);
  261 (* LPAREN *);
  262 (* RPAREN *);
  263 (* DOT *);
  264 (* COMMA *);
  265 (* TRUE *);
  266 (* FALSE *);
  267 (* AND *);
  268 (* OR *);
  269 (* LET *);
  270 (* IN *);
  271 (* IF *);
  272 (* THEN *);
  273 (* ELSE *);
  274 (* WITH *);
  275 (* LAMBDA *);
  276 (* NIL *);
  277 (* CONS *);
  278 (* HEAD *);
  279 (* TAIL *);
  280 (* ISNIL *);
  281 (* TYINT *);
  282 (* TYLIST *);
  283 (* THINARROW *);
  284 (* COLON *);
  285 (* LBRACK *);
  286 (* RBRACK *);
  287 (* PLUS *);
  288 (* SUB *);
  289 (* TIMES *);
  290 (* APP *);
    0|]

let yytransl_block = [|
  291 (* NUMBER *);
  292 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\003\000\004\000\004\000\002\000\002\000\002\000\
\002\000\002\000\002\000\007\000\007\000\007\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\006\000\
\006\000\006\000\006\000\006\000\006\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\001\000\003\000\004\000\008\000\006\000\
\006\000\001\000\001\000\001\000\001\000\001\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\001\000\
\002\000\002\000\002\000\003\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\014\000\000\000\000\000\000\000\013\000\012\000\030\000\000\000\
\010\000\000\000\024\000\002\000\003\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\028\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yydgoto = "\002\000\
\015\000\016\000\026\000\027\000\017\000\018\000\019\000"

let yysindex = "\022\000\
\055\255\000\000\044\000\009\255\002\255\009\255\002\255\009\255\
\000\000\172\255\172\255\172\255\000\000\000\000\000\000\191\000\
\000\000\172\255\000\000\000\000\000\000\028\255\083\255\044\255\
\106\255\041\255\043\255\027\255\027\255\172\255\000\000\002\255\
\002\255\002\255\002\255\002\255\002\255\002\255\002\255\002\255\
\245\254\009\255\000\000\002\255\002\255\009\255\002\255\243\254\
\243\254\243\254\129\255\129\255\031\255\239\254\239\254\031\255\
\050\255\109\255\132\255\000\000\168\255\002\255\002\255\002\255\
\155\255\168\255\168\255\002\255\168\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\106\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\003\255\000\000\001\000\036\000\129\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\071\000\000\000\000\000\000\000\000\000\000\000\000\000\002\001\
\019\001\035\001\014\000\048\000\152\000\214\000\236\000\175\000\
\000\000\000\000\000\000\000\000\064\000\000\000\000\000\000\000\
\000\000\080\000\084\000\000\000\099\000"

let yygindex = "\000\000\
\000\000\251\255\037\000\219\255\000\000\192\000\000\000"

let yytablesize = 564
let yytable = "\023\000\
\025\000\025\000\004\000\037\000\057\000\004\000\005\000\037\000\
\060\000\004\000\010\000\011\000\012\000\021\000\006\000\040\000\
\007\000\038\000\039\000\040\000\008\000\009\000\001\000\010\000\
\011\000\012\000\048\000\049\000\050\000\051\000\052\000\053\000\
\054\000\055\000\056\000\026\000\013\000\014\000\058\000\059\000\
\022\000\061\000\024\000\020\000\021\000\042\000\044\000\022\000\
\046\000\047\000\012\000\037\000\062\000\000\000\003\000\004\000\
\065\000\066\000\067\000\005\000\000\000\000\000\069\000\006\000\
\000\000\000\000\000\000\006\000\000\000\007\000\029\000\000\000\
\000\000\008\000\009\000\000\000\010\000\011\000\012\000\009\000\
\000\000\000\000\000\000\008\000\032\000\033\000\034\000\000\000\
\043\000\013\000\014\000\000\000\000\000\035\000\036\000\000\000\
\000\000\000\000\007\000\000\000\000\000\000\000\000\000\037\000\
\000\000\011\000\000\000\032\000\033\000\034\000\032\000\033\000\
\034\000\038\000\039\000\040\000\035\000\036\000\000\000\035\000\
\036\000\045\000\063\000\000\000\000\000\000\000\037\000\000\000\
\027\000\037\000\032\000\033\000\034\000\032\000\033\000\034\000\
\038\000\039\000\040\000\038\000\039\000\040\000\035\000\036\000\
\000\000\000\000\000\000\000\000\064\000\037\000\000\000\023\000\
\037\000\000\000\000\000\000\000\032\000\033\000\034\000\038\000\
\039\000\040\000\038\000\039\000\040\000\035\000\036\000\000\000\
\068\000\032\000\033\000\034\000\000\000\000\000\017\000\037\000\
\005\000\000\000\035\000\036\000\000\000\000\000\000\000\000\000\
\000\000\038\000\039\000\040\000\037\000\000\000\031\000\009\000\
\000\000\010\000\011\000\012\000\000\000\000\000\038\000\039\000\
\040\000\028\000\029\000\030\000\000\000\000\000\013\000\014\000\
\000\000\041\000\000\000\000\000\000\000\015\000\000\000\000\000\
\000\000\000\000\000\000\041\000\041\000\041\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\041\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\019\000\025\000\025\000\025\000\025\000\025\000\000\000\
\000\000\000\000\000\000\025\000\025\000\000\000\025\000\000\000\
\025\000\025\000\020\000\021\000\025\000\025\000\000\000\000\000\
\021\000\021\000\000\000\021\000\000\000\021\000\021\000\025\000\
\025\000\025\000\018\000\025\000\025\000\026\000\026\000\026\000\
\026\000\026\000\000\000\000\000\000\000\000\000\026\000\026\000\
\000\000\026\000\000\000\026\000\026\000\022\000\000\000\026\000\
\026\000\000\000\022\000\022\000\000\000\022\000\000\000\022\000\
\022\000\000\000\026\000\026\000\026\000\006\000\026\000\026\000\
\029\000\029\000\029\000\029\000\029\000\006\000\000\000\006\000\
\006\000\029\000\029\000\000\000\029\000\009\000\029\000\029\000\
\000\000\008\000\029\000\029\000\000\000\009\000\000\000\009\000\
\009\000\008\000\000\000\008\000\008\000\029\000\029\000\029\000\
\007\000\029\000\029\000\011\000\011\000\011\000\000\000\011\000\
\007\000\000\000\007\000\007\000\011\000\011\000\000\000\011\000\
\000\000\011\000\011\000\000\000\000\000\000\000\011\000\000\000\
\000\000\000\000\027\000\027\000\027\000\000\000\027\000\000\000\
\011\000\011\000\011\000\027\000\027\000\000\000\027\000\000\000\
\027\000\027\000\000\000\000\000\000\000\027\000\000\000\000\000\
\000\000\023\000\023\000\023\000\000\000\023\000\000\000\027\000\
\027\000\027\000\023\000\023\000\000\000\023\000\000\000\023\000\
\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\017\000\017\000\017\000\000\000\017\000\000\000\023\000\023\000\
\023\000\017\000\017\000\000\000\017\000\000\000\017\000\017\000\
\032\000\033\000\034\000\000\000\000\000\000\000\000\000\000\000\
\000\000\035\000\036\000\000\000\000\000\017\000\017\000\017\000\
\000\000\000\000\000\000\037\000\000\000\000\000\000\000\015\000\
\015\000\015\000\000\000\015\000\000\000\038\000\039\000\040\000\
\015\000\015\000\000\000\015\000\000\000\015\000\015\000\000\000\
\000\000\000\000\000\000\000\000\000\000\016\000\016\000\016\000\
\000\000\016\000\000\000\000\000\015\000\015\000\016\000\016\000\
\000\000\016\000\000\000\016\000\016\000\000\000\000\000\000\000\
\000\000\000\000\000\000\019\000\019\000\019\000\000\000\019\000\
\000\000\000\000\016\000\016\000\019\000\019\000\000\000\019\000\
\000\000\019\000\019\000\000\000\020\000\020\000\020\000\000\000\
\020\000\000\000\000\000\000\000\000\000\020\000\020\000\000\000\
\020\000\000\000\020\000\020\000\018\000\018\000\018\000\000\000\
\018\000\000\000\000\000\000\000\000\000\018\000\018\000\000\000\
\018\000\000\000\018\000\018\000"

let yycheck = "\005\000\
\000\000\007\000\001\001\021\001\042\000\003\001\005\001\021\001\
\046\000\007\001\022\001\023\001\024\001\000\000\013\001\033\001\
\015\001\031\001\032\001\033\001\019\001\020\001\001\000\022\001\
\023\001\024\001\032\000\033\000\034\000\035\000\036\000\037\000\
\038\000\039\000\040\000\000\000\035\001\036\001\044\000\045\000\
\004\000\047\000\006\000\000\000\036\001\018\001\003\001\000\000\
\008\001\007\001\024\001\021\001\003\001\255\255\000\001\001\001\
\062\000\063\000\064\000\005\001\255\255\255\255\068\000\000\000\
\255\255\255\255\255\255\013\001\255\255\015\001\000\000\255\255\
\255\255\019\001\020\001\255\255\022\001\023\001\024\001\000\000\
\255\255\255\255\255\255\000\000\002\001\003\001\004\001\255\255\
\006\001\035\001\036\001\255\255\255\255\011\001\012\001\255\255\
\255\255\255\255\000\000\255\255\255\255\255\255\255\255\021\001\
\255\255\000\000\255\255\002\001\003\001\004\001\002\001\003\001\
\004\001\031\001\032\001\033\001\011\001\012\001\255\255\011\001\
\012\001\016\001\014\001\255\255\255\255\255\255\021\001\255\255\
\000\000\021\001\002\001\003\001\004\001\002\001\003\001\004\001\
\031\001\032\001\033\001\031\001\032\001\033\001\011\001\012\001\
\255\255\255\255\255\255\255\255\017\001\021\001\255\255\000\000\
\021\001\255\255\255\255\255\255\002\001\003\001\004\001\031\001\
\032\001\033\001\031\001\032\001\033\001\011\001\012\001\255\255\
\014\001\002\001\003\001\004\001\255\255\255\255\000\000\021\001\
\005\001\255\255\011\001\012\001\255\255\255\255\255\255\255\255\
\255\255\031\001\032\001\033\001\021\001\255\255\000\000\020\001\
\255\255\022\001\023\001\024\001\255\255\255\255\031\001\032\001\
\033\001\010\000\011\000\012\000\255\255\255\255\035\001\036\001\
\255\255\018\000\255\255\255\255\255\255\000\000\255\255\255\255\
\255\255\255\255\255\255\028\000\029\000\030\000\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\041\000\255\255\255\255\000\000\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\000\000\002\001\003\001\004\001\005\001\006\001\255\255\
\255\255\255\255\255\255\011\001\012\001\255\255\014\001\255\255\
\016\001\017\001\000\000\006\001\020\001\021\001\255\255\255\255\
\011\001\012\001\255\255\014\001\255\255\016\001\017\001\031\001\
\032\001\033\001\000\000\035\001\036\001\002\001\003\001\004\001\
\005\001\006\001\255\255\255\255\255\255\255\255\011\001\012\001\
\255\255\014\001\255\255\016\001\017\001\006\001\255\255\020\001\
\021\001\255\255\011\001\012\001\255\255\014\001\255\255\016\001\
\017\001\255\255\031\001\032\001\033\001\006\001\035\001\036\001\
\002\001\003\001\004\001\005\001\006\001\014\001\255\255\016\001\
\017\001\011\001\012\001\255\255\014\001\006\001\016\001\017\001\
\255\255\006\001\020\001\021\001\255\255\014\001\255\255\016\001\
\017\001\014\001\255\255\016\001\017\001\031\001\032\001\033\001\
\006\001\035\001\036\001\002\001\003\001\004\001\255\255\006\001\
\014\001\255\255\016\001\017\001\011\001\012\001\255\255\014\001\
\255\255\016\001\017\001\255\255\255\255\255\255\021\001\255\255\
\255\255\255\255\002\001\003\001\004\001\255\255\006\001\255\255\
\031\001\032\001\033\001\011\001\012\001\255\255\014\001\255\255\
\016\001\017\001\255\255\255\255\255\255\021\001\255\255\255\255\
\255\255\002\001\003\001\004\001\255\255\006\001\255\255\031\001\
\032\001\033\001\011\001\012\001\255\255\014\001\255\255\016\001\
\017\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\002\001\003\001\004\001\255\255\006\001\255\255\031\001\032\001\
\033\001\011\001\012\001\255\255\014\001\255\255\016\001\017\001\
\002\001\003\001\004\001\255\255\255\255\255\255\255\255\255\255\
\255\255\011\001\012\001\255\255\255\255\031\001\032\001\033\001\
\255\255\255\255\255\255\021\001\255\255\255\255\255\255\002\001\
\003\001\004\001\255\255\006\001\255\255\031\001\032\001\033\001\
\011\001\012\001\255\255\014\001\255\255\016\001\017\001\255\255\
\255\255\255\255\255\255\255\255\255\255\002\001\003\001\004\001\
\255\255\006\001\255\255\255\255\031\001\032\001\011\001\012\001\
\255\255\014\001\255\255\016\001\017\001\255\255\255\255\255\255\
\255\255\255\255\255\255\002\001\003\001\004\001\255\255\006\001\
\255\255\255\255\031\001\032\001\011\001\012\001\255\255\014\001\
\255\255\016\001\017\001\255\255\002\001\003\001\004\001\255\255\
\006\001\255\255\255\255\255\255\255\255\011\001\012\001\255\255\
\014\001\255\255\016\001\017\001\002\001\003\001\004\001\255\255\
\006\001\255\255\255\255\255\255\255\255\011\001\012\001\255\255\
\014\001\255\255\016\001\017\001"

let yynames_const = "\
  EOF\000\
  FUN\000\
  GT\000\
  EQ\000\
  LT\000\
  LPAREN\000\
  RPAREN\000\
  DOT\000\
  COMMA\000\
  TRUE\000\
  FALSE\000\
  AND\000\
  OR\000\
  LET\000\
  IN\000\
  IF\000\
  THEN\000\
  ELSE\000\
  WITH\000\
  LAMBDA\000\
  NIL\000\
  CONS\000\
  HEAD\000\
  TAIL\000\
  ISNIL\000\
  TYINT\000\
  TYLIST\000\
  THINARROW\000\
  COLON\000\
  LBRACK\000\
  RBRACK\000\
  PLUS\000\
  SUB\000\
  TIMES\000\
  APP\000\
  "

let yynames_block = "\
  NUMBER\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 44 "parser.mly"
               ( _1 )
# 348 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 45 "parser.mly"
                ( syntax_error () )
# 354 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 48 "parser.mly"
         ( _1 )
# 361 "parser.ml"
               : 'bind))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bind) in
    Obj.repr(
# 51 "parser.mly"
                          ( [_1] )
# 368 "parser.ml"
               : 'bindlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'bind) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'bindlist) in
    Obj.repr(
# 52 "parser.mly"
                          ( _1 :: _3 )
# 376 "parser.ml"
               : 'bindlist))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'bindlist) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 59 "parser.mly"
                                             ( mk_lambdas _2 _4 )
# 384 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'bind) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'bindlist) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 60 "parser.mly"
                                             ( LetBind(_2, Fix (Lambda(_2, mk_lambdas _4 _6)), _8) )
# 394 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                                             ( IfThenElse(_2, _4, _6) )
# 403 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'bind) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                                             ( LetBind(_2, _4, _6) )
# 412 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'binop) in
    Obj.repr(
# 63 "parser.mly"
                                             ( _1 )
# 419 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 64 "parser.mly"
                                             ( _1 )
# 426 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 67 "parser.mly"
                                          ( Var(_1) )
# 433 "parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 68 "parser.mly"
                                          ( NumLit(_1) )
# 440 "parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "parser.mly"
                                          ( ListNil )
# 446 "parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 72 "parser.mly"
                                          ( Binop(_1, Add, _3) )
# 454 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 73 "parser.mly"
                                          ( Binop(_1, Sub, _3) )
# 462 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 74 "parser.mly"
                                          ( Binop(_1, Mul, _3) )
# 470 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 75 "parser.mly"
                                          ( Binop(_1, Lt, _3) )
# 478 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 76 "parser.mly"
                                          ( Binop(_1, Gt, _3) )
# 486 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 77 "parser.mly"
                                          ( Binop(_1, Eq, _3) )
# 494 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 78 "parser.mly"
                                          ( Binop(_1, And, _3) )
# 502 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 79 "parser.mly"
                                          ( Binop(_1, Or, _3) )
# 510 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 80 "parser.mly"
                                          ( ListCons(_1, _3) )
# 518 "parser.ml"
               : 'binop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 83 "parser.mly"
                                          ( _1 )
# 525 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 84 "parser.mly"
                                          ( ListHead _2 )
# 532 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 85 "parser.mly"
                                          ( ListTail _2 )
# 539 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 86 "parser.mly"
                                          ( ListIsNil _2 )
# 546 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 87 "parser.mly"
                                          ( _2 )
# 553 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 88 "parser.mly"
                                          ( App(_1, _2) )
# 561 "parser.ml"
               : 'term))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.expr)
