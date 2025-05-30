open OUnit2

let is_primitive id =
  List.mem
    id
    [ "+"
    ; "-"
    ; "*"
    ; "/"
    ; "cons"
    ; "car"
    ; "cdr"
    ; "pair?"
    ; "vector"
    ; "make-vector"
    ; "vector-length"
    ; "vector-ref"
    ; "vector-set!"
    ; "vector?"
    ; "string"
    ; "make-string"
    ; "string-length"
    ; "string-ref"
    ; "string-set!"
    ; "string?"
    ; "void"
    ]
;;

module%lang L0 = struct
  type expr =
    [ `Var of string
    | `Primitive of string
    | `Constant of [ `Int of int | `Char of char | `String of string ]
    | `Begin of expr list * expr
    | `If1 of expr * expr
    | `If of expr * expr * expr
    | `Lambda of string list * expr list * expr
    | `Let of (string * expr) list * expr list * expr
    | `Letrec of (string * expr) list * expr list * expr
    | `Apply of expr * expr list
    ]
end

module%lang L1 = struct
  include L0

  type expr =
    { del :
        [ `If1 of expr * expr
        | `Lambda of string list * expr list * expr
        | `Let of (string * expr) list * expr list * expr
        | `Letrec of (string * expr) list * expr list * expr
        ]
    ; add :
        [ `Lambda of string list * expr
        | `Let of (string * expr) list * expr
        | `Letrec of (string * expr) list * expr
        ]
    }
end

let%conv[@from L0 => L0] check_primitives =
  let exception Unknown_primitive of string in
  [%passes
    let[@entry] rec expr = function
      | `Primitive p ->
        if is_primitive p then `Primitive p else raise (Unknown_primitive p)
    ;;]
;;

let%conv[@from L0 => L1] make_explicit =
  [%passes
    let[@entry] rec expr = function
      | `If1 ((p [@r]), (e [@r])) -> `If (p, e, `Apply (`Primitive "void", []))
      | `Lambda (xs, (bodies [@r] [@l]), (body [@r])) ->
        `Lambda (xs, `Begin (bodies, body))
      | `Let (((xs, (es [@r])) [@l]), (bodies [@r] [@l]), (body [@r])) ->
        `Let (((xs, es) [@l]), `Begin (bodies, body))
      | `Letrec ((((_, (_ [@r])) [@l]) as binds), (bodies [@r] [@l]), (body [@r])) ->
        `Letrec (binds, `Begin (bodies, body))
    ;;]
;;

let test_ast =
  `Let
    ( [ "x", `Constant (`Int 5) ]
    , []
    , `If1
        ( `Apply (`Var "equal?", [ `Var "x"; `Constant (`Int 6) ])
        , `Apply (`Var "print", [ `Constant (`String "Hello, world!") ]) ) )
;;

let explicit_test_ast =
  `Let
    ( [ "x", `Constant (`Int 5) ]
    , `Begin
        ( []
        , `If
            ( `Apply (`Var "equal?", [ `Var "x"; `Constant (`Int 6) ])
            , `Apply (`Var "print", [ `Constant (`String "Hello, world!") ])
            , `Apply (`Primitive "void", []) ) ) )
;;

let tt =
  "docs_example"
  >::: [ ("make_explicit"
          >:: fun _ -> assert_equal (make_explicit test_ast) explicit_test_ast)
       ; ("check_primitives"
          >:: fun _ -> assert_equal (check_primitives test_ast) test_ast)
       ]
;;
