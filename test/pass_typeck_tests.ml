open OUnit2
open Ppxlib
open Astlib
open Ast_helper

let test_L0 = Parsing_tests.test_L0
let test_L0_a = Parsing_tests.test_L0_a

let tt =
  "pass_typeck"
  >:::
  let open Nanocaml.Pass in
  let open Nanocaml.Lang in
  let module TC = Nanocaml.Pass_typeck in
  let loc = !default_loc in
  let pass1 =
    [%stri
      let[@pass Test_L0 => Test_L0] pass1 =
        let rec a = function
          | `A _ -> true
          | `A0 -> false
        and b = function
          | `B x -> a x
        in
        a
      ;;]
    |> Parsing_tests.stri_value_binding
    |> pass_of_value_binding
  in
  let any = NPpat_any loc in
  let var_x = NPpat_var { txt = "x"; loc } in
  [ ("catamorphism(1)"
     >:: fun _ ->
     let pass =
       Parsing_tests.stri_value_binding
         [%stri
           let[@pass Test_L0 => Test_L0] s =
             let rec a = function
               | `A0 _ -> 0
             in
             0
           ;;]
       |> pass_of_value_binding
     in
     match TC.catamorphism ~loc ~pass test_L0_a with
     | { pexp_desc = Pexp_ident { txt = Lident "a" } } -> ()
     | _ -> assert_failure "cata of 'a' has wrong form")
  ; ("catamorphism(2)"
     >:: fun _ ->
     let pass =
       Parsing_tests.stri_value_binding
         [%stri
           let[@pass Test_L0 => Test_L0] s =
             let rec b = function
               | `B _ -> 0
             in
             0
           ;;]
       |> pass_of_value_binding
     in
     try
       TC.catamorphism ~loc ~pass test_L0_a |> ignore;
       assert_failure "expected cata for 'a' to fail (not defined)"
     with
     | Location.Error _ -> ())
  ; ("typeck_pat(1)"
     >:: fun _ ->
     assert_equal any (TC.typeck_pat ~pass:pass1 (NP_nonterm "a") any);
     assert_equal var_x (TC.typeck_pat ~pass:pass1 (NP_nonterm "b") var_x))
  ; ("typeck_pat(2)"
     >:: fun _ ->
     let pat = NPpat_variant ("A", Some any, loc) in
     assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_nonterm "a") pat))
  ; ("typeck_pat(3)"
     >:: fun _ ->
     let pat = NPpat_alias (var_x, { txt = "y"; loc }) in
     assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_nonterm "a") pat);
     assert_equal pat (TC.typeck_pat ~pass:pass1 (NP_term [%type: int]) pat))
  ; ("typeck_pat(4)"
     >:: fun _ ->
     let pat = NPpat_tuple ([ any; any ], loc) in
     assert_equal
       pat
       (TC.typeck_pat ~pass:pass1 (NP_tuple [ NP_term [%type: int]; NP_nonterm "a" ]) pat)
    )
  ; ("typeck_pat(5)"
     >:: fun _ ->
     try
       TC.typeck_pat
         ~pass:pass1
         (NP_tuple [ NP_term [%type: int]; NP_nonterm "a" ])
         (NPpat_tuple ([ any; any; any ], loc))
       |> ignore;
       assert_failure "expected bad arg-count tuple to fail"
     with
     | Location.Error e ->
       assert_equal
         "wrong number of tuple arguments; expected 2, found 3"
         e.msg
         ~printer:(Printf.sprintf "%S"))
  ; ("typeck_pat(6)"
     >:: fun _ ->
     match TC.typeck_pat ~pass:pass1 (NP_nonterm "a") (NPpat_cata (var_x, None)) with
     (* x [@r] ==> x [@r a] *)
     | NPpat_cata
         (NPpat_var { txt = "x" }, Some { pexp_desc = Pexp_ident { txt = Lident "a" } })
       -> ()
     | _ -> assert_failure "elaborated (x [@r] : a) has wrong form")
  ; ("typeck_pat(7)"
     >:: fun _ ->
     match
       TC.typeck_pat
         ~pass:pass1
         (NP_list (NP_tuple [ NP_nonterm "a"; NP_term [%type: int] ]))
         (NPpat_cata (var_x, None))
     with
     (* x [@r] ==> (_ [@r a], _) [@l] as x *)
     | NPpat_alias
         ( NPpat_map (NPpat_tuple ([ NPpat_cata (NPpat_any _, Some _); NPpat_any _ ], _))
         , { txt = "x" } ) -> ()
     | _ -> assert_failure "elaborated (x [@r] : (a * int) list) has wrong form")
  ; ("typeck_nonterm(1)"
     >:: fun _ ->
     assert_equal None (TC.typeck_nonterm ~pass:pass1 ~loc "a" "A0" None);
     assert_equal (Some var_x) (TC.typeck_nonterm ~pass:pass1 ~loc "a" "A" (Some var_x)))
  ; ("typeck_nonterm(2)"
     >:: fun _ ->
     try
       TC.typeck_nonterm ~pass:pass1 ~loc "a" "A0" (Some any) |> ignore;
       assert_failure "expected typeck to fail (nonterm doesn't expect arguments)"
     with
     | Location.Error e ->
       assert_equal "unexpected" (String.sub e.msg 0 10) ~printer:(Printf.sprintf "%S"))
  ; ("typeck_nonterm(3)"
     >:: fun _ ->
     try
       TC.typeck_nonterm ~pass:pass1 ~loc "a" "A" None |> ignore;
       assert_failure "expected typeck to fail (nonterm expects arguments)"
     with
     | Location.Error e ->
       assert_equal "expected" (String.sub e.msg 0 8) ~printer:(Printf.sprintf "%S"))
  ; ("typeck_cata(1)"
     >:: fun _ ->
     let cata = [%expr fn a b c] in
     assert_equal
       (`Infer cata)
       (TC.typeck_cata ~pass:pass1 ~loc (Some cata) (NP_nonterm "a") any);
     assert_equal
       (`Infer (Exp.ident ~loc { txt = Lident "a"; loc }))
       (TC.typeck_cata ~pass:pass1 ~loc None (NP_nonterm "a") any);
     assert_equal
       (`Rewrite any)
       (TC.typeck_cata ~pass:pass1 ~loc None (NP_term [%type: int]) any))
  ; ("typeck_cata(2)"
     >:: fun _ ->
     match
       TC.typeck_cata
         ~pass:pass1
         ~loc
         None
         (NP_tuple [ NP_term [%type: int]; NP_nonterm "a" ])
         any
     with
     | `Rewrite (NPpat_tuple ([ NPpat_cata (_, None); NPpat_cata (_, None) ], _)) -> ()
     | _ -> assert_failure "rewritten tuple has wrong form")
  ; ("typeck_cata(3)"
     >:: fun _ ->
     match
       TC.typeck_cata
         ~pass:pass1
         ~loc
         None
         (NP_tuple [ NP_term [%type: int]; NP_nonterm "a" ])
         var_x
     with
     | `Rewrite
         (NPpat_alias
            ( NPpat_tuple ([ NPpat_cata (_, None); NPpat_cata (_, None) ], _)
            , { txt = "x" } )) -> ()
     | _ -> assert_failure "rewritten tuple (+ alias) has wrong form")
  ; ("typeck_cata(4)"
     >:: fun _ ->
     let cata = [%expr fn a b c] in
     match TC.typeck_cata ~pass:pass1 ~loc (Some cata) (NP_list (NP_nonterm "a")) any with
     | `Rewrite (NPpat_map (NPpat_cata (NPpat_any _, Some _))) -> ()
     | _ -> assert_failure "rewritten list has wrong form")
  ; ("typeck_cata(5)"
     >:: fun _ ->
     try
       TC.typeck_cata
         ~pass:pass1
         ~loc
         None
         (NP_nonterm "a")
         (NPpat_variant ("A", None, loc))
       |> ignore;
       assert_failure "expected non-total pattern in cata result to fail"
     with
     | Location.Error _ -> ())
  ]
;;
