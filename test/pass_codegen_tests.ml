open Batteries
open OUnit2
open Ppxlib

let mkloc txt loc = { txt; loc }

let tt =
  let open Nanocaml.Pass in
  let open Nanocaml.Pass_codegen in
  let loc = !A.default_loc in
  let id_x = mkloc "x" loc in
  let id_y = mkloc "y" loc in
  let id_z = mkloc "z" loc in
  let id_tmp0 = fresh ~next_id:(ref 0) ~loc in
  let id_tmp1 = fresh ~next_id:(ref 1) ~loc in
  let id_tmp2 = fresh ~next_id:(ref 2) ~loc in
  let var_x = NPpat_var id_x in
  let var_y = NPpat_var id_y in
  let any = NPpat_any loc in
  let test_exp1 = [%expr foo a b c] in
  let test_exp2 = [%expr 1 + (2 * 3)] in
  let gen_pat ?(v = None) p = gen_pattern ~next_id:(ref 0) ~bind_as:v p in
  "pass_codegen"
  >::: [ ("compose_all"
          >:: fun _ ->
          let eq = assert_equal ~printer:Int.to_string in
          eq 4 (compose_all [] 4);
          eq 4 (compose_all [ succ ] 3);
          eq 19 (compose_all [ succ; ( * ) 3; succ ] 5))
       ; ("simple_let"
          >:: fun _ ->
          assert_equal
            (A.Exp.let_
               Asttypes.Nonrecursive
               [ A.Vb.mk (A.Pat.var id_x) test_exp1 ]
               test_exp2)
            (simple_let id_x test_exp1 test_exp2))
       ; ("vars_of_pattern"
          >:: fun _ ->
          assert_equal
            [ id_z; id_x; id_y ]
            (vars_of_pattern
               (NPpat_tuple
                  ( [ var_y
                    ; any
                    ; NPpat_map (NPpat_variant ("X", Some var_x, loc))
                    ; NPpat_cata (NPpat_alias (any, id_z), None)
                    ]
                  , loc ))))
       ; ("fold_exp"
          >:: fun _ ->
          let l = exp_of_id id_y in
          let z0 = exp_of_id id_z in
          let x = A.Pat.var id_x in
          let z = A.Pat.var id_z in
          let e = test_exp1 in
          assert_equal
            (A.Exp.apply
               (A.Exp.ident { txt = Ldot (Lident "List", "fold_right"); loc })
               [ Nolabel, A.Exp.fun_ Nolabel None x (A.Exp.fun_ Nolabel None z e)
               ; Nolabel, l
               ; Nolabel, z0
               ])
            (Lib_ast.fold_exp ~loc l z0 x z e))
       ; ("map_exp"
          >:: fun _ ->
          let l = exp_of_id id_y in
          let x = A.Pat.var id_x in
          let e = test_exp2 in
          assert_equal
            (A.Exp.apply
               (A.Exp.ident { txt = Ldot (Lident "List", "map"); loc })
               [ Nolabel, A.Exp.fun_ Nolabel None x e; Nolabel, l ])
            (Lib_ast.map_exp ~loc l x e))
       ; ("gen_pattern(1)"
          >:: fun _ ->
          assert_equal (A.Pat.any ()) (fst (gen_pat any));
          assert_equal (A.Pat.var id_x) (fst (gen_pat ~v:(Some id_x) any));
          assert_equal (A.Pat.var id_x) (fst (gen_pat var_x));
          assert_equal
            (A.Pat.alias (A.Pat.var id_x) id_y)
            (fst (gen_pat ~v:(Some id_y) var_x)))
       ; ("gen_pattern(2)"
          >:: fun _ ->
          (* _ as x  ==>  x *)
          assert_equal (A.Pat.var id_x) (fst (gen_pat (NPpat_alias (any, id_x))));
          (* BEFORE: (x as y) as z -> ee *)
          (* AFTER:  x as y        -> let z = y in ee *)
          let p, f = gen_pat ~v:(Some id_z) (NPpat_alias (var_x, id_y)) in
          assert_equal (A.Pat.alias (A.Pat.var id_x) id_y) p;
          assert_equal (simple_let id_z (exp_of_id id_y) test_exp1) (f test_exp1))
       ; ("gen_pattern(3)"
          >:: fun _ ->
          assert_equal
            (A.Pat.tuple [ A.Pat.var id_x; A.Pat.any () ])
            (fst (gen_pat (NPpat_tuple ([ var_x; any ], loc))));
          (* BEFORE: (x,_) as y           -> ee
           AFTER:  (x as t_0, t_1)      -> let y = t_0, t_1 in ee *)
          let p, f = gen_pat ~v:(Some id_y) (NPpat_tuple ([ var_x; any ], loc)) in
          assert_equal
            (A.Pat.tuple [ A.Pat.alias (A.Pat.var id_x) id_tmp0; A.Pat.var id_tmp1 ])
            p;
          assert_equal
            (simple_let
               id_y
               (A.Exp.tuple [ exp_of_id id_tmp0; exp_of_id id_tmp1 ])
               test_exp1)
            (f test_exp1))
       ; ("gen_pattern(4)"
          >:: fun _ ->
          assert_equal
            (A.Pat.variant "Z" None)
            (fst (gen_pat (NPpat_variant ("Z", None, loc))));
          assert_equal
            (A.Pat.variant "S" (Some (A.Pat.any ())))
            (fst (gen_pat (NPpat_variant ("S", Some any, loc))));
          (* BEFORE: `Z as y -> ee
           AFTER:  `Z      -> let y = `Z in e *)
          let p1, f1 = gen_pat ~v:(Some id_y) (NPpat_variant ("Z", None, loc)) in
          assert_equal (A.Pat.variant "Z" None) p1;
          assert_equal (simple_let id_y (A.Exp.variant "Z" None) test_exp1) (f1 test_exp1);
          (* BEFORE: (`S _) as y -> ee
           AFTER:  `S t_0      -> let y = `S t_0 in ee *)
          let p2, f2 = gen_pat ~v:(Some id_y) (NPpat_variant ("S", Some any, loc)) in
          assert_equal (A.Pat.variant "S" (Some (A.Pat.var id_tmp0))) p2;
          assert_equal
            (simple_let id_y (A.Exp.variant "S" (Some (exp_of_id id_tmp0))) test_exp2)
            (f2 test_exp2))
       ; ("gen_pattern(5)"
          >:: fun _ ->
          (* BEFORE: x [@r test1] -> ee
           AFTER:  t_0          -> let x = test1 t_0 in ee *)
          let p, f = gen_pat (NPpat_cata (var_x, Some test_exp1)) in
          assert_equal (A.Pat.var id_tmp0) p;
          assert_equal
            (simple_let
               id_x
               (A.Exp.apply test_exp1 [ Nolabel, exp_of_id id_tmp0 ])
               test_exp2)
            (f test_exp2))
       ; ("gen_pattern(6)"
          >:: fun _ ->
          (* BEFORE: (x,_) [@l] -> ee
           AFTER: t0 -> let x = Lib.map t0 (fun (x,_) -> x) in ee *)
          let p, f = gen_pat (NPpat_map (NPpat_tuple ([ var_x; any ], loc))) in
          assert_equal (A.Pat.var id_tmp0) p;
          assert_equal
            (simple_let
               id_x
               (Lib_ast.map_exp
                  ~loc
                  (exp_of_id id_tmp0)
                  (A.Pat.tuple [ A.Pat.var id_x; A.Pat.any () ])
                  (exp_of_id id_x))
               test_exp1)
            (f test_exp1))
       ; ("gen_pattern(7)"
          >:: fun _ ->
          (* BEFORE: (x,_,y) [@l] -> ee
           AFTER: t0 -> let x,y = Lib.fold t0 ([], []) (fun (x,_,y) (t1,t2) -> x::t1, y::t2) in ee *)
          let empty = A.Exp.construct { txt = Lident "[]"; loc } None in
          let cons e1 e2 =
            A.Exp.construct { txt = Lident "::"; loc } (Some (A.Exp.tuple [ e1; e2 ]))
          in
          let p, f = gen_pat (NPpat_map (NPpat_tuple ([ var_x; any; var_y ], loc))) in
          assert_equal (A.Pat.var id_tmp0) p;
          assert_equal
            (simple_pat_let
               (A.Pat.tuple [ A.Pat.var id_y; A.Pat.var id_x ])
               (Lib_ast.fold_exp
                  ~loc
                  (exp_of_id id_tmp0)
                  (A.Exp.tuple [ empty; empty ])
                  (A.Pat.tuple [ A.Pat.var id_x; A.Pat.any (); A.Pat.var id_y ])
                  (A.Pat.tuple [ A.Pat.var id_tmp1; A.Pat.var id_tmp2 ])
                  (A.Exp.tuple
                     [ cons (exp_of_id id_y) (exp_of_id id_tmp1)
                     ; cons (exp_of_id id_x) (exp_of_id id_tmp2)
                     ]))
               test_exp2)
            (f test_exp2))
       ; ("gen_pattern(8)"
          >:: fun _ ->
          (* BEFORE: `A (x [@l]) -> ee
           AFTER: `A t0 -> let x = Lib.map t0 (fun x -> x) in ee *)
          let p, f = gen_pat (NPpat_variant ("A", Some (NPpat_map var_x), loc)) in
          assert_equal (A.Pat.variant "A" (Some (A.Pat.var id_tmp0))) p;
          assert_equal
            (simple_let
               id_x
               (Lib_ast.map_exp
                  ~loc
                  (exp_of_id id_tmp0)
                  (A.Pat.var id_x)
                  (exp_of_id id_x))
               test_exp1)
            (f test_exp1))
       ; ("gen_pattern(9)"
          >:: fun _ ->
          (* BEFORE: x [@r foo] [@l] -> ee
           AFTER: t0 -> let x = Lib.map t0 (fun t1 -> let x = foo t1 in x) in ee *)
          let p, f = gen_pat (NPpat_map (NPpat_cata (var_x, Some test_exp1))) in
          assert_equal (A.Pat.var id_tmp0) p;
          assert_equal
            (simple_let
               id_x
               (Lib_ast.map_exp
                  ~loc
                  (exp_of_id id_tmp0)
                  (A.Pat.var id_tmp1)
                  (simple_let
                     id_x
                     (A.Exp.apply test_exp1 [ Nolabel, exp_of_id id_tmp1 ])
                     (exp_of_id id_x)))
               test_exp2)
            (f test_exp2))
         (* TODO: Fix this!
       ; ("gen_processor_vb(1)"
          >:: fun _ ->
          let proc =
            processor_of_rhs
              ~name:"b_of_a"
              ~dom:test_L0_a
              ~cod:(Some test_L0_b)
              ~loc
              [%expr
                fun u -> function
                | `A _ as a -> 1
                | `A0 -> 0]
          in
          (* let passname u = *)
          match gen_processor_vb test_L0 test_L0 proc with
          | { pvb_pat = { ppat_desc = Ppat_var { txt = "b_of_a"; _ }; _ }
            ; pvb_expr =
                { pexp_desc =
                    Pexp_function
                      ( Nolabel
                      , None
                      , { ppat_desc = Ppat_var { txt = "u"; _ }; _ }
                      , matcher_fn )
                }
            ; _
            } ->
            (* fun (arg0 : L0.a) : L0.b -> match arg0 with ... *)
            (match matcher_fn with
             | { pexp_desc =
                   Pexp_fun
                     ( Nolabel
                     , None
                     , { ppat_desc = Ppat_constraint (_, typ_in) }
                     , { pexp_desc =
                           Pexp_constraint ({ pexp_desc = Pexp_match (_, cases) }, typ_out)
                       } )
               } ->
               assert_equal
                 ~msg:"in = L0.a"
                 (A.Typ.constr { txt = Ldot (Lident "Test_L0", "a"); loc } [])
                 typ_in;
               assert_equal
                 ~msg:"out = L0.b"
                 (A.Typ.constr { txt = Ldot (Lident "Test_L0", "b"); loc } [])
                 typ_out;
               (match cases with
                | [ (* | `A t0 -> let a = `A t0 in 1 *)
                    { pc_lhs = { ppat_desc = Ppat_variant ("A", Some _) }
                    ; pc_guard = None
                    ; pc_rhs =
                        { pexp_desc =
                            Pexp_let
                              ( Nonrecursive
                              , [ _ ]
                              , { pexp_desc = Pexp_constant (Pconst_integer ("1", _)) } )
                        }
                    }
                  ; (* | `A0 -> 0 *)
                    { pc_lhs = { ppat_desc = Ppat_variant ("A0", None) }
                    ; pc_rhs = { pexp_desc = Pexp_constant (Pconst_integer ("0", _)) }
                    }
                  ] -> ()
                | _ -> assert_failure "matcher_fn OK; cases invalid")
             | _ -> assert_failure "outer OK; matcher_fn invalid")
          | _ -> assert_failure "processor output invalid")
       ; ("gen_processor_vb(2)"
          >:: fun _ ->
          let proc =
            processor_of_rhs
              ~name:"a_something"
              ~dom:test_L0_a
              ~cod:None
              ~loc
              [%expr
                function
                | `A _ as a -> 1
                | `A0 -> 0]
          in
          (* let passname (arg0 : L0.a) -> match arg0 with ... -- no output contraint*)
          match gen_processor_vb test_L0 test_L0 proc with
          | { pvb_pat = { ppat_desc = Ppat_var { txt = "a_something" } }
            ; pvb_expr =
                { pexp_desc =
                    Pexp_fun
                      ( Nolabel
                      , None
                      , { ppat_desc = Ppat_constraint (_, typ_in) }
                      , { pexp_desc = Pexp_match (_, [ case1; case2 ]) } )
                }
            } -> ()
          | _ -> assert_failure "processor output invalid")
         *)
       ]
;;
