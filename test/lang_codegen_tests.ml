open OUnit2
open Ppxlib
open Ast_helper

let tt =
  "lang_codegen"
  >:::
  let open Nanocaml.Lang in
  let open Nanocaml.Lang_codegen in
  let loc = !default_loc in
  let ct_int = [%type: int] in
  let ct_expr = Typ.constr { txt = Lident "expr"; loc } [] in
  [ ("gen_core_type(1)"
     >:: fun _ ->
     assert_equal
       (Typ.constr
          ~loc
          { txt = Lident "list"; loc }
          [ Typ.tuple ~loc [ ct_int; ct_expr ] ])
       (gen_core_type ~loc (NP_list (NP_tuple [ NP_term ct_int; NP_nonterm "expr" ]))))
  ; ("gen_type_decl(1)"
     >:: fun _ ->
     assert_equal
       (Type.mk
          ~loc
          { txt = "expr"; loc }
          ~manifest:
            (Typ.variant
               ~loc
               [ { prf_desc = Rtag ({ txt = "Zero"; loc }, true, [])
                 ; prf_loc = loc
                 ; prf_attributes = []
                 }
               ; { prf_desc = Rtag ({ txt = "Succ"; loc }, false, [ ct_expr ])
                 ; prf_loc = loc
                 ; prf_attributes = []
                 }
               ]
               Closed
               None))
       (gen_type_decl
          { npnt_name = "expr"
          ; npnt_loc = loc
          ; npnt_productions =
              [ { nppr_name = "Zero"; nppr_arg = None }
              ; { nppr_name = "Succ"; nppr_arg = Some (NP_nonterm "expr") }
              ]
          }))
  ; ("gen_module_binding(1)"
     >:: fun _ ->
     let var_a =
       Typ.variant
         ~loc
         [ { prf_desc = Rtag ({ txt = "A"; loc }, true, [])
           ; prf_loc = loc
           ; prf_attributes = []
           }
         ]
         Closed
         None
     in
     let var_b =
       Typ.variant
         ~loc
         [ { prf_desc = Rtag ({ txt = "B"; loc }, false, [ ct_int ])
           ; prf_loc = loc
           ; prf_attributes = []
           }
         ]
         Closed
         None
     in
     assert_equal
       (Mb.mk
          ~loc
          { txt = Some "L0"; loc }
          (Mod.structure
             ~loc
             [ Str.type_
                 ~loc
                 Recursive
                 [ Type.mk ~loc { txt = "a"; loc } ~manifest:var_a
                 ; Type.mk ~loc { txt = "b"; loc } ~manifest:var_b
                 ]
             ]))
       (gen_module_binding
          { npl_name = "L0"
          ; npl_loc = loc
          ; npl_nonterms =
              [ { npnt_name = "a"
                ; npnt_loc = loc
                ; npnt_productions = [ { nppr_name = "A"; nppr_arg = None } ]
                }
              ; { npnt_name = "b"
                ; npnt_loc = loc
                ; npnt_productions =
                    [ { nppr_name = "B"; nppr_arg = Some (NP_term ct_int) } ]
                }
              ]
          }))
  ]
;;
