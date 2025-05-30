open Ppxlib
open Astlib

let expand_language ~ctxt node =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  match node with
  | [ { pstr_desc = Pstr_module mb; pstr_loc = loc } ] ->
    let lang = Lang.language_of_module mb in
    Lang.add_language lang;
    let mb' = Lang_codegen.gen_module_binding lang in
    { pstr_loc = loc; pstr_desc = Pstr_module mb' }
  | _ -> Location.raise_errorf ~loc "expecting a module"
;;

let gen_language =
  let pattern = Ast_pattern.(pstr __) in
  Extension.V3.declare
    "nanocaml.lang"
    Extension.Context.structure_item
    pattern
    expand_language
  |> Context_free.Rule.extension
;;

let expand_pass ~ctxt node =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  match node with
  (* let%conv[@from ...] pass_x = ... *)
  | [ ({ pvb_attributes = _; _ } as vb) ] ->
    let pass = Pass.pass_of_value_binding vb |> Pass_typeck.typeck_pass in
    let vb' = Pass_codegen.gen_pass_vb pass in
    { pstr_loc = loc; pstr_desc = Pstr_value (Nonrecursive, [ vb' ]) }
  | _ -> Location.raise_errorf ~loc "expecting a let binding"
;;

let gen_pass =
  let pattern = Ast_pattern.(pstr (pstr_value nonrecursive __ ^:: nil)) in
  Extension.V3.declare
    "nanocaml.conv"
    Extension.Context.structure_item
    pattern
    expand_pass
  |> Context_free.Rule.extension
;;

let () = Driver.register_transformation ~rules:[ gen_language; gen_pass ] "nanocaml"

(*
   let rewriter =
  object
    inherit Ast_traverse.map as super

    method! structure_item =
      function
      (* module%language Lx = ... *)
      | { pstr_loc = loc
        ; pstr_desc =
            Pstr_extension
              (({ txt = "language"; _ }, PStr [ { pstr_desc = Pstr_module mb; _ } ]), [])
        } ->
        Printf.eprintf "Rewriting module %s\n" (Option.get mb.pmb_name.txt);
        let lang = Lang.language_of_module mb in
        Lang.add_language lang;
        let mb' = Lang_codegen.gen_module_binding lang in
        { pstr_loc = loc; pstr_desc = Pstr_module mb' }
      (* let[@pass ...] pass_x = ... *)
      | { pstr_loc = loc
        ; pstr_desc =
            Pstr_value
              ( recflag
              , [ ({ pvb_attributes = [ { attr_name = { txt = "pass"; _ }; _ } ]; _ } as
                   vb)
                ] )
        } ->
        if recflag = Asttypes.Recursive
        then Location.raise_errorf ~loc "nanopass may not be declared recursive"
        else (
          Printf.eprintf "Rewriting pass\n";
          let pass = Pass.pass_of_value_binding vb |> Pass_typeck.typeck_pass in
          let vb' = Pass_codegen.gen_pass_vb pass in
          { pstr_loc = loc; pstr_desc = Pstr_value (Nonrecursive, [ vb' ]) })
      | str -> super#structure_item str
  end
;;

let () = Driver.register_transformation ~impl:rewriter#structure "language"
*)
