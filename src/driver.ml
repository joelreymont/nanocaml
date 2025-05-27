open Ppxlib
open Astlib

let rewriter_old ~ctxt:_ =
  object
    inherit Ast_traverse.map as super

    method! structure_item =
      function
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
          let pass = Pass.pass_of_value_binding vb |> Pass_typeck.typeck_pass in
          let vb' = Pass_codegen.gen_pass_vb pass in
          { pstr_loc = loc; pstr_desc = Pstr_value (Nonrecursive, [ vb' ]) })
      | x -> super#structure_item x
  end
;;

let rewriter ~ctxt node =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  match node with
  | [ { pstr_desc = Pstr_module mb; pstr_loc = loc } ] ->
    let lang = Lang.language_of_module mb in
    Lang.add_language lang;
    let mb' = Lang_codegen.gen_module_binding lang in
    { pstr_loc = loc; pstr_desc = Pstr_module mb' }
  | _ -> Location.raise_errorf ~loc "expecting  module"
;;

let gen_language =
  let pattern =
    let open Ast_pattern in
    (* pstr (pstr_extension (extension drop __) drop ^:: nil) *)
    pstr __
  in
  Extension.V3.declare "language" Extension.Context.structure_item pattern rewriter
  |> Context_free.Rule.extension
;;

let () = Driver.register_transformation ~rules:[ gen_language ] "language"

let pass =
  let pattern =
    let open Ast_pattern in
    pstr (pstr_value nonrecursive __ ^:: nil)
  in
  Attribute.declare "language.pass" Attribute.Context.pstr_extension pattern (fun x -> x)
;;
