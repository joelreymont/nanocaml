open Batteries
open Ppxlib
open Astlib
open Lang
open Ast_helper

(** convert [np_type] into [core_type] **)
let rec gen_core_type ~loc = function
  | NP_term ct -> ct
  | NP_nonterm x ->
    let term_id : lid = { txt = Longident.Lident x; loc } in
    { ptyp_desc = Ptyp_constr (term_id, [])
    ; ptyp_loc = loc
    ; ptyp_attributes = []
    ; ptyp_loc_stack = []
    }
  | NP_tuple npts ->
    let cts = Ptyp_tuple (List.map (gen_core_type ~loc) npts) in
    { ptyp_desc = cts; ptyp_loc = loc; ptyp_attributes = []; ptyp_loc_stack = [] }
  | NP_list npt ->
    let elem_ct = gen_core_type ~loc npt in
    let list_ct = Ptyp_constr ({ txt = Longident.Lident "list"; loc }, [ elem_ct ]) in
    { ptyp_desc = list_ct; ptyp_loc = loc; ptyp_attributes = []; ptyp_loc_stack = [] }
;;

(** convert [np_nonterm] into [type_declaration] **)
let gen_type_decl { npnt_loc = loc; npnt_name = nt_name; npnt_productions = prds } =
  let row_of_prod { nppr_name = name; nppr_arg = arg } =
    let desc =
      Rtag
        ( { txt = name; loc }
        , Option.is_none arg
        , match arg with
          | Some npt -> [ gen_core_type ~loc npt ]
          | None -> [] )
    in
    { prf_desc = desc; prf_loc = loc; prf_attributes = [] }
  in
  let polyvar_desc = Ptyp_variant (List.map row_of_prod prds, Closed, None) in
  { ptype_name = { txt = nt_name; loc }
  ; ptype_loc = loc
  ; ptype_attributes = []
  ; ptype_params = []
  ; ptype_kind = Ptype_abstract
  ; ptype_cstrs = []
  ; ptype_private = Public
  ; ptype_manifest =
      Some
        { ptyp_desc = polyvar_desc
        ; ptyp_loc = loc
        ; ptyp_attributes = []
        ; ptyp_loc_stack = []
        }
  }
;;

(** convert [np_language] into [module_binding] **)
let gen_module_binding { npl_loc = loc; npl_name = lang_name; npl_nonterms = nonterms } =
  let struct_desc =
    Pmod_structure
      [ { pstr_desc = Pstr_type (Recursive, List.map gen_type_decl nonterms)
        ; pstr_loc = loc
        }
      ]
  in
  { pmb_name = { txt = Some lang_name; loc }
  ; pmb_loc = loc
  ; pmb_attributes = []
  ; pmb_expr = { pmod_desc = struct_desc; pmod_loc = loc; pmod_attributes = [] }
  }
;;
