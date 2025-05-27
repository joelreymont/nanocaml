open Batteries
open Ppxlib
module Loc = Location
open Astlib

(** a type recognized by nanopass; usually a part of a production.
    e.g. [string], [stmt], [(string * expr) list] **)
type np_type =
  | NP_term of core_type (** external types are "terminals" **)
  | NP_nonterm of string (** named nonterminal **)
  | NP_tuple of np_type list (** [t * u * ...] **)
  | NP_list of np_type (** [t list] **)

(** a production is one of the forms in a nonterminal -- essentially
    just a variant, e.g. [`Var], [`App]. **)
type np_production =
  { nppr_name : string
  ; nppr_arg : np_type option
  }

(** a nonterminal is a type defined by a nanopass language, e.g.
    [expr], [stmt]. **)
type np_nonterm =
  { npnt_loc : Location.t
  ; npnt_name : string
  ; npnt_productions : np_production list
  }

(** a nanopass language, e.g. L0, L1 (as traditionally named) **)
type np_language =
  { npl_loc : Location.t
  ; npl_name : string
  ; npl_nonterms : np_nonterm list (* TODO: hash tbl? *)
  }

let rec string_of_type = function
  | NP_term core_type ->
    (match core_type.ptyp_desc with
     | Ptyp_constr ({ txt = l; _ }, _) ->
       "<core> (" ^ List.last (Longident.flatten l) ^ ")"
     | _ -> "<core>")
  | NP_nonterm s -> s
  | NP_tuple t -> "(" ^ String.concat "," (List.map string_of_type t) ^ ")"
  | NP_list t -> "[" ^ string_of_type t ^ "]"
;;

(* TODO: nv wants to make this into a real database,
     which would allow caching, cross-file nanopass, etc. *)
(** global table of all defined languages. **)
let languages : (string, np_language) Hashtbl.t = Hashtbl.create 30

(** globally registers the given language. raises
    [Location.Error] if a language with the same
    name is already defined. **)
let add_language lang =
  if Hashtbl.mem languages lang.npl_name
  then Location.raise_errorf ~loc:lang.npl_loc "language %S defined already" lang.npl_name
  else Hashtbl.add languages lang.npl_name lang
;;

(** returns the language with the given name. raises
    [Not_found] if no such language has been defined. **)
let find_language ?(exn = Not_found) name =
  Option.get_exn (Hashtbl.find_option languages name) exn
;;

(** [language_nonterm l name] returns the nonterminal
    in language [l] with the given name. raises [Not_found]
    if no such nonterminal. *)
let language_nonterm ?(exn = Not_found) lang name =
  List.find_exn (fun nt -> nt.npnt_name = name) exn lang.npl_nonterms
;;

(** convert [core_type] into nanopass type. **)
let type_of_core_type ~nt_names t =
  let rec cvt ptyp =
    match ptyp.ptyp_desc with
    (* nonterminal: *)
    | Ptyp_constr ({ txt = Longident.Lident name; _ }, []) when List.mem name nt_names ->
      NP_nonterm name
    (* tuple: *)
    | Ptyp_tuple typs ->
      let npts = List.map cvt typs in
      NP_tuple npts
    (* list: *)
    | Ptyp_constr ({ txt = Longident.Lident "list"; _ }, [ elem ]) -> NP_list (cvt elem)
    (* otherwise, it's a terminal: *)
    | _ -> NP_term ptyp
  in
  cvt t
;;

(** convert [row_field] (from polymorphic variant) into nanopass production **)
let production_of_row_field ~nt_names row =
  match row.prf_desc with
  | Rtag (loc, _, args) ->
    { nppr_name = loc.txt
    ; nppr_arg =
        (match args with
         | [ t ] -> Some (type_of_core_type ~nt_names t)
         | _ -> None)
    }
  | Rinherit { ptyp_loc = loc; _ } ->
    Location.raise_errorf ~loc "invalid nanopass production form"
;;

(** convert [type_declaration] into nanopass nonterminal **)
let nonterm_of_type_decl ?extending ~nt_names = function
  (* type nt = [ `A | `B ... ] *)
  | { ptype_name = { txt = name; _ }
    ; ptype_loc = loc
    ; ptype_params = []
    ; ptype_kind = Ptype_abstract
    ; ptype_manifest = Some { ptyp_desc = Ptyp_variant (rows, Closed, _); _ }
    ; _
    } ->
    let prods = List.map (production_of_row_field ~nt_names) rows in
    { npnt_loc = loc; npnt_name = name; npnt_productions = prods }
  (* type nt = { add : [ `A ... ] ; del : [ `B ... ] } *)
  | { ptype_name = { txt = name; _ }
    ; ptype_loc = loc
    ; ptype_params = []
    ; ptype_kind = Ptype_record decls
    ; _
    } ->
    let lang =
      Option.get_exn
        extending
        (Loc.Error
           (Loc.Error.createf ~loc "must be extending a language to use this form"))
    in
    let old_nontem =
      language_nonterm
        lang
        name
        ~exn:
          (Loc.Error
             (Loc.Error.createf
                ~loc
                "no such nonterminal %S in language %S"
                name
                lang.npl_name))
    in
    (* get the 'lname' label out of the record, and parse
        the productions contained in the type. *)
    let get_prods lname =
      match List.find_opt (fun { pld_name = { txt = x; _ }; _ } -> x = lname) decls with
      | None -> None
      | Some { pld_type = { ptyp_desc = Ptyp_variant (rows, Closed, _); _ }; _ } ->
        Some (List.map (production_of_row_field ~nt_names) rows)
      | Some _ -> Location.raise_errorf ~loc "invalid extended production"
    in
    (* create functions for adding productions / deleting productions
        if the 'add' or 'del' labels are omitted, then nothing is added / removed. *)
    let add =
      Option.map_default
        (fun add_prs -> List.append add_prs)
        identity (* do nothing when [None] *)
        (get_prods "add")
    in
    let del =
      Option.map_default
        (fun del_prs ->
           let keep p = List.for_all (fun p' -> p.nppr_name <> p'.nppr_name) del_prs in
           List.filter keep)
        identity
        (get_prods "del")
    in
    let prods = old_nontem.npnt_productions |> del |> add in
    { npnt_loc = loc; npnt_name = name; npnt_productions = prods }
  (* invalid nonterminal *)
  | { ptype_loc = loc; _ } ->
    Location.raise_errorf ~loc "invalid nanopass type declaration form"
;;

(** convert [module_binding] into nanopass language **)
let language_of_module = function
  (* module L = struct type nt = ... end *)
  (* must be one single recursive type decl *)
  | { pmb_name = { txt = Some lang_name; _ }
    ; pmb_loc = loc
    ; pmb_expr =
        { pmod_desc =
            Pmod_structure [ { pstr_desc = Pstr_type (Recursive, type_decls); _ } ]
        ; _
        }
    ; _
    } ->
    let nt_names = List.map (fun { ptype_name = { txt; _ }; _ } -> txt) type_decls in
    let nonterms = List.map (nonterm_of_type_decl ~nt_names) type_decls in
    { npl_loc = loc; npl_name = lang_name; npl_nonterms = nonterms }
  (* module L = struct
       include L'
       type nt = ...
     end *)
  (* must be a single include + a single recursive type decl*)
  | { pmb_name = { txt = Some lang_name; _ }
    ; pmb_loc = loc
    ; pmb_expr =
        { pmod_desc =
            Pmod_structure
              [ { pstr_desc =
                    Pstr_include
                      { pincl_mod =
                          { pmod_desc = Pmod_ident { txt = Lident ext_lang_name; _ }; _ }
                      ; _
                      }
                ; _
                }
              ; { pstr_desc = Pstr_type (Recursive, type_decls); _ }
              ]
        ; _
        }
    ; _
    } ->
    (* the language we are extending *)
    let ext_lang =
      find_language
        ext_lang_name
        ~exn:
          (Loc.Error
             (Loc.Error.createf ~loc "language %S has not been defined" ext_lang_name))
    in
    (* new nonterminal names *)
    let nt_names = List.map (fun { ptype_name = { txt; _ }; _ } -> txt) type_decls in
    (* old nonterminal names *)
    let nt_names' = List.map (fun { npnt_name; _ } -> npnt_name) ext_lang.npl_nonterms in
    (* new nonterminals *)
    let nonterms =
      List.map
        (nonterm_of_type_decl ~extending:ext_lang ~nt_names:(nt_names @ nt_names'))
        type_decls
    in
    (* old nonterminals (only the unmodified ones) *)
    let nonterms' =
      List.filter_map
        (fun name ->
           if List.mem name nt_names then None else Some (language_nonterm ext_lang name))
        nt_names'
    in
    { npl_loc = loc; npl_name = lang_name; npl_nonterms = nonterms @ nonterms' }
  | { pmb_loc = loc; _ } -> Location.raise_errorf ~loc "invalid nanopass language form"
;;
