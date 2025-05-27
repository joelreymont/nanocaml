open Batteries
open Ppxlib
open Astlib

type 'a loc = 'a Asttypes.loc
type fun_arg = Asttypes.arg_label * expression option * pattern

(** represents a nanopass definition **)
type np_pass =
  { npp_name : string
  ; npp_loc : Location.t
  ; npp_input : Lang.np_language (* source language *)
  ; npp_output : Lang.np_language (* target language *)
  ; npp_pre :
      expression -> expression (* generates expressions to precede productions / entry *)
  ; npp_post : expression (* entry point expression *)
  ; npp_procs : np_processor list (* proccessors *)
  }

(** represents a processor definition (a transformation
    between nonterminals in a nanopass) **)
and np_processor =
  { npc_name : string
  ; npc_loc : Location.t
  ; npc_dom : Lang.np_nonterm (* domain nonterminal *)
  ; npc_cod :
      Lang.np_nonterm option (* co-domain nonterminal (or terminal, when [None]) *)
  ; npc_args : fun_arg list (* arguments to processor *)
  ; npc_clauses : clause list (* processor clauses *)
  ; npc_clauses_loc : Location.t
  }

and clause = np_pat * expression

(** represents a pattern in a production. the pattern must be parsed
    by nanocaml so that we can correctly map over lists and apply
    catamorphims, e.g. for expressions like [(x, e [@r]) [@l]]. **)
and np_pat =
  (* TODO: [] and :: patterns *)
  | NPpat_any of Location.t (* _ *)
  | NPpat_var of string loc (* x *)
  | NPpat_alias of np_pat * string loc (* p as x *)
  | NPpat_tuple of np_pat list * Location.t (* (p, ...) *)
  | NPpat_variant of string * np_pat option * Location.t (* `X p *)
  | NPpat_map of np_pat (* list destructuring, e.g. (p [@l]) *)
  | NPpat_cata of np_pat * expression option (* p [@r <optional explicit cata>] *)

(** returns the [Location.t] of the given pattern. **)
let rec loc_of_pat = function
  | NPpat_any loc -> loc
  | NPpat_var { loc; _ } -> loc
  | NPpat_alias (_, { loc; _ }) -> loc
  | NPpat_tuple (_, loc) -> loc
  | NPpat_variant (_, _, loc) -> loc
  | NPpat_map p -> loc_of_pat p
  | NPpat_cata (p, _) -> loc_of_pat p
;;

(** See the comment on {{!expression_desc.Pexp_function} [Pexp_function]}. 
and function_body = Parsetree.function_body =
  | Pfunction_body of expression
  | Pfunction_cases of cases * location * attributes
       In [Pfunction_cases (_, loc, attrs)], the location extends from the
          start of the [function] keyword to the end of the last case. The
          compiler will only use typechecking-related attributes from [attrs],
          e.g. enabling or disabling a warning.

*)

(** convert the RHS of a [let] into a [np_processor]. **)
let rec processor_of_rhs ~name ~dom ~cod ~loc e0 =
  let arg_of_param param =
    match param.pparam_desc with
    | Pparam_val (lbl, opt, pat) -> lbl, opt, pat
    | Pparam_newtype _ ->
      Location.raise_errorf ~loc:param.pparam_loc "newtype is not allowed"
  in
  let rec get_args acc = function
    | { pexp_desc = Pexp_function (args, _, body); _ } ->
      let args1, cases, clauses_loc =
        match body with
        | Pfunction_cases (cases, clauses_loc, _) -> [], cases, clauses_loc
        | Pfunction_body expr -> get_args acc expr
      in
      acc @ args @ args1, cases, clauses_loc
    | { pexp_loc = loc; _ } ->
      Location.raise_errorf ~loc "processor must end in 'function' expression"
  in
  let clause_of_case { pc_lhs = p; pc_rhs = e; pc_guard = g } =
    match g with
    | Some { pexp_loc = loc; _ } ->
      Location.raise_errorf ~loc "guards not allowed in nanopass clauses"
    | None -> pat_of_pattern p, e
  in
  let args, cases, clauses_loc = get_args [] e0 in
  let args = List.map arg_of_param args in
  let clauses = List.map clause_of_case cases in
  { npc_name = name
  ; npc_dom = dom
  ; npc_cod = cod
  ; npc_loc = loc
  ; npc_args = args
  ; npc_clauses = clauses
  ; npc_clauses_loc = clauses_loc
  }

(** convert a [pattern] into a [np_pat]. **)
and pat_of_pattern p =
  let base_pat =
    match p.ppat_desc with
    | Ppat_any -> NPpat_any p.ppat_loc
    | Ppat_var x -> NPpat_var x
    | Ppat_alias (p, name) -> NPpat_alias (pat_of_pattern p, name)
    | Ppat_tuple ps -> NPpat_tuple (List.map pat_of_pattern ps, p.ppat_loc)
    | Ppat_variant (v, arg) -> NPpat_variant (v, Option.map pat_of_pattern arg, p.ppat_loc)
    | _ ->
      Location.raise_errorf
        ~loc:p.ppat_loc
        "this kind of pattern not allowed in nanopass clause"
  in
  p.ppat_attributes
  |> List.fold_left
       (fun pat { attr_name; attr_payload; _ } ->
          let { txt; loc } : string loc = attr_name in
          match txt, attr_payload with
          | "l", _ -> NPpat_map pat
          | "r", _ ->
            (match attr_payload with
             | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] -> NPpat_cata (pat, Some e)
             | PStr [] -> NPpat_cata (pat, None)
             | _ -> Location.raise_errorf ~loc "invalid argument to [@r] attribute")
          | _ -> pat)
       base_pat
;;

let signature_arrow = "=>"

(** extract [L0] and [L1] out of expression of form [L0 --> L1].
    returns [("L0", loc_L0), ("L1", loc_L1)] (for this particular example). **)
let extract_pass_sig = function
  | { pexp_desc =
        Pexp_apply
          ( { pexp_desc = Pexp_ident { txt = Lident arrow; _ }; _ }
          , [ ( Nolabel
              , { pexp_desc = Pexp_construct ({ txt = Lident l0_name; loc = l0_loc }, None)
                ; _
                } )
            ; ( Nolabel
              , { pexp_desc = Pexp_construct ({ txt = Lident l1_name; loc = l1_loc }, None)
                ; _
                } )
            ] )
    ; _
    }
    when arrow = signature_arrow -> (l0_name, l0_loc), (l1_name, l1_loc)
  | { pexp_loc = loc; _ } ->
    Location.raise_errorf
      ~loc
      "invalid language specification; expected 'LX %s LY'"
      signature_arrow
;;

(** extract domain and co-domain from the name of a production.
    the rules are:
      y_of_x  =>   dom="x", cod="y"
      x_to_y  =>   dom="x", cod="y"
      x       =>   dom=cod="x"
      x_f     =>   dom="x", cof=None

    if the co-domain is not a valid nonterm of the output language,
    then the co-domain is None.

    given the string name, returns [dom, opt_cod].
 **)
let extract_dom_cod ~loc l0 l1 name =
  let get_nt lang name =
    try Lang.language_nonterm lang name with
    | Not_found ->
      Location.raise_errorf
        ~loc
        "no such nonterminal %S in language %S"
        name
        lang.Lang.npl_name
  in
  let get_nt_opt lang name =
    try Some (Lang.language_nonterm lang name) with
    | Not_found -> None
  in
  (* TODO: not split on '_'!!!!! instead just search for "of"/"to" *)
  match String.split_on_char '_' name with
  | [ cod; "of"; dom ] -> get_nt l0 dom, get_nt_opt l1 cod
  | [ dom; "to"; cod ] -> get_nt l0 dom, get_nt_opt l1 cod
  | [ both ] -> get_nt l0 both, get_nt_opt l1 both
  | dom :: _ -> get_nt l0 dom, None
  | _ ->
    Location.raise_errorf
      ~loc
      "unable to infer processor input/output from processor's name"
;;

(** convert a [value_binding] into a [np_pass] *)
let pass_of_value_binding = function
  | { pvb_pat = { ppat_desc = Ppat_var { txt = name; _ }; _ }
    ; pvb_loc = loc
    ; pvb_expr = e0
    ; pvb_attributes = pass_attr :: _
    ; _
    } ->
    (* parse language from [[@pass L0 --> L1]] *)
    let find_lang ~loc l =
      Lang.find_language
        l
        ~exn:
          (Location.Error
             (Location.raise_errorf ~loc "Pass: language %S has not been defined" l))
    in
    let l0, l1 =
      match pass_attr.attr_payload with
      | PStr [ { pstr_desc = Pstr_eval (lang_expr, []); _ } ] ->
        let (l0_name, l0_loc), (l1_name, l1_loc) = extract_pass_sig lang_expr in
        find_lang ~loc:l0_loc l0_name, find_lang ~loc:l1_loc l1_name
      | _ -> Location.raise_errorf ~loc:pass_attr.attr_name.loc "invalid [@pass] syntax"
    in
    (* convert expression [e] into [f, vbs, body], where
        [vbs] are the value_bindings of the processors, [body]
        is the final expression, and [f] is a function that inserts
        its argument in place of the processors/body. *)
    let rec extract_definitions f = function
      | { pexp_desc = Pexp_extension ({ txt = "passes"; _ }, PStr stmts)
        ; pexp_loc = passes_loc
        ; _
        } ->
        let entry = ref None in
        let extract_stmt_bindings = function
          | { pstr_desc = Pstr_value (Recursive, vbs); _ } ->
            let set_entry_name = function
              | Ppat_var { txt = name; _ } -> entry := Some name
              | _ -> ()
            in
            List.iter
              (fun vb ->
                 if
                   List.exists
                     (fun { attr_name = { txt; _ }; _ } -> txt = "entry")
                     vb.pvb_attributes
                 then set_entry_name vb.pvb_pat.ppat_desc)
              vbs;
            vbs
          | _ -> []
        in
        let vbs =
          List.fold_right
            (fun bindings lst -> extract_stmt_bindings bindings @ lst)
            stmts
            []
        and body =
          match !entry with
          | None -> failwith "[%passes ...] requires a designated [@entry] function"
          | Some id ->
            { pexp_desc = Pexp_ident { txt = Lident id; loc = passes_loc }
            ; pexp_loc = passes_loc
            ; pexp_attributes = []
            ; pexp_loc_stack = []
            }
        in
        f, vbs, body
      | { pexp_desc = Pexp_function (_, _, body); _ } ->
        (match body with
         | Pfunction_body expr -> extract_definitions (fun e' -> f e') expr
         | Pfunction_cases (_, loc, _) ->
           Location.raise_errorf
             ~loc
             "let[@pass] must end in either a [%%passes ...] block or a recursive let, \
              followed by a single expression")
      | { pexp_desc = Pexp_letmodule (name, mod_expr, body); _ } as e ->
        extract_definitions
          (fun e' -> f { e with pexp_desc = Pexp_letmodule (name, mod_expr, e') })
          body
      | { pexp_desc = Pexp_letexception (exn, body); _ } as e ->
        extract_definitions
          (fun e' -> f { e with pexp_desc = Pexp_letexception (exn, e') })
          body
      | ({ pexp_desc = Pexp_let (recf, vbs, ({ pexp_desc = Pexp_let _; _ } as body)); _ }
         as e)
      | ({ pexp_desc = Pexp_let (recf, vbs, ({ pexp_desc = Pexp_extension _; _ } as body))
         ; _
         } as e) ->
        extract_definitions
          (fun e' -> f { e with pexp_desc = Pexp_let (recf, vbs, e') })
          body
      | { pexp_desc = Pexp_let (Recursive, vbs, body); _ } -> f, vbs, body
      | { pexp_loc = loc; _ } ->
        Location.raise_errorf
          ~loc
          "let[@pass] must end in either a [%%passes ...] block or a recursive let, \
           followed by a single expression"
    in
    let pre, bindings, post = extract_definitions identity e0 in
    (* parse processors from bindings in final letrec *)
    let procs =
      List.map
        (function
          | { pvb_pat = { ppat_desc = Ppat_var { txt = name; _ }; _ }
            ; pvb_expr = proc_rhs
            ; pvb_loc = loc
            ; _
            } ->
            (* parse dom/cod names *)
            let dom, cod = extract_dom_cod ~loc l0 l1 name in
            processor_of_rhs ~name ~loc ~dom ~cod proc_rhs
          | { pvb_loc = loc; _ } ->
            Location.raise_errorf ~loc "invalid processor definition")
        bindings
    in
    { npp_name = name
    ; npp_loc = loc
    ; npp_input = l0
    ; npp_output = l1
    ; npp_pre = pre
    ; npp_post = post
    ; npp_procs = procs
    }
  | { pvb_loc = loc; _ } -> Location.raise_errorf ~loc "invalid pass definition"
;;
