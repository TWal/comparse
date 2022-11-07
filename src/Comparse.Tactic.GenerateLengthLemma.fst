module Comparse.Tactic.GenerateLengthLemma

open Comparse.Bytes.Typeclass
open Comparse.Parser
open Comparse.Tactic.Utils
open FStar.Tactics

val mk_lemma_type_ensures: GenerateParser.bytes_impl -> term -> term -> list ctor -> Tac term
let mk_lemma_type_ensures bi ps_term x_term ctors =
  let (opt_tag_parser, tag_opt_vals) =
    if GenerateParser.is_tagged_type ctors then (
      let (tag_typ, tag_vals) = GenerateParser.get_tag_from_ctors ctors in
      (Some (fst (GenerateParser.parser_from_type bi tag_typ)), List.Tot.map Some tag_vals)
    ) else (
      (None, List.Tot.map (fun _ -> None) ctors)
    )
  in
  let ctor_to_branch (c:ctor) (opt_tag_val:option term): Tac branch =
    let (ctor_name, ctor_type) = c in
    let binders, _ = collect_arr_bs ctor_type in
    let branch_pattern =
      Pat_Cons (pack_fv ctor_name) None (
        Tactics.Util.map (fun b ->
          let (b_bv, (q, _)) = inspect_binder b in
          (Pat_Var b_bv, not (Q_Explicit? q))
        ) binders
      )
    in
    let term_to_length (ps_t:term) (t:term) =
      (`(prefixes_length (Mkparser_serializer_prefix?.serialize (`#ps_t) (`#t))))
    in
    let binder_to_length (b:binder) =
      let (ps_b, _) = GenerateParser.parser_from_binder bi b in
      term_to_length ps_b (binder_to_term b)
    in
    let binders_length = Tactics.Util.map binder_to_length binders in
    let all_lengthes =
      match opt_tag_parser, opt_tag_val with
      | Some tag_parser, Some tag_val -> (
        (term_to_length tag_parser tag_val)::binders_length
      )
      | None, None -> (
        binders_length
      )
      | _, _ -> fail "mk_lemma_type_ensures: shouldn't happen ?!"
    in let branch_term = foldr1 (fun b_len acc -> (`((`#b_len) + (`#acc)))) all_lengthes in
    (branch_pattern, branch_term)
  in
  let lhs = `(prefixes_length (Mkparser_serializer_prefix?.serialize (`#ps_term) (`#x_term))) in
  let rhs = pack (Tv_Match x_term None (map2 ctor_to_branch ctors tag_opt_vals)) in
  `((`#lhs) == (`#rhs))

val mk_lemma_type_smtpat: term -> term -> Tac term
let mk_lemma_type_smtpat ps_term x_term =
  `(prefixes_length (Mkparser_serializer_prefix?.serialize (`#ps_term) (`#x_term)))

val mk_lemma_type: term -> list binder -> list ctor -> Tac term
let mk_lemma_type type_unapplied params ctors =
  let type_fv =
    match inspect type_unapplied with
    | Tv_FVar fv -> fv
    | _ -> fail ("mk_lemma_type: type_unapplied is not a fv: " ^ term_to_string type_unapplied)
  in
  let type_applied = apply_binders type_unapplied params in
  let (bi, parser_params) = GenerateParser.get_bytes_impl_and_parser_params params in
  let (bytes_term, bytes_like_term) = bi in
  let (ps_term, _) = GenerateParser.parser_from_type bi type_applied in
  let x_bv = fresh_bv_named "x" type_applied in
  let x_term = pack (Tv_Var x_bv) in
  let lemma_requires = (`True) in
  let lemma_ensures = mk_lemma_type_ensures bi ps_term x_term ctors in
  let lemma_smtpat = mk_lemma_type_smtpat ps_term x_term in
  let eff = pack_comp (C_Lemma lemma_requires (`(fun () -> (`#lemma_ensures))) (`([smt_pat (`#lemma_smtpat)]))) in
  mk_arr (parser_params @ [mk_binder x_bv]) eff

val my_isomorphism_length_with_id:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a ->
  a_to_b:(a -> b) -> b_to_a:(b -> a) ->
  a_to_b_to_a:(x:a -> squash (b_to_a (a_to_b x) == x)) ->
  b_to_a_to_b:(x:b -> squash (a_to_b (b_to_a x) == x)) ->
  xb:b ->
  squash
  (prefixes_length ((isomorphism ps_a ({a_to_b = id a_to_b; b_to_a = id b_to_a; a_to_b_to_a; b_to_a_to_b})).serialize xb) == prefixes_length (ps_a.serialize (b_to_a xb)))
let my_isomorphism_length_with_id #bytes #bl #a #b ps_a a_to_b b_to_a a_to_b_to_a b_to_a_to_b xb = ()

val my_isomorphism_length:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a ->
  a_to_b:(a -> b) -> b_to_a:(b -> a) ->
  a_to_b_to_a:(x:a -> squash (b_to_a (a_to_b x) == x)) ->
  b_to_a_to_b:(x:b -> squash (a_to_b (b_to_a x) == x)) ->
  xb:b ->
  squash
  (prefixes_length ((isomorphism ps_a ({a_to_b; b_to_a; a_to_b_to_a; b_to_a_to_b})).serialize xb) == prefixes_length (ps_a.serialize (b_to_a xb)))
let my_isomorphism_length #bytes #bl #a #b ps_a a_to_b b_to_a a_to_b_to_a b_to_a_to_b xb = ()

val simplify_length_lemma: unit -> Tac unit
let simplify_length_lemma () =
  if lax_on() then
    smt ()
  else (
    //Remove garbage from environment
    Tactics.Util.iter (fun b ->
      try clear b
      with _ -> ()
    ) (binders_of_env (cur_env()));

    //Retrieve the parser and value to unfold / destruct
    let (ps_term, x_term) =
      match inspect (cur_goal()) with
      | Tv_App hd (p, Q_Explicit) -> (
        guard (hd `term_fv_eq` (`squash));
        match collect_app p with
        | (eq_term, [_, Q_Implicit; lhs, Q_Explicit; rhs, Q_Explicit]) -> (
          guard (eq_term `term_fv_eq` (`(==)));
          let (prefixes_length_term, prefixes_length_args) = collect_app lhs in
          guard (List.Tot.length prefixes_length_args = 3);
          guard (prefixes_length_term `term_fv_eq` (`prefixes_length));
          let (serialize_term, serialize_args) = collect_app (fst (List.Tot.index prefixes_length_args 2)) in
          guard (List.Tot.length serialize_args = 5);
          guard (serialize_term `term_fv_eq` (`Mkparser_serializer_prefix?.serialize));
          (fst (List.Tot.index serialize_args 3), fst (List.Tot.index serialize_args 4))
        )
        | _ -> fail "goal is not an equality?"
      )
      | _ -> fail "goal is not a app?"
    in

    let ps_qn =
      let (ps_fv, _) = collect_app ps_term in
      implode_qn (get_name_from_fv ps_fv)
    in

    norm [delta_only [ps_qn]];

    let ctrl_with (what:term) (t:term): Tac (bool & ctrl_flag) =
      let (hd, args) = collect_app t in
      let hd_ok = hd `term_fv_eq` (`prefixes_length) in
      if hd_ok && List.Tot.length args = 3 then (
        let (hd2, args2) = collect_app (fst (List.Tot.index args 2)) in
        let hd2_ok = hd2 `term_fv_eq` (`Mkparser_serializer_prefix?.serialize) in
        if hd2_ok && List.Tot.length args2 = 5 then (
            let ps_term = List.Tot.index args2 3 in
            let (ps_unapplied_term, _) = collect_app (fst ps_term) in
            (ps_unapplied_term `term_fv_eq` what, Continue)
        ) else (
            (false, Continue)
        )
      ) else (
          (false, Continue)
      )
    in
    let rw_with_lemma (t:term) (): Tac unit =
      try (
        apply_lemma t
      ) with _ -> trefl()
    in

    //l_to_r [(`my_isomorphism_length); (`my_isomorphism_length_with_id)];
    ctrl_rewrite TopDown (ctrl_with (`isomorphism)) (rw_with_lemma (`my_isomorphism_length_with_id));
    ctrl_rewrite TopDown (ctrl_with (`isomorphism)) (rw_with_lemma (`my_isomorphism_length));

    destruct x_term;
    iterAll (fun () ->
      let destruct_binders = intros() in
      let breq_term = binder_to_term (last destruct_binders) in
      l_to_r_breq [breq_term];
      norm [iota];
      ctrl_rewrite TopDown (ctrl_with (`bind)) (rw_with_lemma (`bind_length));
      ctrl_rewrite TopDown (ctrl_with (`refine)) (rw_with_lemma (`refine_length));
      norm [primops; iota]
    );
    // Solve the goal by SMT, to use facts such as 0 == length (ps_unit.serialize ())
    //trefl();
    smt();
    gather_or_solve_explicit_guards_for_resolved_goals ()
  )

val mk_lemma_val: term -> Tac term
let mk_lemma_val lemma_type =
  let (lemma_binders, lemma_comp) = collect_arr_bs lemma_type in
  let prop =
    match inspect_comp lemma_comp with
    | C_Lemma _ ens _ -> (
      match inspect ens with
      | Tv_Abs _ p -> p
      | _ -> fail "mk_lemma_val: ensures is not a lambda?"
    )
    | _ -> fail "mk_lemma_val: lemma type is not a Lemma?"
  in
  let x = last (lemma_binders) in
  mk_abs lemma_binders (`(assert (`#prop) by (simplify_length_lemma ())))

val gen_length_lemma_def: term -> Tac (typ & term)
let gen_length_lemma_def type_fv =
  let env = top_env () in
  let type_name = get_name_from_fv type_fv in
  let type_declaration =
  match lookup_typ env type_name with
  | Some x -> x
  | None -> fail "Type not found?"
  in
  match inspect_sigelt type_declaration with
  | Sg_Inductive name [] params typ constructors -> (
    let lemma_type = mk_lemma_type type_fv params constructors in
    let lemma_val = mk_lemma_val lemma_type in
    (lemma_type,  lemma_val)
  )
  | Sg_Inductive _ _ _ _ _ -> fail "gen_length_lemma_def: higher order types are not supported"
  | _ -> fail "gen_length_lemma_def: only inductives are supported"

val gen_length_lemma: term -> Tac decls
let gen_length_lemma type_fv =
  let type_name = get_name_from_fv type_fv in
  let lemma_name = List.Tot.snoc (moduleof (top_env ()), "ps_" ^ (last type_name) ^ "_length") in
  let (lemma_type, lemma_val) = gen_length_lemma_def type_fv in
  //dump (term_to_string lemma_type);
  let lemma_letbinding = pack_lb ({
    lb_fv = pack_fv lemma_name;
    lb_us = [];
    lb_typ = lemma_type;
    lb_def = lemma_val;
  }) in
  [pack_sigelt (Sg_Let false [lemma_letbinding])]
