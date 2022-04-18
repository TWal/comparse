module MLS.ParserTac

open FStar.Tactics

assume new type parser_serializer (a:Type)
assume val bind: #a:Type -> #b:(a -> Type) -> parser_serializer a -> (x:a -> parser_serializer (b x)) -> parser_serializer (x:a & b x)

assume new type char
assume val ps_char: parser_serializer char
assume val ps_unit: parser_serializer unit

type nat_lbytes (sz:nat) = n:nat{n < normalize_term (pow2 (8 `op_Multiply` sz))}
assume val ps_nat_lbytes: sz:nat -> parser_serializer (nat_lbytes sz)

assume val isomorphism_explicit:
  #a:Type -> b:Type ->
  ps_a:parser_serializer a -> f:(a -> b) -> g:(b -> a) ->
  g_f_inv:(xa:a -> squash (g (f xa) == xa)) -> f_g_inv:(xb:b -> squash (f (g xb) == xb)) ->
  parser_serializer b

type refined (a:Type) (pred:a -> bool) = x:a{pred x}

assume val refine:
  #a:Type ->
  parser_serializer a -> pred:(a -> bool) -> parser_serializer (refined a pred)

// `l_to_r` is so slow!
val my_l_to_r: list term -> Tac unit
let my_l_to_r l =
  let squashed_equality =
    match l with
    | [x] -> x
    | _ -> fail ""
  in
  let squashed_equality_ty = (tc (cur_env ()) squashed_equality) in
  let x_term =
    match inspect squashed_equality_ty with
    | Tv_App squash_term (equality_term, Q_Explicit) -> (
      guard (squash_term `term_eq` (`squash));
      let eq2_term, args = collect_app equality_term in
      guard (eq2_term `term_eq` (`eq2));
      guard (List.Tot.length args = 3);
      let [_; (x_term, _); _] = args in
      guard (Tv_Var? (inspect x_term));
      x_term
    )
    | _ -> fail "malformed equality"
  in
  let ctrl (t:term) : Tac (bool & ctrl_flag) =
    let res =
      match inspect t with
      | Tv_Var _ -> t `term_eq` x_term
      | _ -> false
    in
    res, Continue
  in
  let rw () : Tac unit =
    apply_lemma_rw squashed_equality
  in
  ctrl_rewrite BottomUp ctrl rw


(*** Utility functions ***)

type parser_term = term & typ

val parser_name_from_type_name: name -> Tac name
let rec parser_name_from_type_name l =
  match l with
  | [] -> fail "parser_name_from_type_name: empty name?"
  | [x] -> ["ps_" ^ x]
  | h::t -> h::(parser_name_from_type_name t)

val mk_ie_app: term -> list term -> list term -> Tac term
let mk_ie_app t implicits explicits =
  let i t = (t, Q_Implicit) in
  let e t = (t, Q_Explicit) in
  mk_app (mk_app t (List.Tot.map i implicits)) (List.Tot.map e explicits)

val parser_from_type: term -> Tac parser_term
let parser_from_type t =
  let type_unapplied, type_args = collect_app t in
  match inspect type_unapplied with
  | Tv_FVar fv ->
    let parser_type_unapplied = pack (Tv_FVar (pack_fv (parser_name_from_type_name (inspect_fv fv)))) in
    (mk_app parser_type_unapplied type_args, t)
  | _ -> fail "parser_from_type: head given by `collect_app` is not a fv?"

val mk_parser_unit: unit -> parser_term
let mk_parser_unit () =
  (`ps_unit, `unit)

val mk_const_function: typ -> term -> Tac term
let mk_const_function ty t =
  pack (Tv_Abs (mk_binder (fresh_bv ty)) t)

(*** Parser for nested pairs ***)

val mk_parser_pair: parser_term -> parser_term -> Tac parser_term
let mk_parser_pair (ps_a, t_a) (ps_b, t_b) =
  let ps_ab = mk_ie_app (quote bind) [t_a; mk_const_function t_a t_b] [ps_a; mk_const_function t_a ps_b] in
  let t_ab = mk_e_app (quote dtuple2) [t_a; mk_const_function t_a t_b] in
  (ps_ab, t_ab)

val mk_parser_pairs: list term -> Tac parser_term
let rec mk_parser_pairs l =
  match l with
  | [] -> mk_parser_unit ()
  | [x] -> parser_from_type x
  | h::t -> (
    let pst_h = parser_from_type h in
    let pst_t = mk_parser_pairs t in
    mk_parser_pair pst_h pst_t
  )

(*** Parser for records ***)

val mkdtuple2_fv: unit -> Tac fv
let mkdtuple2_fv () =
  pack_fv (explode_qn (`%Mkdtuple2))

val mk_destruct_pairs: list typ -> Tac (pattern & list bv)
let rec mk_destruct_pairs l =
  match l with
  | [] -> fail "mk_destruct_pair: list too short (zero element)"
  | [h] -> (
    let bv_h = fresh_bv h in
    (Pat_Var bv_h, [bv_h])
  )
  | h::t -> (
    let bv_h = fresh_bv h in
    let (pattern_t, bv_t) = mk_destruct_pairs t in
    let pattern = Pat_Cons (mkdtuple2_fv ()) [(Pat_Var bv_h, false); (pattern_t, false)] in
    let bvs = bv_h::bv_t in
    (pattern, bvs)
  )

val mk_construct_record: name -> list bv -> Tac term
let mk_construct_record constructor_name bvs =
  let constructor_term = (pack (Tv_FVar (pack_fv constructor_name))) in
  let constructor_args = Tactics.Util.map (fun bv -> (pack (Tv_Var bv), Q_Explicit)) bvs in
  mk_app constructor_term constructor_args

val mk_record_isomorphism_f: typ -> name -> list typ -> Tac term
let mk_record_isomorphism_f result_type constructor_name constructor_types =
  let (match_pattern, bvs) = mk_destruct_pairs constructor_types in
  let match_body = mk_construct_record constructor_name bvs in
  let x_bv = fresh_bv result_type in
  pack (Tv_Abs (mk_binder x_bv) (pack (Tv_Match (pack (Tv_Var x_bv)) None [(match_pattern, match_body)])))

val mk_construct_pairs: list bv -> Tac term
let rec mk_construct_pairs l =
  match l with
  | [] -> fail "mk_construct_pair: list too short (zero element)"
  | [h] -> pack (Tv_Var h)
  | h::t ->
    mk_e_app (quote Mkdtuple2) [pack (Tv_Var h); mk_construct_pairs t]

val mk_record_isomorphism_g: typ -> name -> list typ -> Tac term
let mk_record_isomorphism_g input_type constructor_name constructor_types =
  let bvs = Tactics.Util.map (fun t -> fresh_bv t) constructor_types in
  let match_pattern = Pat_Cons (pack_fv constructor_name) (List.Tot.map (fun bv -> (Pat_Var bv, false)) bvs) in
  let match_body = mk_construct_pairs bvs in
  let x_bv = fresh_bv input_type in
  pack (Tv_Abs (mk_binder x_bv) (pack (Tv_Match (pack (Tv_Var x_bv)) None [(match_pattern, match_body)])))

val dtuple2_ind: #a:Type -> #b:(a -> Type) -> p:((x:a & b x) -> Type0) -> squash (forall (x:a) (y:b x). p (|x, y|)) -> Lemma (forall xy. p xy)
let dtuple2_ind #a #b p _ = ()

val arrow_to_forall: #a:Type -> p:(a -> Type0) -> squash (forall (x:a). p x) -> (x:a -> squash (p x))
let arrow_to_forall #a p _ x =
  ()

val prove_record_isomorphism_from_pair: unit -> Tac unit
let prove_record_isomorphism_from_pair () =
  apply (`arrow_to_forall);
  let _ = repeat (fun () ->
    apply_lemma (`dtuple2_ind);
    let _ = forall_intro () in
    ()
  ) in
  let _ = forall_intro () in
  trefl()

val last: #a:Type0 -> list a -> Tac a
let last l =
  guard (Cons? l);
  List.Tot.last l

val prove_record_isomorphism_from_record: unit -> Tac unit
let prove_record_isomorphism_from_record () =
  apply (`arrow_to_forall);
  let b = forall_intro () in
  destruct (binder_to_term b);
  let binders = intros () in
  let breq = last binders in
  my_l_to_r [binder_to_term breq];
  trefl ()

val mk_record_isomorphism: typ -> name -> list typ -> parser_term -> Tac parser_term
let mk_record_isomorphism result_type constructor_name constructor_types (parser_term, parser_type) =
  let result_parser_term =
    mk_ie_app (quote isomorphism_explicit) [parser_type] [
      result_type;
      parser_term;
      mk_record_isomorphism_f parser_type constructor_name constructor_types;
      mk_record_isomorphism_g result_type constructor_name constructor_types;
      (`(synth_by_tactic (prove_record_isomorphism_from_pair)));
      (`(synth_by_tactic (prove_record_isomorphism_from_record)));
    ]
  in
  (result_parser_term, result_type)

(*** Parser for sum type ***)

// Annotation
let with_tag (#a:Type0) (x:a) = ()

val get_tag_from_annot: name -> list term -> Tac (typ & term)
let rec get_tag_from_annot ctor_name l =
  match l with
  | [] -> fail ("get_tag_from_annot: no annotation for constructor " ^ (implode_qn ctor_name))
  | h::t -> (
    let (head, args) = collect_app h in
    if term_eq head (`with_tag) && List.Tot.length args = 2 then (
      let [(tag_typ, _); (tag_val, _)] = args in
      (tag_typ, tag_val)
    ) else (
      get_tag_from_annot ctor_name t
    )
  )

val get_tag_from_ctor: ctor -> Tac (typ & term)
let get_tag_from_ctor (ctor_name, ctor_typ) =
  match inspect ctor_typ with
  | Tv_Arrow b _ ->
    let _, (_, annotations) = inspect_binder b in
    get_tag_from_annot ctor_name annotations
  | _ -> fail "get_tag: not an arrow"

val sanitize_tags: list (typ & term) -> Tac (typ & (list term))
let sanitize_tags tags =
  guard (Cons? tags);
  let tag_typs, tag_vals = List.Tot.unzip tags in
  let tag_typ =
    guard (List.Tot.for_all (fun x -> term_eq x (Cons?.hd tag_typs)) tag_typs);
    Cons?.hd tag_typs
  in
  (tag_typ, tag_vals)

val mk_tag_parser: typ -> list typ -> Tac parser_term
let mk_tag_parser tag_typ tag_vals =
  let pred =
    let tag_bv = fresh_bv tag_typ in
    let tag_term = pack (Tv_Var tag_bv) in
    let mk_disj value acc: Tac term = `(((`#tag_term) = (`#value)) || (`#acc)) in
    guard (Cons? tag_vals);
    let tag_vals_head::tag_vals_tail = tag_vals in
    let disj = fold_right mk_disj tag_vals_tail (`((`#tag_term) = (`#tag_vals_head))) in
    pack (Tv_Abs (mk_binder tag_bv) disj)
  in
  let (tag_parser, tag_typ) = parser_from_type tag_typ in
  (mk_ie_app (`refine) [tag_typ] [tag_parser; pred], mk_e_app (`refined) [tag_typ; pred])


val term_to_pattern: term -> Tac pattern
let term_to_pattern t =
  match inspect t with
  | Tv_FVar fv -> Pat_Cons fv []
  | Tv_Const c -> Pat_Constant c
  | _ -> fail "term_to_pattern: term type not handled (not fv or const)"

val mk_middle_sum_type_parser: parser_term -> list term -> list ctor -> Tac (parser_term & term)
let mk_middle_sum_type_parser (tag_parser, tag_typ) tag_vals ctors =
  let pair_parsers =
    Tactics.Util.map
      (fun (ctor_name, ctor_typ) ->
        let types, _ = collect_arr ctor_typ in
        mk_parser_pairs types
      )
      ctors
  in
  let (tag_to_pair_type_term, tag_to_pair_parser_term) =
    let tag_bv = fresh_bv tag_typ in
    let tag_term = pack (Tv_Var tag_bv) in
    // Should be provable, but a dynamic check is enough
    guard (List.Tot.length tag_vals = List.Tot.length pair_parsers);
    let (branches_typ, branches_term) =
      List.Tot.unzip (
        Tactics.Util.map
          (fun (tag_val, (pair_parser_term, pair_parser_typ)) -> (
            (term_to_pattern tag_val, pair_parser_typ),
            (term_to_pattern tag_val, pair_parser_term)
          ))
          (List.Pure.zip tag_vals pair_parsers)
      )
    in
    (
      pack (Tv_Abs (mk_binder tag_bv) (pack (Tv_Match tag_term None branches_typ))),
      pack (Tv_Abs (mk_binder tag_bv) (pack (Tv_Match tag_term None branches_term)))
    )
  in
  let middle_parser = mk_ie_app (`bind) [tag_typ; tag_to_pair_type_term] [tag_parser; tag_to_pair_parser_term] in
  let middle_typ = mk_e_app (`dtuple2) [tag_typ; tag_to_pair_type_term] in
  ((middle_parser, middle_typ), tag_to_pair_type_term)

val mk_middle_to_sum_fun: typ -> term -> list term -> list ctor -> Tac term
let mk_middle_to_sum_fun tag_typ tag_to_pair_typ tag_vals ctors =
  guard (List.Tot.length tag_vals = List.Tot.length ctors);
  let branches =
    Tactics.Util.map
      (fun (tag_val, (ctor_name, ctor_typ)) ->
        //dump ("A " ^ term_to_string ctor_typ);
        let types, _ = collect_arr ctor_typ in
        let (pair_pattern, bvs) = mk_destruct_pairs types in
        let rec_term = mk_construct_record ctor_name bvs in
        let bvs = Tactics.Util.map (fun ty -> fresh_bv ty) types in
        let pattern = Pat_Cons (mkdtuple2_fv ()) [(term_to_pattern tag_val, false); (pair_pattern, false)] in
        (pattern, rec_term)
      )
      (List.Pure.zip tag_vals ctors)
  in
  //dump ("B " ^ term_to_string (mk_e_app (`dtuple2) [tag_typ; tag_to_pair_typ]));
  let pair_bv = fresh_bv (mk_e_app (`dtuple2) [tag_typ; tag_to_pair_typ]) in
  pack (Tv_Abs (mk_binder pair_bv) (pack (Tv_Match (pack (Tv_Var pair_bv)) None branches)))

val mk_sum_to_middle_fun: typ -> list term -> list ctor -> Tac term
let mk_sum_to_middle_fun sum_typ tag_vals ctors =
  guard (List.Tot.length tag_vals = List.Tot.length ctors);
  let branches =
    Tactics.Util.map
      (fun (tag_val, (ctor_name, ctor_typ)) ->
        let (ctor_typs, _) = collect_arr ctor_typ in
        let bvs = Tactics.Util.map (fun t -> fresh_bv t) ctor_typs in
        let match_pattern = Pat_Cons (pack_fv ctor_name) (List.Tot.map (fun bv -> (Pat_Var bv, false)) bvs) in
        let pairs_term = mk_construct_pairs bvs in
        let match_body = mk_e_app (`Mkdtuple2) [tag_val; pairs_term] in
        (match_pattern, match_body)
      )
      (List.Pure.zip tag_vals ctors)
  in
  //dump ("C " ^ term_to_string sum_typ);
  let sum_bv = fresh_bv sum_typ in
  pack (Tv_Abs (mk_binder sum_bv) (pack (Tv_Match (pack (Tv_Var sum_bv)) None branches)))

val refined_ind: a:Type -> pred:(a -> bool) -> p:(a -> Type0) -> squash (forall (x:a). pred x ==> p x) -> squash (forall (x:refined a pred). p x)
let refined_ind a pred p _ = ()

val or_split: b1:bool -> b2:bool -> p:Type0 -> squash (b1 ==> p) -> squash (b2 ==> p) -> squash (b1 || b2 ==> p)
let or_split b1 b2 p _ _ = ()

val eq_to_eq: a:eqtype -> x:a -> y:a -> p:Type0 -> squash (x == y ==> p) -> squash (x = y ==> p)
let eq_to_eq a x y p _ = ()
let test_implies_intro_1 p q (f: squash p -> squash q)
  : squash (p ==> q)
  = introduce p ==> q
    with x. f x

val add_squash: p:Type0 -> q:Type0 -> squash (squash p ==> q) -> squash (p ==> q)
let add_squash p q _ =
  introduce p ==> q with _. ()

val remove_refine: a:Type0 -> p:(a -> Type0) -> q:(a -> Type0) -> squash (forall (x:a). q x) -> squash (forall (x:a{p x}). q x)
let remove_refine a p q _ = ()

val prove_pair_sum_pair_isomorphism: unit -> Tac unit
let prove_pair_sum_pair_isomorphism () =
  apply (`arrow_to_forall);
  apply_lemma (`dtuple2_ind);
  apply (`refined_ind);
  // TODO remove this horrible thing.
  // Need https://github.com/FStarLang/FStar/pull/2482 to be merged first
  compute(); let _ = repeatn 2 (fun () -> apply (`remove_refine)) in
  let _ = forall_intro () in
  compute ();
  let solve_one_goal () =
    apply (`eq_to_eq);
    apply (`add_squash);
    let x_eq_term = binder_to_term (implies_intro ()) in
    my_l_to_r [x_eq_term];
    let _ = repeat (fun () ->
      apply_lemma (`dtuple2_ind);
      let _ = forall_intro () in
      ()
    ) in
    let _ = forall_intro () in
    trefl()
  in
  let _ = repeat (fun () ->
    apply (`or_split);
    focus solve_one_goal
  ) in
  focus solve_one_goal

val prove_sum_pair_sum_isomorphism: unit -> Tac unit
let prove_sum_pair_sum_isomorphism () =
  compute();
  apply (`arrow_to_forall);
  let x_term = binder_to_term (forall_intro ()) in
  destruct x_term;
  iterAll (fun () ->
    let destruct_binders = intros() in
    let breq_term = binder_to_term (last destruct_binders) in
    my_l_to_r [breq_term];
    compute();
    trefl ()
  )

val mk_sum_isomorphism: typ -> typ -> term -> list term -> list ctor -> parser_term -> Tac parser_term
let mk_sum_isomorphism tag_typ result_typ tag_to_pair_typ tag_vals ctors (pairs_parser, pairs_typ) =
  let middle_to_sum_def = mk_middle_to_sum_fun tag_typ tag_to_pair_typ tag_vals ctors in
  let sum_to_middle_def = mk_sum_to_middle_fun result_typ tag_vals ctors in
  let middle_typ = mk_e_app (`dtuple2) [tag_typ; tag_to_pair_typ] in
  let mk_a_to_b (a:typ) (b:typ) = (pack (Tv_Arrow (fresh_binder a) (pack_comp (C_Total b [])))) in
  //We need to help F* with the type of things otherwise it is completely lost
  let ascribe_type (t:typ) (x:term) = mk_ie_app (`id) [t] [x] in
  let result_parser = mk_ie_app (`isomorphism_explicit) [pairs_typ] [
    result_typ;
    pairs_parser;
    ascribe_type (mk_a_to_b middle_typ result_typ) middle_to_sum_def;
    ascribe_type (mk_a_to_b result_typ middle_typ) sum_to_middle_def;
    (`(synth_by_tactic prove_pair_sum_pair_isomorphism));
    (`(synth_by_tactic prove_sum_pair_sum_isomorphism))
  ] in
  (result_parser, result_typ)

val mk_sum_type_parser: list ctor -> typ -> Tac parser_term
let mk_sum_type_parser ctors result_type =
  let tags = Tactics.Util.map get_tag_from_ctor ctors in
  let (tag_typ, tag_vals) = sanitize_tags tags in
  let tag_parser_term = mk_tag_parser tag_typ tag_vals in
  let (tag_parser, tag_typ) = tag_parser_term in
  let (middle_sum_type_parser_term, tag_to_pair_typ) = mk_middle_sum_type_parser tag_parser_term tag_vals ctors in
  mk_sum_isomorphism tag_typ result_type tag_to_pair_typ tag_vals ctors middle_sum_type_parser_term

(*** Parser generator ***)

val gen_parser_fun: term -> Tac (list binder & parser_term)
let gen_parser_fun type_fv =
  let env = top_env () in

  let type_name =
    match inspect type_fv with
    | Tv_FVar fv -> (inspect_fv fv)
    | _ -> fail "type_fv is not a free variable"
  in
  let type_declaration =
  match lookup_typ env type_name with
  | Some x -> x
  | None -> fail "Type not found?"
  in

  match inspect_sigelt type_declaration with
  | Sg_Inductive name [] params typ constructors -> (
    guard (term_eq typ (`Type0));
    match constructors with
    | [(c_name, c_typ)] -> (
      let types, _ = collect_arr c_typ in
      let pairs_parser = mk_parser_pairs types in
      let result_parsed_type = mk_e_app type_fv (Tactics.Util.map binder_to_term params) in
      (params, mk_record_isomorphism result_parsed_type c_name types pairs_parser)
    )
    | ctors -> (
      let result_parsed_type = mk_e_app type_fv (Tactics.Util.map binder_to_term params) in
      (params, mk_sum_type_parser ctors result_parsed_type)
    )
  )
  | _ -> fail "gen_parser_fun: only inductives are supported"

val gen_parser: term -> Tac decls
let gen_parser type_fv =
  let type_name =
    match inspect type_fv with
    | Tv_FVar fv -> inspect_fv fv
    | _ -> fail "type_fv is not a free variable"
  in
  let parser_name = parser_name_from_type_name type_name in
  let (params, (parser_fun_body, parsed_type)) = gen_parser_fun type_fv in
  let parser_fun = mk_abs params parser_fun_body in
  //dump (term_to_string parser_fun);
  let unparametrized_parser_type = mk_e_app (quote parser_serializer) [parsed_type] in
  let parser_type =
    match params with
    | [] -> unparametrized_parser_type
    | _::_ -> mk_arr params (pack_comp (C_Total unparametrized_parser_type []))
  in
  let parser_letbinding = pack_lb ({
    lb_fv = pack_fv parser_name;
    lb_us = [];
    lb_typ = parser_type;
    lb_def = parser_fun;
  }) in
  let sv : sigelt_view = Sg_Let false [parser_letbinding] in
  [pack_sigelt sv]

(*** Tests ***)

noeq type test_type2 = {
  a:char;
  b:char;
  c:char;
  d:char;
  e:char;
  f:char;
  g:char;
  h:char;
  i:char;
  j:char;
}

#push-options "--fuel 0 --ifuel 0"
%splice [ps_test_type2] (gen_parser (`test_type2))
#pop-options

assume val blbytes: nat -> Type0
assume val ps_blbytes: n:nat -> parser_serializer (blbytes n)

noeq type test_type3 =
  | Test_1: [@@@with_tag #(nat_lbytes 1) 1] char -> char -> char -> char -> char -> char -> char -> test_type3
  | Test_2: [@@@with_tag #(nat_lbytes 1) 2] char -> char -> char -> char -> test_type3
  | Test_3: [@@@with_tag #(nat_lbytes 1) 3] blbytes 256 -> test_type3
  | Test_4: [@@@with_tag #(nat_lbytes 1) 4] char -> test_type3
  | Test_5: [@@@with_tag #(nat_lbytes 1) 5] char -> test_type3

#push-options "--fuel 0 --ifuel 1"
%splice [ps_test_type3] (gen_parser (`test_type3))
#pop-options

noeq type test_type4 = {
  a:blbytes 256;
  b:blbytes 256;
  c:blbytes 256;
  d:blbytes 256;
}

#push-options "--fuel 0 --ifuel 0"
%splice [ps_test_type4] (gen_parser (`test_type4))
#pop-options

noeq type test_type5 (n:nat) = {
  a:blbytes n;
  b:blbytes n;
  c:blbytes n;
  d:blbytes n;
}

#push-options "--fuel 0 --ifuel 0"
%splice [ps_test_type5] (gen_parser (`test_type5))
#pop-options
