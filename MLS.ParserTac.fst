module MLS.ParserTac

open FStar.Tactics

assume new type parser_serializer (a:Type)
assume val bind: #a:Type -> #b:(a -> Type) -> parser_serializer a -> (x:a -> parser_serializer (b x)) -> parser_serializer (x:a & b x)

assume new type char
assume val ps_char: parser_serializer char
assume val ps_unit: parser_serializer unit

assume val isomorphism_explicit:
  #a:Type -> b:Type ->
  ps_a:parser_serializer a -> f:(a -> b) -> g:(b -> a) ->
  g_f_inv:(xa:a -> squash (g (f xa) == xa)) -> f_g_inv:(xb:b -> squash (f (g xb) == xb)) ->
  parser_serializer b

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

val mk_isomorphism_f: typ -> name -> list typ -> Tac term
let mk_isomorphism_f result_type constructor_name constructor_types =
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

val mk_isomorphism_g: typ -> name -> list typ -> Tac term
let mk_isomorphism_g input_type constructor_name constructor_types =
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
  l_to_r [binder_to_term breq];
  trefl ()

val mk_isomorphism: typ -> name -> list typ -> parser_term -> Tac parser_term
let mk_isomorphism result_type constructor_name constructor_types (parser_term, parser_type) =
  let result_parser_term =
    mk_ie_app (quote isomorphism_explicit) [parser_type] [
      result_type;
      parser_term;
      mk_isomorphism_f parser_type constructor_name constructor_types;
      mk_isomorphism_g result_type constructor_name constructor_types;
      (`(synth_by_tactic (prove_record_isomorphism_from_pair)));
      (`(synth_by_tactic (prove_record_isomorphism_from_record)));
    ]
  in
  (result_parser_term, result_type)

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
      (params, mk_isomorphism result_parsed_type c_name types pairs_parser)
    )
    | _ -> fail "gen_parser_fun: only records are supported"
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

noeq type test_type3 =
  |Test_1: char -> char -> test_type3
  |Test_2: char -> test_type3

#push-options "--fuel 0 --ifuel 0"
%splice [ps_test_type2] (gen_parser (`test_type2))
#pop-options

assume val blbytes: nat -> Type0
assume val ps_blbytes: n:nat -> parser_serializer (blbytes n)

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
