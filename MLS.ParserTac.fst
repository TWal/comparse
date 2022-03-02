module MLS.ParserTac

open FStar.Tactics

assume new type parser_serializer (a:Type)
assume val bind: #a:Type -> #b:Type -> parser_serializer a -> parser_serializer b -> parser_serializer (a & b)

assume new type char
assume val ps_char: parser_serializer char
assume val ps_unit: parser_serializer unit

assume val isomorphism:
  #a:Type -> b:Type ->
  ps_a:parser_serializer a -> f:(a -> b) -> g:(b -> a) ->
  Pure (parser_serializer b)
  (requires (forall xa. g (f xa) == xa) /\ (forall xb. f (g xb) == xb))
  (ensures fun res -> True)

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

//TODO: parametrization
val parser_from_type: term -> Tac parser_term
let parser_from_type t =
  match inspect t with
  | Tv_FVar fv ->
    (pack (Tv_FVar (pack_fv (parser_name_from_type_name (inspect_fv fv)))), t)
  | _ -> fail "parser_from_type: only unparametrized parsers are supported"

val mk_parser_unit: unit -> parser_term
let mk_parser_unit () =
  (`ps_unit, `unit)

val mk_parser_pair: parser_term -> parser_term -> Tac parser_term
let mk_parser_pair (ps_a, t_a) (ps_b, t_b) =
  let ps_ab = mk_ie_app (quote bind) [t_a; t_b] [ps_a; ps_b] in
  let t_ab = mk_e_app (quote tuple2) [t_a; t_b] in
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

val mktuple2_fv: unit -> Tac fv
let mktuple2_fv () =
  pack_fv (explode_qn (`%Mktuple2))

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
    let pattern = Pat_Cons (mktuple2_fv ()) [(Pat_Var bv_h, false); (pattern_t, false)] in
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
    mktuple_n [(pack (Tv_Var h)); mk_construct_pairs t]

val mk_isomorphism_g: typ -> name -> list typ -> Tac term
let mk_isomorphism_g input_type constructor_name constructor_types =
  let bvs = Tactics.Util.map (fun t -> fresh_bv t) constructor_types in
  let match_pattern = Pat_Cons (pack_fv constructor_name) (List.Tot.map (fun bv -> (Pat_Var bv, false)) bvs) in
  let match_body = mk_construct_pairs bvs in
  let x_bv = fresh_bv input_type in
  pack (Tv_Abs (mk_binder x_bv) (pack (Tv_Match (pack (Tv_Var x_bv)) None [(match_pattern, match_body)])))

val mk_isomorphism: typ -> name -> list typ -> parser_term -> Tac parser_term
let mk_isomorphism result_type constructor_name constructor_types (parser_term, parser_type) =
  let result_parser_term =
    mk_ie_app (quote isomorphism) [parser_type] [
      result_type;
      parser_term;
      mk_isomorphism_f parser_type constructor_name constructor_types;
      mk_isomorphism_g result_type constructor_name constructor_types
    ]
  in
  (result_parser_term, result_type)

val gen_parser_fun: term -> Tac parser_term
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
  | Sg_Inductive name [] params _ (*typ*) constructors -> (
    //TODO: parametrization
    match constructors, params with
    | [(c_name, c_typ)], [] -> (
      let types, _ = collect_arr c_typ in
      let pairs_parser = mk_parser_pairs types in
      mk_isomorphism type_fv c_name types pairs_parser
    )
    | _ -> fail "gen_parser_fun: only unparametrized records are supported"
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
  let (parser_fun, parsed_type) = gen_parser_fun type_fv in
  let parser_type = mk_e_app (quote parser_serializer) [parsed_type] in
  let parser_letbinding = pack_lb ({
    lb_fv = pack_fv parser_name;
    lb_us = [];
    //TODO: parametrization
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

#push-options "--ifuel 8"
%splice [ps_test_type2] (gen_parser (`test_type2))
#pop-options
