module MLS.Parser

open MLS.Bytes

(*** Basic definitions ***)

val add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> list (bytes) -> bytes -> bytes

/// What is the reason behind `parser_serializer_unit` and `parser_serializer`?
/// In some functions (such as `pse_list` which is used to build `ps_seq` or `ps_bytes`),
/// it is useful to know that `parse` will never consume 0 bytes, and `serialize` will never return `bytes_empty`.
/// Such types only have one element, hence are isomorphic to `unit`. They are (anti-)recognized by the `is_not_unit` predicate.
/// Thus they depend on a `parser_serializer` which doesn't serialize/parse a unit type.
/// It is however very useful to be able to parse a unit type, in the example of an optional:
///   struct {
///       uint8 present;
///       select (present) {
///           case 0: struct{}; //<-- parsed with ps_unit!
///           case 1: T value;
///       }
///   } optional<T>;
/// In this interface, we tried to use `parser_serializer` for return types when possible,
/// and to use `parser_serializer_unit` for argument types when possible.
/// They are named `parser_serializer_unit` / `parser_serializer` and not `parser_serializer` / `parser_serializer_nonempty`
/// because `parser_serializer_nonempty` is ugly, and it's the type that is the most used by the user.

noeq type parser_serializer_unit (bytes:Type0) {|bytes_like bytes|} (a:Type) = {
  parse: bytes -> option (a & bytes);
  serialize: a -> list bytes;
  parse_serialize_inv: x:a -> suffix:bytes -> Lemma (
    parse (add_prefixes (serialize x) suffix) == Some (x, suffix)
  );
  serialize_parse_inv: buf:bytes -> Lemma (
    match parse buf with
    | Some (x, suffix) -> buf == add_prefixes (serialize x) suffix
    | None -> True
  );

  is_valid: bytes_compatible_pre bytes -> a -> Type0;
  //is_valid_trivial: pre:bytes_compatible_pre bytes -> Lemma
  //  (requires forall b. pre b)
  //  (ensures forall x. is_valid pre x);
  //is_valid_monotonic: pre1:bytes_compatible_pre bytes -> pre2:bytes_compatible_pre bytes{forall b. pre1 b ==> pre2 b} -> x:a -> Lemma
  //  (requires is_valid pre1 x)
  //  (ensures is_valid pre2 x);
  parse_pre: pre:bytes_compatible_pre bytes -> buf:bytes{pre buf} -> Lemma (
    match parse buf with
    | Some (x, suffix) -> is_valid pre x /\ pre suffix
    | None -> True
  );
  serialize_pre: pre:bytes_compatible_pre bytes -> x:a{is_valid pre x} -> Lemma (
    forall b. List.Tot.memP b (serialize x) ==> pre b
  )
}

let is_not_unit (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer_unit bytes a) = ps_a.parse empty == None
let parser_serializer (bytes:Type0) {|bytes_like bytes|} (a:Type) = ps_a:parser_serializer_unit bytes a{is_not_unit ps_a}

(*** Parser combinators ***)

val bind: #a:Type -> #b:(a -> Type) -> #bytes:Type0 -> {| bytes_like bytes |} -> ps_a:parser_serializer_unit bytes a -> ps_b:(xa:a -> parser_serializer_unit bytes (b xa)) -> Pure (parser_serializer_unit bytes (xa:a&(b xa)))
  (requires True)
  (ensures fun res -> is_not_unit res <==> is_not_unit ps_a \/ (forall xa. is_not_unit (ps_b xa)))

val isomorphism_explicit:
  #a:Type -> #bytes:Type0 -> {| bytes_like bytes |} -> b:Type ->
  ps_a:parser_serializer_unit bytes a -> f:(a -> b) -> g:(b -> a) ->
  g_f_inv:(xa:a -> Lemma (g (f xa) == xa)) -> f_g_inv:(xb:b -> Lemma (f (g xb) == xb)) ->
  Pure (parser_serializer_unit bytes b) (requires True)
  (ensures fun res -> is_not_unit res <==> is_not_unit ps_a)

val isomorphism:
  #a:Type -> #bytes:Type0 -> {| bytes_like bytes |} -> b:Type ->
  ps_a:parser_serializer_unit bytes a -> f:(a -> b) -> g:(b -> a) ->
  Pure (parser_serializer_unit bytes b)
  (requires (forall xa. g (f xa) == xa) /\ (forall xb. f (g xb) == xb))
  (ensures fun res -> is_not_unit res <==> is_not_unit ps_a)

(*** Parser for basic types ***)

val ps_unit: #bytes:Type0 -> {| bytes_like bytes |} -> Pure (parser_serializer_unit bytes unit) (requires True)
  (ensures fun res -> forall pre x. res.is_valid pre x)

type lbytes (bytes:Type0) {|bytes_like bytes|} (n:nat) = b:bytes{length b == n}
val ps_lbytes: #bytes:Type0 -> {| bytes_like bytes |} -> n:nat -> Pure (parser_serializer_unit bytes (lbytes bytes n))
  (requires True)
  (ensures fun res -> (
    1 <= n ==> is_not_unit res
  ) /\ (
    forall (pre:bytes_compatible_pre bytes) b. res.is_valid pre b <==> pre b
  ))

//val ps_u8: parser_serializer uint8
//val ps_u16: parser_serializer uint16
//val ps_u32: parser_serializer uint32
//val ps_u64: parser_serializer uint64
//val ps_u128: parser_serializer uint128

(*** Exact parsers ***)

noeq type parser_serializer_exact (bytes:Type0) {|bytes_like bytes|} (a:Type) = {
  parse_exact: bytes -> option a;
  serialize_exact: a -> bytes;
  parse_serialize_inv_exact: x:a -> Lemma (
    parse_exact (serialize_exact x) == Some x
  );
  serialize_parse_inv_exact: buf:bytes -> Lemma (
    match parse_exact buf with
    | Some x -> serialize_exact x == buf
    | None -> True
  );

  is_valid_exact: bytes_compatible_pre bytes -> a -> Type0;
  parse_pre_exact: pre:bytes_compatible_pre bytes -> buf:bytes{pre buf} -> Lemma (
    match parse_exact buf with
    | Some x -> is_valid_exact pre x
    | None -> True
  );
  serialize_pre_exact: pre:bytes_compatible_pre bytes -> x:a{is_valid_exact pre x} -> Lemma (
    pre (serialize_exact x)
  )
}

val ps_to_pse: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> parser_serializer_unit bytes a -> parser_serializer_exact bytes a
val pse_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> parser_serializer_exact bytes (list a)

(*** Parser for variable-length lists ***)

type size_range = {
  min: nat;
  max: max:nat{min <= max /\ max < pow2 64};
}

let in_range (r:size_range) (x:nat) =
  r.min <= x && x <= r.max

let bytes_length (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (l:list a) : nat =
  length ((pse_list ps_a).serialize_exact l)

type blseq (#bytes:Type0) {|bytes_like bytes|} (a:Type) (ps_a:parser_serializer bytes a) (r:size_range) = s:Seq.seq a{in_range r (bytes_length ps_a (Seq.seq_to_list s))}
type blbytes (bytes:Type0) {|bytes_like bytes|} (r:size_range) = b:bytes{in_range r (length b)}
val ps_seq: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> r:size_range -> ps_a:parser_serializer bytes a -> parser_serializer bytes (blseq a ps_a r)
val ps_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> r:size_range -> parser_serializer bytes (blbytes bytes r)
