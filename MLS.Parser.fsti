module MLS.Parser

open MLS.Bytes

(*** Basic definitions ***)

val add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> list bytes -> bytes -> bytes
let is_suffix (#bytes:Type0) {|bytes_like bytes|} (suffix:bytes) (buf:bytes) = exists prefixes. buf == add_prefixes prefixes suffix

type suffix_of (#bytes:Type0) {|bytes_like bytes|} (b:bytes) = suf:bytes{is_suffix suf b}
type extension_of (#bytes:Type0) {|bytes_like bytes|} (suf:bytes) = b:bytes{is_suffix suf b}

type bare_parser (bytes:Type0) {|bytes_like bytes|} (a:Type) = b:bytes -> option (a & suffix_of b)
//type bare_serializer (bytes:Type0) {|bytes_like bytes|} (a:Type) = x:a -> suffix:bytes -> extension_of suffix
type bare_serializer (bytes:Type0) {|bytes_like bytes|} (a:Type) = x:a -> list bytes

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
  parse: bare_parser bytes a;
  serialize: bare_serializer bytes a;
  parse_serialize_inv: x:a -> suffix:bytes -> Lemma (
    parse (add_prefixes (serialize x) suffix) == Some (x, suffix)
  );
  serialize_parse_inv: buf:bytes -> Lemma (
    match parse buf with
    | Some (x, suffix) -> buf == add_prefixes (serialize x) suffix
    | None -> True
  );
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
  Pure (parser_serializer_unit bytes b) (requires True) (ensures fun res -> is_not_unit res <==> is_not_unit ps_a)

val isomorphism:
  #a:Type -> #bytes:Type0 -> {| bytes_like bytes |} -> b:Type ->
  ps_a:parser_serializer_unit bytes a -> f:(a -> b) -> g:(b -> a) ->
  Pure (parser_serializer_unit bytes b)
  (requires (forall xa. g (f xa) == xa) /\ (forall xb. f (g xb) == xb))
  (ensures fun res -> is_not_unit res <==> is_not_unit ps_a)

(*** Parser for basic types ***)

val ps_unit: #bytes:Type0 -> {| bytes_like bytes |} -> parser_serializer_unit bytes unit

type lbytes (bytes:Type0) {|bytes_like bytes|} (n:nat) = b:bytes{length b == n}
val ps_lbytes: #bytes:Type0 -> {| bytes_like bytes |} -> n:nat{1 <= n} -> parser_serializer bytes (lbytes bytes n)

//val ps_u8: parser_serializer uint8
//val ps_u16: parser_serializer uint16
//val ps_u32: parser_serializer uint32
//val ps_u64: parser_serializer uint64
//val ps_u128: parser_serializer uint128

(*** Exact parsers ***)

type bare_parser_exact (bytes:Type0) {|bytes_like bytes|} (a:Type) = b:bytes -> option a
type bare_serializer_exact (bytes:Type0) {|bytes_like bytes|} (a:Type) = a -> bytes
noeq type parser_serializer_exact (bytes:Type0) {|bytes_like bytes|} (a:Type) = {
  parse_exact: bare_parser_exact bytes a;
  serialize_exact: bare_serializer_exact bytes a;
  parse_serialize_inv_exact: x:a -> Lemma (
    parse_exact (serialize_exact x) == Some x
  );
  serialize_parse_inv_exact: buf:bytes -> Lemma (
    match parse_exact buf with
    | Some x -> serialize_exact x == buf
    | None -> True
  );
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

let rec byte_length (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) (l:list a) : nat =
  match l with
  | [] -> 0
  | h::t -> length (add_prefixes (ps_a.serialize h) empty <: bytes) + byte_length ps_a t

type blseq (#bytes:Type0) {|bytes_like bytes|} (a:Type) (ps_a:parser_serializer bytes a) (r:size_range) = s:Seq.seq a{in_range r (byte_length ps_a (Seq.seq_to_list s))}
type blbytes (bytes:Type0) {|bytes_like bytes|} (r:size_range) = b:bytes{in_range r (length b)}
val ps_seq: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> r:size_range -> ps_a:parser_serializer bytes a -> parser_serializer bytes (blseq a ps_a r)
val ps_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> r:size_range -> parser_serializer bytes (blbytes bytes r)
