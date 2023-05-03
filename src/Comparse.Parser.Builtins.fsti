module Comparse.Parser.Builtins

open Comparse.Bytes.Typeclass
open Comparse.Tactic.Attributes
open Comparse.Utils

(*** Basic definitions ***)

let rec for_allP (#a:Type) (pre:a -> prop) (l:list a): prop =
    match l with
    | [] -> True
    | h::t -> pre h /\ for_allP pre t

val for_allP_eq: #a:Type -> pre:(a -> prop) -> l:list a ->
  Lemma (for_allP pre l <==> (forall x. List.Tot.memP x l ==> pre x))

///   add_prefixes [prefix0; prefix1; ...; prefixn] suffix
/// = concat prefix0 (concat prefix1 (... (concat prefixn suffix)))`
let add_prefixes (#bytes:Type) {|bytes_like bytes|} (prefixes:list bytes) (suffix:bytes): bytes =
  List.Tot.fold_right (concat #bytes) prefixes suffix

[@@"opaque_to_smt"]
let prefixes_length (#bytes:Type) {|bytes_like bytes|} (l:list bytes) =
  let add (x:nat) (y:nat): nat = x+y in
  List.Tot.fold_right add (List.Tot.map length l) 0

/// The following structure defines composable parsers / serializer.
/// For a structure that is meant to actually be used by the user, see `parser_serializer_whole`.
///
/// The parser takes as input a `bytes`, and returns an `option` (it can fail on malformed inputs) of an `a` (the parsed value) and a `bytes` (the suffix of the input that was not parsed).
/// The serializer takes as input an `a`, and returns a list of `bytes`, that you need to concatenate with `add_prefixes`.
///
/// -- Begin parenthesis about symbolic bytes --
///
/// Why do we have to concatenate the bytes ourselve, can't the serializer do it itself?
/// See the following example, using a C-like syntax:
/// struct A {
///   int a0;
///   int a1;
/// };
/// struct B {
///   int b0;
///   int b1;
/// };
/// struct C {
///   A a;
///   B b;
/// };
/// If the serializer did the concatenations, where it what would happen:
///   serialize_C c
/// = serialize_A c.a + serialize_B c.b
/// = (serialize_int c.a.a0 + serialize_int c.a.a1) + (serialize_int c.b.b0 + serialize_int c.b.b1)
/// = (int_to_bytes  c.a.a0 + int_to_bytes  c.a.a1) + (int_to_bytes  c.b.b0 + int_to_bytes  c.b.b1)
///
/// When the serializer instead returns a list, you get:
///   serialize_C c
/// = serialize_A c.a @ serialize_B c.b
/// = (serialize_int c.a.a0  @ serialize_int c.a.a1 ) @ (serialize_int c.b.b0  @ serialize_int c.b.b1 )
/// = ([int_to_bytes c.a.a0] @ [int_to_bytes c.a.a1]) @ ([int_to_bytes c.b.b0] @ [int_to_bytes c.b.b1])
/// = [ int_to_bytes c.a.a0;    int_to_bytes c.a.a1;      int_to_bytes c.b.b0;    int_to_bytes c.b.b1]
/// Hence `add_prefixes (serialize_C c) empty` is equal to:
/// = int_to_bytes c.a.a0 + (int_to_bytes c.a.a1 + (int_to_bytes c.b.b0 + (int_to_bytes c.b.b1 + empty)))
///
/// Note how the parenthesing changes!
/// On concrete bytes, this is equivalent. However, on symbolic bytes, we don't have associativity of concatenation.
/// In the symbolic world, if you want to slice `a + b`, then the slice would only work in one of the following cases:
/// - slice from `0` to `length a` to get `a`
/// - slice from `length a` to `length (a+b)` to get `b`
/// It means that in (a + b) + c`, you can't get `a` in one slice, you have to do it in two steps:
/// - slice to obtain `a+b`
/// - slice to obtain `a`
///
/// The last parenthesing is better for parsing, because parsing is done in the following order:
/// - parse a0
/// - parse a1
/// - construct a = A{a0; a1}
/// - parse b0
/// - parse b1
/// - construct b = B{b0; b1}
/// - construct c = C{a; b}
/// In the first parenthesing, the parser would need to guess the size of the structure A.
/// In this example, this would be possible, however in the general case A could e.g. contain a variable-length list.
/// In the last parenthesing, the parser would work fine with symbolic bytes.
///
/// -- End parenthesis about symbolic bytes --
///
/// The parser and serializer are inverse of each other, as stated by the `..._inv` lemmas.

noeq type parser_serializer_prefix (bytes:Type0) {|bytes_like bytes|} (a:Type) = {
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
}

/// Predicate transformer `is_well_formed`:
/// given a predicate on `bytes` compatible with `concat` and `slice`, you get a predicate on `a`,
/// which says whether the bytes predicate is valid on all the bytes contained inside `a`.

let is_well_formed_prefix (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer_prefix bytes a) (pre:bytes_compatible_pre bytes) (x:a) =
  for_allP pre (ps_a.serialize x)

val is_well_formed_prefix_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #a:Type -> ps_a:parser_serializer_prefix bytes a ->
  pre_strong:bytes_compatible_pre bytes -> pre_weak:bytes_compatible_pre bytes ->
  x:a ->
  Lemma
  (requires is_well_formed_prefix ps_a pre_strong x /\ (forall b. pre_strong b ==> pre_weak b))
  (ensures is_well_formed_prefix ps_a pre_weak x)

/// What is the reason behind `parser_serializer_prefix` and `parser_serializer`?
/// In some functions (such as `ps_whole_list` which is used to build `ps_seq` or `ps_bytes`),
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
/// and to use `parser_serializer_prefix` for argument types when possible.
/// The type `parser_serializer` will be the one most often used by the user,
/// hence this nice name instead of something like `parser_serializer_prefix_not_unit`

val is_not_unit: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer_prefix bytes a -> Type0
let parser_serializer (bytes:Type0) {|bytes_like bytes|} (a:Type) = ps_a:parser_serializer_prefix bytes a{is_not_unit ps_a}

(*** Parser combinators ***)

/// A parser for dependant pairs.
/// It can be used both to parse (non-dependant pairs), hence records,
/// or tagged-union-like structures (the second value depend on the tag), hence sum types.

val bind:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_prefix bytes (b xa)) ->
  parser_serializer_prefix bytes (dtuple2 a b)

val bind_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_prefix bytes (b xa)) ->
  xa:a -> xb:b xa ->
  Lemma ((bind ps_a ps_b).serialize (|xa, xb|) == (ps_a.serialize xa) @ ((ps_b xa).serialize xb))
  [SMTPat ((bind ps_a ps_b).serialize (|xa, xb|))]

/// On concrete bytes we actually have an equivalence between the `requires` and the `ensures`.
/// On symbolic bytes where you may have multiple bytes of length 0, this is not true anymore.
/// Hopefully, we only need this implication:
/// the other would be useful to prove that a predicate do parse the unit type,
/// and this is not something we actually need.

val bind_is_not_unit: #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:(a -> Type) -> ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_prefix bytes (b xa)) -> Lemma
  (requires is_not_unit ps_a \/ (forall xa. is_not_unit (ps_b xa)))
  (ensures is_not_unit (bind ps_a ps_b))
  [SMTPat (is_not_unit (bind ps_a ps_b))]

// This is a recursive SMTPat!
// You might want to use #set-options "--z3cliopt 'smt.qi.eager_threshold=100'" (or higher value)
// See this SO question for more information about this parameter:
// https://stackoverflow.com/questions/13198158/proving-inductive-facts-in-z3
val bind_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_prefix bytes (b xa)) ->
  pre:bytes_compatible_pre bytes -> xa:a -> xb:(b xa) ->
  Lemma (is_well_formed_prefix (bind ps_a ps_b) pre (|xa, xb|) <==> is_well_formed_prefix ps_a pre xa /\ is_well_formed_prefix (ps_b xa) pre xb)
  [SMTPat (is_well_formed_prefix (bind ps_a ps_b) pre (|xa, xb|))]

// We use `eq2` intsead of `==` because otherwise the inferred type is `int` and not `nat`.
// This is useful for Comparse.Tactic.GenerateLengthLemma meta-program.
val bind_length:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_prefix bytes (b xa)) ->
  xa:a -> xb:b xa ->
  Lemma (eq2 #nat (prefixes_length ((bind ps_a ps_b).serialize (|xa, xb|))) ((prefixes_length (ps_a.serialize xa)) + (prefixes_length ((ps_b xa).serialize xb))))
  [SMTPat (prefixes_length ((bind ps_a ps_b).serialize (|xa, xb|)))]

noeq type isomorphism_between (a:Type) (b:Type) = {
  a_to_b: a -> b;
  b_to_a: b -> a;
  a_to_b_to_a: x:a -> squash (b_to_a (a_to_b x) == x);
  b_to_a_to_b: x:b -> squash (a_to_b (b_to_a x) == x);
}

let mk_isomorphism_between (#a:Type) (#b:Type) (a_to_b:a -> b) (b_to_a:b -> a):
  Pure (isomorphism_between a b)
       (requires (forall x. a_to_b (b_to_a x) == x) /\ (forall x. b_to_a (a_to_b x) == x))
       (ensures fun _ -> True)
  = {
    a_to_b;
    b_to_a;
    a_to_b_to_a = (fun _ -> ());
    b_to_a_to_b = (fun _ -> ());
  }

/// The workflow to use this parser framework is to use `bind` to parse a big nested dependant pair,
/// then use the `isomorphism` transformer to derive a parser for your actual type.
val isomorphism:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a -> iso:isomorphism_between a b ->
  parser_serializer_prefix bytes b

/// This helper function is extremely valuable to help F*'s type inference.
/// Using it, F* is able to automatically deduce the type of `a`, which is often ugly.
/// (This is in general why you use `isomorphism`: because you want to replace the ugly `a` with a nicer `b`)
let mk_isomorphism
  (#bytes:Type0) {| bytes_like bytes |} (#a:Type) (b:Type)
  (ps_a:parser_serializer_prefix bytes a) (a_to_b:a -> b) (b_to_a:b -> a):
  Pure (parser_serializer_prefix bytes b)
    (requires (forall x. a_to_b (b_to_a x) == x) /\ (forall x. b_to_a (a_to_b x) == x))
    (ensures fun _ -> True)
  =
  isomorphism ps_a (mk_isomorphism_between a_to_b b_to_a)

let mk_trivial_isomorphism
  (#bytes:Type0) {| bytes_like bytes |} (#a:Type) (#b:Type)
  (ps_a:parser_serializer_prefix bytes a):
  Pure (parser_serializer_prefix bytes b)
    (requires a `subtype_of` b /\ b `subtype_of` a)
    (ensures fun _ -> True)
  =
  mk_isomorphism b ps_a (fun x -> x) (fun x -> x)

val isomorphism_serialize:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a -> iso:isomorphism_between a b ->
  x:b ->
  Lemma ((isomorphism ps_a iso).serialize x == ps_a.serialize (iso.b_to_a x))
  [SMTPat ((isomorphism ps_a iso).serialize x)]

/// This type we have the equivalence even with symbolic bytes, but we don't need it so we can keep a consistent interface.
val isomorphism_is_not_unit:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a -> iso:isomorphism_between a b ->
  Lemma
    (requires is_not_unit ps_a)
    (ensures is_not_unit (isomorphism ps_a iso))
    [SMTPat (is_not_unit (isomorphism ps_a iso))]

val isomorphism_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a -> iso:isomorphism_between a b ->
  pre:bytes_compatible_pre bytes -> xb:b ->
  Lemma
  (is_well_formed_prefix (isomorphism ps_a iso) pre xb <==> is_well_formed_prefix ps_a pre (iso.b_to_a xb))
  [SMTPat (is_well_formed_prefix (isomorphism ps_a iso) pre xb)]

val isomorphism_length:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_prefix bytes a -> iso:isomorphism_between a b ->
  xb:b ->
  Lemma (prefixes_length ((isomorphism ps_a iso).serialize xb) == prefixes_length (ps_a.serialize (iso.b_to_a xb)))
  [SMTPat (prefixes_length ((isomorphism ps_a iso).serialize xb))]



// Introducing this type helps SMTPats to avoid dealing with the lambda `fun x -> pred x`
type refined (a:Type) (pred:a -> bool) = x:a{pred x}

/// Parser for a refinement.
val refine:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type ->
  parser_serializer_prefix bytes a -> pred:(a -> bool) ->
  parser_serializer_prefix bytes (refined a pred)

val refine_serialize:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a -> pred:(a -> bool) ->
  x:refined a pred ->
  Lemma ((refine ps_a pred).serialize x == ps_a.serialize x)
  [SMTPat ((refine ps_a pred).serialize x)]

val refine_is_not_unit:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a -> pred:(a -> bool) ->
  Lemma
    (requires is_not_unit ps_a)
    (ensures is_not_unit (refine ps_a pred))
    [SMTPat (is_not_unit (refine ps_a pred))]

val refine_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a -> pred:(a -> bool) ->
  pre:bytes_compatible_pre bytes -> x:a{pred x} ->
  Lemma (is_well_formed_prefix (refine ps_a pred) pre x <==> is_well_formed_prefix ps_a pre x)
  [SMTPat (is_well_formed_prefix (refine ps_a pred) pre x)]

val refine_length:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a -> pred:(a -> bool) ->
  x:a{pred x} ->
  Lemma (prefixes_length ((refine ps_a pred).serialize x) == prefixes_length (ps_a.serialize x))
  [SMTPat (prefixes_length ((refine ps_a pred).serialize x))]

(*** Parser for basic types ***)

[@@is_parser; is_parser_for (`%unit)]
val ps_unit: #bytes:Type0 -> {| bytes_like bytes |} -> parser_serializer_prefix bytes unit

val ps_unit_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:unit ->
  Lemma ((ps_unit #bytes).serialize x == [])
  [SMTPat ((ps_unit #bytes).serialize x)]

val ps_unit_is_well_formed:
  #bytes:Type0 -> {| bl:bytes_like bytes |} ->
  pre:bytes_compatible_pre bytes -> x:unit ->
  Lemma (is_well_formed_prefix (ps_unit #bytes #bl) pre x <==> True)
  [SMTPat (is_well_formed_prefix (ps_unit #bytes #bl) pre x)]

val ps_unit_length:
  #bytes:Type0 -> {| bl:bytes_like bytes |} ->
  x:unit ->
  Lemma (prefixes_length ((ps_unit #bytes #bl).serialize x) == 0)
  [SMTPat (prefixes_length ((ps_unit #bytes #bl).serialize x))]

(*** Whole parsers ***)

/// This structure describe the non-composable interface for parser
/// The lemmas are similar (but simpler!) as the ones in `parser_serializer_prefix`
///
/// -- Begin parenthesis --
///
/// Actually, these parsers are useful for composability purposes.
/// Here is how we construct a `parser_serializer (list a)` given a `parser_serializer a:
///
/// Step 1: use `ps_whole_list` to construct a `parser_serializer_whole (list a)` using `parser_serializer a`.
/// This whole parser runs repeatedly the parser of a to the bytes, to construct a list of a.
///
/// Step 2: use `pse_to_ps` that first read a prefix containing the length, then slice the input bytes to have exactly the bytes containing the list and feed it to the whole parser.
///
/// -- End parenthesis --

noeq type parser_serializer_whole (bytes:Type0) {|bytes_like bytes|} (a:Type) = {
  parse: bytes -> option a;
  serialize: a -> bytes;
  parse_serialize_inv: x:a -> Lemma (
    parse (serialize x) == Some x
  );
  serialize_parse_inv: buf:bytes -> Lemma (
    match parse buf with
    | Some x -> serialize x == buf
    | None -> True
  );
}

let is_well_formed_whole (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer_whole bytes a) (pre:bytes_compatible_pre bytes) (x:a) =
  pre (ps_a.serialize x)

val bind_whole:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_whole bytes (b xa)) ->
  parser_serializer_whole bytes (dtuple2 a b)

val bind_whole_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_whole bytes (b xa)) ->
  xa:a -> xb:b xa ->
  Lemma ((bind_whole ps_a ps_b).serialize (|xa, xb|) == add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb))
  [SMTPat ((bind_whole ps_a ps_b).serialize (|xa, xb|))]

val bind_whole_is_well_formed_whole:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:(a -> Type) ->
  ps_a:parser_serializer_prefix bytes a -> ps_b:(xa:a -> parser_serializer_whole bytes (b xa)) ->
  pre:bytes_compatible_pre bytes -> xa:a -> xb:(b xa) ->
  Lemma (is_well_formed_whole (bind_whole ps_a ps_b) pre (|xa, xb|) <==> is_well_formed_prefix ps_a pre xa /\ is_well_formed_whole (ps_b xa) pre xb)
  [SMTPat (is_well_formed_whole (bind_whole ps_a ps_b) pre (|xa, xb|))]

val isomorphism_whole:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_whole bytes a -> iso:isomorphism_between a b ->
  parser_serializer_whole bytes b

val isomorphism_whole_serialize:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_whole bytes a -> iso:isomorphism_between a b ->
  x:b ->
  Lemma ((isomorphism_whole ps_a iso).serialize x == ps_a.serialize (iso.b_to_a x))
  [SMTPat ((isomorphism_whole ps_a iso).serialize x)]

val isomorphism_whole_is_well_formed:
  #bytes:Type0 -> {| bytes_like bytes |} -> #a:Type -> #b:Type ->
  ps_a:parser_serializer_whole bytes a -> iso:isomorphism_between a b ->
  pre:bytes_compatible_pre bytes -> xb:b ->
  Lemma
  (is_well_formed_whole (isomorphism_whole ps_a iso) pre xb <==> is_well_formed_whole ps_a pre (iso.b_to_a xb))
  [SMTPat (is_well_formed_whole (isomorphism_whole ps_a iso) pre xb)]

/// This helper function is extremely valuable to help F*'s type inference.
/// Using it, F* is able to automatically deduce the type of `a`, which is often ugly.
/// (This is in general why you use `isomorphism`: because you want to replace the ugly `a` with a nicer `b`)
let mk_isomorphism_whole
  (#bytes:Type0) {| bytes_like bytes |} (#a:Type) (b:Type)
  (ps_a:parser_serializer_whole bytes a) (a_to_b:a -> b) (b_to_a:b -> a):
  Pure (parser_serializer_whole bytes b)
    (requires (forall x. a_to_b (b_to_a x) == x) /\ (forall x. b_to_a (a_to_b x) == x))
    (ensures fun _ -> True)
  =
  isomorphism_whole ps_a (mk_isomorphism_between a_to_b b_to_a)

let mk_trivial_isomorphism_whole
  (#bytes:Type0) {| bytes_like bytes |} (#a:Type) (#b:Type)
  (ps_a:parser_serializer_whole bytes a):
  Pure (parser_serializer_whole bytes b)
    (requires a `subtype_of` b /\ b `subtype_of` a)
    (ensures fun _ -> True)
  =
  isomorphism_whole ps_a ({a_to_b = (fun (x:a) -> (x <: b)); b_to_a = (fun (x:b) -> (x <: a)); a_to_b_to_a = (fun _ -> ()); b_to_a_to_b = (fun _ -> ()); })

val refine_whole:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser_serializer_whole bytes a -> pred:(a -> bool) ->
  parser_serializer_whole bytes (refined a pred)

val refine_whole_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer_whole bytes a -> pred:(a -> bool) ->
  x:refined a pred ->
  Lemma ((refine_whole ps_a pred).serialize x == ps_a.serialize x)
  [SMTPat ((refine_whole ps_a pred).serialize x)]

(*** Conversion between prefix and whole parsers ***)

val ps_prefix_to_ps_whole:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser_serializer_prefix bytes a ->
  parser_serializer_whole bytes a

val ps_prefix_to_ps_whole_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a ->
  x:a ->
  Lemma ((ps_prefix_to_ps_whole ps_a).serialize x == add_prefixes (ps_a.serialize x) empty)
  [SMTPat ((ps_prefix_to_ps_whole ps_a).serialize x)]

val ps_prefix_to_ps_whole_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a ->
  pre:bytes_compatible_pre bytes -> x:a ->
  Lemma (is_well_formed_whole (ps_prefix_to_ps_whole ps_a) pre x <==> is_well_formed_prefix ps_a pre x)
  [SMTPat (is_well_formed_whole (ps_prefix_to_ps_whole ps_a) pre x)]

val ps_prefix_to_ps_whole_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a ->
  x:a ->
  Lemma (length ((ps_prefix_to_ps_whole ps_a).serialize x) == prefixes_length (ps_a.serialize x))
  [SMTPat (length ((ps_prefix_to_ps_whole ps_a).serialize x))]

let ps_whole_length_pred
  (#bytes:Type0) {|bytes_like bytes|} (#a:Type)
  (ps_a:parser_serializer_whole bytes a) (n:nat) (x:a)
  : bool =
  length (ps_a.serialize x) = n

val ps_whole_to_bare_ps_prefix:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  len:nat -> ps_a:parser_serializer_whole bytes a{forall x. length (ps_a.serialize x) == len} ->
  parser_serializer_prefix bytes a

val ps_whole_to_bare_ps_prefix_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  len:nat -> ps_a:parser_serializer_whole bytes a{forall x. length (ps_a.serialize x) == len} ->
  x:a ->
  Lemma ((ps_whole_to_bare_ps_prefix len ps_a).serialize x == [ps_a.serialize x])
  [SMTPat ((ps_whole_to_bare_ps_prefix len ps_a).serialize x)]

val ps_whole_to_bare_ps_prefix_is_not_unit:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  len:nat -> ps_a:parser_serializer_whole bytes a{forall x. length (ps_a.serialize x) == len} ->
  Lemma
  (requires 1 <= len)
  (ensures is_not_unit (ps_whole_to_bare_ps_prefix len ps_a))
  [SMTPat (is_not_unit (ps_whole_to_bare_ps_prefix len ps_a))]

(*** Whole parsers ***)

val ps_whole_bytes:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer_whole bytes bytes

val ps_whole_bytes_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  b:bytes ->
  Lemma ((ps_whole_bytes #bytes).serialize b == b)
  [SMTPat ((ps_whole_bytes #bytes).serialize b)]

val ps_whole_list:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a ->
  parser_serializer_whole bytes (list a)

val ps_whole_list_serialize:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a ->
  x:list a ->
  Lemma ((ps_whole_list ps_a).serialize x == List.Tot.fold_right add_prefixes (List.Tot.map (ps_a.serialize) x) empty)
  [SMTPat ((ps_whole_list ps_a).serialize x)]

val ps_whole_list_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a ->
  pre:bytes_compatible_pre bytes -> l:list a ->
  Lemma (is_well_formed_whole (ps_whole_list ps_a) pre l <==> for_allP (is_well_formed_prefix ps_a pre) l)
  [SMTPat (is_well_formed_whole (ps_whole_list ps_a) pre l)]

let rec bytes_length (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer_prefix bytes a) (l:list a): nat =
  match l with
  | [] -> 0
  | h::t -> (prefixes_length (ps_a.serialize h)) + bytes_length ps_a t

val ps_whole_list_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a ->
  l:list a ->
  Lemma (length ((ps_whole_list ps_a).serialize l) == bytes_length ps_a l)
  [SMTPat (length ((ps_whole_list ps_a).serialize l))]

(*** Another list combinator ***)

let pred_not (#a:Type) (pred:a -> bool) (x:a): bool =
  not (pred x)

type list_until (a:Type) (pred:a -> bool) =
  list (refined a (pred_not pred)) & refined a pred

val ps_list_until:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  parser_serializer bytes a -> pred:(a -> bool) ->
  parser_serializer bytes (list_until a pred)

val ps_list_until_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer bytes a -> pred:(a -> bool) ->
  pre:bytes_compatible_pre bytes -> x:list_until a pred ->
  Lemma
  (is_well_formed_prefix (ps_list_until ps_a pred) pre x <==> (
    let (l, last) = x in
    for_allP (is_well_formed_prefix ps_a pre) l /\
    is_well_formed_prefix ps_a pre last
  ))
  [SMTPat (is_well_formed_prefix (ps_list_until ps_a pred) pre x)]
