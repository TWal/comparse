module Comparse.Bytes

open FStar.Mul
open FStar.UInt //Bring in scope the `pow2_values` lemma

type nat_lbytes (sz:nat) = n:nat{n < pow2 (8*sz)}

/// Minimal interface to manipulate symbolic bytes.
/// Here are the explanations for a few design decisions:
/// - We don't require that only `empty` has length zero, e.g. we may have `concat empty empty <> empty`.
/// - We implement `split` and not `slice`, because `slice` causes trouble in the symbolic case:
///   with `slice`, how do you get the left and right part of `concat empty (concat empty empty)`?
/// - `split` returns an option, hence can fail if the indexes are not on the correct bounds.
///   * We require `split` to succeed on the bound of a `concat` (see `split_concat_...`).
///   * This is useful to state the `concat_split` lemma in a way which would be correct on symbolic bytes.
/// - To compensate the last fact, and the fact that we don't require decidable equality,
///   we need a function that recognize the `empty` bytes.
/// - The `to_nat` function can fail, if the bytes are not public for example

class bytes_like (bytes:Type0) = {
  length: bytes -> nat;

  empty: bytes;
  empty_length: unit -> Lemma (length empty == 0);
  recognize_empty: b:bytes -> res:bool{res <==> b == empty};

  concat: bytes -> bytes -> bytes;
  concat_length: b1:bytes -> b2:bytes -> Lemma (length (concat b1 b2) == (length b1) + (length b2));

  split: b:bytes -> i:nat{i <= length b} -> option (bytes & bytes);
  split_length: b:bytes -> i:nat{i <= length b} -> Lemma (
    match split b i with
    | Some (b1, b2) -> length b1 == i /\ i+length b2 == length b
    | None -> True
  );

  split_concat: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures split (concat b1 b2) (length b1) == Some (b1, b2));

  concat_split: b:bytes -> i:nat{i <= length b} -> Lemma (
    match split b i with
    | Some (lhs, rhs) -> concat lhs rhs == b
    | _ -> True
  );

  to_nat: sz:nat -> b:bytes{length b == sz} -> option (nat_lbytes sz);
  from_nat: sz:nat -> nat_lbytes sz -> b:bytes{length b == sz};

  from_to_nat: sz:nat -> n:nat_lbytes sz -> Lemma
    (to_nat sz (from_nat sz n) == Some n);

  to_from_nat: sz:nat -> b:bytes{length b == sz} -> Lemma (
    match to_nat sz b with
    | Some n -> b == from_nat sz n
    | None -> True
  );
}

/// This type defines a predicate on `bytes` that is compatible with its structure.
/// It is meant to be used for labeling predicates, which are typically compatible with the `bytes` structure.

let bytes_pre_is_compatible (#bytes:Type0) {|bytes_like bytes|} (pre:bytes -> Type0) =
    (pre empty) /\
    (forall b1 b2. pre b1 /\ pre b2 ==> pre (concat b1 b2)) /\
    (forall b i. pre b /\ Some? (split b i) ==> pre (fst (Some?.v (split b i))) /\ pre (snd (Some?.v (split b i)))) /\
    (forall sz n. pre (from_nat sz n))

type bytes_compatible_pre (bytes:Type0) {|bytes_like bytes|} =
  pre:(bytes -> Type0){bytes_pre_is_compatible pre}

(*
open FStar.Seq

instance seq_bytes_like (a:Type0): bytes_like (Seq.seq a) =
  {
    length = Seq.length;

    empty = Seq.empty;
    empty_length = (fun () -> ());
    length_zero = (fun b -> assert(Seq.equal b Seq.empty));

    concat = Seq.append;
    concat_length = (fun b1 b2 -> ());

    concat_empty_left = (fun b -> assert(Seq.equal (Seq.append Seq.empty b) b));

    slice = Seq.slice;
    slice_length = (fun b i j -> ());

    slice_concat_left = (fun b1 b2 -> assert(Seq.equal (Seq.slice (Seq.append b1 b2) 0 (Seq.length b1)) b1));
    slice_concat_right = (fun b1 b2 -> assert(Seq.equal (Seq.slice (Seq.append b1 b2) (Seq.length b1) (Seq.length (Seq.append b1 b2))) b2));

    concat_slice = (fun b i -> assert(Seq.equal (Seq.append (Seq.slice b 0 i) (Seq.slice b i (Seq.length b))) b));
  }
*)
