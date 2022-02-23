module MLS.Bytes

open FStar.Mul

type nat_lbytes (sz:nat) = n:nat{n < pow2 (8*sz)}

class bytes_like (bytes:Type0) = {
  length: bytes -> nat;

  empty: bytes;
  empty_length: unit -> Lemma (length empty == 0);
  length_zero: b:bytes -> Lemma
    (requires length b == 0)
    (ensures b == empty);

  concat: bytes -> bytes -> bytes;
  concat_length: b1:bytes -> b2:bytes -> Lemma (length (concat b1 b2) == (length b1) + (length b2));

  concat_empty_left: b:bytes -> Lemma (concat empty b == b);

  slice: b:bytes -> i:nat -> j:nat{i <= j /\ j <= length b} -> option bytes;
  slice_length: b:bytes -> i:nat -> j:nat{i <= j /\ j <= length b} -> Lemma (
    match slice b i j with
    | Some res -> length res == j-i
    | None -> True
  );

  slice_concat_left: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures slice (concat b1 b2) 0 (length b1)  == Some b1);
  slice_concat_right: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures slice (concat b1 b2) (length b1) (length (concat b1 b2)) == Some b2);

  concat_slice: b:bytes -> i:nat{i <= length b} -> Lemma (
    match slice b 0 i, slice b i (length b) with
    | Some lhs, Some rhs -> concat lhs rhs == b
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

type bytes_compatible_pre (bytes:Type0) {|bytes_like bytes|} =
  pre:(bytes -> Type0){
    (pre empty) /\
    (forall b1 b2. pre b1 /\ pre b2 ==> pre (concat b1 b2)) /\
    (forall b i j. pre b /\ Some? (slice b i j) ==> pre (Some?.v (slice b i j))) /\
    (forall sz n. pre (from_nat sz n))
  }

(*
type bytes_coercion (bytes1:Type0) {|bl1:bytes_like bytes1|} (bytes2:Type0) {|bl2:bytes_like bytes2|} (pre:bytes_compatible_pre bytes1) =
  f:(b:bytes1 -> Pure bytes2 (requires pre b) (ensures fun _ -> True)) {
    (forall b. pre b ==> length (f b) == length b) /\
    (f empty == empty) /\
    (forall b1 b2. pre b1 /\ pre b2 ==> f (concat b1 b2) == concat (f b1) (f b2)) /\
    (forall (b:bytes1) (i:nat) (j:nat{i <= j /\ j < length b}). pre b ==> (
      match (slice (f b) i j, slice b i j) with
      | Some fx, Some x -> fx == f x
      | None, None -> True
      | _ -> False
    )) /\
    (forall sz (b:bytes1{length b == sz}). pre b ==> (to_nat sz (f b)) == to_nat sz b) /\
    (forall sz n. f (from_nat sz n) == from_nat sz n)
  }
*)

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
