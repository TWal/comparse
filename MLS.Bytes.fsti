module MLS.Bytes

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

  slice: b:bytes -> i:nat -> j:nat{i <= j /\ j <= length b} -> bytes;
  slice_length: b:bytes -> i:nat -> j:nat{i <= j /\ j <= length b} -> Lemma (length (slice b i j) == j-i);

  slice_concat_left: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures slice (concat b1 b2) 0 (length b1) == b1);
  slice_concat_right: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures slice (concat b1 b2) (length b1) (length (concat b1 b2)) == b2);

  //TODO: is this lemma true on symbolic bytes?
  //It is only used for `serialize_parse_inv` of `ps_lbytes`
  //A workaround could probably live with `slice` that returns an option?
  concat_slice: b:bytes -> i:nat{i <= length b} -> Lemma
    (concat (slice b 0 i) (slice b i (length b)) == b);

  //is_public: bytes -> Type0;
  //to_nat: b:bytes{is_public b} -> nat;
  //from_nat: nat -> b:bytes{is_public b};
}

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
