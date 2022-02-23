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

  slice: b:bytes -> i:nat -> j:nat{i <= j /\ j <= length b} -> bytes;
  slice_length: b:bytes -> i:nat -> j:nat{i <= j /\ j <= length b} -> Lemma (length (slice b i j) == j-i);

  slice_concat_left: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures slice (concat b1 b2) 0 (length b1) == b1);
  slice_concat_right: b1:bytes -> b2:bytes -> Lemma
    (requires (length b1) <= (length (concat b1 b2)))
    (ensures slice (concat b1 b2) (length b1) (length (concat b1 b2)) == b2);

  concat_slice: b:bytes -> i:nat{i <= length b} -> Lemma
    (concat (slice b 0 i) (slice b i (length b)) == b);
}

