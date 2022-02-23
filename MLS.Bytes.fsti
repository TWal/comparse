module MLS.Bytes

val bytes: Type0
val bytes_length: bytes -> nat

let lbytes (n:nat) = b:bytes{bytes_length b == n}

val bytes_empty: bytes
val bytes_empty_length: unit -> Lemma
  (bytes_length bytes_empty == 0)
val bytes_length_zero: b:bytes -> Lemma
  (requires bytes_length b == 0)
  (ensures b == bytes_empty)

val bytes_concat: bytes -> bytes -> bytes
val bytes_concat_length: b1:bytes -> b2:bytes -> Lemma
  (bytes_length (bytes_concat b1 b2) == (bytes_length b1) + (bytes_length b2))
  //[SMTPat (bytes_length (bytes_concat b1 b2))]

val bytes_slice: b:bytes -> i:nat -> j:nat{i <= j /\ j <= bytes_length b} -> bytes
val bytes_slice_length:b:bytes -> i:nat -> j:nat{i <= j /\ j <= bytes_length b} -> Lemma
  (bytes_length (bytes_slice b i j) == j-i)
  //[SMTPat (bytes_length (bytes_slice b i j))]

val bytes_slice_concat_left: b1:bytes -> b2:bytes -> Lemma
  (requires (bytes_length b1) <= (bytes_length (bytes_concat b1 b2)))
  (ensures bytes_slice (bytes_concat b1 b2) 0 (bytes_length b1) == b1)
val bytes_slice_concat_right: b1:bytes -> b2:bytes -> Lemma
  (requires (bytes_length b1) <= (bytes_length (bytes_concat b1 b2)))
  (ensures bytes_slice (bytes_concat b1 b2) (bytes_length b1) (bytes_length (bytes_concat b1 b2)) == b2)

val bytes_concat_slice: b:bytes -> i:nat{i <= bytes_length b} -> Lemma
  (bytes_concat (bytes_slice b 0 i) (bytes_slice b i (bytes_length b)) == b)

val bytes_slice_whole: b:bytes -> Lemma
  (bytes_slice b 0 (bytes_length b) == b)

val bytes_slice_slice: b:bytes -> i1:nat -> j1:nat{i1 <= j1 /\ j1 <= bytes_length b} -> i2:nat -> j2:nat{i2 <= j2 /\ j2 <= j1-i1} -> Lemma
  (bytes_slice_length b i1 j1;
  bytes_slice (bytes_slice b i1 j1) i2 j2 == bytes_slice b (i1+i2) (i1+j2))
