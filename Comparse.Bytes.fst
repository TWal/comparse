module Comparse.Bytes

val find_nbytes_aux: n:pos -> acc:pos -> Pure pos (requires pow2 (8 * (acc-1)) <= n)
  (ensures fun res -> pow2 (8 * (res-1)) <= n /\ n < pow2 (8 * res))
  (decreases n - pow2 (8 * (acc-1)))
let rec find_nbytes_aux n acc =
  if n < pow2 (8* acc) then
    acc
  else (
    Math.Lemmas.pow2_lt_compat (8 * acc) (8 * (acc-1));
    find_nbytes_aux n (acc+1)
  )

let find_nbytes n =
  if n = 0 then 1
  else (
    assert_norm(pow2 (8*0) == 1);
    find_nbytes_aux n 1
  )

let nat_lbytes_helper (sz:nat) = ()

let seq_u8_bytes_like = {
  length = Seq.length;

  empty = (Seq.empty);
  empty_length = (fun () -> ());
  recognize_empty = (fun b ->
    assert(Seq.length b = 0 ==> b `Seq.eq` Seq.empty);
    Seq.length b = 0
  );

  concat = (fun b1 b2 -> Seq.append b1 b2);
  concat_length = (fun b1 b2 -> ());

  split = (fun b i ->
    Some (Seq.slice b 0 i, Seq.slice b i (Seq.length b))
  );

  split_length = (fun b i -> ());
  split_concat = (fun b1 b2 ->
    assert(b1 `Seq.eq` (Seq.slice (Seq.append b1 b2) 0 (Seq.length b1)));
    assert(b2 `Seq.eq` (Seq.slice (Seq.append b1 b2) (Seq.length b1) (Seq.length (Seq.append b1 b2))))
  );
  concat_split = (fun b i ->
    assert(b `Seq.eq` Seq.append (Seq.slice b 0 i) (Seq.slice b i (Seq.length b)))
  );

  to_nat = (fun sz b ->
    FStar.Endianness.lemma_be_to_n_is_bounded b;
    Some (FStar.Endianness.be_to_n b)
  );
  from_nat = (fun sz n ->
    FStar.Endianness.n_to_be sz n
  );

  from_to_nat = (fun sz n -> ());
  to_from_nat = (fun sz b -> ());
}

let refine_bytes_like (bytes:Type0) {|bytes_like bytes|} (pre:bytes_compatible_pre bytes) = {
  length = (fun (b:bytes{pre b}) -> length #bytes b);

  empty = empty #bytes;
  empty_length = (fun () -> empty_length #bytes ());
  recognize_empty = (fun b -> recognize_empty #bytes b);

  concat = (fun b1 b2 -> concat #bytes b1 b2);
  concat_length = (fun b1 b2 -> concat_length #bytes b1 b2);

  split = (fun b i ->
    match split #bytes b i with
    | None -> None
    | Some (b1, b2) -> Some (b1, b2)
  );
  split_length = (fun b i -> split_length #bytes b i);

  split_concat = (fun b1 b2 -> split_concat #bytes b1 b2);
  concat_split = (fun b i -> concat_split #bytes b i);

  to_nat = (fun sz b -> to_nat #bytes sz b);
  from_nat = (fun sz n -> from_nat #bytes sz n);

  from_to_nat = (fun sz n -> from_to_nat #bytes sz n);
  to_from_nat = (fun sz b -> to_from_nat #bytes sz b);
}
