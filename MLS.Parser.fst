module MLS.Parser

open MLS.Bytes

#set-options "--fuel 0 --ifuel 2"

(*** Helper functions ***)

let rec add_prefixes #bytes #bl l suffix =
  match l with
  | [] -> suffix
  | h::t -> concat h ((add_prefixes t suffix))

#push-options "--ifuel 1 --fuel 1"
val add_prefixes_add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> l1:list bytes -> l2:list bytes -> suffix:bytes -> Lemma
  (add_prefixes l1 (add_prefixes l2 suffix) == add_prefixes (l1@l2) suffix)
let rec add_prefixes_add_prefixes l1 l2 suffix =
  match l1 with
  | [] -> ()
  | h::t -> add_prefixes_add_prefixes t l2 suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_length: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (length suffix <= length (add_prefixes l suffix))
let rec add_prefixes_length #bytes #bl l suffix =
  match l with
  | [] -> ()
  | h::t ->
    add_prefixes_length t suffix;
    concat_length h (add_prefixes t suffix)
#pop-options

val prefixes_is_empty: #bytes:Type0 -> {|bytes_like bytes|} -> list bytes -> bool
let prefixes_is_empty l = List.Tot.for_all (fun b -> length b = 0) l

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_identity: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (requires add_prefixes l suffix == suffix)
  (ensures prefixes_is_empty l)
let rec add_prefixes_identity #bytes #bl l suffix =
  match l with
  | [] -> ()
  | h::t ->
    concat_length h (add_prefixes t suffix);
    add_prefixes_length t suffix;
    length_zero h;
    concat_empty_left (add_prefixes t suffix);
    add_prefixes_identity #bytes #bl t suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_identity_inv: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (requires prefixes_is_empty l)
  (ensures add_prefixes l suffix == suffix)
let rec add_prefixes_identity_inv #bytes #bl l suffix =
  match l with
  | [] -> ()
  | h::t ->
    length_zero h;
    concat_empty_left (add_prefixes t suffix);
    add_prefixes_identity_inv #bytes #bl t suffix
#pop-options

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_length_strict: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (requires ~(prefixes_is_empty l))
  (ensures length suffix < length (add_prefixes l suffix))
let rec add_prefixes_length_strict #bytes #bl l suffix =
  match l with
  | [] -> ()
  | h::t ->
    concat_length h (add_prefixes t suffix);
    if length h = 0 then (
      add_prefixes_length_strict t suffix
    ) else (
      add_prefixes_length t suffix
    )
#pop-options

(*** Parser combinators ***)

let bind #a #b #bytes ps_a ps_b =
  let parse_ab (buf:bytes): option ((xa:a&(b xa)) & bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, buf_suffix) -> begin
      match (ps_b xa).parse buf_suffix with
      | None -> None
      | Some (xb, buf_suffix_suffix) -> (
        Some ((|xa, xb|), buf_suffix_suffix)
      )
    end
  in
  let serialize_ab (x:(xa:a&(b xa))): list bytes =
    let (|xa, xb|) = x in
    let la = ps_a.serialize xa in
    let lb = (ps_b xa).serialize xb in
    la@lb
  in
  let lemma_not_unit (): Lemma((parse_ab empty == None) <==> (ps_a.parse empty == None) \/ (forall xa. (ps_b xa).parse empty == None)) = begin
    match ps_a.parse empty with
    | None -> ()
    | Some (xa, empty_suffix) -> (
      ps_a.serialize_parse_inv empty;
      add_prefixes_length (ps_a.serialize xa) empty_suffix;
      empty_length #bytes ();
      length_zero empty_suffix;
      introduce forall x. x == xa with (
        ps_a.parse_serialize_inv xa (add_prefixes (ps_a.serialize x) empty);
        let l_xa = ps_a.serialize xa in
        let l_x = ps_a.serialize x in
        add_prefixes_add_prefixes l_xa l_x empty;
        add_prefixes_identity (l_xa) empty;
        add_prefixes_add_prefixes l_xa l_x empty;
        add_prefixes_identity_inv (l_xa) (add_prefixes l_x empty);
        ps_a.parse_serialize_inv x empty
      )
    )
  end in

  lemma_not_unit ();
  ({
    parse = parse_ab;
    serialize = serialize_ab;
    parse_serialize_inv = (fun (x:(xa:a&(b xa))) (suffix:bytes) ->
      let (|xa, xb|) = x in
      let la = ps_a.serialize xa in
      let lb = ((ps_b xa).serialize xb) in
      ps_a.parse_serialize_inv xa (add_prefixes lb suffix);
      (ps_b xa).parse_serialize_inv xb suffix;
      add_prefixes_add_prefixes la lb suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_ab buf with
      | None -> ()
      | Some (xab, suffix) ->
        let (|xa, xb|) = xab in
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let (xb, suffix) = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix;
        add_prefixes_add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb) suffix
    );
  })

let isomorphism_explicit #a #bytes b ps_a f g g_f_inv f_g_inv =
  let parse_b buf =
    match ps_a.parse buf with
    | Some (xa, l) -> Some (f xa, l)
    | None -> None
  in
  let serialize_b xb =
    ps_a.serialize (g xb)
  in
  {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      f_g_inv x;
      ps_a.parse_serialize_inv (g x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match ps_a.parse buf with
      | Some (xa, l) -> (
        g_f_inv xa;
        ps_a.serialize_parse_inv buf
      )
      | None -> ()
    );
  }

let isomorphism #a b ps_a f g =
  isomorphism_explicit #a b ps_a f g (fun _ -> ()) (fun _ -> ())

(*** Parser for basic types ***)

let ps_unit #bytes #bl =
  {
    parse = (fun b -> Some ((), b));
    serialize = (fun _ -> []);
    parse_serialize_inv = (fun _ b -> assert_norm(add_prefixes [] b == b));
    serialize_parse_inv = (fun buf -> assert_norm(add_prefixes [] buf == buf));
  }

//WHY THE #bytes #bl EVERYWHERE?????
#push-options "--fuel 2"
let ps_lbytes #bytes #bl n =
  let parse_lbytes (buf:bytes): option (lbytes bytes n & bytes) =
    if length buf < n then
      None
    else (
      slice_length buf 0 n;
      let x = slice #bytes #bl buf 0 n in
      let suffix = slice #bytes #bl buf n (length buf) in
      Some (x, suffix)
    )
  in
  let serialize_lbytes (b:lbytes bytes n): list bytes =
    [b]
  in
  empty_length #bytes #bl ();
  {
    parse = parse_lbytes;
    serialize = serialize_lbytes;
    parse_serialize_inv = (fun b suffix ->
      concat_length b suffix;
      slice_concat_left b suffix;
      slice_concat_right b suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_lbytes buf with
      | None -> ()
      | Some (b, suffix) -> (
        concat_slice buf n
      )
    );
  }
#pop-options

(*
val ps_uint: t:IT.inttype{IT.unsigned t /\ ~(IT.U1? t)} -> parser_serializer (IT.uint_t t IT.SEC)
let ps_uint t =
  let nbytes = IT.numbytes t in
  isomorphism_explicit (IT.uint_t t IT.SEC)
    (ps_lbytes nbytes)
    (fun b -> uint_from_bytes_be b)
    (fun x -> uint_to_bytes_be x)
    (fun b -> lemma_uint_from_to_bytes_be_preserves_value #t #IT.SEC b)
    (fun x -> lemma_uint_to_from_bytes_be_preserves_value x)

let ps_u8 = ps_uint IT.U8
let ps_u16 = ps_uint IT.U16
let ps_u32 = ps_uint IT.U32
let ps_u64 = ps_uint IT.U64
let ps_u128 = ps_uint IT.U128
*)

(*** Exact parsers ***)

let ps_to_pse #bytes #bl #a ps_a =
  let parse_exact_a (buf:bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (x, suffix) ->
      if length suffix = 0 then
        Some x
      else
        None
  in
  let serialize_exact_a (x:a) =
    add_prefixes (ps_a.serialize x) empty
  in
  {
    parse_exact = parse_exact_a;
    serialize_exact = serialize_exact_a;
    parse_serialize_inv_exact = (fun x ->
      ps_a.parse_serialize_inv x empty;
      empty_length #bytes ()
    );
    serialize_parse_inv_exact = (fun buf ->
      match parse_exact_a buf with
      | None -> ()
      | Some _ -> (
        let (x, suffix) = Some?.v (ps_a.parse buf) in
        ps_a.serialize_parse_inv buf;
        length_zero suffix
      )
    );
  }

//The two following functions are defined here because F* can't reason on recursive functions defined inside a function
val _parse_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> parser_serializer bytes a -> buf:bytes -> Tot (option (list a)) (decreases (length buf))
let rec _parse_la #bytes #bl #a ps_a buf =
  if length buf = 0 then (
    Some []
  ) else (
    match ps_a.parse buf with
    | None -> None
    | Some (h, suffix) -> begin
      if length suffix >= length buf then (
        None //Impossible case
      ) else (
        match _parse_la ps_a suffix with
        | None -> None
        | Some t -> Some (h::t)
      )
    end
  )

val _serialize_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> parser_serializer bytes a -> l:list a -> bytes
let rec _serialize_la #bytes #bl #a ps_a l =
  match l with
  | [] -> empty
  | h::t ->
    add_prefixes (ps_a.serialize h) (_serialize_la ps_a t)

#push-options "--fuel 1"
let pse_list #bytes #bl #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a) = _serialize_la ps_a l in
  let rec parse_serialize_inv_la (l:list a): Lemma (parse_la (serialize_la l) == Some l) =
    match l with
    | [] -> empty_length #bytes ()
    | h::t ->
      ps_a.parse_serialize_inv h (serialize_la t);
      let suffix = (_serialize_la ps_a t) in
      if prefixes_is_empty (ps_a.serialize h) then (
        add_prefixes_identity_inv (ps_a.serialize h) empty;
        ps_a.parse_serialize_inv h empty;
        assert(False)
      ) else (
        add_prefixes_length_strict (ps_a.serialize h) suffix;
        parse_serialize_inv_la t
      )
  in
  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (length buf)) =
    if length buf = 0 then (
      length_zero buf
    ) else (
       match parse_la buf with
       | None -> ()
       | Some l ->
         let (_, suffix) = Some?.v (ps_a.parse buf) in
         ps_a.serialize_parse_inv buf;
         serialize_parse_inv_la suffix
    )
  in
  {
    parse_exact = parse_la;
    serialize_exact = serialize_la;
    parse_serialize_inv_exact = parse_serialize_inv_la;
    serialize_parse_inv_exact = serialize_parse_inv_la;
  }
#pop-options


(*** Parser for variable-length lists ***)

type nat_in_range (r:size_range) = n:nat{in_range r n}

val ps_nat_in_range: r:size_range -> parser_serializer (nat_in_range r)
let ps_nat_in_range r =
  let size_int_type =
    if r.max < pow2 8 then IT.uint8
    else if r.max < pow2 16 then IT.uint16
    else if r.max < pow2 32 then IT.uint32
    else IT.uint64
  in
  let ps_it: parser_serializer size_int_type =
    if r.max < pow2 8 then ps_u8
    else if r.max < pow2 16 then ps_u16
    else if r.max < pow2 32 then ps_u32
    else ps_u64
  in
  let nat_to_it (n:nat_in_range r): size_int_type =
    if r.max < pow2 8 then IT.u8 n
    else if r.max < pow2 16 then IT.u16 n
    else if r.max < pow2 32 then IT.u32 n
    else IT.u64 n
  in
  let it_to_nat (n:size_int_type): nat =
    if r.max < pow2 8 then IT.v #IT.U8 #IT.SEC n
    else if r.max < pow2 16 then IT.v #IT.U16 #IT.SEC n
    else if r.max < pow2 32 then IT.v #IT.U32 #IT.SEC n
    else IT.v #IT.U64 #IT.SEC n
  in
  let parse (buf:bytes): option (nat_in_range r & consumed_length buf) =
    match ps_it.parse buf with
    | None -> None
    | Some (n_it, len) ->
      let n_nat = it_to_nat n_it in
      if in_range r n_nat then
        Some (n_nat, len)
      else
        None
  in
  let serialize (n:nat_in_range r): bytes =
    ps_it.serialize (nat_to_it n)
  in
  {
    parse = parse;
    serialize = serialize;
    parse_serialize_inv = (fun x ->
      ps_it.parse_serialize_inv (nat_to_it x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      ps_it.serialize_parse_inv buf
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      match parse b1 with
      | None -> ()
      | Some _ -> ps_it.parse_no_lookahead b1 b2
    )
  }

#push-options "--z3rlimit 20"
val parser_serializer_exact_to_parser_serializer: #a:Type -> r:size_range -> pse_a:parser_serializer_exact a{forall x. in_range r (bytes_length (pse_a.serialize_exact x))} -> parser_serializer a
let parser_serializer_exact_to_parser_serializer #a r pse_a =
  let ps_nat = ps_nat_in_range r in
  let parse_a (buf:bytes) =
    match ps_nat.parse buf with
    | None -> None
    | Some (sz, l) -> begin
      let buf2 = delete_prefix buf l in
      if bytes_length buf2 < sz then (
        None
      ) else (
        match pse_a.parse_exact (bytes_slice buf2 0 sz) with
        | None -> None
        | Some x -> Some (x, ((l + sz) <: consumed_length buf))
      )
    end
  in
  let serialize_a (x_a:a): bytes =
    let x_serialized = pse_a.serialize_exact x_a in
    bytes_append (ps_nat.serialize (bytes_length x_serialized)) x_serialized
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x ->
      let x_serialized = pse_a.serialize_exact x in
      let x_sz = bytes_length (x_serialized) in
      let l = bytes_length (ps_nat.serialize x_sz) in
      ps_nat.parse_no_lookahead (ps_nat.serialize x_sz) (serialize_a x);
      ps_nat.parse_serialize_inv x_sz;
      pse_a.parse_serialize_inv_exact x;
      assert (bytes_equal (bytes_slice (delete_prefix (serialize_a x) l) 0 (bytes_length x_serialized)) x_serialized)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_a buf with
      | None -> ()
      | Some (x, l) ->
        let (sz, l) = Some?.v (ps_nat.parse buf) in
        ps_nat.serialize_parse_inv buf;
        pse_a.serialize_parse_inv_exact (bytes_slice (delete_prefix buf l) 0 sz);
        assert (bytes_equal (bytes_slice buf 0 (l+sz)) (serialize_a x))
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      match parse_a b1 with
      | None -> ()
      | Some (x, len) ->
        ps_nat.parse_no_lookahead b1 b2;
        let (sz, l) = Some?.v (ps_nat.parse b1) in
        assert (bytes_equal (bytes_slice (delete_prefix b1 l) 0 sz) (bytes_slice (delete_prefix b2 l) 0 sz))
    )
  }
#pop-options

type bllist (a:Type) (ps_a:parser_serializer a) (r:size_range) = l:list a{in_range r (byte_length ps_a l)}

#push-options "--fuel 1"
val byte_length_lemma: #a:Type -> ps_a:parser_serializer a -> l:list a -> Lemma
  (byte_length ps_a l == bytes_length ((pse_list ps_a).serialize_exact l))
  [SMTPat (bytes_length ((pse_list ps_a).serialize_exact l))]
let rec byte_length_lemma #a ps_a l =
  //Why is this needed?
  assert_norm(forall x. (pse_list ps_a).serialize_exact x == _serialize_la ps_a x);
  match l with
  | [] -> ()
  | h::t -> byte_length_lemma ps_a t
#pop-options


val ps_list: #a:Type -> r:size_range -> ps_a:parser_serializer a -> parser_serializer (bllist a ps_a r)
let ps_list #a r ps_a =
  let pse_la = pse_list ps_a in
  let pse_bllist_a: parser_serializer_exact (bllist a ps_a r) =
    {
      parse_exact = (fun buf ->
        if in_range r (bytes_length buf) then
          match pse_la.parse_exact buf with
          | Some x ->
            byte_length_lemma ps_a x;
            pse_la.serialize_parse_inv_exact buf;
            Some (x <: bllist a ps_a r)
          | None -> None
        else
          None
      );
      serialize_exact = (fun x ->
        (pse_list ps_a).serialize_exact x
      );
      parse_serialize_inv_exact = (fun x ->
        pse_la.parse_serialize_inv_exact x;
        byte_length_lemma ps_a x
      );
      serialize_parse_inv_exact = (fun buf -> pse_la.serialize_parse_inv_exact buf);
    }
  in
  parser_serializer_exact_to_parser_serializer r pse_bllist_a

let ps_seq #a r ps_a =
  FStar.Classical.forall_intro (bytes_lemma_list_seq_bij #a);
  FStar.Classical.forall_intro (bytes_lemma_seq_list_bij #a);
  isomorphism
    (blseq a ps_a r)
    (ps_list r ps_a)
    (fun l -> bytes_seq_of_list l)
    (fun s -> bytes_seq_to_list s)

#push-options "--fuel 1"
let ps_bytes r =
  let rec lemma (b:bytes): Lemma (ensures byte_length ps_u8 (bytes_seq_to_list b) == bytes_length b) (decreases (bytes_length b)) [SMTPat (byte_length ps_u8 (bytes_seq_to_list b))] =
    if bytes_length b = 0 then (
      ()
    ) else (
      lemma (bytes_slice b 1 (bytes_length b))
    )
  in
  isomorphism
    (blbytes r)
    (ps_seq r ps_u8)
    (fun s -> s)
    (fun b -> b)
#pop-options
