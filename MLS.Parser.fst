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
  let lemma_not_unit (): Lemma((parse_ab (empty <: bytes) == None) <==> (ps_a.parse (empty <: bytes) == None) \/ (forall xa. (ps_b xa).parse (empty <: bytes) == None)) = begin
    match ps_a.parse (empty <: bytes) with
    | None -> ()
    | Some (xa, empty_suffix) -> (
      ps_a.serialize_parse_inv (empty <: bytes);
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
  let res = {
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
  } in
  res

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
      match slice #bytes #bl buf 0 n, slice #bytes #bl buf n (length buf) with
      | Some x, Some suffix -> Some (x, suffix)
      | _ -> None
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


val ps_uint: #bytes:Type0 -> {|bytes_like bytes|} -> sz:pos -> parser_serializer bytes (nat_lbytes sz)
let ps_uint #bytes #bl sz =
  let parse_uint (buf:bytes): option (nat_lbytes sz & bytes) =
    match (ps_lbytes sz).parse buf with
    | Some (x, suffix) -> (
      match to_nat sz (x <: bytes) with
      | Some n -> Some (n, suffix)
      | None -> None
    )
    | None -> None
  in
  let serialize_uint (n:nat_lbytes sz): list bytes =
    (ps_lbytes sz).serialize (from_nat sz n <: bytes)
  in
  {
    parse = parse_uint;
    serialize = serialize_uint;
    parse_serialize_inv = (fun n suffix ->
      from_to_nat #bytes sz n;
      (ps_lbytes sz).parse_serialize_inv (from_nat sz n <: bytes) suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      (ps_lbytes sz).serialize_parse_inv buf;
      match (ps_lbytes sz).parse buf with
      | Some (x, suffix) -> to_from_nat #bytes sz x
      | None -> ()
    );
  }

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
  let serialize_exact_a (x:a): b:bytes =
    ps_a.parse_serialize_inv x empty;
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

//The following functions are defined here because F* can't reason on recursive functions defined inside a function
#push-options "--fuel 1"
val _parse_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> buf:bytes -> Tot (option (list a)) (decreases (length (buf <: bytes)))
let rec _parse_la #bytes #bl #a ps_a buf =
  if length (buf <: bytes) = 0 then (
    Some []
  ) else (
    match ps_a.parse (buf <: bytes) with
    | None -> None
    | Some (h, suffix) -> begin
      if length suffix >= length (buf <: bytes) then (
        None //Impossible case, but no need to prove it here
      ) else (
        match _parse_la ps_a suffix with
        | None -> None
        | Some t -> Some (h::t)
      )
    end
  )
#pop-options

#push-options "--fuel 1"
val _serialize_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> l:list a -> bytes
let rec _serialize_la #bytes #bl #a ps_a l =
  match l with
  | [] -> empty
  | h::t ->
    add_prefixes (ps_a.serialize h) (_serialize_la ps_a t)

#push-options "--fuel 1"
let pse_list #bytes #bl #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a): bytes = _serialize_la ps_a l in
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
  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (length (buf <: bytes))) =
    if length (buf <: bytes) = 0 then (
      length_zero (buf <: bytes)
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

val ps_nat_in_range: #bytes:Type0 -> {|bytes_like bytes|} -> r:size_range -> parser_serializer bytes (nat_in_range r)
let ps_nat_in_range #bytes #bl r =
  let sz =
    if r.max < pow2 8 then 1
    else if r.max < pow2 16 then 2
    else if r.max < pow2 32 then 4
    else 8
  in
  let parse (buf:bytes): option (nat_in_range r & bytes) =
    match (ps_uint sz).parse buf with
    | None -> None
    | Some (n, suffix) ->
      if in_range r n then
        Some (n, suffix)
      else
        None
  in
  let serialize (n:nat_in_range r): list bytes =
    (ps_uint #bytes sz).serialize n
  in
  {
    parse = parse;
    serialize = serialize;
    parse_serialize_inv = (fun x suffix ->
      (ps_uint sz).parse_serialize_inv x suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      (ps_uint sz).serialize_parse_inv buf
    );
  }

val parser_serializer_exact_to_parser_serializer: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> r:size_range -> pse_a:parser_serializer_exact bytes a{forall x. in_range r (length (pse_a.serialize_exact x))} -> parser_serializer bytes a
let parser_serializer_exact_to_parser_serializer #bytes #bl #a r pse_a =
  let ps_nat = ps_nat_in_range r in
  let parse_a (buf:bytes) =
    match ps_nat.parse buf with
    | None -> None
    | Some (sz, suffix) -> begin
      match (ps_lbytes sz).parse suffix with
      | None -> None
      | Some (x_lbytes, suffix2) -> begin
        match pse_a.parse_exact x_lbytes with
        | None -> None
        | Some x_a -> Some (x_a, suffix2)
      end
    end
  in
  let serialize_a (x_a:a): list bytes =
    let x_serialized = pse_a.serialize_exact x_a in
    (ps_nat.serialize (length x_serialized)) @ [x_serialized]
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x_a suffix ->
      let x_serialized = pse_a.serialize_exact x_a in
      let sz = (length x_serialized) in
      ps_nat.parse_serialize_inv sz (add_prefixes [x_serialized] suffix);
      add_prefixes_add_prefixes (ps_nat.serialize sz) [x_serialized] suffix;
      pse_a.parse_serialize_inv_exact x_a;
      (ps_lbytes sz).parse_serialize_inv x_serialized suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_a buf with
      | None -> ()
      | Some (x_a, suffix) ->
        let (sz, suffix) = Some?.v (ps_nat.parse buf) in
        let (x_lbytes, suffix2) = Some?.v ((ps_lbytes sz).parse suffix) in
        let x_a = Some?.v (pse_a.parse_exact x_lbytes) in
        ps_nat.serialize_parse_inv buf;
        (ps_lbytes sz).serialize_parse_inv suffix;
        pse_a.serialize_parse_inv_exact x_lbytes;
        add_prefixes_add_prefixes (ps_nat.serialize sz) [x_lbytes] suffix2
    )
  }

type bllist (#bytes:Type0) {|bytes_like bytes|} (a:Type) (ps_a:parser_serializer bytes a) (r:size_range) = l:list a{in_range r (bytes_length ps_a l)}

val ps_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> r:size_range -> ps_a:parser_serializer bytes a -> parser_serializer bytes (bllist a ps_a r)
let ps_list #bytes #bl #a r ps_a =
  let pse_la = pse_list ps_a in
  let pse_bllist_a: parser_serializer_exact bytes (bllist a ps_a r) =
    {
      parse_exact = (fun buf ->
        if in_range r (length buf) then
          match pse_la.parse_exact buf with
          | Some x ->
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
        pse_la.parse_serialize_inv_exact x
      );
      serialize_parse_inv_exact = (fun buf -> pse_la.serialize_parse_inv_exact buf);
    }
  in
  parser_serializer_exact_to_parser_serializer r pse_bllist_a

let ps_seq #bytes #bl #a r ps_a =
  FStar.Classical.forall_intro (Seq.lemma_list_seq_bij #a);
  FStar.Classical.forall_intro (Seq.lemma_seq_list_bij #a);
  isomorphism
    (blseq a ps_a r)
    (ps_list r ps_a)
    (fun l -> Seq.seq_of_list l)
    (fun s -> Seq.seq_to_list s)

let ps_bytes #bytes #bl r =
  let parse_bytes (buf:bytes): option (blbytes bytes r) =
    if in_range r (length (buf <: bytes)) then
      Some buf
    else
      None
  in
  let serialize_bytes (buf:blbytes bytes r): bytes =
    buf
  in
  let pse_bytes: parser_serializer_exact bytes (blbytes bytes r)=
    {
      parse_exact = parse_bytes;
      serialize_exact = serialize_bytes;
      parse_serialize_inv_exact = (fun _ -> ());
      serialize_parse_inv_exact = (fun _ -> ());
    }
  in
  parser_serializer_exact_to_parser_serializer r pse_bytes

