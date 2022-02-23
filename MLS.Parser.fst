module MLS.Parser

open MLS.Bytes

#set-options "--fuel 0 --ifuel 2"

(*** Helper functions ***)

#push-options "--ifuel 1 --fuel 1"
val is_suffix_explicit_transitive: b1:bytes -> b2:bytes -> b3:bytes -> l1:list bytes -> l2:list bytes -> Lemma
  (requires is_suffix_explicit b1 b2 l1 /\ is_suffix_explicit b2 b3 l2)
  (ensures is_suffix_explicit b1 b3 (l1@l2))
  (decreases l1)
let rec is_suffix_explicit_transitive b1 b2 b3 l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> is_suffix_explicit_transitive (bytes_concat h b1) b2 b3 t l2
#pop-options

let is_suffix_transitive b1 b2 b3 =
  eliminate exists l1. is_suffix_explicit b1 b2 l1
  returns _
  with _.
  eliminate exists l2. is_suffix_explicit b2 b3 l2
  returns is_suffix b1 b3
  with _. is_suffix_explicit_transitive b1 b2 b3 l1 l2

val is_suffix_explicit_to_implicit: b1:bytes -> b2:bytes -> l:list bytes -> Lemma
  (requires is_suffix_explicit b1 b2 l)
  (ensures is_suffix b1 b2)
let is_suffix_explicit_to_implicit b1 b2 l =
  introduce exists l. is_suffix_explicit b1 b2 l
  with l
  and _

#push-options "--fuel 1 --ifuel 1"
val is_suffix_reflexive: b:bytes -> Lemma (is_suffix b b)
let is_suffix_reflexive b =
  is_suffix_explicit_to_implicit b b []
#pop-options

(*** Parser combinators ***)

let bind #a #b ps_a ps_b =
  let parse_ab (buf:bytes): option ((xa:a&(b xa)) & suffix_of buf) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, buf_suffix) -> begin
      match (ps_b xa).parse buf_suffix with
      | None -> None
      | Some (xb, buf_suffix_suffix) -> (
        is_suffix_transitive buf_suffix_suffix buf_suffix buf;
        Some ((|xa, xb|), buf_suffix_suffix)
      )
    end
  in
  let serialize_ab (x:(xa:a&(b xa))) (suffix:bytes): extension_of suffix =
    let (|xa, xb|) = x in
    let xb_suffix = ((ps_b xa).serialize xb suffix) in
    let xa_xb_suffix = ps_a.serialize xa xb_suffix in
    is_suffix_transitive suffix xb_suffix xa_xb_suffix;
    xa_xb_suffix
  in
  let lemma_not_unit (): Lemma((parse_ab bytes_empty == None) <==> (ps_a.parse bytes_empty == None) \/ (forall xa. (ps_b xa).parse bytes_empty == None)) = begin
    admit()
    //match parse_ab bytes_empty with
    //| None -> begin
    //  match ps_a.parse bytes_empty with
    //  | None -> ()
    //  | Some (xa, la) ->
    //    FStar.Classical.forall_intro (fun (x:a) -> (
    //      let lemma (): Lemma ((delete_prefix bytes_empty la) == bytes_empty) =
    //        delete_prefix_length bytes_empty la;
    //        bytes_empty_length ();
    //        bytes_length_zero (delete_prefix bytes_empty la)
    //      in lemma ();
    //      ps_a.parse_serialize_inv x;
    //      let lemma (): Lemma (la == 0) =
    //        bytes_empty_length ()
    //      in lemma ();
    //      let lemma (): Lemma (bytes_slice bytes_empty 0 la == bytes_empty) =
    //        bytes_slice_length bytes_empty 0 la;
    //        bytes_length_zero (bytes_slice bytes_empty 0 la)
    //      in lemma ();
    //      let lemma (): Lemma (bytes_slice (ps_a.serialize x) 0 la == bytes_empty) =
    //        bytes_slice_length (ps_a.serialize x) 0 la;
    //        bytes_length_zero (bytes_slice (ps_a.serialize x) 0 la)
    //      in lemma ();
    //      //ps_a.parse_no_lookahead bytes_empty (ps_a.serialize x);
    //      admit()
    //    ) <: Lemma (is_not_unit (ps_b x)))
    //end
    //| Some _ -> (
    //  match ps_a.parse bytes_empty with
    //  | None -> ()
    //  | Some (xa, la) -> (
    //    let lemma (): Lemma ((delete_prefix bytes_empty la) == bytes_empty) =
    //      delete_prefix_length bytes_empty la;
    //      bytes_empty_length ();
    //      bytes_length_zero (delete_prefix bytes_empty la)
    //    in lemma ()
    //  )
    //)
  end in
  lemma_not_unit ();
  ({
    parse = parse_ab;
    serialize = serialize_ab;
    parse_serialize_inv = (fun (x:(xa:a&(b xa))) (suffix:bytes) ->
      let (|xa, xb|) = x in
      let xb_suffix = ((ps_b xa).serialize xb suffix) in
      let xa_xb_suffix = ps_a.serialize xa xb_suffix in
      (ps_b xa).parse_serialize_inv xb suffix;
      ps_a.parse_serialize_inv xa xb_suffix;
      is_suffix_transitive suffix xb_suffix xa_xb_suffix;
      ()
    );

    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_ab buf with
      | None -> ()
      | Some (xab, suffix) ->
        let (|xa, xb|) = xab in
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let (xb, suffix) = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      bytes_concat_length b1 b2;
      match parse_ab b1 with
      | None -> ()
      | Some (x, l) -> (
        let (xa, la) = Some?.v (ps_a.parse b1) in
        //ps_a.parse_no_lookahead b1 b2;
        //assert (ps_a.parse (bytes_concat b1 b2) == Some(xa, la));
        //let (xb, lb) = Some?.v ((ps_b xa).parse (delete_prefix b1 la)) in
        //assume (delete_prefix (bytes_concat b1 b2) la)
        //assume (parse_ab (bytes_concat b1 b2) == Some (x, l))
        ()
      )
    )
  })

let isomorphism_explicit #a b ps_a f g g_f_inv f_g_inv =
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
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      ps_a.parse_no_lookahead b1 b2
    )
  }

let isomorphism #a b ps_a f g =
  isomorphism_explicit #a b ps_a f g (fun _ -> ()) (fun _ -> ())

(*** Parser for basic types ***)

let ps_unit =
  {
    parse = (fun b -> is_suffix_reflexive b; Some ((), b));
    serialize = (fun _ b -> is_suffix_reflexive b; b);
    parse_serialize_inv = (fun _ b -> ());
    serialize_parse_inv = (fun buf -> ());
    parse_no_lookahead = (fun _ _ -> ());
  }

#push-options "--fuel 2"
let ps_lbytes n =
  let parse_lbytes (buf:bytes): option (lbytes n & suffix_of buf) =
    if bytes_length buf < n then
      None
    else (
      bytes_slice_length buf 0 n;
      let x = bytes_slice buf 0 n in
      let suffix = bytes_slice buf n (bytes_length buf) in
      bytes_concat_slice buf n;
      is_suffix_explicit_to_implicit suffix buf [x];
      Some (x, suffix)
    )
  in
  let serialize_lbytes (b:lbytes n) (suffix:bytes): extension_of suffix =
    is_suffix_explicit_to_implicit suffix (bytes_concat b suffix) [b];
    bytes_concat b suffix
  in
  bytes_empty_length ();
  {
    parse = parse_lbytes;
    serialize = serialize_lbytes;
    parse_serialize_inv = (fun b suffix ->
      bytes_concat_length b suffix;
      bytes_slice_concat_left b suffix;
      bytes_slice_concat_right b suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_lbytes buf with
      | None -> ()
      | Some (b, suffix) -> (
        bytes_concat_slice buf n
      )
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      ()
    )
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

let ps_to_pse #a ps_a =
  let parse_exact_a (buf:bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (x, suffix) ->
      if bytes_length suffix = 0 then
        Some x
      else
        None
  in
  let serialize_exact_a (x:a) =
    ps_a.serialize x bytes_empty
  in
  {
    parse_exact = parse_exact_a;
    serialize_exact = serialize_exact_a;
    parse_serialize_inv_exact = (fun x ->
      ps_a.parse_serialize_inv x bytes_empty;
      bytes_empty_length ()
    );
    serialize_parse_inv_exact = (fun buf ->
      match parse_exact_a buf with
      | None -> ()
      | Some _ -> (
        let (x, suffix) = Some?.v (ps_a.parse buf) in
        ps_a.serialize_parse_inv buf;
        bytes_length_zero suffix
      )
    );
  }

//The two following functions are defined here because F* can't reason on recursive functions defined inside a function
val _parse_la: #a:Type -> parser_serializer a -> buf:bytes -> Tot (option (list a)) (decreases (bytes_length buf))
let rec _parse_la #a ps_a buf =
  if bytes_length buf = 0 then (
    Some []
  ) else (
    match ps_a.parse buf with
    | None -> None
    | Some (h, suffix) -> begin
      if bytes_length suffix >= bytes_length buf then (
        None //Impossible case
      ) else (
        match _parse_la ps_a suffix with
        | None -> None
        | Some t -> Some (h::t)
      )
    end
  )

val _serialize_la: #a:Type -> parser_serializer a -> l:list a -> bytes
let rec _serialize_la #a ps_a l =
  match l with
  | [] -> bytes_empty
  | h::t ->
    ps_a.serialize h (_serialize_la ps_a t)

#push-options "--fuel 1"
let pse_list #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a) = _serialize_la ps_a l in
  let rec parse_serialize_inv_la (l:list a): Lemma (parse_la (serialize_la l) == Some l) =
    match l with
    | [] -> bytes_empty_length ()
    | h::t ->
      ps_a.parse_serialize_inv h (serialize_la t);
      let suffix = (_serialize_la ps_a t) in
      assume(bytes_length suffix < bytes_length (serialize_la l));
      parse_serialize_inv_la t
  in
  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (bytes_length buf)) =
    if bytes_length buf = 0 then (
      bytes_length_zero buf
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
