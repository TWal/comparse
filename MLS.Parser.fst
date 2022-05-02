module MLS.Parser

open FStar.List.Tot
open MLS.Bytes

#set-options "--fuel 0 --ifuel 2"

#push-options "--fuel 1"
let rec for_allP_eq #a pre l =
  match l with
  | [] -> ()
  | h::t -> for_allP_eq pre t
#pop-options

let rec add_prefixes #bytes #bl l suffix =
  match l with
  | [] -> suffix
  | h::t -> concat h ((add_prefixes t suffix))

let is_not_unit #bytes #bl #a ps_a = forall b. length b == 0 ==> ps_a.parse b == None

(*** Helper functions ***)

#push-options "--ifuel 1 --fuel 1"
val for_allP_append: #a:Type -> pre:(a -> Type0) -> l1:list a -> l2:list a -> Lemma
  (for_allP pre (l1@l2) <==> for_allP pre l1 /\ for_allP pre l2)
  [SMTPat (for_allP pre (l1@l2))]
let rec for_allP_append #a pre l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> for_allP_append pre t l2
#pop-options

#push-options "--ifuel 1 --fuel 1"
val add_prefixes_add_prefixes: #bytes:Type0 -> {|bytes_like bytes|} -> l1:list bytes -> l2:list bytes -> suffix:bytes -> Lemma
  (add_prefixes l1 (add_prefixes l2 suffix) == add_prefixes (l1@l2) suffix)
let rec add_prefixes_add_prefixes l1 l2 suffix =
  match l1 with
  | [] -> ()
  | h::t -> add_prefixes_add_prefixes t l2 suffix
#pop-options

#push-options "--ifuel 1 --fuel 1"
val prefixes_length: #bytes:Type0 -> {|bytes_like bytes|} -> list bytes -> nat
let rec prefixes_length #bytes #bl l =
  match l with
  | [] -> 0
  | h::t -> length h + (prefixes_length t)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val add_prefixes_length: #bytes:Type0 -> {|bytes_like bytes|} -> l:list bytes -> suffix:bytes -> Lemma
  (length (add_prefixes l suffix) == prefixes_length l + length suffix)
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
val add_prefixes_pre: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> l:list bytes -> suffix:bytes -> Lemma
  (requires for_allP pre l /\ pre suffix)
  (ensures pre (add_prefixes l suffix))
let rec add_prefixes_pre #bytes #bl pre l suffix =
  match l with
  | [] -> ()
  | h::t -> add_prefixes_pre pre t suffix
#pop-options

(*** Parser combinators ***)

let bind #bytes #bl #a #b ps_a ps_b =
  let parse_ab (buf:bytes): option (dtuple2 a b & bytes) =
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
  let serialize_ab (x:dtuple2 a b): list bytes =
    let (|xa, xb|) = x in
    let la = ps_a.serialize xa in
    let lb = (ps_b xa).serialize xb in
    la@lb
  in
  let is_valid_ab (pre:bytes_compatible_pre bytes) (x:dtuple2 a b): Type0 =
    let (|xa, xb|) = x in
    ps_a.is_valid pre xa /\ (ps_b xa).is_valid pre xb
  in

  ({
    parse = parse_ab;
    serialize = serialize_ab;
    parse_serialize_inv = (fun (|xa, xb|) (suffix:bytes) ->
      let la = ps_a.serialize xa in
      let lb = ((ps_b xa).serialize xb) in
      ps_a.parse_serialize_inv xa (add_prefixes lb suffix);
      (ps_b xa).parse_serialize_inv xb suffix;
      add_prefixes_add_prefixes la lb suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_ab buf with
      | None -> ()
      | Some ((|xa, xb|), suffix) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let (xb, suffix) = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv xb_suffix;
        add_prefixes_add_prefixes (ps_a.serialize xa) ((ps_b xa).serialize xb) suffix
    );

    is_valid = is_valid_ab;
    //is_valid_trivial = (fun pre ->
    //  ps_a.is_valid_trivial pre;
    //  introduce forall xa xb. (ps_b xa).is_valid pre xb with (
    //    (ps_b xa).is_valid_trivial pre
    //  )
    //);
    //is_valid_monotonic = (fun pre1 pre2 (|xa, xb|) ->
    //  ps_a.is_valid_monotonic pre1 pre2 xa;
    //  (ps_b xa).is_valid_monotonic pre1 pre2 xb
    //);
    parse_pre = (fun pre buf ->
      match parse_ab buf with
      | None -> ()
      | Some ((|xa, xb|), suffix) ->
        let (xa, xb_suffix) = Some?.v (ps_a.parse buf) in
        let (xb, suffix) = Some?.v ((ps_b xa).parse xb_suffix) in
        ps_a.parse_pre pre buf;
        (ps_b xa).parse_pre pre xb_suffix
    );
    serialize_pre = (fun pre (|xa, xb|) ->
      ps_a.serialize_pre pre xa;
      (ps_b xa).serialize_pre pre xb
    );
  })

let bind_is_not_unit #bytes #bl #a #b ps_a ps_b =
  introduce forall b. length b == 0 ==> (bind ps_a ps_b).parse b == None with (
    match ps_a.parse b with
    | None -> ()
    | Some (xa, b_suffix) ->
      ps_a.serialize_parse_inv b;
      add_prefixes_length (ps_a.serialize xa) b_suffix
  )

let bind_is_valid #bytes #bl #a #b ps_a ps_b pre xa xb = ()

let isomorphism #bytes #bl #a #b ps_a iso =
  let parse_b buf =
    match ps_a.parse buf with
    | Some (xa, l) -> Some (iso.a_to_b xa, l)
    | None -> None
  in
  let serialize_b xb =
    ps_a.serialize (iso.b_to_a xb)
  in
  let is_valid_b pre xb =
    ps_a.is_valid pre (iso.b_to_a xb)
  in
  let res = {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      iso.b_to_a_to_b x;
      ps_a.parse_serialize_inv (iso.b_to_a x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match ps_a.parse buf with
      | Some (xa, l) -> (
        iso.a_to_b_to_a xa;
        ps_a.serialize_parse_inv buf
      )
      | None -> ()
    );
    is_valid = is_valid_b;
    parse_pre = (fun pre buf ->
      introduce forall xa. iso.b_to_a (iso.a_to_b xa) == xa with iso.a_to_b_to_a xa;
      ps_a.parse_pre pre buf
    );
    serialize_pre = (fun pre xb ->
      iso.b_to_a_to_b xb;
      ps_a.serialize_pre pre (iso.b_to_a xb)
    );
  } in
  res

let isomorphism_is_not_unit #bytes #bl #a #b ps_a iso = ()

let isomorphism_is_valid #bytes #bl #a #b ps_a iso pre xb = ()

let refine #bytes #bl #a ps_a pred =
  {
    parse = (fun buf ->
      match ps_a.parse buf with
      | Some (x, suffix) ->
        if pred x then Some ((x <: refined a pred), suffix)
        else None
      | None -> None
    );
    serialize = (fun x -> ps_a.serialize x);
    parse_serialize_inv = (fun x suffix -> ps_a.parse_serialize_inv x suffix);
    serialize_parse_inv = (fun buf -> ps_a.serialize_parse_inv buf);
    is_valid = (fun pre (x:a{pred x}) -> ps_a.is_valid pre x);
    parse_pre = (fun pre buf -> ps_a.parse_pre pre buf);
    serialize_pre = (fun pre xb -> ps_a.serialize_pre pre xb);
  }

let refine_is_not_unit #bytes #bl #a ps_a pred = ()

let refine_is_valid #bytes #bl #a ps_a pred pre x = ()

(*** Parser for basic types ***)

let ps_unit #bytes #bl =
  {
    parse = (fun b -> Some ((), b));
    serialize = (fun _ -> []);
    parse_serialize_inv = (fun _ b -> assert_norm(add_prefixes [] b == b));
    serialize_parse_inv = (fun buf -> assert_norm(add_prefixes [] buf == buf));
    is_valid = (fun _ _ -> True);
    parse_pre = (fun pre buf -> ());
    serialize_pre = (fun pre xb -> assert_norm(for_allP pre []));
  }

let ps_unit_is_valid #bytes #bl pre x = ()

//WHY THE #bytes #bl EVERYWHERE?????
#push-options "--fuel 2"
let ps_lbytes #bytes #bl n =
  let parse_lbytes (buf:bytes): option (lbytes bytes n & bytes) =
    if length buf < n then
      None
    else (
      split_length buf n;
      match split #bytes #bl buf n with
      | Some (x, suffix) -> Some (x, suffix)
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
      split_concat b suffix
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_lbytes buf with
      | None -> ()
      | Some (b, suffix) -> (
        concat_split buf n
      )
    );
    is_valid = (fun pre b -> pre b);
    parse_pre = (fun pre buf -> ());
    serialize_pre = (fun pre b -> ());
  }
#pop-options

let ps_lbytes_is_not_unit #bytes #bl n = ()

let ps_lbytes_is_valid #bytes #bl n pre x = ()

let ps_nat_lbytes #bytes #bl sz =
  let parse_nat_lbytes (buf:bytes): option (nat_lbytes sz & bytes) =
    match (ps_lbytes sz).parse buf with
    | Some (x, suffix) -> (
      match to_nat sz (x <: bytes) with
      | Some n -> Some (n, suffix)
      | None -> None
    )
    | None -> None
  in
  let serialize_nat_lbytes (n:nat_lbytes sz): list bytes =
    (ps_lbytes sz).serialize (from_nat sz n <: bytes)
  in
  {
    parse = parse_nat_lbytes;
    serialize = serialize_nat_lbytes;
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
    is_valid = (fun pre _ -> True);
    parse_pre = (fun pre buf -> ());
    serialize_pre = (fun pre n -> assert_norm (for_allP pre (serialize_nat_lbytes n) <==> pre (from_nat sz n <: bytes)));
  }

let ps_nat_lbytes_is_valid #bytes #bl sz pre x = ()

(*** Exact parsers ***)

let ps_to_pse #bytes #bl #a ps_a =
  let parse_exact_a (buf:bytes) =
    match ps_a.parse buf with
    | None -> None
    | Some (x, suffix) ->
      if recognize_empty suffix then
        Some x
      else
        None
  in
  let serialize_exact_a (x:a): bytes =
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
        ps_a.serialize_parse_inv buf
      )
    );
    is_valid_exact = ps_a.is_valid;
    parse_pre_exact = (fun pre buf -> ps_a.parse_pre pre buf);
    serialize_pre_exact = (fun pre x ->
      ps_a.serialize_pre pre x;
      add_prefixes_pre pre (ps_a.serialize x) empty
    );
  }

let ps_to_pse_is_valid #bytes #bl #a ps_a pre x = ()

//The following functions are defined here because F* can't reason on recursive functions defined inside a function
#push-options "--fuel 1"
val _parse_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> buf:bytes -> Tot (option (list a)) (decreases (length (buf <: bytes)))
let rec _parse_la #bytes #bl #a ps_a buf =
  if recognize_empty buf then (
    Some []
  ) else if length (buf <: bytes) = 0 then (
    None
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
#pop-options

val _is_valid_la: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer bytes a -> pre:bytes_compatible_pre bytes -> l:list a -> Type0
let _is_valid_la #bytes #bl #a ps_a pre l =
  for_allP (ps_a.is_valid pre) l

#push-options "--fuel 1"
let pse_list #bytes #bl #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a): bytes = _serialize_la ps_a l in
  let is_valid_la (pre:bytes_compatible_pre bytes) (l:list a): Type0 = _is_valid_la ps_a pre l in
  let rec parse_serialize_inv_la (l:list a): Lemma (parse_la (serialize_la l) == Some l) =
    match l with
    | [] -> empty_length #bytes ()
    | h::t ->
      ps_a.parse_serialize_inv h (serialize_la t);
      let suffix = (_serialize_la ps_a t) in
      if prefixes_length (ps_a.serialize h) = 0 then (
        empty_length #bytes ();
        ps_a.parse_serialize_inv h empty;
        add_prefixes_length (ps_a.serialize h) empty;
        assert(False)
      ) else (
        empty_length #bytes ();
        add_prefixes_length (ps_a.serialize h) suffix;
        parse_serialize_inv_la t
      )
  in

  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (length (buf <: bytes))) =
    if recognize_empty buf then (
      ()
    ) else if length (buf <: bytes) = 0 then (
      ()
    ) else (
       match parse_la buf with
       | None -> ()
       | Some l ->
         let (_, suffix) = Some?.v (ps_a.parse buf) in
         ps_a.serialize_parse_inv buf;
         serialize_parse_inv_la suffix
    )
  in
  let rec parse_pre_exact_la (pre:bytes_compatible_pre bytes) (buf:bytes{pre buf}): Lemma (ensures (match parse_la buf with | Some x -> is_valid_la pre x | None -> True)) (decreases (length (buf <: bytes))) =
    if recognize_empty (buf <: bytes) then (
      ()
    ) else if length (buf <: bytes) = 0 then (
      ()
    ) else (
      match parse_la buf with
      | None -> ()
      | Some l ->
        let (_, suffix) = Some?.v (ps_a.parse buf) in
        ps_a.parse_pre pre buf;
        parse_pre_exact_la pre suffix
    )
  in
  let rec serialize_pre_exact_la (pre:bytes_compatible_pre bytes) (l:list a{is_valid_la pre l}): Lemma (pre (serialize_la l)) =
    match l with
    | [] -> ()
    | h::t ->
      serialize_pre_exact_la pre t;
      ps_a.serialize_pre pre h;
      add_prefixes_pre pre (ps_a.serialize h) (serialize_la t)
  in
  {
    parse_exact = parse_la;
    serialize_exact = serialize_la;
    parse_serialize_inv_exact = parse_serialize_inv_la;
    serialize_parse_inv_exact = serialize_parse_inv_la;
    is_valid_exact = is_valid_la;
    parse_pre_exact = parse_pre_exact_la;
    serialize_pre_exact = serialize_pre_exact_la;
  }
#pop-options

#push-options "--fuel 1"
let pse_list_is_valid #bytes #bl #a ps_a pre l =
  // ????????
  assert_norm ((pse_list ps_a).is_valid_exact pre l == _is_valid_la ps_a pre l)
#pop-options


(*** Parser for variable-length lists ***)

val parser_serializer_exact_to_parser_serializer: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> length_pre:(nat -> bool) -> nat_parser_serializer bytes length_pre -> pse_a:parser_serializer_exact bytes a{forall x. length_pre (length (pse_a.serialize_exact x))} -> parser_serializer bytes a
let parser_serializer_exact_to_parser_serializer #bytes #bl #a length_pre ps_nat pse_a =
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
    );
    is_valid = pse_a.is_valid_exact;
    parse_pre = (fun pre buf ->
      match parse_a buf with
      | None -> ()
      | Some (x_a, suffix) ->
        let (sz, suffix) = Some?.v (ps_nat.parse buf) in
        let (x_lbytes, suffix2) = Some?.v ((ps_lbytes sz).parse suffix) in
        ps_nat.parse_pre pre buf;
        (ps_lbytes sz).parse_pre pre suffix;
        pse_a.parse_pre_exact pre x_lbytes
    );
    serialize_pre = (fun pre x ->
      let x_serialized = pse_a.serialize_exact x in
      ps_nat.serialize_pre pre (length x_serialized);
      pse_a.serialize_pre_exact pre x;
      assert_norm (for_allP pre [x_serialized] <==> pre x_serialized)
    );
  }

type pre_length_list (#bytes:Type0) {|bytes_like bytes|} (a:Type) (ps_a:parser_serializer bytes a) (pre_length:nat -> bool) = l:list a{pre_length (bytes_length ps_a l)}

val ps_pre_length_list: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> pre_length:(nat -> bool) -> ps_length:nat_parser_serializer bytes pre_length -> ps_a:parser_serializer bytes a -> parser_serializer bytes (pre_length_list a ps_a pre_length)
let ps_pre_length_list #bytes #bl #a pre_length ps_length ps_a =
  let pse_la = pse_list ps_a in
  let pse_pre_length_list_a: parser_serializer_exact bytes (pre_length_list a ps_a pre_length) =
    {
      parse_exact = (fun buf ->
        if pre_length (length buf) then
          match pse_la.parse_exact buf with
          | Some x ->
            pse_la.serialize_parse_inv_exact buf;
            Some (x <: pre_length_list a ps_a pre_length)
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
      is_valid_exact = (pse_list ps_a).is_valid_exact;
      parse_pre_exact = (fun pre buf -> (pse_list ps_a).parse_pre_exact pre buf);
      serialize_pre_exact = (fun pre x -> (pse_list ps_a).serialize_pre_exact pre x);
    }
  in
  parser_serializer_exact_to_parser_serializer pre_length ps_length pse_pre_length_list_a

let ps_pre_length_bytes #bytes #bl pre_length ps_length =
  let parse_bytes (buf:bytes): option (pre_length_bytes bytes pre_length) =
    if pre_length (length (buf <: bytes)) then
      Some buf
    else
      None
  in
  let serialize_bytes (buf:pre_length_bytes bytes pre_length): bytes =
    buf
  in
  let pse_bytes: parser_serializer_exact bytes (pre_length_bytes bytes pre_length)=
    {
      parse_exact = parse_bytes;
      serialize_exact = serialize_bytes;
      parse_serialize_inv_exact = (fun _ -> ());
      serialize_parse_inv_exact = (fun _ -> ());
      is_valid_exact = (fun pre b -> pre (b <: bytes));
      parse_pre_exact = (fun pre buf -> ());
      serialize_pre_exact = (fun pre x -> ());
    }
  in
  parser_serializer_exact_to_parser_serializer pre_length ps_length pse_bytes

let ps_pre_length_bytes_is_valid #bytes #bl pre_length ps_length pre x = ()

let ps_pre_length_seq #bytes #bl #a pre_length ps_length ps_a =
  FStar.Classical.forall_intro (Seq.lemma_list_seq_bij #a);
  FStar.Classical.forall_intro (Seq.lemma_seq_list_bij #a);
  mk_isomorphism (pre_length_seq a ps_a pre_length) (ps_pre_length_list pre_length ps_length ps_a)
    (fun (l:pre_length_list a ps_a pre_length) -> Seq.seq_of_list l)
    (fun (s:pre_length_seq a ps_a pre_length) -> Seq.seq_to_list s)

let ps_pre_length_seq_is_valid #bytes #bl #a pre_length ps_length ps_a pre x = ()

let ps_nat_in_range #bytes #bl r =
  let sz =
    if r.max < pow2 8 then 1
    else if r.max < pow2 16 then 2
    else if r.max < pow2 32 then 4
    else 8
  in
  assert_norm (r.max < pow2 64);
  mk_isomorphism (refined nat (in_range r)) (refine (ps_nat_lbytes sz) (in_range r)) (fun n -> n) (fun n -> n)

val _parse_nat: #bytes:Type0 -> {| bytes_like bytes |} -> b:bytes -> Tot (option (nat & bytes)) (decreases length b)
let rec _parse_nat #bytes #bl b =
  if length b = 0 then (
    None
  ) else (
    split_length b 1;
    match split #bytes b 1 with
    | None -> None
    | Some (l, r) -> (
      if length l <> 1 then (
        None
      ) else (
        match to_nat #bytes 1 l with
        | None -> None
        | Some l_value -> (
          if l_value = 0 then (
            Some (0, r)
          ) else if l_value = 1 then (
            match _parse_nat r with
            | None -> None
            | Some (result, suffix) -> Some (1+result, suffix)
          ) else (
            None
          )
        )
      )
    )
  )

val _serialize_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat -> list bytes
let rec _serialize_nat #bytes #bl n =
  assert_norm (1 < pow2 (8 `op_Multiply` 1));
  if n = 0 then [from_nat 1 0]
  else ((from_nat 1 1)::(_serialize_nat (n-1)))

#push-options "--fuel 1"
val ps_nat_unary: #bytes:Type0 -> {| bytes_like bytes |} -> parser_serializer bytes nat
let ps_nat_unary #bytes #bl =
  let rec parse_serialize_inv (n:nat) (suffix:bytes): Lemma (_parse_nat (add_prefixes (_serialize_nat n) suffix) == Some (n, suffix)) =
    if n = 0 then (
      assert_norm (add_prefixes #bytes [from_nat 1 0] suffix == concat (from_nat 1 0) suffix);
      concat_length #bytes (from_nat 1 0) suffix;
      split_concat #bytes (from_nat 1 0) suffix;
      split_length (concat #bytes (from_nat 1 0) suffix) 1;
      from_to_nat #bytes 1 0
    ) else (
      parse_serialize_inv (n-1) suffix;
      concat_length #bytes (from_nat 1 1) (add_prefixes (_serialize_nat (n-1)) suffix);
      split_concat #bytes (from_nat 1 1) (add_prefixes (_serialize_nat (n-1)) suffix);
      split_length (concat #bytes (from_nat 1 1) (add_prefixes (_serialize_nat (n-1)) suffix)) 1;
      from_to_nat #bytes 1 1
    )
  in
  let rec serialize_parse_inv (buf:bytes): Lemma (ensures (match _parse_nat buf with | Some (x, suffix) -> buf == add_prefixes (_serialize_nat x) suffix | None -> True)) (decreases length buf) =
    match _parse_nat buf with
    | None -> ()
    | Some (n, suffix) -> (
      let (l, r) = Some?.v (split #bytes buf 1) in
      let l_value = Some?.v (to_nat #bytes 1 l) in
      if l_value = 0 then (
        to_from_nat 1 l;
        concat_split buf 1;
        assert_norm (add_prefixes #bytes [from_nat 1 0] suffix == concat (from_nat 1 0) suffix)
      ) else if l_value = 1 then (
        to_from_nat 1 l;
        concat_split buf 1;
        split_length (concat #bytes l r) 1;
        serialize_parse_inv r
      ) else (
        ()
      )
    )
  in
  let rec parse_pre (pre:bytes_compatible_pre bytes) (buf:bytes{pre buf}): Lemma (ensures (match _parse_nat buf with | Some (x, suffix) -> pre suffix | None -> True)) (decreases length #bytes buf) =
    match _parse_nat #bytes buf with
    | None -> ()
    | Some (n, suffix) ->
      let (l, r) = Some?.v (split #bytes buf 1) in
      let l_value = Some?.v (to_nat #bytes 1 l) in
      if l_value = 1 then (
        concat_split #bytes buf 1;
        split_length (concat #bytes l r) 1;
        parse_pre pre r
      ) else (
        ()
      )
  in
  let rec serialize_pre (pre:bytes_compatible_pre bytes) (n:nat): Lemma (for_allP pre (_serialize_nat n)) =
    if n = 0 then (
      assert_norm (for_allP pre (_serialize_nat 0) <==> pre (from_nat 1 0))
    ) else (
      serialize_pre pre (n-1)
    )
  in

  {
    parse = _parse_nat;
    serialize = _serialize_nat;
    parse_serialize_inv = parse_serialize_inv;
    serialize_parse_inv = serialize_parse_inv;
    is_valid = (fun _ _ -> True);
    parse_pre = (fun pre buf -> parse_pre pre buf);
    serialize_pre = (fun pre x -> serialize_pre pre x);
  }
#pop-options

open FStar.Mul

val find_nbytes_aux: n:pos -> acc:nat -> Pure nat (requires pow2 (8 * acc) <= n)
  (ensures fun res -> pow2 (8 * res) <= n /\ n < pow2 (8 * (res+1)))
  (decreases n - pow2 (8 * acc))
let rec find_nbytes_aux n acc =
  if n < pow2 (8* (acc+1)) then
    acc
  else (
    Math.Lemmas.pow2_lt_compat (8 * (acc+1)) (8 * acc);
    find_nbytes_aux n (acc+1)
  )

val find_nbytes: n:nat -> Pure nat (requires True)
  (ensures fun res -> (n == 0 /\ res == 0) \/ (pow2 (8 * res) <= n /\ n < pow2 (8 * (res+1))))
let find_nbytes n =
  if n = 0 then 0
  else (
    assert_norm(pow2 (8*0) == 1);
    find_nbytes_aux n 0
  )

// Use a "slow" nat parser to derive a more compact one
val ps_nat_accelerate: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes nat -> parser_serializer bytes nat
let ps_nat_accelerate #bytes #bl ps_nat_slow =
  let nbytes_to_pred (nbytes:nat) (n:nat) = (nbytes = 0 && n = 0) || (pow2 (8 * nbytes)) <= n in
  introduce forall (nbytes:nat) (n:nat_lbytes (nbytes+1)). pow2 (8 * nbytes) <= n ==> nbytes == find_nbytes n with (
    if pow2 (8 * nbytes) <= n then (
      let found_nbytes = find_nbytes n in
      if nbytes < found_nbytes then (
        Math.Lemmas.pow2_le_compat (8 * found_nbytes) (8 * (nbytes+1));
        assert(False)
      ) else if found_nbytes < nbytes then (
        Math.Lemmas.pow2_le_compat (8 * nbytes) (8 * (found_nbytes+1));
        assert(False)
      ) else (
        ()
      )
    ) else (
      ()
    )
  );
  mk_isomorphism nat
    (
      bind #_ #_ #nat #(fun nbytes -> refined (nat_lbytes (nbytes+1)) (nbytes_to_pred nbytes)) ps_nat_slow (fun nbytes ->
        refine (ps_nat_lbytes (nbytes+1)) (nbytes_to_pred nbytes)
      )
    )
    (fun (|nbytes, n|) -> n)
    (fun n -> (|find_nbytes n, n|))

let ps_true_nat #bytes #bl =
  assert_norm(forall pre n. (ps_nat_unary #bytes).is_valid pre n); //???
  mk_isomorphism (refined nat true_nat_pred) (ps_nat_accelerate ps_nat_unary) (fun n -> n) (fun n -> n)
