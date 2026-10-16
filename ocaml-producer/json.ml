(* Small dependency-free JSON codec. All input is data; duplicate keys fail. *)
type t = Null | Bool of bool | Number of string | String of string
       | Array of t list | Object of (string * t) list
exception Error of string
let fail s = raise (Error s)
let obj = function Object xs -> xs | _ -> fail "expected object"
let field k j = match List.assoc_opt k (obj j) with
  | Some x -> x | None -> fail ("missing field: " ^ k)
let str = function String s -> s | _ -> fail "expected string"
let list = function Array xs -> xs | _ -> fail "expected array"
let boolean = function Bool b -> b | _ -> fail "expected boolean"
let int n = Number (string_of_int n)
let parse s =
  let i = ref 0 and n = String.length s in
  let error m = fail (Printf.sprintf "JSON byte %d: %s" !i m) in
  let peek () = if !i < n then s.[!i] else '\000' in
  let take () = let c = peek () in if !i >= n then error "unexpected end"; incr i; c in
  let rec ws () = match peek () with ' ' | '\n' | '\r' | '\t' -> incr i; ws () | _ -> () in
  let hex () = let v = ref 0 in for _ = 1 to 4 do
    let c = take () in let d = match c with
    | '0'..'9' -> Char.code c - 48 | 'a'..'f' -> Char.code c - 87
    | 'A'..'F' -> Char.code c - 55 | _ -> error "invalid unicode escape" in
    v := !v * 16 + d done; !v in
  let string () =
    if take () <> '"' then error "expected string";
    let b = Buffer.create 32 in
    let rec loop () = match take () with
    | '"' -> Buffer.contents b
    | '\\' -> (match take () with
      | ('"' | '\\' | '/') as c -> Buffer.add_char b c
      | 'b' -> Buffer.add_char b '\b' | 'f' -> Buffer.add_char b '\012'
      | 'n' -> Buffer.add_char b '\n' | 'r' -> Buffer.add_char b '\r'
      | 't' -> Buffer.add_char b '\t'
      | 'u' -> let u = hex () in
        let u = if u >= 0xd800 && u <= 0xdbff then begin
          if take () <> '\\' || take () <> 'u' then error "missing low surrogate";
          let v = hex () in if v < 0xdc00 || v > 0xdfff then error "invalid low surrogate";
          0x10000 + (u - 0xd800) * 1024 + v - 0xdc00
        end else u in
        if not (Uchar.is_valid u) then error "invalid unicode scalar";
        Buffer.add_utf_8_uchar b (Uchar.of_int u)
      | _ -> error "invalid escape"); loop ()
    | c when Char.code c < 32 -> error "control character in string"
    | c -> Buffer.add_char b c; loop () in loop () in
  let literal text value = String.iter (fun c -> if take () <> c then error "invalid literal") text; value in
  let rec value () = ws (); match peek () with
    | 'n' -> literal "null" Null | 't' -> literal "true" (Bool true)
    | 'f' -> literal "false" (Bool false) | '"' -> String (string ())
    | '[' -> incr i; Array (sequence ']' value)
    | '{' -> incr i;
      let pairs = sequence '}' (fun () -> ws (); let k = string () in ws ();
        if take () <> ':' then error "expected colon"; (k, value ())) in
      if List.length (List.sort_uniq String.compare (List.map fst pairs)) <> List.length pairs
      then error "duplicate object key"; Object pairs
    | '-' | '0'..'9' ->
      let start = !i in
      if peek () = '-' then incr i;
      let digits () = let before = !i in
        while peek () >= '0' && peek () <= '9' do incr i done;
        if !i = before then error "expected digit" in
      if peek () = '0' then incr i else digits ();
      if peek () = '.' then (incr i; digits ());
      if peek () = 'e' || peek () = 'E' then begin incr i;
        if peek () = '+' || peek () = '-' then incr i; digits () end;
      Number (String.sub s start (!i-start))
    | _ -> error "expected value"
  and sequence : 'a. char -> (unit -> 'a) -> 'a list = fun close read ->
    ws (); if peek () = close then (incr i; []) else
    let rec items acc = let x = read () in ws (); match take () with
      | c when c = close -> List.rev (x::acc)
      | ',' -> items (x::acc) | _ -> error "expected separator" in items [] in
  let result = value () in ws (); if !i <> n then error "trailing input"; result
let rec encode = function
  | Null -> "null" | Bool b -> string_of_bool b | Number n -> n
  | String s -> let b = Buffer.create 32 in Buffer.add_char b '"';
    String.iter (function
      | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
      | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) s; Buffer.add_char b '"'; Buffer.contents b
  | Array xs -> "[" ^ String.concat "," (List.map encode xs) ^ "]"
  | Object xs -> "{" ^ String.concat "," (List.map (fun (k,v) -> encode (String k)^":"^encode v) xs) ^ "}"
let read path = let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch) (fun () -> parse (really_input_string ch (in_channel_length ch)))
