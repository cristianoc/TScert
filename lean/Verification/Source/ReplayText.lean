import Lean.Data.Json
import Std.Data.String.ToInt
import Init.Data.List.SplitOn.Lemmas
import Init.Data.String.Lemmas.Intercalate

/-! Exact text for the raw JSON data in a group key. An object retains the
shape and stored sizes of its tree. Each token occupies one JSON array entry. -/
namespace Verification.ReplayText
open Lean

private abbrev ObjectTree := Std.DTreeMap.Internal.Impl String (fun _ => Json)

private inductive Token where
  | null | boolean (b : Bool) | number (n : JsonNumber) | text (s : String)
  | array | stop | object | branch | leaf

private inductive Cell where
  | value (j : Json) | tree (t : ObjectTree) | stop

private def arrayCells : List Cell → List Json → Option (List Cell)
  | .stop :: rest, xs => some (.value (.arr xs.reverse.toArray) :: rest)
  | .value j :: rest, xs => arrayCells rest (j :: xs)
  | _, _ => none

private def step (t : Token) (rest : Option (List Cell)) : Option (List Cell) := do
  let stk ← rest
  match t with
  | .null => return .value .null :: stk
  | .boolean b => return .value (.bool b) :: stk
  | .number n => return .value (.num n) :: stk
  | .text s => return .value (.str s) :: stk
  | .stop => return .stop :: stk
  | .leaf => return .tree .leaf :: stk
  | .array => arrayCells stk []
  | .object =>
    let .tree t :: r := stk | none
    return .value (.obj ⟨⟨t⟩⟩) :: r
  | .branch =>
    let .value (.num ⟨.ofNat n,0⟩) :: .value (.str k) :: .value j :: .tree l :: .tree r :: s := stk | none
    return .tree (.inner n k j l r) :: s

mutual
private def tokens : Json → List Token
  | .null => [.null]
  | .bool b => [.boolean b]
  | .num n => [.number n]
  | .str s => [.text s]
  | .arr ⟨xs⟩ => .array :: itemTokens xs
  | .obj ⟨⟨t⟩⟩ => .object :: treeTokens t
termination_by j => sizeOf j
private def itemTokens : List Json → List Token
  | [] => [.stop]
  | j :: js => tokens j ++ itemTokens js
termination_by xs => sizeOf xs
private def treeTokens : ObjectTree → List Token
  | .leaf => [.leaf]
  | .inner n k j l r =>
    .branch :: .number ⟨n,0⟩ :: .text k :: (tokens j ++ treeTokens l ++ treeTokens r)
termination_by t => sizeOf t
end

private theorem arrayCells_values (xs : List Json) (rest : List Cell) (acc : List Json) :
    arrayCells (xs.map Cell.value ++ .stop :: rest) acc =
      some (.value (.arr (acc.reverse ++ xs).toArray) :: rest) := by
  induction xs generalizing acc with
  | nil => simp [arrayCells]
  | cons j js ih => simp [arrayCells, ih, List.append_assoc]

mutual
private theorem fold_tokens : (j : Json) → (s : List Cell) →
    (tokens j).foldr step (some s) = some (.value j :: s)
  | .null, _ | .bool _, _ | .num _, _ | .str _, _ => by simp [tokens, step]
  | .arr ⟨xs⟩, s => by simp [tokens, fold_items xs s, step, arrayCells_values]
  | .obj ⟨⟨t⟩⟩, s => by simp [tokens, fold_tree t s, step]
termination_by j _ => sizeOf j
private theorem fold_items : (xs : List Json) → (s : List Cell) →
    (itemTokens xs).foldr step (some s) = some (xs.map Cell.value ++ .stop :: s)
  | [], _ => by simp [itemTokens, step]
  | j :: js, s => by simp [itemTokens, List.foldr_append, fold_items js s, fold_tokens j]
termination_by xs _ => sizeOf xs
private theorem fold_tree : (t : ObjectTree) → (s : List Cell) →
    (treeTokens t).foldr step (some s) = some (.tree t :: s)
  | .leaf, _ => by simp [treeTokens, step]
  | .inner n k j l r, s => by
    simp [treeTokens, List.foldr_append, fold_tree r s, fold_tree l, fold_tokens j, step]
    rfl
termination_by t _ => sizeOf t
end

private def safeChar (c : Char) : Bool :=
  c.toNat ≥ 32 && c != ',' && c != '"' && c != '\\'

private def unicodeText (s : String) : String :=
  ".".intercalate ("0" :: s.toList.map (fun c => c.toNat.repr))

private def strToken (s : String) : String :=
  if s.all safeChar then "\"s" ++ s ++ "\"" else "\"u" ++ unicodeText s ++ "\""

private def numberToken (n : JsonNumber) : String :=
  if n.exponent = 0 then n.mantissa.repr else n.mantissa.repr ++ "e-" ++ n.exponent.repr

private def spelling : Token → String
  | .null => "null" | .boolean b => if b then "true" else "false"
  | .number n => numberToken n | .text s => strToken s
  | .array => "\"a\"" | .stop => "\"z\"" | .object => "\"o\""
  | .branch => "\"b\"" | .leaf => "\"l\""

private def readUnicode (cs : List Char) : Option String :=
  do
    let _ :: digits := cs.splitOn '.' | none
    return String.ofList (← digits.mapM fun ds => Char.ofNat <$> (String.ofList ds).toNat?)

private def readNumber (cs : List Char) : Option JsonNumber := do
  match cs.splitOn 'e' with
  | [m] => return ⟨← (String.ofList m).toInt?,0⟩
  | [m,'-' :: e] => return ⟨← (String.ofList m).toInt?,← (String.ofList e).toNat?⟩
  | _ => none

private def readToken (s : String) : Option Token :=
  if s.toList.head?.any (fun c => c.isDigit || c == '-') then
    return .number (← readNumber s.toList)
  else match s.toList with
  | '"' :: 's' :: xs => some (.text (String.ofList xs.dropLast))
  | '"' :: 'u' :: xs => Token.text <$> readUnicode xs.dropLast
  | ['"','a','"'] => some .array | ['"','z','"'] => some .stop
  | ['"','o','"'] => some .object | ['"','b','"'] => some .branch
  | ['"','l','"'] => some .leaf
  | ['n','u','l','l'] => some .null
  | ['t','r','u','e'] => some (.boolean true)
  | ['f','a','l','s','e'] => some (.boolean false)
  | _ => none

private theorem natDigit {n : Nat} {c : Char} (h : c ∈ n.repr.toList) : c.isDigit :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) (Nat.toList_repr ▸ h)

private theorem intDigit {i : Int} {c : Char} (h : c ∈ i.repr.toList) : c = '-' ∨ c.isDigit := by
  rw [Int.repr_eq_ite] at h
  split at h
  · exact Or.inr (natDigit h)
  · change c ∈ ("-".toList ++ (-i).toNat.repr.toList) at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (List.mem_singleton.mp h)
    · exact Or.inr (natDigit h)

private theorem noNat {n : Nat} {c : Char} (h : c.isDigit = false) : c ∉ n.repr.toList := by
  intro hm; have hd := natDigit hm; simp [h] at hd

private theorem noInt {i : Int} {c : Char} (h : c.isDigit = false) (hm : c ≠ '-') :
    c ∉ i.repr.toList := by
  intro hmem; rcases intDigit hmem with he | hd
  · exact hm he
  · simp [h] at hd

private theorem readNumber_number (n : JsonNumber) :
    readNumber (numberToken n).toList = some n := by
  obtain ⟨m,e⟩ := n
  have sep : 'e' ∉ m.repr.toList := noInt (by decide) (by decide)
  by_cases he : e = 0
  · subst e
    simp [numberToken, readNumber, List.splitOn_eq_singleton sep]
  · have esep : 'e' ∉ '-' :: e.repr.toList :=
      fun h => (List.mem_cons.mp h).elim (by decide) (noNat (by decide))
    simp only [numberToken, he, ↓reduceIte, String.toList_append, List.append_assoc]
    change readNumber (m.repr.toList ++ 'e' :: '-' :: e.repr.toList) = _
    rw [readNumber, List.splitOn_append_cons_self_of_not_mem sep,
      List.splitOn_eq_singleton esep]
    simp [-Nat.toList_repr]

private theorem mapM_some (xs : List α) : xs.mapM (fun x => some x) = some xs := by
  induction xs <;> simp_all

private theorem readUnicode_unicode (s : String) : readUnicode (unicodeText s).toList = some s := by
  let ds := s.toList.map fun c => c.toNat.repr.toList
  have hds : ∀ cs ∈ ['0'] :: ds, '.' ∉ cs := by
    intro cs hm
    rcases List.mem_cons.mp hm with rfl | h
    · decide
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      exact noNat (by decide)
  simp only [readUnicode, unicodeText, String.toList_intercalate, List.map_cons, List.map_map,
    Function.comp_def]
  change (do
    let _ :: digits := (['.'].intercalate (['0'] :: ds)).splitOn '.' | none
    return String.ofList (← digits.mapM fun xs => Char.ofNat <$> (String.ofList xs).toNat?)) = _
  rw [List.splitOn_intercalate '.' hds (by simp)]
  simp [ds, List.mapM_map, Function.comp_def, -Nat.toList_repr, mapM_some]

private theorem numHead (n : JsonNumber) :
    (numberToken n).toList.head?.any (fun c => c.isDigit || c == '-') = true := by
  have hn : n.mantissa.repr.toList ≠ [] := by
    rw [Int.repr_eq_ite]
    split
    · simp [Nat.toDigits_ne_nil]
    · simp [String.toList_append]
  obtain ⟨c,cs,h⟩ := List.exists_cons_of_ne_nil hn
  have hc := intDigit (i := n.mantissa) (c := c) (by simp [h])
  have hh : (c.isDigit || c == '-') = true := by rcases hc with rfl | hd <;> simp_all
  unfold numberToken
  split <;> simp [String.toList_append, h, hh]

private theorem read_spelling : (t : Token) → readToken (spelling t) = some t
  | .null | .boolean true | .boolean false | .array | .stop | .object | .branch | .leaf => rfl
  | .number n => by simp [readToken, spelling, numHead, readNumber_number]
  | .text s => by
    simp only [spelling, strToken]
    split
    · simp [readToken, String.toList_append]
    · simp [readToken, String.toList_append, readUnicode_unicode]

private theorem unicode_chars {sep : Char} (h : sep.isDigit = false) (hdot : sep ≠ '.') (s : String) :
    sep ∉ (unicodeText s).toList := by
  simp only [unicodeText, String.toList_intercalate, List.map_cons, List.map_map, Function.comp_def]
  generalize s.toList = cs
  have safe : ∀ (xs : List (List Char)), (∀ x ∈ xs, sep ∉ x) → sep ∉ ['.'].intercalate xs := by
    intro xs hx
    induction xs with
    | nil => simp
    | cons x xs ih =>
      cases xs with
      | nil => simpa using hx x (by simp)
      | cons y ys =>
        rw [List.intercalate_cons_cons]
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨⟨hx x (by simp), hdot⟩, ih (fun v hv => hx v (List.mem_cons_of_mem _ hv))⟩
  apply safe
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · intro hm; have he : sep = '0' := List.mem_singleton.mp hm
    subst sep; contradiction
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx; exact noNat h

private theorem spelling_avoids (t : Token) (sep : Char) (hs : sep = ',' ∨ sep = '\n') :
    sep ∉ (spelling t).toList := by
  cases t with
  | number n =>
    have hm : sep ∉ n.mantissa.repr.toList := noInt (by rcases hs with rfl | rfl <;> decide)
      (by rcases hs with rfl | rfl <;> decide)
    have he : sep ∉ n.exponent.repr.toList := noNat (by rcases hs with rfl | rfl <;> decide)
    have hx : sep ∉ "e-".toList := by rcases hs with rfl | rfl <;> decide
    simp only [spelling, numberToken]
    split
    · exact hm
    · simp only [String.toList_append, List.mem_append, not_or]; exact ⟨⟨hm,hx⟩,he⟩
  | text s =>
    have hu := unicode_chars (sep := sep) (by rcases hs with rfl | rfl <;> decide)
      (by rcases hs with rfl | rfl <;> decide) s
    simp only [spelling, strToken]
    split <;> rename_i h
    · have hm : sep ∉ s.toList := by
        intro hmem
        have hok := List.all_eq_true.mp (String.all_bool_eq ▸ h) sep hmem
        rcases hs with rfl | rfl <;> contradiction
      have ha : sep ∉ "\"s".toList := by rcases hs with rfl | rfl <;> decide
      have hb : sep ∉ "\"".toList := by rcases hs with rfl | rfl <;> decide
      simp only [String.toList_append, List.mem_append, not_or]; exact ⟨⟨ha,hm⟩,hb⟩
    · have ha : sep ∉ "\"u".toList := by rcases hs with rfl | rfl <;> decide
      have hb : sep ∉ "\"".toList := by rcases hs with rfl | rfl <;> decide
      simp only [String.toList_append, List.mem_append, not_or]; exact ⟨⟨ha,hu⟩,hb⟩
  | boolean b => cases b <;> rcases hs with rfl | rfl <;> decide
  | _ => rcases hs with rfl | rfl <;> decide

private def emit (acc : String) (t : Token) : String := acc ++ spelling t ++ ","

mutual
private def write (acc : String) : Json → String
  | .null => emit acc .null
  | .bool b => emit acc (.boolean b)
  | .num n => emit acc (.number n)
  | .str s => emit acc (.text s)
  | .arr ⟨xs⟩ => writeItems (emit acc .array) xs
  | .obj ⟨⟨t⟩⟩ => writeTree (emit acc .object) t
termination_by j => sizeOf j
private def writeItems (acc : String) : List Json → String
  | [] => emit acc .stop
  | j :: js => writeItems (write acc j) js
termination_by js => sizeOf js
private def writeTree (acc : String) : ObjectTree → String
  | .leaf => emit acc .leaf
  | .inner n k j l r =>
    let acc := emit (emit (emit acc .branch) (.number ⟨n,0⟩)) (.text k)
    writeTree (writeTree (write acc j) l) r
termination_by t => sizeOf t
end

mutual
private theorem write_tokens : (j : Json) → (a : String) → write a j = (tokens j).foldl emit a
  | .null, _ | .bool _, _ | .num _, _ | .str _, _ => by simp [write, tokens]
  | .arr ⟨xs⟩, _ => by simp [write, tokens, write_items xs]
  | .obj ⟨⟨t⟩⟩, _ => by simp [write, tokens, write_tree t]
termination_by j _ => sizeOf j
private theorem write_items : (xs : List Json) → (a : String) →
    writeItems a xs = (itemTokens xs).foldl emit a
  | [], _ => by simp [writeItems, itemTokens]
  | j :: js, _ => by simp [writeItems, itemTokens, List.foldl_append, write_items js, write_tokens j]
termination_by xs _ => sizeOf xs
private theorem write_tree : (t : ObjectTree) → (a : String) →
    writeTree a t = (treeTokens t).foldl emit a
  | .leaf, _ => by simp [writeTree, treeTokens]
  | .inner n k j l r, _ => by
    simp [writeTree, treeTokens, List.foldl_append, write_tree r, write_tree l, write_tokens j]
termination_by t _ => sizeOf t
end

def encode (j : Json) : String := write "[" j ++ "null]"

private def chars : List Token → List Char
  | [] => "null]".toList
  | t :: ts => (spelling t).toList ++ ',' :: chars ts

private theorem fold_chars (ts : List Token) (a : String) :
    (ts.foldl emit a ++ "null]").toList = a.toList ++ chars ts := by
  induction ts generalizing a with
  | nil => simp [chars]
  | cons t ts ih => simp only [List.foldl_cons, ih, emit, String.toList_append, chars, List.append_assoc]; rfl

private theorem split_chars (ts : List Token) :
    (chars ts).splitOn ',' = ts.map (fun t => (spelling t).toList) ++ ["null]".toList] := by
  induction ts with
  | nil => decide
  | cons t ts ih =>
    rw [chars, List.splitOn_append_cons_self_of_not_mem (spelling_avoids t ',' (Or.inl rfl)), ih]; rfl

private theorem chars_no_lf (ts : List Token) : '\n' ∉ chars ts := by
  induction ts with
  | nil => decide
  | cons t ts ih =>
    simpa only [chars, List.mem_append, not_or, List.mem_cons, not_or] using
      And.intro (spelling_avoids t '\n' (Or.inr rfl)) (And.intro (by decide : '\n' ≠ ',') ih)

theorem encode_no_lf (j : Json) : '\n' ∉ (encode j).toList := by
  rw [encode, write_tokens, fold_chars]
  exact fun h => (List.mem_cons.mp h).elim (by decide) (chars_no_lf _)

def decode (s : String) : Except String Json := do
  let .some ts := ((s.toList.drop 1).splitOn ',').dropLast.mapM
      (fun cs => readToken (String.ofList cs)) | throw "invalid key token"
  let some [.value j] := ts.foldr step (some []) | throw "invalid key value"
  return j

@[simp] theorem decode_encode (j : Json) : decode (encode j) = .ok j := by
  simp only [decode, encode, write_tokens, fold_chars]
  change (do
    let some ts := ((chars (tokens j)).splitOn ',').dropLast.mapM
        (fun cs => readToken (String.ofList cs)) | throw "invalid key token"
    let some [.value v] := ts.foldr step (some []) | throw "invalid key value"
    return v) = Except.ok j
  rw [split_chars]
  simp [List.mapM_map, Function.comp_def, read_spelling, mapM_some, fold_tokens]
  rfl

end Verification.ReplayText
