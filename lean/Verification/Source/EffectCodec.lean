import Lean.Data.Json
import Std.Data.TreeMap.Raw.Lemmas
import Verification.Semantics.CallEffects

/-! # The serialized effect

The one JSON form of a callable's effect (`CallEffects.Effect`): its two
exits, each a frame and a list of two-state postconditions, its promise, its
precondition on the receiver's elements and its index-fact preconditions
([the request protocol](../../../docs/REQUEST-PROTOCOL.md) owns the
grammar; [effects of commands](../../../docs/drafts/effects-of-commands.md),
"The serialized effect", its design).

Each record is an object of its fields, each constructor of a union an
object of one field, its name, holding its fields, and a constructor with
no field its name. An integer is a JSON number in the safe range and its
decimal string outside it. The decoder (`decode`) reads a value and writes
it again: a document that is not exactly the writing of what it read (an
unknown, missing or repeated field, a second tag, a noncanonical number or
literal) is refused at the first place it differs. Serialization is defined
on the effects of the serialization predicate (`Serializable`): formulas
referencing no assertion-arena node, primitive literals, and nesting at most
`nestingLimit`. -/
namespace Verification.EffectCodec
open Lean Verification Footprints CallEffects Parity HeapKnowledge

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
@[simp] theorem map_ok {ε α β : Type} (a : α) (f : α → β) : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
@[simp] theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-! ## Objects -/

/-- An object of the keys `ks`, holding the values `vs` in turn. -/
def obj (ks : List String) (vs : List Json) : Json := Json.mkObj (ks.zip vs)

/-- A constructor of a union with fields: an object of one field, its name. -/
def tagged (k : String) (v : Json) : Json := Json.mkObj [(k, v)]

/-- An error located below a field or a constructor `k`. -/
def under {α : Type} (k : String) (r : Except String α) : Except String α := r.mapError fun m => s!"{k}/{m}"

@[simp] theorem under_ok {α : Type} (k : String) (a : α) : under k (.ok a : Except String α) = .ok a := rfl

/-- A field of an object. -/
def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"{k}: a required field is missing"

/-- The fields `ks` of an object, in turn. -/
def fields (j : Json) (ks : List String) : Except String (List Json) := ks.mapM (field j)

/-- The field and the value of an object of one field, or a constructor
with no field as its name. -/
def tagOf (j : Json) : Except String (String × Json) :=
  match j with
  | .obj kvs => match kvs.toList with
    | [(k, v)] => .ok (k, v)
    | _ => .error "a constructor is an object of one field, its name"
  | .str s => .ok (s, Json.null)
  | _ => .error "a constructor is its name or an object of one field"

@[simp] theorem tagOf_tagged (k : String) (v : Json) : tagOf (tagged k v) = .ok (k, v) := rfl
@[simp] theorem tagOf_str (s : String) : tagOf (Json.str s) = .ok (s, Json.null) := rfl

private theorem lookup_of_mem {l : List (String × Json)} {k : String} {v : Json}
    (hd : (l.map Prod.fst).Nodup) (hm : (k, v) ∈ l) : l.lookup k = some v := by
  induction l with
  | nil => cases hm
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rcases List.mem_cons.mp hm with h | h
    · cases h; simp [List.lookup]
    · have hka : k ≠ a := by
        intro hk; subst hk
        exact (List.nodup_cons.mp hd).1 (List.mem_map.mpr ⟨(k, v), h, rfl⟩)
      have hb : (k == a) = false := by simpa using hka
      simp only [List.lookup, hb]
      exact ih (List.nodup_cons.mp hd).2 h

/-- A field of an object built of distinct keys is the value it was built
with (proved, by the tree map's lemmas). -/
theorem field_mkObj {l : List (String × Json)} {k : String} {v : Json}
    (hd : (l.map Prod.fst).Nodup) (hmem : (k, v) ∈ l) : field (Json.mkObj l) k = .ok v := by
  have hdist : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    (List.pairwise_map.mp hd).imp fun h h' => h (Std.LawfulEqCmp.eq_of_compare h')
  have hg := Std.TreeMap.Raw.getElem?_ofList_of_mem (k := k) (k' := k) Std.ReflCmp.compare_self hdist hmem
  simp only [field, Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?, hg]
  rfl

/-- **The fields of an object are the values it was built with** (proved). -/
@[simp] theorem fields_obj (ks : List String) (vs : List Json) (hk : ks.Nodup)
    (hl : ks.length = vs.length) : fields (obj ks vs) ks = .ok vs := by
  have hd : ((ks.zip vs).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (Nat.le_of_eq hl)]; exact hk
  have key : ∀ (pre : List (String × Json)) (ks' : List String) (vs' : List Json),
      pre ++ ks'.zip vs' = ks.zip vs → ks'.length = vs'.length → ks'.mapM (field (obj ks vs)) = .ok vs' := by
    intro pre ks'
    induction ks' generalizing pre with
    | nil => intro vs' _ hl'; cases vs' with
      | nil => rfl
      | cons _ _ => simp at hl'
    | cons k ks'' ih =>
      intro vs' heq hl'
      cases vs' with
      | nil => simp at hl'
      | cons v vs'' =>
        have hm : (k, v) ∈ ks.zip vs := by rw [← heq]; simp
        have hf : field (obj ks vs) k = .ok v := field_mkObj hd hm
        have hr := ih (pre ++ [(k, v)]) vs'' (by rw [← heq]; simp) (by simpa using hl')
        simp only [List.mapM_cons, hf, hr, ok_bind]
        rfl
  exact key [] ks vs (by simp) hl

/-! ## Scalars -/

/-- The largest magnitude a JSON number states exactly in every reader:
`2^53 − 1`. -/
def safeBound : Nat := 9007199254740992

/-- A decimal digit's character. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- A character's decimal digit. -/
def digitOf (c : Char) : Option Nat := if 48 ≤ c.toNat ∧ c.toNat < 58 then some (c.toNat - 48) else none

theorem digitOf_digitChar {d : Nat} (h : d < 10) : digitOf (digitChar d) = some d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

/-- **A natural number's decimal digits**, most significant first, with no
leading zero. -/
def decDigits (n : Nat) : List Nat :=
  if n < 10 then [n] else decDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by omega

/-- The number decimal digits state, most significant first. -/
def ofDecDigits (ds : List Nat) : Nat := ds.foldl (fun a d => a * 10 + d) 0

theorem decDigits_lt (n : Nat) : ∀ d ∈ decDigits n, d < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decDigits]
    split
    · simpa
    · intro d hd
      rcases List.mem_append.mp hd with h | h
      · exact ih (n / 10) (by omega) d h
      · simp at h; omega

theorem ofDecDigits_decDigits (n : Nat) : ofDecDigits (decDigits n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decDigits]
    split
    · simp [ofDecDigits]
    · simp only [ofDecDigits, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih (n / 10) (by omega)]
      omega

/-- The natural number decimal characters state. -/
def natOfChars (cs : List Char) : Except String Nat :=
  match cs.mapM digitOf with
  | some (d :: ds) => .ok (ofDecDigits (d :: ds))
  | _ => .error s!"'{String.ofList cs}' is no decimal integer"

theorem mapM_digitOf (ds : List Nat) (h : ∀ d ∈ ds, d < 10) : (ds.map digitChar).mapM digitOf = some ds := by
  induction ds with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, List.mapM_cons, digitOf_digitChar (h d (by simp)),
      ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem decDigits_ne_nil (n : Nat) : decDigits n ≠ [] := by
  rw [decDigits]; split <;> simp

theorem natOfChars_dec (n : Nat) : natOfChars ((decDigits n).map digitChar) = .ok n := by
  unfold natOfChars
  rw [mapM_digitOf _ (decDigits_lt n)]
  cases h : decDigits n with
  | nil => exact absurd h (decDigits_ne_nil n)
  | cons d ds => simp only; rw [← h, ofDecDigits_decDigits]

theorem digitChar_ne_minus {d : Nat} (h : d < 10) : digitChar d ≠ '-' := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

/-- An integer's decimal characters: its magnitude's, after `-` where it is
negative. -/
def intChars (i : Int) : List Char :=
  (if i < 0 then ['-'] else []) ++ (decDigits i.natAbs).map digitChar

/-- An integer's decimal text. -/
def intDec (i : Int) : String := String.ofList (intChars i)

/-- The integer a decimal text states. -/
def intOfDec (s : String) : Except String Int :=
  match s.toList with
  | '-' :: cs => (fun n => -(n : Int)) <$> natOfChars cs
  | cs => (fun n => (n : Int)) <$> natOfChars cs

theorem intOfDec_intDec (i : Int) : intOfDec (intDec i) = .ok i := by
  unfold intOfDec intDec intChars
  rw [String.toList_ofList]
  by_cases hi : i < 0
  · simp only [hi, if_true, List.singleton_append]
    rw [natOfChars_dec]
    show Except.ok (-((i.natAbs : Nat) : Int)) = Except.ok i
    congr 1; omega
  · simp only [hi, if_false, List.nil_append]
    cases hd : decDigits i.natAbs with
    | nil => exact absurd hd (decDigits_ne_nil _)
    | cons d ds =>
      have hd10 : d < 10 := decDigits_lt i.natAbs d (by simp [hd])
      have hne := digitChar_ne_minus hd10
      simp only [List.map_cons]
      split
      · rename_i h; simp only [List.cons.injEq] at h; exact absurd h.1 hne
      · rw [← List.map_cons, ← hd, natOfChars_dec]
        show Except.ok ((i.natAbs : Nat) : Int) = Except.ok i
        congr 1; omega

/-- **An integer as a JSON value**: a number in the safe range, its decimal
string outside it. -/
def intJ (i : Int) : Json := if i.natAbs < safeBound then Json.num ⟨i, 0⟩ else Json.str (intDec i)

/-- The integer a JSON value states. -/
def intOf : Json → Except String Int
  | .num ⟨i, 0⟩ => .ok i
  | .str s => intOfDec s
  | _ => .error "an integer is a number or its decimal string"

@[simp] theorem intOf_intJ (i : Int) : intOf (intJ i) = .ok i := by
  unfold intJ; split
  · rfl
  · exact intOfDec_intDec i

/-- **A natural number as a JSON value** (`intJ`). -/
def natJ (n : Nat) : Json := intJ n

/-- The natural number a JSON value states. -/
def natOf (j : Json) : Except String Nat := do
  match ← intOf j with
  | .ofNat n => pure n
  | .negSucc _ => throw "a natural number is at least 0"

@[simp] theorem natOf_natJ (n : Nat) : natOf (natJ n) = .ok n := by
  simp only [natOf, natJ, intOf_intJ, ok_bind] <;> try rfl

def strOf : Json → Except String String
  | .str s => .ok s
  | _ => .error "a string"

@[simp] theorem strOf_str (s : String) : strOf (Json.str s) = .ok s := rfl

def boolOf : Json → Except String Bool
  | .bool b => .ok b
  | _ => .error "a Boolean"

@[simp] theorem strOf_obj (ks : List String) (vs : List Json) : strOf (obj ks vs) = .error "a string" := rfl

@[simp] theorem boolOf_bool (b : Bool) : boolOf (Json.bool b) = .ok b := rfl

/-- A list as a JSON array. -/
def listJ {α : Type} (f : α → Json) (l : List α) : Json := Json.arr (l.map f).toArray

/-- A JSON array's elements, each read by `f`, located by its index. -/
def listOf {α : Type} (f : Json → Except String α) : Json → Except String (List α)
  | .arr a => (a.toList.zipIdx).mapM fun (x, i) => under s!"[{i}]" (f x)
  | _ => .error "a list"

theorem listOf_listJ {α : Type} (f : Json → Except String α) (g : α → Json) (l : List α)
    (h : ∀ x ∈ l, f (g x) = .ok x) : listOf f (listJ g l) = .ok l := by
  simp only [listOf, listJ]
  suffices ∀ (k : Nat) (l : List α), (∀ x ∈ l, f (g x) = .ok x) →
      ((l.map g).zipIdx k).mapM (fun (x, i) => under s!"[{i}]" (f x)) = .ok l from this 0 l h
  intro k l h
  induction l generalizing k with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.mapM_cons, h x (by simp), under_ok,
      ih (k + 1) (fun y hy => h y (by simp [hy])), ok_bind]
    rfl

/-- A pair as a JSON array of two. -/
def pairJ {α β : Type} (f : α → Json) (g : β → Json) (p : α × β) : Json := Json.arr #[f p.1, g p.2]

def pairOf {α β : Type} (f : Json → Except String α) (g : Json → Except String β) : Json → Except String (α × β)
  | .arr a => match a.toList with
    | [x, y] => do pure (← under "[0]" (f x), ← under "[1]" (g y))
    | _ => .error "a pair is a list of two"
  | _ => .error "a pair is a list of two"

theorem pairOf_pairJ {α β : Type} (f : Json → Except String α) (g : Json → Except String β) (f' : α → Json)
    (g' : β → Json) (p : α × β) (hf : f (f' p.1) = .ok p.1) (hg : g (g' p.2) = .ok p.2) :
    pairOf f g (pairJ f' g' p) = .ok p := by
  simp only [pairOf, pairJ]
  show (do pure (← under "[0]" (f (f' p.1)), ← under "[1]" (g (g' p.2)))) = _
  rw [hf, hg]; rfl

/-- An optional value: `null` where there is none. -/
def optJ {α : Type} (f : α → Json) : Option α → Json
  | none => Json.null
  | some a => f a

def optOf {α : Type} (f : Json → Except String α) : Json → Except String (Option α)
  | .null => .ok none
  | j => some <$> f j

theorem optOf_optJ {α : Type} (f : Json → Except String α) (g : α → Json) (o : Option α)
    (hn : ∀ a, g a ≠ Json.null) (h : ∀ a, o = some a → f (g a) = .ok a) : optOf f (optJ g o) = .ok o := by
  cases o with
  | none => rfl
  | some a =>
    simp only [optJ]
    unfold optOf
    split
    · exact absurd ‹_› (hn a)
    · rw [h a rfl]; rfl

/-- A name of a finite set of constants. -/
def nameOf {α : Type} (names : List (α × String)) (what : String) (s : String) : Except String α :=
  match names.find? (·.2 == s) with
  | some (a, _) => .ok a
  | none => .error s!"'{s}' is no {what}"

/-! ## Hexadecimal bits -/

/-- A hexadecimal digit's character, lowercase. -/
def hexChar (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- A character's hexadecimal digit, lowercase. -/
def hexOf (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat < 58 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat < 103 then some (c.toNat - 87) else none

theorem hexOf_hexChar {d : Nat} (h : d < 16) : hexOf (hexChar d) = some d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | n + 16, h => omega

/-- `w` digits base 16 of `n`, least significant first. -/
def hexDigits : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, n => n % 16 :: hexDigits w (n / 16)

def ofHexDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 16 * ofHexDigits ds

theorem ofHexDigits_hexDigits (w n : Nat) : ofHexDigits (hexDigits w n) = n % 16 ^ w := by
  induction w generalizing n with
  | zero => simp [hexDigits, ofHexDigits, Nat.mod_one]
  | succ w ih =>
    simp only [hexDigits, ofHexDigits, ih, Nat.pow_succ, Nat.mul_comm (16 ^ w) 16, Nat.mod_mul]

theorem hexDigits_lt (w n : Nat) : ∀ d ∈ hexDigits w n, d < 16 := by
  induction w generalizing n with
  | zero => simp [hexDigits]
  | succ w ih =>
    intro d hd
    simp only [hexDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ d hd

theorem hexDigits_length (w n : Nat) : (hexDigits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [hexDigits, ih]

/-- **A double's bits**: sixteen lowercase hexadecimal digits, most
significant first. -/
def bitsText (b : UInt64) : String := String.ofList ((hexDigits 16 b.toNat).reverse.map hexChar)

/-- The bits sixteen hexadecimal digits state. -/
def bitsOf (s : String) : Except String UInt64 :=
  match s.toList.mapM hexOf with
  | some ds => if ds.length = 16 then .ok (UInt64.ofNat (ofHexDigits ds.reverse))
    else .error s!"'{s}' is no sixteen hexadecimal digits"
  | none => .error s!"'{s}' is no sixteen hexadecimal digits"

theorem mapM_hexOf (ds : List Nat) (h : ∀ d ∈ ds, d < 16) : (ds.map hexChar).mapM hexOf = some ds := by
  induction ds with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, List.mapM_cons, hexOf_hexChar (h d (by simp)),
      ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem bitsOf_bitsText (b : UInt64) : bitsOf (bitsText b) = .ok b := by
  unfold bitsOf bitsText
  rw [String.toList_ofList, mapM_hexOf _ (fun d hd => hexDigits_lt 16 _ d (List.mem_reverse.mp hd))]
  simp only [List.length_reverse, hexDigits_length, List.reverse_reverse, ofHexDigits_hexDigits, if_true]
  have : b.toNat % 16 ^ 16 = b.toNat := Nat.mod_eq_of_lt (by have := b.toNat_lt; simpa using this)
  rw [this, UInt64.ofNat_toNat]

/-! ## Literals

A literal of a specification is one of the calculus's eight primitive
constants: `null`, `undefined`, the two Booleans, a number by its double's
bits, a string, a bigint and a symbol by its identity. No object identity,
store or executable term is a literal (`Tm.isLiteral`, by every constructor
of `Tm`). -/

/-- **Whether a term is a literal of a specification**. -/
def _root_.Verification.Tm.isLiteral : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | _ => false

def litJ : Tm → Json
  | .nul => "null"
  | .undef => "undefined"
  | .tru => "true"
  | .fls => "false"
  | .num b => tagged "num" (obj ["bits"] [Json.str (bitsText b)])
  | .str s => tagged "str" (obj ["value"] [Json.str s])
  | .bigint i => tagged "bigint" (obj ["value"] [Json.str (intDec i)])
  | .sym id => tagged "sym" (obj ["id"] [natJ id])
  | _ => Json.null

def litOf (j : Json) : Except String Tm := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "null" => pure .nul
  | "undefined" => pure .undef
  | "true" => pure .tru
  | "false" => pure .fls
  | "num" => do
    let [b] ← fields v ["bits"] | throw "num"
    pure (.num (← under "bits" (bitsOf (← strOf b))))
  | "str" => do
    let [s] ← fields v ["value"] | throw "str"
    pure (.str (← under "value" (strOf s)))
  | "bigint" => do
    let [s] ← fields v ["value"] | throw "bigint"
    pure (.bigint (← under "value" (intOfDec (← strOf s))))
  | "sym" => do
    let [i] ← fields v ["id"] | throw "sym"
    pure (.sym (← under "id" (natOf i)))
  | _ => throw "a literal is a primitive constant"

theorem litOf_litJ {v : Tm} (h : v.isLiteral = true) : litOf (litJ v) = .ok v := by
  cases v <;> simp_all [Tm.isLiteral, litJ, litOf, fields_obj, bitsOf_bitsText, intOfDec_intDec] <;> try rfl


/-! ## Constants -/

def changeJ : Change → Json
  | .keep => "keep" | .init => "init" | .scalar => "scalar" | .grow => "grow" | .any => "any"

def changeOf (j : Json) : Except String Change := do
  match ← strOf j with
  | "keep" => pure .keep | "init" => pure .init | "scalar" => pure .scalar | "grow" => pure .grow
  | "any" => pure .any
  | c => throw s!"'{c}' is no change"

@[simp] theorem changeOf_changeJ (c : Change) : changeOf (changeJ c) = .ok c := by cases c <;> rfl

def kindJ : HeapKnowledge.Term.Kind → Json
  | .value => "value" | .length => "length" | .view => "view" | .strLength => "strLength"

def kindOf (j : Json) : Except String HeapKnowledge.Term.Kind := do
  match ← strOf j with
  | "value" => pure .value | "length" => pure .length | "view" => pure .view | "strLength" => pure .strLength
  | k => throw s!"'{k}' is no term kind"

@[simp] theorem kindOf_kindJ (k : HeapKnowledge.Term.Kind) : kindOf (kindJ k) = .ok k := by cases k <;> rfl

def guardJ : GuardTag → Json
  | .null => "null" | .undef => "undefined" | .tru => "true" | .fls => "false"

def guardOf (j : Json) : Except String GuardTag := do
  match ← strOf j with
  | "null" => pure .null | "undefined" => pure .undef | "true" => pure .tru | "false" => pure .fls
  | g => throw s!"'{g}' is no guard tag"

@[simp] theorem guardOf_guardJ (g : GuardTag) : guardOf (guardJ g) = .ok g := by cases g <;> rfl

def phaseJ : Phase → Json
  | .before => "before" | .after => "after"

def phaseOf (j : Json) : Except String Phase := do
  match ← strOf j with
  | "before" => pure .before | "after" => pure .after
  | p => throw s!"'{p}' is no phase"

@[simp] theorem phaseOf_phaseJ (p : Phase) : phaseOf (phaseJ p) = .ok p := by cases p <;> rfl

def formatJ : ViewFormat → Json
  | .uint8 => "uint8" | .uint16 => "uint16" | .int32 => "int32" | .float64 => "float64"

def formatOf (j : Json) : Except String ViewFormat := do
  match ← strOf j with
  | "uint8" => pure .uint8 | "uint16" => pure .uint16 | "int32" => pure .int32 | "float64" => pure .float64
  | f => throw s!"'{f}' is no view format"

@[simp] theorem formatOf_formatJ (f : ViewFormat) : formatOf (formatJ f) = .ok f := by cases f <;> rfl

theorem formatJ_ne_null (f : ViewFormat) : formatJ f ≠ Json.null := by cases f <;> simp [formatJ]

def arithJ : Arith → Json
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .pow => "pow" | .xor => "xor"
  | .rem => "rem" | .bitAnd => "bitAnd" | .bitOr => "bitOr" | .shl => "shl" | .shr => "shr"
  | .ushr => "ushr" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge" | .eq => "eq"
  | .looseEq => "looseEq"

def arithOf (j : Json) : Except String Arith := do
  match ← strOf j with
  | "add" => pure .add | "sub" => pure .sub | "mul" => pure .mul | "div" => pure .div | "pow" => pure .pow
  | "xor" => pure .xor | "rem" => pure .rem | "bitAnd" => pure .bitAnd | "bitOr" => pure .bitOr
  | "shl" => pure .shl | "shr" => pure .shr | "ushr" => pure .ushr | "lt" => pure .lt | "le" => pure .le
  | "gt" => pure .gt | "ge" => pure .ge | "eq" => pure .eq | "looseEq" => pure .looseEq
  | a => throw s!"'{a}' is no operator"

@[simp] theorem arithOf_arithJ (a : Arith) : arithOf (arithJ a) = .ok a := by cases a <;> rfl

/-- An elements predicate: the kinds it admits, in this order. -/
def predKinds (R : ElemPred) : List String :=
  [("null", R.nul), ("undefined", R.undef), ("boolean", R.bool), ("number", R.num), ("string", R.str),
    ("bigint", R.big), ("symbol", R.sym), ("object", R.obj)].filterMap fun (k, b) => if b then some k else none

def predOfKinds (ks : List String) : ElemPred :=
  ⟨ks.contains "null", ks.contains "undefined", ks.contains "boolean", ks.contains "number",
    ks.contains "string", ks.contains "bigint", ks.contains "symbol", ks.contains "object"⟩

theorem predOfKinds_predKinds (R : ElemPred) : predOfKinds (predKinds R) = R := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := R
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> rfl

def predJ (R : ElemPred) : Json := listJ Json.str (predKinds R)

def predOf (j : Json) : Except String ElemPred := predOfKinds <$> listOf strOf j

@[simp] theorem predOf_predJ (R : ElemPred) : predOf (predJ R) = .ok R := by
  simp only [predOf, predJ, listOf_listJ strOf Json.str _ (fun _ _ => rfl), map_ok, predOfKinds_predKinds]

theorem predJ_ne_null (R : ElemPred) : predJ R ≠ Json.null := by simp [predJ, listJ]

def keyJ : PropKey → Json
  | .str s => Json.str s
  | .sym i => obj ["symbol"] [natJ i]

def keyOf (j : Json) : Except String PropKey :=
  match strOf j with
  | .ok s => .ok (.str s)
  | .error _ => do
    let [i] ← fields j ["symbol"] | throw "a key is a string or a symbol"
    pure (.sym (← under "symbol" (natOf i)))

@[simp] theorem keyOf_keyJ (k : PropKey) : keyOf (keyJ k) = .ok k := by
  cases k with
  | str s => rfl
  | sym i => simp [keyJ, keyOf, fields_obj]

def selectorJ (c : Selector) : Json := obj ["value", "array", "view"] [c.value, c.array, c.view]

def selectorOf (j : Json) : Except String Selector := do
  let [a, b, c] ← fields j ["value", "array", "view"] | throw "a selector"
  pure ⟨← under "value" (boolOf a), ← under "array" (boolOf b), ← under "view" (boolOf c)⟩

@[simp] theorem selectorOf_selectorJ (c : Selector) : selectorOf (selectorJ c) = .ok c := by
  simp [selectorJ, selectorOf, fields_obj]

def strsJ (l : List String) : Json := listJ Json.str l

@[simp] theorem listOf_strsJ (l : List String) : listOf strOf (strsJ l) = .ok l :=
  listOf_listJ strOf Json.str l (fun _ _ => rfl)

/-! ## Nesting

The decoder reads a recursive value within a nesting bound: each layer of a
recursive constructor takes one unit of it (`nestingLimit`). -/

/-- The largest of a function's values over a list. -/
def maxOf {α : Type} (f : α → Nat) (l : List α) : Nat := l.foldr (fun x m => max (f x) m) 0

theorem le_maxOf {α : Type} (f : α → Nat) {l : List α} {x : α} (h : x ∈ l) : f x ≤ maxOf f l := by
  induction l with
  | nil => cases h
  | cons y t ih =>
    simp only [maxOf, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- The nesting a decoder reads. -/
def nestingLimit : Nat := 256

/-! ## Regions and frames -/

def regionJ : Region → Json
  | .field x k => tagged "field" (obj ["x", "key"] [natJ x, keyJ k])
  | .own x => tagged "own" (obj ["x"] [natJ x])
  | .elems x => tagged "elems" (obj ["x"] [natJ x])
  | .cls c => tagged "cls" (selectorJ c)
  | .all => "all"
  | .path x p k => tagged "path" (obj ["x", "fields", "key"] [natJ x, strsJ p, keyJ k])
  | .pathOwn x p => tagged "pathOwn" (obj ["x", "fields"] [natJ x, strsJ p])
  | .pathElems x p => tagged "pathElems" (obj ["x", "fields"] [natJ x, strsJ p])
  | .cell b => tagged "cell" (obj ["name"] [Json.str b])
  | .inCls r c => tagged "inCls" (obj ["region", "selector"] [regionJ r, selectorJ c])
  | .store x p => tagged "store" (obj ["x", "fields"] [natJ x, strsJ p])

def regionDepth : Region → Nat
  | .inCls r _ => regionDepth r + 1
  | _ => 1

def regionOf : Nat → Json → Except String Region
  | 0, _ => .error "a region nested beyond the limit"
  | n + 1, j => do
    let (k, v) ← tagOf j
    under k <| match k with
    | "field" => do
      let [x, key] ← fields v ["x", "key"] | throw "field"
      pure (.field (← under "x" (natOf x)) (← under "key" (keyOf key)))
    | "own" => do
      let [x] ← fields v ["x"] | throw "own"
      pure (.own (← under "x" (natOf x)))
    | "elems" => do
      let [x] ← fields v ["x"] | throw "elems"
      pure (.elems (← under "x" (natOf x)))
    | "cls" => .cls <$> selectorOf v
    | "all" => pure .all
    | "path" => do
      let [x, p, key] ← fields v ["x", "fields", "key"] | throw "path"
      pure (.path (← under "x" (natOf x)) (← under "fields" (listOf strOf p)) (← under "key" (keyOf key)))
    | "pathOwn" => do
      let [x, p] ← fields v ["x", "fields"] | throw "pathOwn"
      pure (.pathOwn (← under "x" (natOf x)) (← under "fields" (listOf strOf p)))
    | "pathElems" => do
      let [x, p] ← fields v ["x", "fields"] | throw "pathElems"
      pure (.pathElems (← under "x" (natOf x)) (← under "fields" (listOf strOf p)))
    | "cell" => do
      let [b] ← fields v ["name"] | throw "cell"
      pure (.cell (← under "name" (strOf b)))
    | "inCls" => do
      let [r, c] ← fields v ["region", "selector"] | throw "inCls"
      pure (.inCls (← under "region" (regionOf n r)) (← under "selector" (selectorOf c)))
    | "store" => do
      let [x, p] ← fields v ["x", "fields"] | throw "store"
      pure (.store (← under "x" (natOf x)) (← under "fields" (listOf strOf p)))
    | _ => throw "no region"

theorem regionOf_regionJ (r : Region) : ∀ n, regionDepth r ≤ n → regionOf n (regionJ r) = .ok r := by
  induction r with
  | inCls r c ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [regionDepth] at hn; omega⟩
    have h := ih m (by simp [regionDepth] at hn; omega)
    simp [regionJ, regionOf, fields_obj, h] <;> try rfl
  | _ =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [regionDepth] at hn; omega⟩
    simp [regionJ, regionOf, fields_obj] <;> try rfl

def entryJ (e : Region × Change) : Json := obj ["region", "change"] [regionJ e.1, changeJ e.2]

def entryOf (n : Nat) (j : Json) : Except String (Region × Change) := do
  let [r, c] ← fields j ["region", "change"] | throw "a frame entry"
  pure (← under "region" (regionOf n r), ← under "change" (changeOf c))

def frameJ (Φ : Footprint) : Json := listJ entryJ Φ

def frameDepth (Φ : Footprint) : Nat := maxOf (fun e => regionDepth e.1) Φ

def frameOf (n : Nat) (j : Json) : Except String Footprint := listOf (entryOf n) j

theorem frameOf_frameJ (Φ : Footprint) (n : Nat) (h : frameDepth Φ ≤ n) : frameOf n (frameJ Φ) = .ok Φ := by
  apply listOf_listJ
  intro e he
  have hd := Nat.le_trans (le_maxOf (fun e : Region × Change => regionDepth e.1) he) h
  simp [entryJ, entryOf, fields_obj, regionOf_regionJ e.1 n hd]

/-! ## Paths, witnesses and literals -/

def pathJ (p : Path) : Json := obj ["root", "fields"] [natJ p.root, strsJ p.fields]

def pathOf (j : Json) : Except String Path := do
  let [r, f] ← fields j ["root", "fields"] | throw "a path"
  pure ⟨← under "root" (natOf r), ← under "fields" (listOf strOf f)⟩

@[simp] theorem pathOf_pathJ (p : Path) : pathOf (pathJ p) = .ok p := by
  simp [pathJ, pathOf, fields_obj]

def witnessLitOk : Witness → Bool
  | .path _ => true
  | .literal v => v.isLiteral

def witnessJ : Witness → Json
  | .path p => tagged "path" (pathJ p)
  | .literal v => tagged "literal" (litJ v)

def witnessOf (j : Json) : Except String Witness := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "path" => .path <$> pathOf v
  | "literal" => .literal <$> litOf v
  | _ => throw "a witness is a path or a literal"

theorem witnessOf_witnessJ (w : Witness) (h : witnessLitOk w = true) : witnessOf (witnessJ w) = .ok w := by
  cases w with
  | path p => simp [witnessJ, witnessOf]
  | literal v => simp [witnessJ, witnessOf, litOf_litJ (by simpa [witnessLitOk] using h)]

def seqLitOk : WitnessSeq → Bool
  | .fixed xs => xs.all witnessLitOk
  | .restFrom _ => true
  | .append a b => seqLitOk a && seqLitOk b

def seqDepth : WitnessSeq → Nat
  | .append a b => max (seqDepth a) (seqDepth b) + 1
  | _ => 1

def seqJ : WitnessSeq → Json
  | .fixed xs => tagged "fixed" (obj ["xs"] [listJ witnessJ xs])
  | .restFrom k => tagged "restFrom" (obj ["first"] [natJ k])
  | .append a b => tagged "append" (obj ["left", "right"] [seqJ a, seqJ b])

def seqOf : Nat → Json → Except String WitnessSeq
  | 0, _ => .error "a sequence nested beyond the limit"
  | n + 1, j => do
    let (k, v) ← tagOf j
    under k <| match k with
    | "fixed" => do
      let [xs] ← fields v ["xs"] | throw "fixed"
      pure (.fixed (← under "xs" (listOf witnessOf xs)))
    | "restFrom" => do
      let [f] ← fields v ["first"] | throw "restFrom"
      pure (.restFrom (← under "first" (natOf f)))
    | "append" => do
      let [a, b] ← fields v ["left", "right"] | throw "append"
      pure (.append (← under "left" (seqOf n a)) (← under "right" (seqOf n b)))
    | _ => throw "a sequence is fixed, a rest or an append"

theorem seqOf_seqJ (s : WitnessSeq) (hl : seqLitOk s = true) :
    ∀ n, seqDepth s ≤ n → seqOf n (seqJ s) = .ok s := by
  induction s with
  | fixed xs =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [seqDepth] at hn; omega⟩
    have h := listOf_listJ witnessOf witnessJ xs (fun w hw => witnessOf_witnessJ w
      (by simp [seqLitOk] at hl; exact hl w hw))
    simp [seqJ, seqOf, fields_obj, h] <;> try rfl
  | restFrom k =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [seqDepth] at hn; omega⟩
    simp [seqJ, seqOf, fields_obj] <;> try rfl
  | append a b iha ihb =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [seqDepth] at hn; omega⟩
    simp only [seqLitOk, Bool.and_eq_true] at hl
    have ha := iha hl.1 m (by simp [seqDepth] at hn; omega)
    have hb := ihb hl.2 m (by simp [seqDepth] at hn; omega)
    simp [seqJ, seqOf, fields_obj, ha, hb] <;> try rfl

def transportLitOk (t : TransportSchema) : Bool := t.overrides.all (witnessLitOk ·.2)

def transportJ (t : TransportSchema) : Json :=
  obj ["shift", "overrides", "boxed", "stable"]
    [natJ t.shift, listJ (pairJ natJ witnessJ) t.overrides, Json.bool t.boxed, listJ natJ t.stable]

def transportOf (j : Json) : Except String TransportSchema := do
  let [s, o, b, st] ← fields j ["shift", "overrides", "boxed", "stable"] | throw "a transport"
  pure ⟨← under "shift" (natOf s), ← under "overrides" (listOf (pairOf natOf witnessOf) o),
    ← under "boxed" (boolOf b), ← under "stable" (listOf natOf st)⟩

theorem transportOf_transportJ (t : TransportSchema) (h : transportLitOk t = true) :
    transportOf (transportJ t) = .ok t := by
  have ho := listOf_listJ (pairOf natOf witnessOf) (pairJ natJ witnessJ) t.overrides fun p hp =>
    pairOf_pairJ natOf witnessOf natJ witnessJ p (natOf_natJ _)
      (witnessOf_witnessJ _ (by simp [transportLitOk] at h; exact h p.1 p.2 hp))
  have hs := listOf_listJ natOf natJ t.stable fun _ _ => natOf_natJ _
  simp [transportJ, transportOf, fields_obj, ho, hs]

/-! ## Terms and linear facts -/

def termJ (t : HeapKnowledge.Term) : Json :=
  if t.atEntry then obj ["kind", "slot", "path", "atEntry"] [kindJ t.kind, natJ t.slot, strsJ t.path, Json.bool true]
  else obj ["kind", "slot", "path"] [kindJ t.kind, natJ t.slot, strsJ t.path]

def termOf (j : Json) : Except String HeapKnowledge.Term :=
  match (j.getObjVal? "atEntry").toOption with
  | some _ => do
    let [k, s, p, a] ← fields j ["kind", "slot", "path", "atEntry"] | throw "a term"
    let .true ← under "atEntry" (boolOf a) | throw "atEntry: an entry term states true"
    pure (.old (← under "kind" (kindOf k)) (← under "slot" (natOf s)) (← under "path" (listOf strOf p)))
  | none => do
    let [k, s, p] ← fields j ["kind", "slot", "path"] | throw "a term"
    pure (.now (← under "kind" (kindOf k)) (← under "slot" (natOf s)) (← under "path" (listOf strOf p)))

@[simp] theorem termOf_termJ (t : HeapKnowledge.Term) : termOf (termJ t) = .ok t := by
  rw [Term.eta t]
  cases h : t.atEntry
  · simp only [Term.now_atEntry, termJ, if_false, Bool.false_eq_true]
    simp [termOf, fields_obj] <;> try rfl
  · simp only [Term.old_atEntry, termJ, if_true]
    simp [termOf, fields_obj] <;> try rfl

def stepVarJ : StepVar → Json
  | .before t => tagged "before" (obj ["t"] [termJ t])
  | .after t => tagged "after" (obj ["t"] [termJ t])

def stepVarOf (j : Json) : Except String StepVar := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "before" => do
    let [t] ← fields v ["t"] | throw "before"
    pure (.before (← under "t" (termOf t)))
  | "after" => do
    let [t] ← fields v ["t"] | throw "after"
    pure (.after (← under "t" (termOf t)))
  | _ => throw "a two-state variable is before or after"

@[simp] theorem stepVarOf_stepVarJ (x : StepVar) : stepVarOf (stepVarJ x) = .ok x := by
  cases x <;> simp [stepVarJ, stepVarOf, fields_obj] <;> try rfl

def boundJ : Bound → Json
  | .index => "index"
  | .elem => "elem"
  | .offset d => tagged "offset" (obj ["delta"] [natJ d])
  | .project k p => tagged "project" (obj ["kind", "path"] [kindJ k, strsJ p])
  | .free t => tagged "free" (obj ["t"] [termJ t])

def boundOf (j : Json) : Except String Bound := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "index" => pure .index
  | "elem" => pure .elem
  | "offset" => do
    let [d] ← fields v ["delta"] | throw "offset"
    pure (.offset (← under "delta" (natOf d)))
  | "project" => do
    let [kd, p] ← fields v ["kind", "path"] | throw "project"
    pure (.project (← under "kind" (kindOf kd)) (← under "path" (listOf strOf p)))
  | "free" => do
    let [t] ← fields v ["t"] | throw "free"
    pure (.free (← under "t" (termOf t)))
  | _ => throw "a body variable"

@[simp] theorem boundOf_boundJ (b : Bound) : boundOf (boundJ b) = .ok b := by
  cases b <;> simp [boundJ, boundOf, fields_obj] <;> try rfl

/-- A linear fact over variables a codec writes. -/
def linearJ {V : Type} (vJ : V → Json) : Linear.Fact V → Json
  | .le f d => tagged "le" (obj ["form", "bound"] [listJ (pairJ vJ intJ) f, intJ d])
  | .ne f d => tagged "ne" (obj ["form", "bound"] [listJ (pairJ vJ intJ) f, intJ d])

def linearOf {V : Type} (vOf : Json → Except String V) (j : Json) : Except String (Linear.Fact V) := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "le" => do
    let [f, d] ← fields v ["form", "bound"] | throw "le"
    pure (.le (← under "form" (listOf (pairOf vOf intOf) f)) (← under "bound" (intOf d)))
  | "ne" => do
    let [f, d] ← fields v ["form", "bound"] | throw "ne"
    pure (.ne (← under "form" (listOf (pairOf vOf intOf) f)) (← under "bound" (intOf d)))
  | _ => throw "a linear fact is le or ne"

theorem linearOf_linearJ {V : Type} (vOf : Json → Except String V) (vJ : V → Json)
    (hv : ∀ x, vOf (vJ x) = .ok x) (F : Linear.Fact V) : linearOf vOf (linearJ vJ F) = .ok F := by
  have hf : ∀ f : Linear.Form V, listOf (pairOf vOf intOf) (listJ (pairJ vJ intJ) f) = .ok f := fun f =>
    listOf_listJ _ _ f fun p _ => pairOf_pairJ vOf intOf vJ intJ p (hv _) (intOf_intJ _)
  cases F <;> simp [linearJ, linearOf, fields_obj, hf] <;> try rfl

def clauseDepth {V : Type} : LinearClause V → Nat
  | .either a b => max (clauseDepth a) (clauseDepth b) + 1
  | .atom _ => 1

def clauseJ {V : Type} (vJ : V → Json) : LinearClause V → Json
  | .atom F => linearJ vJ F
  | .either a b => tagged "either" (obj ["left", "right"] [clauseJ vJ a, clauseJ vJ b])

def clauseOf {V : Type} (vOf : Json → Except String V) : Nat → Json → Except String (LinearClause V)
  | 0, _ => .error "a clause nested beyond the limit"
  | n + 1, j => do
    let (k, v) ← tagOf j
    match k with
    | "either" => under k do
      let [a, b] ← fields v ["left", "right"] | throw "either"
      pure (.either (← under "left" (clauseOf vOf n a)) (← under "right" (clauseOf vOf n b)))
    | _ => .atom <$> linearOf vOf j

theorem clauseOf_clauseJ {V : Type} (vOf : Json → Except String V) (vJ : V → Json)
    (hv : ∀ x, vOf (vJ x) = .ok x) (c : LinearClause V) : ∀ n, clauseDepth c ≤ n → clauseOf vOf n (clauseJ vJ c) = .ok c := by
  induction c with
  | atom F =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [clauseDepth] at hn; omega⟩
    cases F <;> simp [clauseJ, clauseOf, linearJ] <;> rw [← linearJ] <;>
      simp [linearOf_linearJ vOf vJ hv]
  | either a b iha ihb =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [clauseDepth] at hn; omega⟩
    have ha := iha m (by simp [clauseDepth] at hn; omega)
    have hb := ihb m (by simp [clauseDepth] at hn; omega)
    simp [clauseJ, clauseOf, fields_obj, ha, hb] <;> try rfl

/-! ## Index facts -/

def factDepth : IndexFact → Nat
  | .either a b => max (factDepth a) (factDepth b) + 1
  | .guarded _ _ _ b => factDepth b + 1
  | .every _ _ _ body => maxOf (clauseDepth (V := Bound)) body + 1
  | _ => 1

def factJ : IndexFact → Json
  | .index k => tagged "index" (obj ["slot"] [natJ k])
  | .length x n => tagged "length" (obj ["array", "length"] [natJ x, natJ n])
  | .bound x k s => tagged "bound" (obj ["array", "index", "strict"] [natJ x, natJ k, Json.bool s])
  | .int k => tagged "int" (obj ["slot"] [natJ k])
  | .pastSafe k => tagged "pastSafe" (obj ["slot"] [natJ k])
  | .linear F => tagged "linear" (obj ["fact"] [linearJ termJ F])
  | .either a b => tagged "either" (obj ["left", "right"] [factJ a, factJ b])
  | .guarded k p g b => tagged "guarded" (obj ["slot", "path", "tag", "body"] [natJ k, strsJ p, guardJ g, factJ b])
  | .element v x k => tagged "element" (obj ["value", "array", "index"] [natJ v, natJ x, natJ k])
  | .every k p stop body => tagged "every"
      (obj ["slot", "path", "stop", "body"] [natJ k, strsJ p, termJ stop, listJ (clauseJ boundJ) body])
  | .apart a b => tagged "apart" (obj ["slot", "other"] [natJ a, natJ b])
  | .storeApart a p b q => tagged "storeApart"
      (obj ["slot", "path", "other", "otherPath"] [natJ a, strsJ p, natJ b, strsJ q])

def factOf : Nat → Json → Except String IndexFact
  | 0, _ => .error "a fact nested beyond the limit"
  | n + 1, j => do
    let (k, v) ← tagOf j
    under k <| match k with
    | "index" => do
      let [s] ← fields v ["slot"] | throw "index"
      pure (.index (← under "slot" (natOf s)))
    | "length" => do
      let [x, l] ← fields v ["array", "length"] | throw "length"
      pure (.length (← under "array" (natOf x)) (← under "length" (natOf l)))
    | "bound" => do
      let [x, i, s] ← fields v ["array", "index", "strict"] | throw "bound"
      pure (.bound (← under "array" (natOf x)) (← under "index" (natOf i)) (← under "strict" (boolOf s)))
    | "int" => do
      let [s] ← fields v ["slot"] | throw "int"
      pure (.int (← under "slot" (natOf s)))
    | "pastSafe" => do
      let [s] ← fields v ["slot"] | throw "pastSafe"
      pure (.pastSafe (← under "slot" (natOf s)))
    | "linear" => do
      let [f] ← fields v ["fact"] | throw "linear"
      pure (.linear (← under "fact" (linearOf termOf f)))
    | "either" => do
      let [a, b] ← fields v ["left", "right"] | throw "either"
      pure (.either (← under "left" (factOf n a)) (← under "right" (factOf n b)))
    | "guarded" => do
      let [s, p, g, b] ← fields v ["slot", "path", "tag", "body"] | throw "guarded"
      pure (.guarded (← under "slot" (natOf s)) (← under "path" (listOf strOf p)) (← under "tag" (guardOf g))
        (← under "body" (factOf n b)))
    | "element" => do
      let [a, x, i] ← fields v ["value", "array", "index"] | throw "element"
      pure (.element (← under "value" (natOf a)) (← under "array" (natOf x)) (← under "index" (natOf i)))
    | "every" => do
      let [s, p, st, b] ← fields v ["slot", "path", "stop", "body"] | throw "every"
      pure (.every (← under "slot" (natOf s)) (← under "path" (listOf strOf p)) (← under "stop" (termOf st))
        (← under "body" (listOf (clauseOf boundOf n) b)))
    | "apart" => do
      let [a, b] ← fields v ["slot", "other"] | throw "apart"
      pure (.apart (← under "slot" (natOf a)) (← under "other" (natOf b)))
    | "storeApart" => do
      let [a, p, b, q] ← fields v ["slot", "path", "other", "otherPath"] | throw "storeApart"
      pure (.storeApart (← under "slot" (natOf a)) (← under "path" (listOf strOf p)) (← under "other" (natOf b))
        (← under "otherPath" (listOf strOf q)))
    | _ => throw "no index fact"

theorem factOf_factJ (F : IndexFact) : ∀ n, factDepth F ≤ n → factOf n (factJ F) = .ok F := by
  induction F with
  | either a b iha ihb =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [factDepth] at hn; omega⟩
    have ha := iha m (by simp [factDepth] at hn; omega)
    have hb := ihb m (by simp [factDepth] at hn; omega)
    simp [factJ, factOf, fields_obj, ha, hb] <;> try rfl
  | guarded k p g b ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [factDepth] at hn; omega⟩
    have hb := ih m (by simp [factDepth] at hn; omega)
    simp [factJ, factOf, fields_obj, hb] <;> try rfl
  | every k p stop body =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [factDepth] at hn; omega⟩
    have hb := listOf_listJ (clauseOf boundOf m) (clauseJ boundJ) body fun c hc =>
      clauseOf_clauseJ boundOf boundJ boundOf_boundJ c m
        (Nat.le_trans (le_maxOf _ hc) (by simp [factDepth] at hn; omega))
    simp [factJ, factOf, fields_obj, hb] <;> try rfl
  | linear F =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [factDepth] at hn; omega⟩
    simp [factJ, factOf, fields_obj, linearOf_linearJ termOf termJ termOf_termJ] <;> try rfl
  | _ =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [factDepth] at hn; omega⟩
    simp [factJ, factOf, fields_obj] <;> try rfl


/-! ## Operation posts and formulas -/

def postDepth : OperationPostF WitnessSeq → Nat
  | .push _ _ args => seqDepth args
  | .fact _ _ F => factDepth F
  | _ => 0

def postLitOk : OperationPostF WitnessSeq → Bool
  | .arith _ l r _ => witnessLitOk l && witnessLitOk r
  | .stringRead _ i _ => witnessLitOk i
  | .push _ _ args => seqLitOk args
  | .elementsWhen _ v _ _ => v.isLiteral
  | _ => true

def postJ : OperationPostF WitnessSeq → Json
  | .arith op l r y => tagged "arith"
      (obj ["op", "left", "right", "result"] [arithJ op, witnessJ l, witnessJ r, pathJ y])
  | .stringLength x y => tagged "stringLength" (obj ["string", "result"] [pathJ x, pathJ y])
  | .stringRead x i y => tagged "stringRead" (obj ["string", "index", "result"] [pathJ x, witnessJ i, pathJ y])
  | .lengthsKept x x' => tagged "lengthsKept" (obj ["x", "exit"] [natJ x, natJ x'])
  | .boundedWrite x i x' => tagged "boundedWrite" (obj ["x", "i", "exit"] [natJ x, natJ i, natJ x'])
  | .push x x' args => tagged "push" (obj ["x", "exit", "args"] [natJ x, natJ x', seqJ args])
  | .fact ph l F => tagged "fact" (obj ["phase", "lift", "fact"] [phaseJ ph, natJ l, factJ F])
  | .freshStore x => tagged "freshStore" (obj ["x"] [natJ x])
  | .freshObject x => tagged "freshObject" (obj ["x"] [natJ x])
  | .elementsWhen x v y R => tagged "elementsWhen"
      (obj ["x", "value", "y", "predicate"] [natJ x, litJ v, natJ y, predJ R])
  | .storeExtends x => tagged "storeExtends" (obj ["x"] [natJ x])
  | .viewWrite x i v g => tagged "viewWrite" (obj ["x", "i", "v", "format"] [natJ x, natJ i, natJ v, optJ formatJ g])

def postOf (n : Nat) (j : Json) : Except String (OperationPostF WitnessSeq) := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "arith" => do
    let [op, l, r, y] ← fields v ["op", "left", "right", "result"] | throw "arith"
    pure (.arith (← under "op" (arithOf op)) (← under "left" (witnessOf l)) (← under "right" (witnessOf r))
      (← under "result" (pathOf y)))
  | "stringLength" => do
    let [x, y] ← fields v ["string", "result"] | throw "stringLength"
    pure (.stringLength (← under "string" (pathOf x)) (← under "result" (pathOf y)))
  | "stringRead" => do
    let [x, i, y] ← fields v ["string", "index", "result"] | throw "stringRead"
    pure (.stringRead (← under "string" (pathOf x)) (← under "index" (witnessOf i)) (← under "result" (pathOf y)))
  | "lengthsKept" => do
    let [x, x'] ← fields v ["x", "exit"] | throw "lengthsKept"
    pure (.lengthsKept (← under "x" (natOf x)) (← under "exit" (natOf x')))
  | "boundedWrite" => do
    let [x, i, x'] ← fields v ["x", "i", "exit"] | throw "boundedWrite"
    pure (.boundedWrite (← under "x" (natOf x)) (← under "i" (natOf i)) (← under "exit" (natOf x')))
  | "push" => do
    let [x, x', a] ← fields v ["x", "exit", "args"] | throw "push"
    pure (.push (← under "x" (natOf x)) (← under "exit" (natOf x')) (← under "args" (seqOf n a)))
  | "fact" => do
    let [ph, l, F] ← fields v ["phase", "lift", "fact"] | throw "fact"
    pure (.fact (← under "phase" (phaseOf ph)) (← under "lift" (natOf l)) (← under "fact" (factOf n F)))
  | "freshStore" => do
    let [x] ← fields v ["x"] | throw "freshStore"
    pure (.freshStore (← under "x" (natOf x)))
  | "freshObject" => do
    let [x] ← fields v ["x"] | throw "freshObject"
    pure (.freshObject (← under "x" (natOf x)))
  | "elementsWhen" => do
    let [x, a, y, R] ← fields v ["x", "value", "y", "predicate"] | throw "elementsWhen"
    pure (.elementsWhen (← under "x" (natOf x)) (← under "value" (litOf a)) (← under "y" (natOf y))
      (← under "predicate" (predOf R)))
  | "storeExtends" => do
    let [x] ← fields v ["x"] | throw "storeExtends"
    pure (.storeExtends (← under "x" (natOf x)))
  | "viewWrite" => do
    let [x, i, a, g] ← fields v ["x", "i", "v", "format"] | throw "viewWrite"
    pure (.viewWrite (← under "x" (natOf x)) (← under "i" (natOf i)) (← under "v" (natOf a))
      (← under "format" (optOf formatOf g)))
  | _ => throw "no operation post"

theorem postOf_postJ (q : OperationPostF WitnessSeq) (hl : postLitOk q = true) (n : Nat) (hn : postDepth q ≤ n) :
    postOf n (postJ q) = .ok q := by
  cases q with
  | arith op l r y =>
    simp only [postLitOk, Bool.and_eq_true] at hl
    simp [postJ, postOf, fields_obj, witnessOf_witnessJ l hl.1, witnessOf_witnessJ r hl.2] <;> try rfl
  | stringRead x i y =>
    simp [postJ, postOf, fields_obj, witnessOf_witnessJ i (by simpa [postLitOk] using hl)] <;> try rfl
  | push x x' args =>
    simp [postJ, postOf, fields_obj, seqOf_seqJ args (by simpa [postLitOk] using hl) n (by simpa [postDepth] using hn)]
      <;> try rfl
  | fact ph l F =>
    simp [postJ, postOf, fields_obj, factOf_factJ F n (by simpa [postDepth] using hn)] <;> try rfl
  | elementsWhen x v y R =>
    simp [postJ, postOf, fields_obj, litOf_litJ (by simpa [postLitOk] using hl)] <;> try rfl
  | viewWrite x i v g =>
    simp [postJ, postOf, fields_obj, optOf_optJ formatOf formatJ g formatJ_ne_null (fun a _ => formatOf_formatJ a)]
      <;> try rfl
  | _ => simp [postJ, postOf, fields_obj] <;> try rfl

/-- **Whether a formula serializes**: it references no assertion-arena node,
and its literals are primitive constants. -/
def formulaOk : FormulaSchema → Bool
  | .at .. => false
  | .operation q => postLitOk q
  | .transport t => transportLitOk t
  | .and a b => formulaOk a && formulaOk b
  | _ => true

def formulaDepth : FormulaSchema → Nat
  | .and a b => max (formulaDepth a) (formulaDepth b) + 1
  | .transition Φ => frameDepth Φ + 1
  | .operation q => postDepth q + 1
  | _ => 1

def formulaJ : FormulaSchema → Json
  | .at .. => Json.null
  | .transition Φ => tagged "transition" (obj ["effect"] [frameJ Φ])
  | .operation q => tagged "operation" (obj ["post"] [postJ q])
  | .linear F => tagged "linear" (obj ["fact"] [linearJ stepVarJ F])
  | .defined v => tagged "defined" (obj ["v"] [stepVarJ v])
  | .transport t => tagged "transport" (transportJ t)
  | .and a b => tagged "and" (obj ["left", "right"] [formulaJ a, formulaJ b])
  | .truth => "truth"
  | .falsity => "falsity"

def formulaOf : Nat → Json → Except String FormulaSchema
  | 0, _ => .error "a formula nested beyond the limit"
  | n + 1, j => do
    let (k, v) ← tagOf j
    under k <| match k with
    | "transition" => do
      let [Φ] ← fields v ["effect"] | throw "transition"
      pure (.transition (← under "effect" (frameOf n Φ)))
    | "operation" => do
      let [q] ← fields v ["post"] | throw "operation"
      pure (.operation (← under "post" (postOf n q)))
    | "linear" => do
      let [F] ← fields v ["fact"] | throw "linear"
      pure (.linear (← under "fact" (linearOf stepVarOf F)))
    | "defined" => do
      let [x] ← fields v ["v"] | throw "defined"
      pure (.defined (← under "v" (stepVarOf x)))
    | "transport" => .transport <$> transportOf v
    | "and" => do
      let [a, b] ← fields v ["left", "right"] | throw "and"
      pure (.and (← under "left" (formulaOf n a)) (← under "right" (formulaOf n b)))
    | "truth" => pure .truth
    | "falsity" => pure .falsity
    | _ => throw "no formula of a specification"

theorem formulaOf_formulaJ (F : FormulaSchema) (hF : formulaOk F = true) :
    ∀ n, formulaDepth F ≤ n → formulaOf n (formulaJ F) = .ok F := by
  induction F with
  | «at» => cases hF
  | and a b iha ihb =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [formulaDepth] at hn; omega⟩
    simp only [formulaOk, Bool.and_eq_true] at hF
    have ha := iha hF.1 m (by simp [formulaDepth] at hn; omega)
    have hb := ihb hF.2 m (by simp [formulaDepth] at hn; omega)
    simp [formulaJ, formulaOf, fields_obj, ha, hb] <;> try rfl
  | transition Φ =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [formulaDepth] at hn; omega⟩
    simp [formulaJ, formulaOf, fields_obj, frameOf_frameJ Φ m (by simp [formulaDepth] at hn; omega)] <;> try rfl
  | operation q =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [formulaDepth] at hn; omega⟩
    simp [formulaJ, formulaOf, fields_obj,
      postOf_postJ q (by simpa [formulaOk] using hF) m (by simp [formulaDepth] at hn; omega)] <;> try rfl
  | linear F =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [formulaDepth] at hn; omega⟩
    simp [formulaJ, formulaOf, fields_obj, linearOf_linearJ stepVarOf stepVarJ stepVarOf_stepVarJ] <;> try rfl
  | transport t =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [formulaDepth] at hn; omega⟩
    simp [formulaJ, formulaOf, transportOf_transportJ t (by simpa [formulaOk] using hF)] <;> try rfl
  | _ =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [formulaDepth] at hn; omega⟩
    simp [formulaJ, formulaOf, fields_obj] <;> try rfl

/-! ## Exits and effects -/

def exitDepth (q : ExitSchema) : Nat := max (frameDepth q.frame) (maxOf formulaDepth q.ensures)

def exitJ (q : ExitSchema) : Json := obj ["frame", "ensures"] [frameJ q.frame, listJ formulaJ q.ensures]

def exitOf (n : Nat) (j : Json) : Except String ExitSchema := do
  let [Φ, E] ← fields j ["frame", "ensures"] | throw "an exit"
  pure ⟨← under "frame" (frameOf n Φ), ← under "ensures" (listOf (formulaOf n) E)⟩

theorem exitOf_exitJ (q : ExitSchema) (hq : q.ensures.all formulaOk = true) (n : Nat) (hn : exitDepth q ≤ n) :
    exitOf n (exitJ q) = .ok q := by
  have hf := frameOf_frameJ q.frame n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have he := listOf_listJ (formulaOf n) formulaJ q.ensures fun F hF =>
    formulaOf_formulaJ F (List.all_eq_true.mp hq F hF) n
      (Nat.le_trans (le_maxOf formulaDepth hF) (Nat.le_trans (Nat.le_max_right _ _) hn))
  simp [exitJ, exitOf, fields_obj, hf, he]

def promiseJ : TypePromise → Json
  | .guards p => tagged "guards" (obj ["param"] [natJ p])
  | .asserts p => tagged "asserts" (obj ["param"] [natJ p])

def promiseOf (j : Json) : Except String TypePromise := do
  let (k, v) ← tagOf j
  under k <| match k with
  | "guards" => do
    let [p] ← fields v ["param"] | throw "guards"
    pure (.guards (← under "param" (natOf p)))
  | "asserts" => do
    let [p] ← fields v ["param"] | throw "asserts"
    pure (.asserts (← under "param" (natOf p)))
  | _ => throw "a promise is a guard's or an assertion function's"

@[simp] theorem promiseOf_promiseJ (p : TypePromise) : promiseOf (promiseJ p) = .ok p := by
  cases p <;> simp [promiseJ, promiseOf, fields_obj] <;> try rfl

theorem promiseJ_ne_null (p : TypePromise) : promiseJ p ≠ Json.null := by
  cases p <;> simp [promiseJ, tagged, Json.mkObj]

/-- **Whether an effect serializes** (the serialization predicate): its
formulas reference no assertion-arena node and state primitive literals,
and its nesting is at most `nestingLimit`. -/
def serializable (e : Effect) : Bool :=
  e.exits.normal.ensures.all formulaOk && e.exits.exceptional.ensures.all formulaOk &&
    decide (max (max (exitDepth e.exits.normal) (exitDepth e.exits.exceptional)) (maxOf factDepth e.pre) ≤ nestingLimit)

def Serializable (e : Effect) : Prop := serializable e = true

/-- A callable's two exits. -/
def exitsJ (x : Exits ExitSchema) : Json := obj ["normal", "exceptional"] [exitJ x.normal, exitJ x.exceptional]

def exitsOf (j : Json) : Except String (Exits ExitSchema) := do
  let [nm, ex] ← fields j ["normal", "exceptional"] | throw "exits"
  pure ⟨← under "normal" (exitOf nestingLimit nm), ← under "exceptional" (exitOf nestingLimit ex)⟩

/-- **The encoder**: an effect's exits, promise, elements precondition and
preconditions. -/
def encode (e : Effect) : Json :=
  obj ["exits", "promise", "requires", "pre"]
    [exitsJ e.exits, optJ promiseJ e.promise, optJ predJ e.requires, listJ factJ e.pre]

/-- The effect a document states, read within the nesting limit. -/
def parse (j : Json) : Except String Effect := do
  let [x, p, r, pre] ← fields j ["exits", "promise", "requires", "pre"] | throw "an effect"
  pure ⟨← under "exits" (exitsOf x), ← under "promise" (optOf promiseOf p), ← under "requires" (optOf predOf r),
    ← under "pre" (listOf (factOf nestingLimit) pre)⟩

theorem parse_encode {e : Effect} (h : Serializable e) : parse (encode e) = .ok e := by
  obtain ⟨⟨qn, qe⟩, p, r, pre⟩ := e
  simp only [Serializable, serializable, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn, he⟩, hd⟩ := h
  have h1 := exitOf_exitJ qn hn nestingLimit (by simp at hd; omega)
  have h2 := exitOf_exitJ qe he nestingLimit (by simp at hd; omega)
  have h3 := optOf_optJ promiseOf promiseJ p promiseJ_ne_null (fun a _ => promiseOf_promiseJ a)
  have h4 := optOf_optJ predOf predJ r predJ_ne_null (fun a _ => predOf_predJ a)
  have h5 := listOf_listJ (factOf nestingLimit) factJ pre fun F hF =>
    factOf_factJ F nestingLimit (Nat.le_trans (le_maxOf factDepth hF) (by simp at hd; omega))
  simp [encode, parse, exitsJ, exitsOf, fields_obj, h1, h2, h3, h4, h5]

/-- The first place two JSON values differ, by its path. -/
partial def firstDifference (path : String) (a b : Json) : String :=
  match a, b with
  | .obj x, .obj y =>
    let keys := (x.toList.map (·.1) ++ y.toList.map (·.1)).eraseDups
    match keys.find? (fun k => (x.get? k).map Json.compress != (y.get? k).map Json.compress) with
    | some k => match x.get? k, y.get? k with
      | some u, some v => firstDifference s!"{path}/{k}" u v
      | none, _ => s!"{path}/{k}: a field the effect does not have"
      | _, none => s!"{path}/{k}: a required field is missing"
    | none => path
  | .arr x, .arr y =>
    if x.size != y.size then s!"{path}: a list of {y.size} where {x.size} are read"
    else match (List.range x.size).find? (fun i => (x[i]?.map Json.compress) != (y[i]?.map Json.compress)) with
      | some i => firstDifference s!"{path}[{i}]" (x[i]?.getD .null) (y[i]?.getD .null)
      | none => path
  | _, _ => s!"{path}: {b.compress} where the effect is written {a.compress}"

/-- **The decoder**: a document's effect, refused unless the document is
exactly the writing of the effect read (`encode`, up to the order of object
members), at the first place it differs. -/
def decode (j : Json) : Except String Effect := do
  let e ← parse j
  if !serializable e then throw "an effect beyond the nesting limit"
  if (encode e).compress == j.compress then pure e
  else throw s!"an effect differs from its writing at {firstDifference "" (encode e) j}"

/-- **Encoding then decoding returns every serializable effect** (proved). -/
theorem decode_encode {e : Effect} (h : Serializable e) : decode (encode e) = .ok e := by
  simp only [decode, parse_encode h, ok_bind]
  simp only [Serializable] at h
  simp [h]

/-- **A decoded effect is serializable, and the document is its writing** up
to the order of object members (proved). -/
theorem decode_sound {j : Json} {e : Effect} (h : decode j = .ok e) :
    Serializable e ∧ (encode e).compress = j.compress := by
  unfold decode at h
  cases hp : parse j with
  | error _ => rw [hp] at h; cases h
  | ok e' =>
    rw [hp] at h
    simp only [ok_bind] at h
    by_cases hs : serializable e' = true
    · simp only [hs, Bool.not_true] at h
      by_cases hc : ((encode e').compress == j.compress) = true
      · simp only [hc] at h; cases h; exact ⟨hs, by simpa using hc⟩
      · simp only [hc] at h; cases h
    · simp only [Bool.not_eq_true] at hs; simp [hs] at h; cases h

/-- **Encoding keeps the effect**: two serializable effects of one writing are
one effect (proved, by `decode_encode`). -/
theorem encode_injective {e e' : Effect} (h : Serializable e) (h' : Serializable e') (he : encode e = encode e') :
    e = e' := by
  have := decode_encode h
  rw [he, decode_encode h'] at this
  exact (Except.ok.inj this).symm

/-- **The serializable effects** and their total encoder. -/
def SerializableEffect := {e : Effect // Serializable e}

def SerializableEffect.encode (e : SerializableEffect) : Json := EffectCodec.encode e.val

/-- An effect with its evidence of serializing, or the reason it does not. -/
def checked (e : Effect) : Except String SerializableEffect :=
  if h : serializable e = true then .ok ⟨e, h⟩
  else .error "an effect whose formulas reference an assertion, state a literal of no primitive constant or nest beyond the limit"


/-- **A value read exactly**: what `parse` reads of a document, refused unless
the document is its writing (`enc`), up to the order of object members, at
the first place it differs. -/
def exactly {α : Type} (enc : α → Json) (parse : Json → Except String α) (j : Json) : Except String α := do
  let a ← parse j
  if (enc a).compress == j.compress then pure a
  else throw s!"a value differs from its writing at {firstDifference "" (enc a) j}"

/-- Whether a callable's exits serialize (`serializable`). -/
def exitsSerializable (x : Exits ExitSchema) : Bool := serializable ⟨x, none, none, []⟩

/-- **A callable's exits, read exactly** (a statement's, a claim's): the
exits of the serialized effect. -/
def decodeExits (j : Json) : Except String (Exits ExitSchema) := do
  let x ← exactly exitsJ exitsOf j
  if !exitsSerializable x then throw "exits beyond the nesting limit"
  pure x

/-- The fields of a serialized effect (`encode`). -/
def effectFields : List String := ["exits", "promise", "requires", "pre"]

/-- **Every effect a document holds reads back as an effect**: each object
of exactly the effect's fields (`effectFields`, the shape `encode` writes
at every effect) decodes (`decode`), or the document is refused whole,
naming the first effect's place by its path and the decoder's reason. The
encoder writes `null` at an assertion reference and at a term literal, and
the decoder reads the nesting limit, so an effect outside the serialization
predicate does not read back. -/
partial def effectsRead (path : String) : Json → Except String Unit
  | .obj kvs =>
    let ks := kvs.toArray.toList.map (·.1)
    if ks.length == effectFields.length && effectFields.all ks.contains then
      match decode (.obj kvs) with
      | .ok _ => .ok ()
      | .error m => .error s!"{if path.isEmpty then "/" else path}: an effect the document cannot write: {m}"
    else kvs.toArray.toList.forM fun (k, v) => effectsRead s!"{path}/{k}" v
  | .arr a => a.toList.zipIdx.forM fun (v, i) => effectsRead s!"{path}[{i}]" v
  | _ => .ok ()

/-- **A document holding effects, written**: the document where every effect
it holds reads back as one (`effectsRead`), otherwise the refusal of the
whole document naming the place. Every writer of a document that holds an
effect writes through it. -/
def document (j : Json) : Except String Json := do
  effectsRead "" j
  pure j

/-- The UTF-16 code unit four hexadecimal digits state. -/
def hexUnit (cs : List Char) : Option Nat :=
  (cs.mapM fun c => hexOf c.toLower).map fun ds => ds.foldl (fun a d => a * 16 + d) 0

/-- **A document's text states no object key twice** (at its first repeated
key): the reader reads objects into maps, which keep one value of a key.
Keys are compared as the strings they state, their escapes decoded (`\u0070`
is `p`, a surrogate pair one character). -/
partial def duplicateKey? (text : String) : Option String :=
  let rec str (cs : List Char) (acc : List Char) : Option (String × List Char) :=
    match cs with
    | '"' :: rest => some (String.ofList acc.reverse, rest)
    | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
      match hexUnit [a, b, c, d] with
      | none => none
      | some u =>
        if 0xD800 ≤ u ∧ u < 0xDC00 then
          match rest with
          | '\\' :: 'u' :: e :: f :: g :: h :: rest' =>
            match hexUnit [e, f, g, h] with
            | some l => if 0xDC00 ≤ l ∧ l < 0xE000 then
                str rest' (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)) :: acc)
              else str rest (Char.ofNat u :: acc)
            | none => none
          | _ => str rest (Char.ofNat u :: acc)
        else str rest (Char.ofNat u :: acc)
    | '\\' :: c :: rest => str rest ((match c with
        | 'b' => '\x08' | 'f' => '\x0c' | 'n' => '\n' | 'r' => '\r' | 't' => '\t' | c => c) :: acc)
    | c :: rest => str rest (c :: acc)
    | [] => none
  -- `stack`: per open object its keys, `none` for an array; `key`: whether a
  -- string read now is an object's key.
  let rec go (cs : List Char) (stack : List (Option (List String))) (key : Bool) : Option String :=
    match cs with
    | [] => none
    | '"' :: rest => match str rest [] with
      | none => none
      | some (s, rest') =>
        if key then match stack with
          | some ks :: up =>
            if ks.contains s then some s!"an object states the key '{s}' twice"
            else go rest' (some (s :: ks) :: up) false
          | _ => go rest' stack false
        else go rest' stack false
    | '{' :: rest => go rest (some [] :: stack) true
    | '[' :: rest => go rest (none :: stack) false
    | '}' :: rest | ']' :: rest => go rest stack.tail false
    | ',' :: rest => go rest stack (match stack with | some _ :: _ => true | _ => false)
    | _ :: rest => go rest stack key
  go text.toList [] false


/-! ## Examples

Effects of every grammar form round-trip, and documents outside the grammar
are refused at their first difference. -/

private def roundTrips (e : Effect) : Bool :=
  match decode (encode e) with
  | .ok d => d == e
  | .error _ => false

private def refuses (text : String) : Bool :=
  match Json.parse text with
  | .ok j => (decode j).toOption.isNone
  | .error _ => false

private def topFrame : Footprint := Parity.topEffect

/-- An exceptional postcondition, a rest sequence, a nested conjunction and
a transport with overrides and stable slots. -/
private def sample : Effect :=
  ⟨⟨⟨[(.cls ⟨true, false, false⟩, .keep), (.inCls (.pathOwn 1 ["a"]) ⟨true, false, false⟩, .any),
        (.path 0 [] (.sym 3), .grow)],
      [.operation (.push 0 1 (.append (.fixed [.literal (.num 0x3ff0000000000000)]) (.restFrom 1))),
        .and (.operation (.fact .after 0 (.linear (.le [(.old .length 1 [], -9007199254740993)] 4))))
          (.and .truth (.linear (.ne [(.after (.now .value 0 []), 1)] 0))),
        .operation (.elementsWhen 0 .tru 1 ⟨true, false, false, true, false, false, false, false⟩),
        .operation (.arith .add (.literal (.bigint (-123456789012345678901234567890))) (.literal (.str "x\"y"))
          ⟨2, ["f"]⟩)]⟩,
    ⟨topFrame, [.transport ⟨1, [(3, .path ⟨0, []⟩), (3, .literal .undef)], true, [2, 2]⟩,
      .operation (.freshStore 0)]⟩⟩,
    some (.asserts 1), some ⟨false, true, false, false, false, false, false, true⟩,
    [.every 1 ["x"] (.now .length 1 ["x"]) [.either (.atom (.le [(.offset 2, 1)] 0)) (.atom (.ne [(.elem, 1)] 5))],
      .apart 1 2]⟩

#guard roundTrips sample
#guard roundTrips Effect.ordinary
-- An assertion-arena reference does not serialize, at any depth.
#guard !serializable { sample with exits := ⟨⟨[], [.and .truth (.at .after ⟨0⟩)]⟩, ⟨[], []⟩⟩ }
-- A term literal does not serialize.
#guard !serializable { sample with exits := ⟨⟨[], [.operation (.elementsWhen 0 (.var 0) 1 {})]⟩, ⟨[], []⟩⟩ }
-- An unknown nested field, an `at` formula, a transport without its stable slots, a repeated constructor tag and a noncanonical integer.
#guard refuses r#"{"exits":{"normal":{"frame":[],"ensures":["truth"]},"exceptional":{"frame":[],"ensures":[{"and":{"left":"truth","right":"falsity","extra":1}}]}},"promise":null,"requires":null,"pre":[]}"#
#guard refuses r#"{"exits":{"normal":{"frame":[],"ensures":[{"at":{"phase":"after","assertion":{"index":0}}}]},"exceptional":{"frame":[],"ensures":[]}},"promise":null,"requires":null,"pre":[]}"#
#guard refuses r#"{"exits":{"normal":{"frame":[],"ensures":[{"transport":{"shift":1,"overrides":[],"boxed":false}}]},"exceptional":{"frame":[],"ensures":[]}},"promise":null,"requires":null,"pre":[]}"#
#guard refuses r#"{"exits":{"normal":{"frame":[],"ensures":[{"transport":{"shift":1,"overrides":[[1]],"boxed":false,"stable":[]}}]},"exceptional":{"frame":[],"ensures":[]}},"promise":null,"requires":null,"pre":[]}"#
#guard refuses r#"{"exits":{"normal":{"frame":[],"ensures":[{"and":{"left":"truth","right":"truth"},"truth":null}]},"exceptional":{"frame":[],"ensures":[]}},"promise":null,"requires":null,"pre":[]}"#
#guard refuses r#"{"exits":{"normal":{"frame":[],"ensures":[]},"exceptional":{"frame":[],"ensures":[]}},"promise":null,"requires":null,"pre":[{"index":{"slot":"5"}}]}"#
#guard !refuses r#"{"exits":{"normal":{"frame":[],"ensures":[]},"exceptional":{"frame":[],"ensures":[]}},"promise":null,"requires":null,"pre":[{"index":{"slot":5}}]}"#
-- A document holding an effect outside the predicate is refused whole, at
-- the effect's place (a boundary no CLI input reaches: the verifier builds
-- the effects it writes).
#guard (document (Json.mkObj [("rows", Json.arr #[Json.null,
    encode { sample with exits := ⟨⟨[], [.and .truth (.at .after ⟨0⟩)]⟩, ⟨[], []⟩⟩ }])])) matches .error _
#guard (document (Json.mkObj [("rows", Json.arr #[encode sample])])) matches .ok _
-- A key stated twice is refused before the document is read into maps.
#guard (duplicateKey? r#"{"a":{"b":1,"c":[{"b":2}],"b":3}}"#).isSome
#guard (duplicateKey? r#"{"a":{"b":1,"c":[{"b":2}]},"b":"\"b\""}"#).isNone

end Verification.EffectCodec
