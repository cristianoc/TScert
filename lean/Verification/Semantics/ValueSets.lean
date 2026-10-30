import Verification.Semantics.HeapAtoms
import Verification.Semantics.CanonicalLists

/-! Value sets: what a heap fact states of a value, one component per kind
of value (heap-knowledge draft, §2). A primitive component is a set of
literals, written as the literals or as every literal but them; objects
carry a conjunction of clauses of tag answers. Meet and join are exact, and
every atom of `HeapFacts` translates to the set it denotes. -/
namespace Verification.ValueSets
open ProgramTyping HeapFacts CanonicalLists

/-- A set of literals: these, or every literal but these. -/
inductive Lit (α : Type) where
  | these (xs : List α)
  | allBut (xs : List α)
  deriving DecidableEq, Hashable, Repr

namespace Lit
variable {α : Type} [DecidableEq α]

def mem : Lit α → α → Bool
  | these xs, a => xs.contains a
  | allBut xs, a => !xs.contains a

def none : Lit α := these []
def all : Lit α := allBut []

def join : Lit α → Lit α → Lit α
  | these a, these b => these (a ++ b.filter (!a.contains ·))
  | these a, allBut b => allBut (b.filter (!a.contains ·))
  | allBut a, these b => allBut (a.filter (!b.contains ·))
  | allBut a, allBut b => allBut (a.filter (b.contains ·))

def meet : Lit α → Lit α → Lit α
  | these a, these b => these (a.filter (b.contains ·))
  | these a, allBut b => these (a.filter (!b.contains ·))
  | allBut a, these b => these (b.filter (!a.contains ·))
  | allBut a, allBut b => allBut (a ++ b.filter (!a.contains ·))

/-- Inclusion, decided exactly but for `allBut` against `these`, which an
infinite universe never includes. -/
def le : Lit α → Lit α → Bool
  | these a, l => a.all l.mem
  | allBut a, allBut b => b.all a.contains
  | allBut _, these _ => false

theorem mem_these (xs : List α) (x : α) : (these xs).mem x = xs.contains x := rfl
theorem mem_allBut (xs : List α) (x : α) : (allBut xs).mem x = !xs.contains x := rfl

@[simp] theorem mem_none (x : α) : (none : Lit α).mem x = false := by simp [none, mem]
@[simp] theorem mem_all (x : α) : (all : Lit α).mem x = true := by simp [all, mem]

theorem mem_join (l m : Lit α) (x : α) : (join l m).mem x = (l.mem x || m.mem x) := by
  cases l <;> cases m <;> simp [join, mem, Bool.or_comm] <;>
    (rename_i a b; cases decide (x ∈ a) <;> cases decide (x ∈ b) <;> rfl)

theorem mem_meet (l m : Lit α) (x : α) : (meet l m).mem x = (l.mem x && m.mem x) := by
  cases l <;> cases m <;> simp [meet, mem, Bool.and_comm] <;>
    (rename_i a b; cases decide (x ∈ a) <;> cases decide (x ∈ b) <;> rfl)

theorem le_sound {l m : Lit α} {x : α} (h : le l m = true) (hx : l.mem x = true) : m.mem x = true := by
  cases l with
  | these a =>
    simp only [le, List.all_eq_true] at h
    exact h x (by simpa [mem, List.contains_iff_mem] using hx)
  | allBut a =>
    cases m with
    | these b => simp [le] at h
    | allBut b =>
      simp only [le, List.all_eq_true, List.contains_iff_mem] at h
      simp only [mem] at hx ⊢
      cases hb : b.contains x
      · rfl
      · have := h x (List.contains_iff_mem.mp hb)
        simp_all

end Lit

deriving instance Hashable for Tag

/-- A tag answer on an object: the tag answers `answer`, or reads a
prototype for it (`Atom.holds`). -/
structure Literal where
  tag : Tag
  answer : Bool
  deriving DecidableEq, Hashable, Repr

abbrev Clause := List Literal

def Literal.sat (v : Tm) (l : Literal) : Bool := tagHolds l.tag v == l.answer || !protoFree l.tag v

/-- An integer as a natural number, one-to-one. -/
def zig (i : Int) : Nat := if 0 ≤ i then 2 * i.toNat else 2 * (-i).toNat - 1

theorem zig_inj {i j : Int} (h : zig i = zig j) : i = j := by
  unfold zig at h; split at h <;> split at h <;> omega

def propKey : PropKey → List Nat
  | .str s => 0 :: s.toList.map Char.toNat
  | .sym n => [1, n]

/-- A tag as a list of numbers, one-to-one, ordering literals. -/
def tagKey : Tag → List Nat
  | .isNul => [0] | .isBool => [1] | .isRef => [2] | .isFun => [3] | .isUndef => [4]
  | .isNullish => [5] | .isNum => [6] | .isStr => [7] | .numEq b => [8, b.toNat]
  | .strEq s => 9 :: s.toList.map Char.toNat | .isBigint => [10] | .isSymbol => [11]
  | .truthy => [12] | .isArray => [13] | .boolEq b => [14, if b then 1 else 0]
  | .bigintEq i => [15, zig i] | .typeofObject => [16] | .hasKey k => 17 :: propKey k

theorem chars_inj {s t : String} (h : s.toList.map Char.toNat = t.toList.map Char.toNat) : s = t := by
  apply String.toList_inj.mp
  generalize s.toList = l₁ at h
  generalize t.toList = l₂ at h
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Char.toNat_inj.mp h.1, ih _ h.2]

theorem propKey_inj {a b : PropKey} (h : propKey a = propKey b) : a = b := by
  cases a <;> cases b <;> simp [propKey] at h
  · rw [chars_inj h]
  · rw [h]

theorem tagKey_inj {a b : Tag} (h : tagKey a = tagKey b) : a = b := by
  cases a <;> cases b <;> simp [tagKey] at h
  all_goals first
    | rfl
    | (rw [UInt64.toNat_inj.mp h])
    | (rw [chars_inj h])
    | (rw [zig_inj h])
    | (rw [propKey_inj h])
    | (rename_i a b; cases a <;> cases b <;> simp_all)
    | skip

def Literal.key (l : Literal) : List Nat := (if l.answer then 1 else 0) :: tagKey l.tag

instance : LT Literal := ⟨fun a b => a.key < b.key⟩
instance : DecidableLT Literal := fun a b => inferInstanceAs (Decidable (a.key < b.key))

instance : StrictTotal Literal where
  irrefl a := StrictTotal.irrefl a.key
  trans h₁ h₂ := StrictTotal.trans (α := List Nat) h₁ h₂
  total {a b} h := StrictTotal.total (α := List Nat) fun e => h (by
    cases a; cases b
    simp only [Literal.key, List.cons.injEq] at e
    obtain ⟨e₁, e₂⟩ := e
    rw [tagKey_inj e₂]
    congr
    split at e₁ <;> split at e₁ <;> simp_all)

def Clause.sat (v : Tm) (c : Clause) : Bool := c.any (Literal.sat v)

/-- A conjunction of clauses; `none` admits no object. -/
abbrev Obj := Option (List Clause)

def Obj.mem : Obj → Tm → Bool
  | none, _ => false
  | some cs, v => cs.all (Clause.sat v)

def Obj.join : Obj → Obj → Obj
  | none, o | o, none => o
  | some a, some b => some (a.flatMap fun c => b.map (c ++ ·))

def Obj.meet : Obj → Obj → Obj
  | none, _ | _, none => none
  | some a, some b => some (a ++ b.filter (!a.contains ·))

def Obj.le : Obj → Obj → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => b.all fun c => a.any fun d => d.all c.contains

theorem Obj.mem_join (a b : Obj) (v : Tm) : (Obj.join a b).mem v = (a.mem v || b.mem v) := by
  cases a with
  | none => cases b <;> simp [Obj.join, Obj.mem]
  | some a =>
    cases b with
    | none => simp [Obj.join, Obj.mem]
    | some b =>
      simp only [Obj.join, Obj.mem, List.all_flatMap, List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp_apply, Clause.sat, List.any_append,
        Bool.or_eq_true]
      constructor
      · intro h
        by_cases ha : ∃ c ∈ a, c.any (Literal.sat v) = false
        · right
          obtain ⟨c, hc, hn⟩ := ha
          intro d hd
          simpa [hn] using h c hc d hd
        · left
          intro c hc
          cases hcv : c.any (Literal.sat v)
          · exact absurd ⟨c, hc, hcv⟩ ha
          · rfl
      · rintro (h | h) c hc d hd
        · exact Or.inl (h c hc)
        · exact Or.inr (h d hd)

theorem Obj.mem_meet (a b : Obj) (v : Tm) : (Obj.meet a b).mem v = (a.mem v && b.mem v) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => simp [Obj.meet, Obj.mem]
    | some b =>
      simp only [Obj.meet, Obj.mem, List.all_append]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, Bool.not_eq_true']
      constructor
      · rintro ⟨ha, hb⟩
        refine ⟨ha, fun c hc => ?_⟩
        by_cases hca : c ∈ a
        · exact ha c hca
        · exact hb c ⟨hc, by simpa using hca⟩
      · rintro ⟨ha, hb⟩
        exact ⟨ha, fun c hc => hb c hc.1⟩

theorem Obj.le_sound {a b : Obj} {v : Tm} (h : Obj.le a b = true) (hv : a.mem v = true) : b.mem v = true := by
  cases a with
  | none => simp [Obj.mem] at hv
  | some a =>
    cases b with
    | none => simp [Obj.le] at h
    | some b =>
      simp only [Obj.le, List.all_eq_true, List.any_eq_true] at h
      simp only [Obj.mem, List.all_eq_true] at hv ⊢
      intro c hc
      obtain ⟨d, hd, hdc⟩ := h c hc
      obtain ⟨l, hl, hs⟩ := List.any_eq_true.mp (hv d hd)
      exact List.any_eq_true.mpr ⟨l, List.contains_iff_mem.mp (hdc l hl), hs⟩

/-- A set of values, one component per kind of value. -/
structure ValueSet where
  nul : Bool := false
  undef : Bool := false
  tru : Bool := false
  fls : Bool := false
  sym : Bool := false
  arr : Bool := false
  num : Lit UInt64 := .none
  str : Lit String := .none
  big : Lit Int := .none
  obj : Obj := none
  deriving DecidableEq, Hashable, Repr

namespace ValueSet

def mem (V : ValueSet) : Tm → Bool
  | .nul => V.nul
  | .undef => V.undef
  | .tru => V.tru
  | .fls => V.fls
  | .num b => V.num.mem b
  | .str s => V.str.mem s
  | .bigint i => V.big.mem i
  | .sym _ => V.sym
  | .arr _ => V.arr
  | v@(.objAt ..) => V.obj.mem v
  | _ => false

def bot : ValueSet := {}

def top : ValueSet :=
  ⟨true, true, true, true, true, true, .all, .all, .all, some []⟩

def join (a b : ValueSet) : ValueSet :=
  ⟨a.nul || b.nul, a.undef || b.undef, a.tru || b.tru, a.fls || b.fls, a.sym || b.sym, a.arr || b.arr,
    a.num.join b.num, a.str.join b.str, a.big.join b.big, a.obj.join b.obj⟩

def meet (a b : ValueSet) : ValueSet :=
  ⟨a.nul && b.nul, a.undef && b.undef, a.tru && b.tru, a.fls && b.fls, a.sym && b.sym, a.arr && b.arr,
    a.num.meet b.num, a.str.meet b.str, a.big.meet b.big, a.obj.meet b.obj⟩

def le (a b : ValueSet) : Bool :=
  (!a.nul || b.nul) && (!a.undef || b.undef) && (!a.tru || b.tru) && (!a.fls || b.fls) &&
    (!a.sym || b.sym) && (!a.arr || b.arr) && a.num.le b.num && a.str.le b.str && a.big.le b.big &&
    a.obj.le b.obj

theorem mem_isVal {V : ValueSet} {v : Tm} (h : V.mem v = true) : isVal v = true := by
  cases v <;> simp_all [mem, isVal]

@[simp] theorem mem_bot (v : Tm) : bot.mem v = false := by
  cases v <;> simp [bot, mem, Obj.mem]

theorem mem_top {v : Tm} (h : isVal v = true) : top.mem v = true := by
  cases v <;> simp_all [top, mem, isVal, Obj.mem]

theorem mem_join (a b : ValueSet) (v : Tm) : (join a b).mem v = (a.mem v || b.mem v) := by
  cases v <;> simp [join, mem, Lit.mem_join, Obj.mem_join]

theorem mem_meet (a b : ValueSet) (v : Tm) : (meet a b).mem v = (a.mem v && b.mem v) := by
  cases v <;> simp [meet, mem, Lit.mem_meet, Obj.mem_meet]

theorem le_sound {a b : ValueSet} {v : Tm} (h : le a b = true) (hv : a.mem v = true) : b.mem v = true := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hu⟩, ht⟩, hf⟩, hs⟩, har⟩, hnum⟩, hstr⟩, hbig⟩, hobj⟩ := h
  cases v with
  | nul => simp only [mem] at hv ⊢; rcases hn with h | h <;> simp_all
  | undef => simp only [mem] at hv ⊢; rcases hu with h | h <;> simp_all
  | tru => simp only [mem] at hv ⊢; rcases ht with h | h <;> simp_all
  | fls => simp only [mem] at hv ⊢; rcases hf with h | h <;> simp_all
  | sym => simp only [mem] at hv ⊢; rcases hs with h | h <;> simp_all
  | arr => simp only [mem] at hv ⊢; rcases har with h | h <;> simp_all
  | num => exact Lit.le_sound hnum hv
  | str => exact Lit.le_sound hstr hv
  | bigint => exact Lit.le_sound hbig hv
  | objAt => exact Obj.le_sound hobj hv
  | _ => simp [mem] at hv

end ValueSet

/-! ## Today's atoms -/

/-- The numbers answering a tag: exact but for an equality with a zero or a
NaN, a failed equality and truthiness, which keep every number, as
`observeAtom` does. -/
def tagNum (t : Tag) (q : Bool) : Lit UInt64 :=
  match t with
  | .numEq b => if q && (b &&& 0x7fffffffffffffff) != 0 then .these [b] else .all
  | .truthy => .all
  | t => if tagHolds t (.num 0) == q then .all else .none

theorem tagNum_mem {t : Tag} {q : Bool} {b : UInt64} (h : tagHolds t (.num b) = q) :
    (tagNum t q).mem b = true := by
  cases t
  case numEq bits =>
    simp only [tagNum]
    split
    · rename_i hb
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
      obtain ⟨rfl, hb⟩ := hb
      simp only [tagHolds, numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      rcases h.2 with h | h
      · simp [Lit.mem, h]
      · exact absurd h.2 hb
    · simp
  case truthy => simp [tagNum]
  all_goals (subst h; simp [tagNum, tagHolds, Lit.mem, Lit.all])

def tagStr (t : Tag) (q : Bool) : Lit String :=
  match t with
  | .strEq s => if q then .these [s] else .allBut [s]
  | .truthy => if q then .allBut [""] else .these [""]
  | t => if tagHolds t (.str "") == q then .all else .none

theorem tagStr_mem {t : Tag} {q : Bool} {s : String} (h : tagHolds t (.str s) = q) :
    (tagStr t q).mem s = true := by
  cases t
  case strEq x => subst h; simp only [tagStr]; by_cases e : x = s <;> simp [Lit.mem, tagHolds, e, Ne.symm]
  case truthy => subst h; simp only [tagStr]; by_cases e : s = "" <;> simp [Lit.mem, tagHolds, e]
  all_goals (subst h; simp [tagStr, tagHolds, Lit.mem, Lit.all])

def tagBig (t : Tag) (q : Bool) : Lit Int :=
  match t with
  | .bigintEq i => if q then .these [i] else .allBut [i]
  | .truthy => if q then .allBut [0] else .these [0]
  | t => if tagHolds t (.bigint 0) == q then .all else .none

theorem tagBig_mem {t : Tag} {q : Bool} {i : Int} (h : tagHolds t (.bigint i) = q) :
    (tagBig t q).mem i = true := by
  cases t
  case bigintEq x => subst h; simp only [tagBig]; by_cases e : x = i <;> simp [Lit.mem, tagHolds, e, Ne.symm]
  case truthy => subst h; simp only [tagBig]; by_cases e : i = 0 <;> simp [Lit.mem, tagHolds, e]
  all_goals (subst h; simp [tagBig, tagHolds, Lit.mem, Lit.all])

/-- The objects answering a tag: a unit clause where the answer depends on
the object, every object or none where it does not. -/
def tagObj (t : Tag) (q : Bool) : Obj :=
  match t with
  | .isRef | .isFun | .isArray | .typeofObject | .hasKey _ => some [[⟨t, q⟩]]
  | t => if tagHolds t (.objAt [] .absent 0) == q then some [] else none

theorem tagObj_mem {t : Tag} {q : Bool} {flds c oid}
    (h : tagHolds t (.objAt flds c oid) = q ∨ protoFree t (.objAt flds c oid) = false) :
    (tagObj t q).mem (.objAt flds c oid) = true := by
  cases t
  case isRef | isFun | isArray | typeofObject | hasKey =>
    simp only [tagObj, Obj.mem, List.all_cons, List.all_nil, Clause.sat, List.any_cons, List.any_nil,
      Literal.sat, Bool.and_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact h
  all_goals
    have h := h.resolve_right (by simp [protoFree])
    subst h
    simp [tagObj, tagHolds, Obj.mem]

/-- The values answering `t` with `q`, or reading a prototype for it. -/
def ofTag (t : Tag) (q : Bool) : ValueSet :=
  ⟨tagHolds t .nul == q, tagHolds t .undef == q, tagHolds t .tru == q, tagHolds t .fls == q,
    tagHolds t (.sym 0) == q, tagHolds t (.arr []) == q, tagNum t q, tagStr t q, tagBig t q, tagObj t q⟩

theorem ofTag_holds {t : Tag} {q : Bool} {v : Tm} (hv : isVal v = true)
    (hq : tagHolds t v = q ∨ protoFree t v = false) : (ofTag t q).mem v = true := by
  cases v with
  | objAt flds c oid => exact tagObj_mem hq
  | _ =>
    simp only [isVal] at hv
    all_goals first
      | contradiction
      | (have hq := hq.resolve_right (by cases t <;> simp [protoFree])
         simp only [ofTag, ValueSet.mem]
         first
           | exact tagNum_mem hq
           | exact tagStr_mem hq
           | exact tagBig_mem hq
           | (subst hq; cases t <;> simp [tagHolds]))

/-- The set an atom denotes. -/
def ofAtom : Atom → ValueSet
  | .nul => { nul := true }
  | .undef => { undef := true }
  | .tru => { tru := true }
  | .fls => { fls := true }
  | .num => { num := .all }
  | .numLit b => { num := .these [b] }
  | .str => { str := .all }
  | .strLit s => { str := .these [s] }
  | .defined => { ValueSet.top with undef := false }
  | .nonNull => { ValueSet.top with nul := false }
  | .nonNullish => { ValueSet.top with nul := false, undef := false }
  | .tag t q => ofTag t q

theorem ofAtom_holds {a : Atom} {v : Tm} (h : a.holds v) : (ofAtom a).mem v = true := by
  cases a
  case tag t q => exact ofTag_holds h.1 h.2
  all_goals
    simp only [Atom.holds] at h
    first
      | (subst h; simp [ofAtom, ValueSet.mem, Lit.mem])
      | (obtain ⟨_, rfl⟩ := h; rfl)
      | (obtain ⟨hv, hn⟩ := h; cases v <;> simp_all [ofAtom, ValueSet.mem, ValueSet.top, isVal, Obj.mem])
      | (obtain ⟨hv, hn, hu⟩ := h; cases v <;> simp_all [ofAtom, ValueSet.mem, ValueSet.top, isVal, Obj.mem])

/-- Every atom but a tag answer denotes exactly its set. -/
theorem holds_ofAtom {a : Atom} {v : Tm} (ht : a.isTag = false) (h : (ofAtom a).mem v = true) :
    a.holds v := by
  cases a
  case tag => simp [Atom.isTag] at ht
  all_goals cases v <;> simp_all [ofAtom, ValueSet.mem, ValueSet.top, isVal, Obj.mem, Atom.holds,
    Lit.mem, Lit.none, Lit.all]

/-- A union whose literal lists are appended without removing repeats:
linear, where the union removing them is quadratic. -/
def Lit.append {α : Type} [DecidableEq α] : Lit α → Lit α → Lit α
  | .these a, .these b => .these (a ++ b)
  | l, m => l.join m

theorem Lit.mem_append {α : Type} [DecidableEq α] (l m : Lit α) (x : α) :
    (l.append m).mem x = (l.mem x || m.mem x) := by
  cases l <;> cases m <;> simp only [Lit.append, Lit.mem_join] <;> simp [Lit.mem]

def ValueSet.append (a b : ValueSet) : ValueSet :=
  ⟨a.nul || b.nul, a.undef || b.undef, a.tru || b.tru, a.fls || b.fls, a.sym || b.sym, a.arr || b.arr,
    a.num.append b.num, a.str.append b.str, a.big.append b.big, a.obj.join b.obj⟩

theorem ValueSet.mem_append (a b : ValueSet) (v : Tm) : (a.append b).mem v = (a.mem v || b.mem v) := by
  cases v <;> simp [ValueSet.append, ValueSet.mem, Lit.mem_append, Obj.mem_join]

/-- A list of atoms denotes the union of their sets. -/
def ofAtoms (as : List Atom) : ValueSet := as.foldr (fun a V => (ofAtom a).append V) ValueSet.bot

theorem ofAtoms_holds {as : List Atom} {v : Tm} (h : ∃ a ∈ as, a.holds v) : (ofAtoms as).mem v = true := by
  induction as with
  | nil => simp at h
  | cons a as ih =>
    simp only [ofAtoms, List.foldr_cons, ValueSet.mem_append, Bool.or_eq_true] at ih ⊢
    obtain ⟨b, hb, hv⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl (ofAtom_holds hv)
    · exact Or.inr (ih ⟨b, hb, hv⟩)

theorem holds_ofAtoms {as : List Atom} {v : Tm} (ht : as.all (!·.isTag) = true)
    (h : (ofAtoms as).mem v = true) : ∃ a ∈ as, a.holds v := by
  induction as with
  | nil => simp [ofAtoms] at h
  | cons a as ih =>
    simp only [ofAtoms, List.foldr_cons, ValueSet.mem_append, Bool.or_eq_true] at ih h
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at ht
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self .., holds_ofAtom ht.1 h⟩
    · obtain ⟨b, hb, hv⟩ := ih ht.2 h
      exact ⟨b, List.mem_cons_of_mem _ hb, hv⟩

/-! ## The normal form (heap-knowledge draft, §2.5) -/

namespace Lit
variable {α : Type} [LT α] [DecidableLT α] [StrictTotal α] [DecidableEq α]

/-- A literal component restricted to its context's component, then
encoded: under a finite context, the shorter of the literals kept and the
literals excluded (the kept ones on a tie), every literal where all are
kept; otherwise the literals, or every literal but the excluded ones not
already excluded by the context. -/
def normIn (c v : Lit α) : Lit α :=
  match c, v with
  | these f, v =>
    let keep := canon (f.filter v.mem)
    let drop := canon (f.filter (!v.mem ·))
    if drop = [] then all else if drop.length < keep.length then allBut drop else these keep
  | allBut g, these p => these (canon (p.filter (!g.contains ·)))
  | allBut g, allBut a => allBut (canon (a.filter (!g.contains ·)))

omit [StrictTotal α] in
theorem normIn_mem {c v : Lit α} {x : α} (hc : c.mem x = true) : (normIn c v).mem x = v.mem x := by
  cases c with
  | these f =>
    have hf : x ∈ f := by simpa [mem] using hc
    simp only [normIn]
    split
    · rename_i hd
      have : (!v.mem x) = false := by
        cases h : v.mem x
        · have : x ∈ canon (f.filter (!v.mem ·)) := mem_canon.mpr (List.mem_filter.mpr ⟨hf, by simp [h]⟩)
          simp [hd] at this
        · rfl
      simpa using this
    · split
      all_goals cases h : v.mem x <;> simp [mem_these, mem_allBut, mem_canon, List.mem_filter, hf, h]
  | allBut g =>
    have hg : g.contains x = false := by simpa [mem] using hc
    cases v <;> simp [normIn, mem, mem_canon, List.mem_filter] <;> simp_all

/-- Under a finite context, the normal form depends only on the contextual
set. -/
theorem normIn_these_congr {f : List α} {v w : Lit α}
    (h : ∀ x, x ∈ f → v.mem x = w.mem x) : normIn (these f) v = normIn (these f) w := by
  have hk : canon (f.filter v.mem) = canon (f.filter w.mem) :=
    canon_eq fun x => by simp only [List.mem_filter]; constructor <;> intro ⟨hx, hm⟩ <;> simp_all
  have hd : canon (f.filter (!v.mem ·)) = canon (f.filter (!w.mem ·)) :=
    canon_eq fun x => by simp only [List.mem_filter]; constructor <;> intro ⟨hx, hm⟩ <;> simp_all
  simp only [normIn, hk, hd]

/-- Under a cofinite context, two literal sets of one form with one
contextual set have one normal form. -/
theorem normIn_allBut_congr {g : List α} {v w : Lit α}
    (hform : (∃ p q, v = these p ∧ w = these q) ∨ (∃ a b, v = allBut a ∧ w = allBut b))
    (h : ∀ x, g.contains x = false → v.mem x = w.mem x) :
    normIn (allBut g) v = normIn (allBut g) w := by
  rcases hform with ⟨p, q, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩
  · simp only [normIn]
    congr 1
    exact canon_eq fun x => by
      have := h x
      cases hg : g.contains x <;> simp_all [mem_these, List.mem_filter]
  · simp only [normIn]
    congr 1
    exact canon_eq fun x => by
      have := h x
      cases hg : g.contains x <;> simp_all [mem_allBut, List.mem_filter]

/-- In an infinite universe, a finite and a cofinite set are distinct, so
two literal sets with one contextual set have one normal form. -/
theorem normIn_congr (inf : ∀ l : List α, ∃ x, x ∉ l) {c v w : Lit α}
    (h : ∀ x, c.mem x = true → v.mem x = w.mem x) : normIn c v = normIn c w := by
  cases c with
  | these f => exact normIn_these_congr fun x hx => h x (by simpa [mem_these] using hx)
  | allBut g =>
    have h' : ∀ x, g.contains x = false → v.mem x = w.mem x := fun x hx => h x (by
      simp only [mem_allBut, Bool.not_eq_true']; exact hx)
    cases v with
    | these p =>
      cases w with
      | these q => exact normIn_allBut_congr (Or.inl ⟨p, q, rfl, rfl⟩) h'
      | allBut b =>
        obtain ⟨x, hx⟩ := inf (p ++ b ++ g)
        have := h' x (by simpa using fun m => hx (by simp [m]))
        simp only [mem_these, mem_allBut] at this
        have hp : x ∉ p := fun m => hx (by simp [m])
        have hb : x ∉ b := fun m => hx (by simp [m])
        simp [hp, hb] at this
    | allBut a =>
      cases w with
      | these q =>
        obtain ⟨x, hx⟩ := inf (q ++ a ++ g)
        have := h' x (by simpa using fun m => hx (by simp [m]))
        simp only [mem_these, mem_allBut] at this
        have hq : x ∉ q := fun m => hx (by simp [m])
        have ha : x ∉ a := fun m => hx (by simp [m])
        simp [hq, ha] at this
      | allBut b => exact normIn_allBut_congr (Or.inr ⟨a, b, rfl, rfl⟩) h'

theorem normIn_idem (c v : Lit α) : normIn c (normIn c v) = normIn c v := by
  cases c with
  | these f => exact normIn_these_congr fun x hx => normIn_mem (by simpa [mem_these] using hx)
  | allBut g =>
    apply normIn_allBut_congr ?_ fun x hx => normIn_mem (by simp only [mem_allBut, hx]; rfl)
    cases v <;> simp [normIn]

end Lit

/-! ### Objects -/

/-- A clause holding a tag answer and its opposite holds of every value. -/
def Clause.taut (c : Clause) : Bool := c.any fun l => c.contains ⟨l.tag, !l.answer⟩

def Clause.sub (c d : Clause) : Bool := c.all d.contains

/-- Two unit clauses with opposite answers of a tag that reads no
prototype: no value meets both. -/
def contradicts (cs : List Clause) : Bool :=
  cs.any fun c => match c with
    | [l] => (match l.tag with | .hasKey _ => false | _ => true) && cs.contains [⟨l.tag, !l.answer⟩]
    | _ => false

/-- The clauses no other clause is strictly included in. -/
def minimal (cs : List Clause) : List Clause :=
  cs.filter fun c => !cs.any fun d => d.sub c && !c.sub d

/-- An object component's normal form: each clause sorted, tautologies
removed, *none* where a clause is empty or two unit clauses contradict, the
minimal clauses, sorted. -/
def objNorm : Obj → Obj
  | none => none
  | some cs =>
    let cs := (cs.map canon).filter (fun c => !Clause.taut c)
    if cs.any (·.isEmpty) then none
    else
      let m := minimal cs
      if contradicts m then none else some (canon m)

theorem Clause.sat_of_mem_iff {c d : Clause} {v : Tm} (h : ∀ l, l ∈ c ↔ l ∈ d) :
    Clause.sat v c = Clause.sat v d := by
  apply Bool.eq_iff_iff.mpr
  simp only [Clause.sat, List.any_eq_true]
  exact ⟨fun ⟨l, hl, hs⟩ => ⟨l, (h l).mp hl, hs⟩, fun ⟨l, hl, hs⟩ => ⟨l, (h l).mpr hl, hs⟩⟩

theorem Clause.sat_canon (c : Clause) (v : Tm) : Clause.sat v (canon c) = Clause.sat v c :=
  Clause.sat_of_mem_iff fun _ => mem_canon

theorem Clause.taut_sat {c : Clause} {v : Tm} (h : c.taut = true) : Clause.sat v c = true := by
  simp only [Clause.taut, List.any_eq_true, List.contains_iff_mem] at h
  obtain ⟨l, hl, hn⟩ := h
  simp only [Clause.sat, List.any_eq_true]
  by_cases e : (tagHolds l.tag v == l.answer || !protoFree l.tag v) = true
  · exact ⟨l, hl, e⟩
  · refine ⟨⟨l.tag, !l.answer⟩, hn, ?_⟩
    simp only [Literal.sat]
    cases ha : l.answer <;> cases ht : tagHolds l.tag v <;> cases hp : protoFree l.tag v <;> simp_all

theorem Clause.sat_sub {c d : Clause} {v : Tm} (h : c.sub d = true) (hc : Clause.sat v c = true) :
    Clause.sat v d = true := by
  simp only [Clause.sub, List.all_eq_true, List.contains_iff_mem] at h
  simp only [Clause.sat, List.any_eq_true] at hc ⊢
  obtain ⟨l, hl, hs⟩ := hc
  exact ⟨l, h l hl, hs⟩

theorem Clause.sub_refl (c : Clause) : c.sub c = true := by
  simp [Clause.sub]

theorem Clause.sub_trans {c d e : Clause} (h₁ : c.sub d = true) (h₂ : d.sub e = true) : c.sub e = true := by
  simp only [Clause.sub, List.all_eq_true, List.contains_iff_mem] at h₁ h₂ ⊢
  exact fun l hl => h₂ l (h₁ l hl)

theorem length_filter_lt {α : Type} {l : List α} {p q : α → Bool} (hpq : ∀ x ∈ l, p x = true → q x = true)
    (hx : ∃ x ∈ l, q x = true ∧ p x = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    have hle : ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length := by
      intro l h
      induction l with
      | nil => simp
      | cons b l ih' =>
        have := ih' fun x hx => h x (List.mem_cons_of_mem _ hx)
        simp only [List.filter_cons]
        cases hp : p b <;> cases hq : q b <;> simp_all <;> omega
    obtain ⟨x, hxl, hq, hp⟩ := hx
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hxl with rfl | hxl
    · have := hle l fun y hy => hpq y (List.mem_cons_of_mem _ hy)
      simp only [hp, hq]; simp; omega
    · have := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy)) ⟨x, hxl, hq, hp⟩
      cases hpa : p x <;> cases hpb : p a <;> cases hqa : q a <;> simp_all <;> omega

/-- Every clause is implied by the minimal ones: a non-minimal clause
strictly includes another, which fewer clauses are included in. -/
theorem minimal_sat {cs : List Clause} {v : Tm}
    (h : ∀ c ∈ minimal cs, Clause.sat v c = true) : ∀ c ∈ cs, Clause.sat v c = true := by
  suffices ∀ n, ∀ c ∈ cs, (cs.filter (·.sub c)).length ≤ n → Clause.sat v c = true from
    fun c hc => this _ c hc (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro c hc hn
    have : c ∈ cs.filter (·.sub c) := List.mem_filter.mpr ⟨hc, Clause.sub_refl c⟩
    have := List.length_pos_of_mem this
    omega
  | succ n ih =>
    intro c hc hn
    by_cases hm : c ∈ minimal cs
    · exact h c hm
    · simp only [minimal, List.mem_filter, hc, true_and, Bool.not_eq_true', Bool.not_eq_false,
        List.any_eq_true, Bool.and_eq_true] at hm
      obtain ⟨d, hd, hdc, hcd⟩ := hm
      have hlt : (cs.filter (·.sub d)).length < (cs.filter (·.sub c)).length :=
        length_filter_lt (fun e _ he => Clause.sub_trans he hdc) ⟨c, hc, Clause.sub_refl c, by simpa using hcd⟩
      exact Clause.sat_sub hdc (ih d hd (by omega))

theorem all_sat_of_mem_iff {cs ds : List Clause} {v : Tm} (h : ∀ c, c ∈ cs ↔ c ∈ ds) :
    cs.all (Clause.sat v) = ds.all (Clause.sat v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun hc c hd => hc c ((h c).mpr hd), fun hd c hc => hd c ((h c).mp hc)⟩

theorem contradicts_unsat {m : List Clause} {v : Tm} (h : contradicts m = true) :
    m.all (Clause.sat v) = false := by
  simp only [contradicts, List.any_eq_true] at h
  obtain ⟨c, hc, hcon⟩ := h
  match c, hcon with
  | [l], hcon =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hcon
    obtain ⟨hk, hm⟩ := hcon
    have hp : protoFree l.tag v = true := by
      cases ht : l.tag <;> simp_all [protoFree]
    cases hall : m.all (Clause.sat v)
    · rfl
    · have h₁ := List.all_eq_true.mp hall _ hc
      have h₂ := List.all_eq_true.mp hall _ hm
      simp only [Clause.sat, List.any_cons, List.any_nil, Bool.or_false, Literal.sat, hp,
        Bool.not_true] at h₁ h₂
      cases ha : l.answer <;> cases ht : tagHolds l.tag v <;> simp_all

theorem objNorm_mem (o : Obj) (v : Tm) : (objNorm o).mem v = o.mem v := by
  cases o with
  | none => rfl
  | some cs =>
    -- Sorting each clause and removing tautologies keeps the conjunction.
    have h₁ : ((cs.map canon).filter (fun c => !Clause.taut c)).all (Clause.sat v) = cs.all (Clause.sat v) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_filter, List.mem_map, Bool.not_eq_true']
      constructor
      · intro h c hc
        by_cases ht : Clause.taut (canon c) = true
        · rw [← Clause.sat_canon]; exact Clause.taut_sat ht
        · rw [← Clause.sat_canon]; exact h _ ⟨⟨c, hc, rfl⟩, by simpa using ht⟩
      · rintro h _ ⟨⟨c, hc, rfl⟩, _⟩
        rw [Clause.sat_canon]; exact h c hc
    simp only [objNorm]
    generalize (cs.map canon).filter (fun c => !Clause.taut c) = ds at h₁ ⊢
    simp only [Obj.mem, ← h₁]
    by_cases he : (ds.any fun x => x.isEmpty) = true
    · rw [if_pos he]
      obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp he
      have : c = [] := by simpa using hce
      subst this
      symm
      apply Bool.eq_false_iff.mpr
      intro hall
      have := List.all_eq_true.mp hall [] hc
      simp [Clause.sat] at this
    · rw [if_neg he]
      have hm : (minimal ds).all (Clause.sat v) = ds.all (Clause.sat v) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true]
        exact ⟨fun h => minimal_sat h, fun h c hc => h c (List.mem_filter.mp hc).1⟩
      by_cases hcon : contradicts (minimal ds) = true
      · rw [if_pos hcon, ← hm, contradicts_unsat hcon]
      · rw [if_neg hcon]
        show (canon (minimal ds)).all (Clause.sat v) = _
        rw [all_sat_of_mem_iff fun _ => mem_canon, hm]

theorem minimal_congr {cs ds : List Clause} (h : ∀ c, c ∈ cs ↔ c ∈ ds) :
    ∀ c, c ∈ minimal cs ↔ c ∈ minimal ds := by
  intro c
  simp only [minimal, List.mem_filter, h c]
  have : (cs.any fun d => d.sub c && !c.sub d) = (ds.any fun d => d.sub c && !c.sub d) := by
    apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
    exact ⟨fun ⟨d, hd, e⟩ => ⟨d, (h d).mp hd, e⟩, fun ⟨d, hd, e⟩ => ⟨d, (h d).mpr hd, e⟩⟩
  rw [this]

theorem contradicts_congr {cs ds : List Clause} (h : ∀ c, c ∈ cs ↔ c ∈ ds) :
    contradicts cs = contradicts ds := by
  apply Bool.eq_iff_iff.mpr
  simp only [contradicts, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, e⟩; refine ⟨c, (h c).mp hc, ?_⟩
    split at e <;> simp_all
  · rintro ⟨c, hc, e⟩; refine ⟨c, (h c).mpr hc, ?_⟩
    split at e <;> simp_all

theorem objNorm_idem (o : Obj) : objNorm (objNorm o) = objNorm o := by
  cases o with
  | none => rfl
  | some cs =>
    simp only [objNorm]
    generalize hds : (cs.map canon).filter (fun c => !Clause.taut c) = ds
    by_cases he : (ds.any fun x => x.isEmpty) = true
    · simp only [if_pos he]
    · simp only [if_neg he]
      by_cases hcon : contradicts (minimal ds) = true
      · simp only [if_pos hcon]
      · simp only [if_neg hcon]
        -- Every clause kept is in `ds`: sorted, no tautology, not empty, and minimal there.
        have hin : ∀ c ∈ canon (minimal ds), c ∈ ds ∧ c ∈ minimal ds := fun c hc =>
          ⟨(List.mem_filter.mp (mem_canon.mp hc)).1, mem_canon.mp hc⟩
        have hds' : ∀ c ∈ ds, canon c = c ∧ Clause.taut c = false := fun c hc => by
          rw [← hds] at hc
          obtain ⟨hc, ht⟩ := List.mem_filter.mp hc
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
          exact ⟨canon_canon d, by simpa using ht⟩
        generalize hM : canon (minimal ds) = M at hin ⊢
        have hmap : M.map canon = M := by
          conv => rhs; rw [← List.map_id M]
          exact List.map_congr_left fun c hc => (hds' c (hin c hc).1).1
        have hfil : M.filter (fun c => !Clause.taut c) = M :=
          List.filter_eq_self.mpr fun c hc => by simp [(hds' c (hin c hc).1).2]
        have hemp : (M.any fun x => x.isEmpty) = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          obtain ⟨c, hc, e⟩ := List.any_eq_true.mp h
          exact he (List.any_eq_true.mpr ⟨c, (hin c hc).1, e⟩)
        -- No clause of `M` strictly includes another, since none of `ds` does.
        have hmin : minimal M = M := by
          apply List.filter_eq_self.mpr
          intro c hc
          have hcm := (hin c hc).2
          simp only [minimal, List.mem_filter] at hcm
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
          apply Bool.eq_false_iff.mpr
          intro h
          obtain ⟨d, hd, e⟩ := List.any_eq_true.mp h
          have := hcm.2
          simp only [Bool.not_eq_true', Bool.eq_false_iff] at this
          exact this (List.any_eq_true.mpr ⟨d, (hin d hd).1, e⟩)
        have hsame : ∀ c, c ∈ M ↔ c ∈ minimal ds := fun c => by rw [← hM, mem_canon]
        simp only [hmap, hfil, hemp, hmin, contradicts_congr hsame, hcon, Bool.false_eq_true,
          ite_false]
        rw [← hM, canon_canon]

/-- Law 1: the normal form depends on the clauses' members alone, so the
order of literals and clauses and their repetitions do not change it. -/
theorem objNorm_congr {cs cs' : List Clause} (h : ∀ c, c ∈ cs.map canon ↔ c ∈ cs'.map canon) :
    objNorm (some cs) = objNorm (some cs') := by
  simp only [objNorm]
  have hd : ∀ c, c ∈ (cs.map canon).filter (fun c => !Clause.taut c) ↔
      c ∈ (cs'.map canon).filter (fun c => !Clause.taut c) := fun c => by
    simp only [List.mem_filter, h c]
  generalize (cs.map canon).filter (fun c => !Clause.taut c) = ds at hd ⊢
  generalize (cs'.map canon).filter (fun c => !Clause.taut c) = ds' at hd ⊢
  have he : (ds.any fun x => x.isEmpty) = (ds'.any fun x => x.isEmpty) := by
    apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
    exact ⟨fun ⟨c, hc, e⟩ => ⟨c, (hd c).mp hc, e⟩, fun ⟨c, hc, e⟩ => ⟨c, (hd c).mpr hc, e⟩⟩
  have hm := minimal_congr hd
  rw [he, contradicts_congr hm, canon_eq hm]

/-- Law 3: a clause including another changes nothing. -/
theorem objNorm_absorb {cs : List Clause} {c d : Clause} (hd : d ∈ cs) (hdc : Clause.sub d c = true) :
    objNorm (some (cs ++ [c])) = objNorm (some cs) := by
  have hsub : Clause.sub (canon d) (canon c) = true := by
    simp only [Clause.sub, List.all_eq_true, List.contains_iff_mem] at hdc ⊢
    exact fun l hl => mem_canon.mpr (hdc l (mem_canon.mp hl))
  -- A tautology's inclusions are tautologies.
  have htaut : Clause.taut (canon d) = true → Clause.taut (canon c) = true := by
    simp only [Clause.taut, List.any_eq_true, List.contains_iff_mem]
    simp only [Clause.sub, List.all_eq_true, List.contains_iff_mem] at hsub
    exact fun ⟨l, hl, hn⟩ => ⟨l, hsub l hl, hsub _ hn⟩
  simp only [objNorm, List.map_append, List.map_cons, List.map_nil, List.filter_append]
  by_cases ht : Clause.taut (canon c) = true
  · simp [ht]
  · simp only [List.filter_cons, ht, Bool.not_false, ite_true, List.filter_nil]
    have hdt : Clause.taut (canon d) = false := by
      cases e : Clause.taut (canon d)
      · rfl
      · exact absurd (htaut e) ht
    have hdin : canon d ∈ (cs.map canon).filter (fun c => !Clause.taut c) :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨d, hd, rfl⟩, by simp [hdt]⟩
    generalize (cs.map canon).filter (fun c => !Clause.taut c) = ds at hdin ⊢
    generalize hc' : canon c = c' at hsub ht
    generalize hd' : canon d = d' at hsub hdin
    -- An empty `c'` includes only an empty `d'`, already in `ds`.
    have he : ((ds ++ [c']).any fun x => x.isEmpty) = (ds.any fun x => x.isEmpty) := by
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      cases ec : c'.isEmpty
      · simp
      · have : d'.isEmpty = true := by
          simp only [List.isEmpty_iff] at ec ⊢
          subst ec
          simp only [Clause.sub, List.all_eq_true, List.contains_iff_mem] at hsub
          cases d' with
          | nil => rfl
          | cons l _ => exact absurd (hsub l (List.mem_cons_self ..)) (by simp)
        simp [List.any_eq_true.mpr ⟨d', hdin, this⟩]
    rw [he]
    -- The minimal clauses keep their members.
    have hm : ∀ e, e ∈ minimal (ds ++ [c']) ↔ e ∈ minimal ds := by
      intro e
      simp only [minimal, List.mem_filter, List.mem_append, List.mem_singleton, List.any_append,
        List.any_cons, List.any_nil, Bool.or_false, Bool.not_or, Bool.and_eq_true,
        Bool.not_eq_true']
      constructor
      · rintro ⟨he | rfl, hn, hc⟩
        · exact ⟨he, hn⟩
        · -- `c'` minimal: `d'` is not strictly in it, so they have one set of
          -- literals and, both sorted, are equal.
          refine ⟨?_, hn⟩
          have hcd : Clause.sub e d' = true := by
            cases h : Clause.sub e d'
            · have hw : (ds.any fun d => Clause.sub d e && !Clause.sub e d) = true :=
                List.any_eq_true.mpr ⟨d', hdin, by rw [hsub, h]; rfl⟩
              rw [hn] at hw
              exact absurd hw Bool.false_ne_true
            · rfl
          have : e = d' := by
            rw [← hc', ← hd']
            apply canon_eq
            intro l
            have h₁ := List.all_eq_true.mp hcd
            have h₂ := List.all_eq_true.mp hsub
            constructor
            · intro hl
              have hle : l ∈ e := hc' ▸ mem_canon.mpr hl
              exact mem_canon.mp (hd' ▸ List.contains_iff_mem.mp (h₁ l hle))
            · intro hl
              have hld : l ∈ d' := hd' ▸ mem_canon.mpr hl
              exact mem_canon.mp (hc' ▸ List.contains_iff_mem.mp (h₂ l hld))
          exact this ▸ hdin
      · rintro ⟨he, hn⟩
        refine ⟨Or.inl he, hn, ?_⟩
        -- Were `c'` strictly in `e`, so would `d'` be, and `e` would not be minimal.
        cases h₁ : Clause.sub c' e
        · rfl
        · cases h₂ : Clause.sub e c'
          · have hde : Clause.sub d' e = true := Clause.sub_trans hsub h₁
            have hed : Clause.sub e d' = false := by
              cases h₃ : Clause.sub e d'
              · rfl
              · exact absurd (Clause.sub_trans h₃ hsub) (by simp [h₂])
            have hw : (ds.any fun d => Clause.sub d e && !Clause.sub e d) = true :=
              List.any_eq_true.mpr ⟨d', hdin, by rw [hde, hed]; rfl⟩
            rw [hn] at hw
            exact absurd hw Bool.false_ne_true
          · rfl
    rw [contradicts_congr hm, canon_eq hm]

/-! ### Value sets -/

namespace ValueSet

/-- A value set at a context `C`: each component restricted to `C`'s and
in its normal form (heap-knowledge draft, §2.5). -/
def normIn (C V : ValueSet) : ValueSet :=
  ⟨V.nul && C.nul, V.undef && C.undef, V.tru && C.tru, V.fls && C.fls, V.sym && C.sym, V.arr && C.arr,
    C.num.normIn V.num, C.str.normIn V.str, C.big.normIn V.big,
    match C.obj with | none => none | some _ => objNorm V.obj⟩

/-- At its context, the normal form holds of a value exactly where the value set does. -/
theorem normIn_mem {C V : ValueSet} {v : Tm} (hc : C.mem v = true) : (normIn C V).mem v = V.mem v := by
  cases v <;> simp only [mem] at hc ⊢ <;> simp only [normIn, hc, Bool.and_true]
  · exact Lit.normIn_mem hc
  · exact Lit.normIn_mem hc
  · exact Lit.normIn_mem hc
  · cases ho : C.obj with
    | none => simp [ho, Obj.mem] at hc
    | some _ => exact objNorm_mem _ _

theorem normIn_idem (C V : ValueSet) : normIn C (normIn C V) = normIn C V := by
  simp only [normIn, Bool.and_assoc, Bool.and_self, Lit.normIn_idem]
  cases C.obj <;> simp [objNorm_idem]

/-- Widening at a merge (heap-knowledge draft, §2.3): the object component
in its normal form, keeping at most 8 clauses. Fewer clauses admit more
objects, so the widened set holds wherever the set does. -/
def widen (V : ValueSet) : ValueSet :=
  { V with obj := (objNorm V.obj).map (·.take 8) }

theorem widen_mem {V : ValueSet} {v : Tm} (h : V.mem v = true) : V.widen.mem v = true := by
  cases v <;> simp only [mem, widen] at h ⊢ <;> try exact h
  rename_i flds c oid
  have hn : (objNorm V.obj).mem (.objAt flds c oid) = true := by rw [objNorm_mem]; exact h
  cases ho : objNorm V.obj with
  | none => rw [ho] at hn; cases hn
  | some cs =>
    rw [ho] at hn
    simp only [Option.map_some, Obj.mem, List.all_eq_true] at hn ⊢
    exact fun c hc => hn c (List.mem_of_mem_take hc)

end ValueSet

theorem le_sum_of_mem {l : List Nat} {n : Nat} (h : n ∈ l) : n ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp; omega

/-- Strings form an infinite universe: one longer than every listed string
is not listed. -/
theorem string_fresh (l : List String) : ∃ x, x ∉ l := by
  refine ⟨String.ofList (List.replicate ((l.map String.length).sum + 1) 'a'), fun h => ?_⟩
  have hle : ∀ s ∈ l, s.length ≤ (l.map String.length).sum := fun s hs =>
    le_sum_of_mem (List.mem_map.mpr ⟨s, hs, rfl⟩)
  have := hle _ h
  simp at this
  omega

theorem int_fresh (l : List Int) : ∃ x, x ∉ l := by
  refine ⟨(l.map Int.natAbs).sum + 1, fun h => ?_⟩
  have : ((l.map Int.natAbs).sum + 1 : Int).natAbs ≤ (l.map Int.natAbs).sum :=
    le_sum_of_mem (List.mem_map.mpr ⟨_, h, rfl⟩)
  omega

/-- **Unique**: value sets holding of the same values at their context have
one normal form there, given that numbers, a finite universe, are under a
finite context or in one form, and objects have one normal form of their
clauses (laws 1–5 relate them: `objNorm_congr`, `objNorm_absorb`). -/
theorem ValueSet.normIn_congr {C V W : ValueSet} (h : ∀ v, C.mem v = true → V.mem v = W.mem v)
    (hnum : (∃ f, C.num = .these f) ∨ (∃ p q, V.num = .these p ∧ W.num = .these q) ∨
      (∃ a b, V.num = .allBut a ∧ W.num = .allBut b))
    (hobj : C.obj = none ∨ objNorm V.obj = objNorm W.obj) : ValueSet.normIn C V = ValueSet.normIn C W := by
  have flag : ∀ {t : Tm} {c x y : Bool}, C.mem t = c → V.mem t = x → W.mem t = y → (x && c) = (y && c) :=
    fun {t c x y} hc hx hy => by
      cases c
      · simp
      · rw [← hx, ← hy, h t hc]
  simp only [ValueSet.normIn]
  congr 1
  · exact flag (t := .nul) rfl rfl rfl
  · exact flag (t := .undef) rfl rfl rfl
  · exact flag (t := .tru) rfl rfl rfl
  · exact flag (t := .fls) rfl rfl rfl
  · exact flag (t := .sym 0) rfl rfl rfl
  · exact flag (t := .arr []) rfl rfl rfl
  · rcases hnum with ⟨f, hf⟩ | hform
    · rw [hf]; exact Lit.normIn_these_congr fun x hx => h (.num x) (by simp [ValueSet.mem, hf, Lit.mem_these, hx])
    · cases hc : C.num with
      | these f => exact Lit.normIn_these_congr fun x hx => h (.num x) (by simp [ValueSet.mem, hc, Lit.mem_these, hx])
      | allBut g => exact Lit.normIn_allBut_congr hform fun x hx => h (.num x) (by
          simp only [ValueSet.mem, hc, Lit.mem_allBut, hx]; rfl)
  · exact Lit.normIn_congr string_fresh fun x hx => h (.str x) hx
  · exact Lit.normIn_congr int_fresh fun x hx => h (.bigint x) hx
  · rcases hobj with ho | ho <;> cases hc : C.obj <;> simp_all

/-- Atoms covering a value set: each value of the set meets one. Strings
and finitely many numbers keep their literals; every other kind is covered
by its family or, for kinds no primitive atom names, by `defined`. -/
def ValueSet.atomsView (V : ValueSet) : List Atom :=
  (if V.nul then [.nul] else []) ++ (if V.undef then [.undef] else []) ++
  (if V.tru then [.tru] else []) ++ (if V.fls then [.fls] else []) ++
  (match V.num with | .these bs => bs.map .numLit | .allBut _ => [.num]) ++
  (match V.str with | .these ss => ss.map .strLit | .allBut _ => [.str]) ++
  (if V.big = .none && !V.sym && !V.arr && V.obj = none then [] else [.defined])

theorem ValueSet.atomsView_holds {V : ValueSet} {v : Tm} (h : V.mem v = true) :
    ∃ a ∈ V.atomsView, a.holds v := by
  cases v <;> simp only [ValueSet.mem] at h
  case nul => exact ⟨.nul, by simp [atomsView, h], rfl⟩
  case undef => exact ⟨.undef, by simp [atomsView, h], rfl⟩
  case tru => exact ⟨.tru, by simp [atomsView, h], rfl⟩
  case fls => exact ⟨.fls, by simp [atomsView, h], rfl⟩
  case num b =>
    cases hn : V.num with
    | these bs =>
      rw [hn] at h
      exact ⟨.numLit b, by simp [atomsView, hn]; exact Or.inl (by simpa [Lit.mem_these] using h), rfl⟩
    | allBut _ => exact ⟨.num, by simp [atomsView, hn], b, rfl⟩
  case str s =>
    cases hs : V.str with
    | these ss =>
      rw [hs] at h
      exact ⟨.strLit s, by simp [atomsView, hs]; exact Or.inr (by simpa [Lit.mem_these] using h), rfl⟩
    | allBut _ => exact ⟨.str, by simp [atomsView, hs], s, rfl⟩
  all_goals first
    | contradiction
    | (refine ⟨.defined, ?_, by simp [Atom.holds, isVal]⟩
       simp only [atomsView, List.mem_append]
       right
       split
       · rename_i e
         simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at e
         simp_all [Obj.mem, Lit.mem_none]
       · simp)

/-- Whether a tag's answer is one on every number (string, bigint): every
tag but the literal equalities and truthiness. -/
def numConst : Tag → Bool | .numEq _ | .truthy => false | _ => true
def strConst : Tag → Bool | .strEq _ | .truthy => false | _ => true
def bigConst : Tag → Bool | .bigintEq _ | .truthy => false | _ => true

/-- The tags whose answer on an object depends on the object. -/
def objTag : Tag → Bool | .isRef | .isFun | .isArray | .typeofObject | .hasKey _ => true | _ => false

def numAnswers (t : Tag) (q : Bool) : Lit UInt64 → Bool
  | .these bs => bs.all fun b => tagHolds t (.num b) == q
  | .allBut _ => numConst t && tagHolds t (.num 0) == q

def strAnswers (t : Tag) (q : Bool) : Lit String → Bool
  | .these ss => ss.all fun x => tagHolds t (.str x) == q
  | .allBut _ => strConst t && tagHolds t (.str "") == q

def bigAnswers (t : Tag) (q : Bool) : Lit Int → Bool
  | .these is => is.all fun i => tagHolds t (.bigint i) == q
  | .allBut _ => bigConst t && tagHolds t (.bigint 0) == q

def objAnswers (t : Tag) (q : Bool) : Obj → Bool
  | none => true
  | some cs => if objTag t then cs.contains [⟨t, q⟩] else tagHolds t (.objAt [] .absent 0) == q

theorem numAnswers_sound {t q l b} (h : numAnswers t q l = true) (hb : l.mem b = true) :
    tagHolds t (.num b) = q := by
  cases l with
  | these bs => simpa using List.all_eq_true.mp h b (by simpa [Lit.mem_these] using hb)
  | allBut _ =>
    simp only [numAnswers, Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.2]; cases t <;> simp_all [tagHolds, numConst]

theorem strAnswers_sound {t q l x} (h : strAnswers t q l = true) (hx : l.mem x = true) :
    tagHolds t (.str x) = q := by
  cases l with
  | these ss => simpa using List.all_eq_true.mp h x (by simpa [Lit.mem_these] using hx)
  | allBut _ =>
    simp only [strAnswers, Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.2]; cases t <;> simp_all [tagHolds, strConst]

theorem bigAnswers_sound {t q l i} (h : bigAnswers t q l = true) (hi : l.mem i = true) :
    tagHolds t (.bigint i) = q := by
  cases l with
  | these is => simpa using List.all_eq_true.mp h i (by simpa [Lit.mem_these] using hi)
  | allBut _ =>
    simp only [bigAnswers, Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.2]; cases t <;> simp_all [tagHolds, bigConst]

theorem objAnswers_sound {t q o flds c oid} (h : objAnswers t q o = true)
    (hv : o.mem (.objAt flds c oid) = true) :
    tagHolds t (.objAt flds c oid) = q ∨ protoFree t (.objAt flds c oid) = false := by
  cases o with
  | none => simp [Obj.mem] at hv
  | some cs =>
    simp only [objAnswers] at h
    split at h
    · have hc := List.all_eq_true.mp hv _ (List.contains_iff_mem.mp h)
      simpa [Clause.sat, Literal.sat] using hc
    · left
      rename_i ho
      simp only [beq_iff_eq] at h
      rw [← h]; cases t <;> simp_all [tagHolds, objTag]

/-- Whether every value of the set answers `t` with `q`, or reads a
prototype for it. -/
def ValueSet.answers (V : ValueSet) (t : Tag) (q : Bool) : Bool :=
  (!V.nul || tagHolds t .nul == q) && (!V.undef || tagHolds t .undef == q) &&
  (!V.tru || tagHolds t .tru == q) && (!V.fls || tagHolds t .fls == q) &&
  (!V.sym || tagHolds t (.sym 0) == q) && (!V.arr || tagHolds t (.arr []) == q) &&
  numAnswers t q V.num && strAnswers t q V.str && bigAnswers t q V.big && objAnswers t q V.obj

theorem ValueSet.answers_sound {V : ValueSet} {t : Tag} {q : Bool} {v : Tm} (h : V.answers t q = true)
    (hv : V.mem v = true) : tagHolds t v = q ∨ protoFree t v = false := by
  simp only [answers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hu⟩, ht⟩, hf⟩, hs⟩, ha⟩, hnum⟩, hstr⟩, hbig⟩, hobj⟩ := h
  cases v with
  | objAt flds c oid => exact objAnswers_sound hobj hv
  | num b => exact Or.inl (numAnswers_sound hnum hv)
  | str x => exact Or.inl (strAnswers_sound hstr hv)
  | bigint i => exact Or.inl (bigAnswers_sound hbig hv)
  | nul => simp only [mem] at hv; left; rcases hn with e | e <;> simp_all
  | undef => simp only [mem] at hv; left; rcases hu with e | e <;> simp_all
  | tru => simp only [mem] at hv; left; rcases ht with e | e <;> simp_all
  | fls => simp only [mem] at hv; left; rcases hf with e | e <;> simp_all
  | sym x =>
    simp only [mem] at hv; left
    rcases hs with e | e
    · simp_all
    · rw [← e]; cases t <;> rfl
  | arr x =>
    simp only [mem] at hv; left
    rcases ha with e | e
    · simp_all
    · rw [← e]; cases t <;> rfl
  | _ => simp [mem] at hv

/-- The tag answers the object component states alone, as unit clauses. -/
def ValueSet.unitTags (V : ValueSet) : List (Tag × Bool) :=
  match V.obj with
  | some cs => cs.filterMap fun c => match c with | [l] => some (l.tag, l.answer) | _ => none
  | none => []

end Verification.ValueSets
