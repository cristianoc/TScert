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

/-- `(ofAtom a).append V`, a primitive atom's by updating the one component
it names (`consAtom_eq`). -/
def consAtom (a : Atom) (V : ValueSet) : ValueSet :=
  match a with
  | .nul => { V with nul := true }
  | .undef => { V with undef := true }
  | .tru => { V with tru := true }
  | .fls => { V with fls := true }
  | .numLit b => { V with num := Lit.append (.these [b]) V.num }
  | .strLit s => { V with str := Lit.append (.these [s]) V.str }
  | a => (ofAtom a).append V

private theorem Lit.append_none {α : Type} [DecidableEq α] (l : Lit α) : Lit.append .none l = l := by
  cases l <;> simp [Lit.append, Lit.none, Lit.join]

private theorem Obj.join_none (o : Obj) : Obj.join none o = o := by
  cases o <;> rfl

theorem consAtom_eq (a : Atom) (V : ValueSet) : consAtom a V = (ofAtom a).append V := by
  cases a <;> simp [consAtom, ofAtom, ValueSet.append, Lit.append_none, Obj.join_none]

/-- `ofAtoms`, one atom at a time by `consAtom`. The compiler runs it in
place of `ofAtoms` (`ofAtoms_eq_cons`). -/
def ofAtomsCons : List Atom → ValueSet
  | [] => ValueSet.bot
  | a :: as => consAtom a (ofAtomsCons as)

@[csimp] theorem ofAtoms_eq_cons : @ofAtoms = @ofAtomsCons := by
  funext as
  induction as with
  | nil => rfl
  | cons a as ih => simp only [ofAtoms, List.foldr_cons, ofAtomsCons, consAtom_eq] at ih ⊢; rw [ih]

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

/-! ### Value sets -/

namespace ValueSet

/-- A value set at a context `C`: each component restricted to `C`'s and
in its normal form (heap-knowledge draft, §2.5). -/
def normIn (C V : ValueSet) : ValueSet :=
  ⟨V.nul && C.nul, V.undef && C.undef, V.tru && C.tru, V.fls && C.fls, V.sym && C.sym, V.arr && C.arr,
    C.num.normIn V.num, C.str.normIn V.str, C.big.normIn V.big,
    match C.obj with | none => none | some _ => objNorm V.obj⟩

/-- Widening at a merge (heap-knowledge draft, §2.3): the object component
in its normal form, keeping at most 8 clauses. Fewer clauses admit more
objects, so the widened set holds wherever the set does. -/
def widen (V : ValueSet) : ValueSet :=
  { V with obj := (objNorm V.obj).map (·.take 8) }

end ValueSet

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
