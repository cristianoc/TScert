import Verification.Semantics.HeapKnowledge
import Verification.Semantics.LinkClasses
import Verification.Semantics.SeparationNormal

/-! The normal form of heap facts (heap-knowledge draft, §4): one value fact
per alias class, the meet of every value fact on its slots and of every cell
fact a read link makes its value, at the class's context and absent where it
states no more than the context; one cell fact per class and field no read
link answers; the links in their normal form (`LinkClasses.norm`). -/
namespace Verification.KnowledgeNormal
open ProgramTyping HeapFacts HeapKnowledge ValueSets CanonicalLists

/-- A slot's context: the values its type admits, where a value set states
them. -/
abbrev Ctx := Nat → Option ValueSet

def CtxOk (ctx : Ctx) (ρ : Env) : Prop := ∀ i C, ctx i = some C → C.mem (ρ i) = true

/-- A meet, the first set itself where the two are one: a repeated fact
costs a comparison. -/
def meetStep (V W : ValueSet) : ValueSet := if V = W then V else V.meet W

theorem mem_meetStep (V W : ValueSet) (v : Tm) : (meetStep V W).mem v = (V.mem v && W.mem v) := by
  unfold meetStep
  split
  · rename_i e; subst e; simp
  · exact ValueSet.mem_meet V W v

/-- The meet of a list of value sets, from `init`. -/
def meetAll (init : ValueSet) (l : List ValueSet) : ValueSet := l.foldl meetStep init

theorem mem_meetAll {init : ValueSet} {l : List ValueSet} {v : Tm} :
    (meetAll init l).mem v = true ↔ init.mem v = true ∧ ∀ x ∈ l, x.mem v = true := by
  induction l generalizing init with
  | nil => simp [meetAll]
  | cons a l ih =>
    simp only [meetAll, List.foldl_cons] at ih ⊢
    rw [ih, mem_meetStep]
    simp only [Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- A class and a field, the key of a cell fact. -/
structure CellKey where
  slot : Nat
  field : PropKey
  deriving DecidableEq

def CellKey.key (c : CellKey) : List Nat := c.slot :: ValueSets.propKey c.field

instance : LT CellKey := ⟨fun a b => a.key < b.key⟩
instance : DecidableLT CellKey := fun a b => inferInstanceAs (Decidable (a.key < b.key))

instance : StrictTotal CellKey where
  irrefl a := StrictTotal.irrefl a.key
  trans h₁ h₂ := StrictTotal.trans (α := List Nat) h₁ h₂
  total {a b} h := StrictTotal.total (α := List Nat) fun e => h (by
    cases a; cases b
    simp only [CellKey.key, List.cons.injEq] at e
    rw [e.1, ValueSets.propKey_inj e.2])

section
variable (ctx : Ctx) (k : Knowledge)

/-- The context of class `r`: the meet of its slots' contexts, where any has one. -/
def classCtx (r : Nat) : Option ValueSet :=
  match (canon (Partitions.cls (LinkClasses.closure k.links) r)).filterMap ctx with
  | [] => none
  | C :: Cs => some (meetAll C Cs)

end

section sound
variable {ctx : Ctx} {k : Knowledge} {ρ : Env} {h : Heap}

end sound

section complete
variable {ctx : Ctx} {k : Knowledge} {ρ : Env} {h : Heap}

end complete

section idem
variable {ctx : Ctx} {k : Knowledge}

end idem

section idem2
variable {ctx : Ctx} {k : Knowledge}

end idem2

section idem3
variable {ctx : Ctx} {k : Knowledge}

end idem3

section idem4
variable {ctx : Ctx} {k : Knowledge}

end idem4

section unique
variable {ctx : Ctx} {k₁ k₂ : Knowledge}

end unique

/-! ## Computing the normal form with one closure -/

/-- First read of each receiver and field, preserving the link order. -/
private def readIndex : HeapLinks.Links → Std.HashMap (Nat × PropKey) Nat
  | [] => {}
  | g :: gs =>
    let m := readIndex gs
    if g.alias then m else m.insert (g.cell, g.field) g.value

/-- Contents grouped by a key, in the facts' order, retaining duplicates. -/
@[nospecialize] private def buckets {α : Type} [BEq α] [Hashable α]
    (key : HeapFacts.Fact → α) : HeapFacts.Facts → Std.HashMap α (List ValueSet)
  | [] => {}
  | F :: fs =>
    let m := buckets key fs
    let a := key F
    m.insert a (F.contents :: (m[a]?).getD [])

/-- `norm`, computing the alias closure and the normal links once. -/
def normFast (ctx : Ctx) (k : Knowledge) : Knowledge :=
  let cs := LinkClasses.closure k.links
  let classesBySlot := Partitions.index cs
  let members := fun x => (classesBySlot[x]?).getD [x]
  let r := fun x => LinkClasses.least x (members x)
  let nl := canon (LinkClasses.linksIn k.links cs)
  let reads := readIndex nl
  let readDest := fun (x : Nat) (f : PropKey) => reads[(x, f)]?
  let classCtx := fun (x : Nat) => match (canon (members x)).filterMap ctx with
    | [] => none
    | C :: Cs => some (meetAll C Cs)
  let valuesByClass := buckets (fun f => r f.slot) k.values
  let cellsByRead := buckets (fun f => readDest (r f.slot) f.field) k.cells
  let valueParts := fun (x : Nat) =>
    (valuesByClass[x]?).getD [] ++ (cellsByRead[some x]?).getD []
  let classes := canon ((k.values.map fun f => r f.slot) ++ k.cells.filterMap fun f => readDest (r f.slot) f.field)
  let valueFact := fun (x : Nat) =>
    let C := (classCtx x).getD ValueSet.top
    let V := C.normIn (meetAll ValueSet.top (valueParts x))
    if (classCtx x).isSome && V == C.normIn ValueSet.top then none else some (⟨x, V, valueField⟩ : Fact)
  let cellKeys := canon (k.cells.filterMap fun f =>
    if readDest (r f.slot) f.field = none then some (⟨r f.slot, f.field⟩ : CellKey) else none)
  let cellsByKey := buckets (fun f => (r f.slot, f.field)) k.cells
  let cellParts := fun (c : CellKey) => (cellsByKey[(c.slot, c.field)]?).getD []
  ⟨cellKeys.map (fun c => ⟨c.slot, ValueSet.top.normIn (meetAll ValueSet.top (cellParts c)), c.field⟩),
   classes.filterMap valueFact, nl, SeparationNormal.compact r k.separation, k.elems, k.indices⟩

end Verification.KnowledgeNormal
