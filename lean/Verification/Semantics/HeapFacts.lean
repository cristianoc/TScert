import Verification.Programs.PointClaims
import Verification.Semantics.HeapObservations

/-! Finite current-content assertions. They constrain the current heap, never
change a world's contract, and carry no ownership or disjointness promise.
Edge entailment selects facts by runtime-environment slots and weakens their
primitive predicates. The representation has no execution indices in its syntax. -/
namespace Verification.HeapFacts
open ProgramTyping PositiveRules PositiveGraphs HeapObservations

/-- Finite predicates on current values. Primitive predicates describe a
value family. Nullish exclusions apply to values of any shape and support a
read at the storage contract's corresponding negative slice. A tag atom is
a test's observed answer, `tagHolds` as `BranchRefinement.Observation`
states it, and supports a read at the contract's slice by that answer. -/
inductive Atom where
  | nul | undef | tru | fls | num | numLit (bits : UInt64) | str | strLit (value : String)
  | defined | nonNull | nonNullish
  | tag (test : Tag) (answer : Bool)
  deriving DecidableEq, Repr

def Atom.holds : Atom → Tm → Prop
  | .nul, v => v = .nul
  | .undef, v => v = .undef
  | .tru, v => v = .tru
  | .fls, v => v = .fls
  | .num, v => ∃ bits, v = .num bits
  | .numLit bits, v => v = .num bits
  | .str, v => ∃ s, v = .str s
  | .strLit s, v => v = .str s
  | .defined, v => isVal v = true ∧ v ≠ .undef
  | .nonNull, v => isVal v = true ∧ v ≠ .nul
  | .nonNullish, v => isVal v = true ∧ v ≠ .nul ∧ v ≠ .undef
  | .tag t q, v => isVal v = true ∧ (tagHolds t v = q ∨ protoFree t v = false)

theorem Atom.isValue {a : Atom} {v} (h : a.holds v) : isVal v = true := by
  cases a <;> simp only [Atom.holds] at h
  all_goals first | exact h.1 | (rcases h with ⟨bits,rfl⟩; rfl) | (subst v; rfl)

def Atom.clause (a : Atom) : PositiveNormalization.Clause α :=
  match a with
  | .nul => .nul | .undef => .undef | .tru => .boolLit true
  | .fls => .boolLit false | .num => .num | .numLit b => .numLit b
  | .str => .str | .strLit s => .strLit s
  | .defined | .nonNull | .nonNullish | .tag _ _ => .top

/-- Whether an atom is a tag's observed answer. -/
def Atom.isTag : Atom → Bool
  | .tag _ _ => true
  | _ => false

/-- A primitive atom is exactly its clause. -/
theorem Atom.sem {a : Atom} {S : α → Fam} {P : α → ArgFam} {n W v} (hd : a ≠ .defined) (hn : a ≠ .nonNull) (hb : a ≠ .nonNullish)
    (ht : a.isTag = false) :
    PositiveNormalization.semWithArgs Ξ S P a.clause n W v ↔ a.holds v := by
  cases a <;> first | rfl | exact absurd rfl hd | exact absurd rfl hn | exact absurd rfl hb | simp [Atom.isTag] at ht

/-- The nullish tests a predicate guarantees false. -/
def Atom.excludes (a : Atom) (tag : Tag) : Bool :=
  match tag, a with
  | _, .tag _ _ => false
  | .isUndef, .undef | .isUndef, .nonNull => false
  | .isNul, .nul | .isNul, .defined => false
  | .isNullish, .nul | .isNullish, .undef | .isNullish, .defined | .isNullish, .nonNull => false
  | .isUndef, _ | .isNul, _ | .isNullish, _ => true
  | _, _ => false

theorem Atom.excludes_sound {a : Atom} {tag : Tag} {v : Tm}
    (he : a.excludes tag = true) (hv : a.holds v) : tagHolds tag v = false := by
  cases tag <;> cases a <;> simp_all [Atom.excludes, Atom.holds]
  all_goals first
    | (subst v; rfl)
    | (obtain ⟨_, rfl⟩ := hv; rfl)
    | (cases v <;> simp_all [tagHolds])

/-- Whether a value meeting the atom answers `t` with `q`, or reads a
prototype for it: a nullish exclusion answers its test `false`, and a tag
atom is the answer. -/
def Atom.answers (a : Atom) (t : Tag) (q : Bool) : Bool :=
  (!q && a.excludes t) || a == .tag t q

theorem Atom.answers_sound {a : Atom} {t : Tag} {q : Bool} {v : Tm}
    (h : a.answers t q = true) (hv : a.holds v) : tagHolds t v = q ∨ protoFree t v = false := by
  simp only [Atom.answers, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h with ⟨rfl, he⟩ | rfl
  · exact Or.inl (Atom.excludes_sound he hv)
  · exact hv.2

def Atom.le (a b : Atom) : Bool :=
  a == b || match b with
    | .defined => a.excludes .isUndef
    | .nonNull => a.excludes .isNul
    | .nonNullish => a.excludes .isNullish
    | _ => match a, b with
      | .numLit _, .num | .strLit _, .str => true
      | _, _ => false

theorem Atom.le_sound {a b : Atom} {v} (h : a.le b = true) (hv : a.holds v) : b.holds v := by
  simp only [Atom.le, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact hv
  · cases b with
    | defined =>
      have ht := Atom.excludes_sound h hv
      exact ⟨Atom.isValue hv, by intro he; subst v; simp [tagHolds] at ht⟩
    | nonNull =>
      have ht := Atom.excludes_sound h hv
      exact ⟨Atom.isValue hv, by intro he; subst v; simp [tagHolds] at ht⟩
    | nonNullish =>
      have ht := Atom.excludes_sound h hv
      exact ⟨Atom.isValue hv, by intro he; subst v; simp [tagHolds] at ht,
        by intro he; subst v; simp [tagHolds] at ht⟩
    | _ => cases a <;> simp_all [Atom.holds]


def covers (source target : List Atom) : Bool :=
  source.all fun a => target.any a.le

theorem covers_sound {source target v} (h : covers source target = true)
    (hv : ∃ a ∈ source, a.holds v) : ∃ b ∈ target, b.holds v := by
  obtain ⟨a,ha,hv⟩ := hv
  obtain ⟨b,hb,hab⟩ := List.any_eq_true.mp (List.all_eq_true.mp h a ha)
  exact ⟨b,hb,Atom.le_sound hab hv⟩

/-- The result of an own-property read. An absent key yields undefined when
there is no prototype to consult. -/
def ReadGave (flds : List (PropKey × Nat)) (field : PropKey) (h : Heap) (v : Tm) : Prop :=
  match flds.lookup field with
  | some l => h[l]? = some v
  | none => flds.lookup CallArguments.protoField = none ∧ v = .undef

theorem ReadGave.present {flds field h l v} (hf : flds.lookup field = some l)
    (hv : h[l]? = some v) : ReadGave flds field h v := by simp [ReadGave, hf, hv]

theorem ReadGave.alloc_frames {flds field h v} (vs : List Val) (hr : ReadGave flds field h v) :
    ReadGave flds field (h ++ vs) v := by
  unfold ReadGave at hr ⊢
  cases hl : flds.lookup field with
  | some l => rw [hl] at hr; exact HeapObservations.alloc_frames vs hr
  | none => rw [hl] at hr; exact hr

theorem ReadGave.step {flds field h v c oid} (hr : ReadGave flds field h v) :
    Step h (.readAt field (.objAt flds c oid)) h v := by
  unfold ReadGave at hr
  cases hf : flds.lookup field with
  | some l => rw [hf] at hr; exact .readField hf hr
  | none => rw [hf] at hr; rw [hr.2]; exact .readMissing hf hr.1

/-- **A stable key frames its read** (HOST-FAMILIES.md, "Stable links"):
what a read of a key the object reads one way for its life (`StableAt`) gave,
every heap a normally returning execution reaches gives again. A present
key's location holds its contract's one value
(`HeapObservations.stable_frame`); an absent key of an object without a
prototype reads `undefined` from the value alone. A thrown outcome carries no
postcondition, so this supplies nothing to an exceptional edge. -/
theorem ReadGave.stable_frame {T Q} {flds : List (PropKey × Nat)} {field : PropKey} {u : Tm} :
    ∀ {n W h t}, StableAt W flds field → HeapOk n W h → ReadGave flds field h u →
      HeapObservations.SafePost Ξ T Q n W h t →
      HeapObservations.SafePost Ξ T (fun h' v => Q h' v ∧ ReadGave flds field h' u) n W h t := by
  intro n W h t hs hh hr hp
  cases n with
  | zero => trivial
  | succ n =>
    unfold ReadGave at hr
    cases hl : flds.lookup field with
    | none =>
      rw [hl] at hr
      exact HeapObservations.consequence (fun _ _ _ h => h)
        (fun _ _ hq => ⟨hq, by simp only [ReadGave, hl]; exact hr⟩) hp
    | some l =>
      rw [hl] at hr
      obtain ⟨c, value, hw, hc⟩ := hs.present hl
      have hval := hh.stable_value (Nat.zero_lt_succ n) hw hc
      rw [hr] at hval
      obtain rfl := Option.some.inj hval
      exact HeapObservations.consequence (fun _ _ _ h => h)
        (fun _ _ hq => ⟨hq.1, ReadGave.present hl hq.2⟩) (HeapObservations.stable_frame hw hc hh hp)

/-- A semantic stable-key requirement frames the read of that key through a
normally returning execution. -/
theorem stable_key_frame {T Q} {keys : List PropKey} {key : PropKey}
    {n : Nat} {W : WorldT n} {h : Heap} {object t : Tm}
    (hk : key ∈ keys) (ho : stableKeysT keys n W object)
    (hh : HeapOk n W h) (hs : HeapObservations.SafePost Ξ T Q n W h t) :
    ∃ (flds : List (PropKey × Nat)) (oid : Nat), object = .objAt flds .absent oid ∧
      ∀ u, ReadGave flds key h u →
        HeapObservations.SafePost Ξ T (fun h' v => Q h' v ∧ ReadGave flds key h' u) n W h t := by
  obtain ⟨flds, oid, he, hst⟩ := stableKeysT_at ho hk
  exact ⟨flds, oid, he, fun _ hr => ReadGave.stable_frame hst hh hr hs⟩

/-- A property-read observation at the current heap. The field may be absent.
Value facts reuse the shape and ignore the field. -/
structure Fact where
  slot : Nat
  contents : List Atom
  field : PropKey := valueField
  deriving DecidableEq, Repr

abbrev Facts := List Fact

def Holds (facts : Facts) (ρ : Env) (h : Heap) : Prop :=
  ∀ f ∈ facts, ∃ flds c oid v, ρ f.slot = .objAt flds c oid ∧ ReadGave flds f.field h v ∧ ∃ a ∈ f.contents, a.holds v

theorem holds_nil (ρ h) : Holds [] ρ h := by simp [Holds]

/-- All target facts must have an incoming justification. Repeated slot maps
retain aliases; different slot numbers do not imply different locations. -/
def check (source target : Facts) (mapping : PointClaims.Mapping) : Bool :=
  target.all fun f =>
    let s := PointClaims.slot mapping f.slot
    source.any fun g => g.slot == s && g.field == f.field && covers g.contents f.contents

theorem check_sound {source target mapping ρ h}
    (hc : check source target mapping = true) (hs : Holds source ρ h) :
    Holds target (PointClaims.mapEnv mapping ρ) h := by
  intro f hmem
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc f hmem)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨flds,c,oid,v,hl,hr,hm⟩ := hs g hg
  refine ⟨flds,c,oid,v,?_,?_,covers_sound hc.2 hm⟩
  · simpa [PointClaims.mapEnv,hc.1.1] using hl
  · rw [← hc.1.2]; exact hr

/-- The value added by a bind shifts every old environment slot. -/
def shift (facts : Facts) : Facts := facts.map fun f => { f with slot := f.slot+1 }

theorem shift_holds {facts ρ h v} (hf : Holds facts ρ h) :
    Holds (shift facts) (push v ρ) h := by
  intro f hm
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
  exact hf g hg

/-- A read observation gives both its value and its unchanged heap. -/
theorem ReadGave.observed {flds field h v c oid n W}
    (hr : ReadGave flds field h v) (hv : isVal v = true)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost Ξ (exact v) (fun h' u => h' = h ∧ u = v) n W h
      (.readAt field (.objAt flds c oid)) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact .inr ⟨trunc n (Nat.le_succ n) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hw, hr.step, HeapOk_trunc n W h hh,
      HeapObservations.value hv rfl ⟨rfl, rfl⟩⟩

end Verification.HeapFacts
