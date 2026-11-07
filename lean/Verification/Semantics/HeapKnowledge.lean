import Verification.Semantics.HeapSeparation
import Verification.Semantics.SafeIntegers
import Verification.Semantics.Linear
import Verification.Programs.BranchRefinement

/-! Primitive heap and immutable-value facts for expression postconditions. Facts
are execution-state assertions, not extra world contracts or source type labels. -/
namespace Verification.HeapKnowledge
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts

/-- An elements atom: every present element of the array the slot `slot`
holds satisfies `pred` (`CallEffects.ElemsAt`), where the slot `cond`, if
stated, holds a truthy value, or a falsy one where `negated`. -/
structure ElemAtom where
  slot : Nat
  pred : CallEffects.ElemPred
  cond : Option Nat := none
  negated : Bool := false
  deriving DecidableEq, Repr, Hashable

/-- The safe integer a value is, where it is one (`SafeIntegers.safeIntOfBits`). -/
def intValue : Val → Option Int
  | .num b => SafeIntegers.safeIntOfBits b
  | _ => none

/-- The integers an environment's slots hold, `0` where a slot holds no safe
integer: the valuation the linear facts are read at. -/
def valuation (ρ : Env) (s : Nat) : Int := (intValue (ρ s)).getD 0

theorem intValue_safe {v : Val} {i : Int} (h : intValue v = some i) : ∃ b, v = .num b ∧ SafeIntegers.SafeInt b i := by
  cases v <;> simp only [intValue, reduceCtorEq] at h
  exact ⟨_, rfl, SafeIntegers.safeIntOfBits_sound h⟩

theorem intValue_num {b : UInt64} {i : Int} (h : SafeIntegers.SafeInt b i) : intValue (.num b) = some i :=
  SafeIntegers.safeIntOfBits_complete h

/-- An index fact (DESIGN of the guarded write, PROGRAM-TYPING.md, "Writes at
a checked index"): the slot `k` holds a number that is an array index
(`index`); the slot `n` holds the length of the store the array in slot `x`
holds (`length`); the slot `k` holds an array index at most that length
(`bound`); the slot `k` holds a safe integer (`int`); the slots of a linear
fact hold safe integers meeting it (`linear`, PROGRAM-TYPING.md, "Linear
facts"). `index`, `int` and `linear` read no heap; the others read the
location of the array's store field. -/
inductive IndexFact where
  | index (k : Nat)
  | length (x n : Nat)
  | bound (x k : Nat)
  | int (k : Nat)
  | linear (F : Linear.Fact)
  deriving DecidableEq, Repr, Hashable

namespace IndexFact

/-- The slots a fact names. -/
def slots : IndexFact → List Nat
  | .index k => [k]
  | .length x n => [x, n]
  | .bound x k => [x, k]
  | .int k => [k]
  | .linear F => F.vars

/-- The fact with each slot renamed by a partial map, where it maps every slot. -/
def mapM (f : Nat → Option Nat) : IndexFact → Option IndexFact
  | .index k => (f k).map .index
  | .length x n => do pure (.length (← f x) (← f n))
  | .bound x k => do pure (.bound (← f x) (← f k))
  | .int k => (f k).map .int
  | .linear F => (F.mapVars f).map .linear

/-- The fact with each slot renamed. -/
def map (f : Nat → Nat) (F : IndexFact) : IndexFact := (F.mapM (some ∘ f)).getD F

def HoldsAt : IndexFact → Env → Heap → Prop
  | .index k, ρ, _ => ∃ b i, ρ k = .num b ∧ indexOfBits b = some i
  | .length x n, ρ, h => ∃ s ls, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ n = .num (bitsOfNat ls.length) ∧ ls.length ≤ maxArrayLength
  | .bound x k, ρ, h => ∃ s ls b i, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ k = .num b ∧ indexOfBits b = some i ∧ i ≤ ls.length
  | .int k, ρ, _ => (intValue (ρ k)).isSome
  | .linear F, ρ, _ => (∀ s ∈ F.vars, (intValue (ρ s)).isSome) ∧ F.Holds (valuation ρ)

theorem holdsAt_mapM {F F' : IndexFact} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hm : F.mapM f = some F') (hf : ∀ s ∈ F.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    F'.HoldsAt ρ' h ↔ F.HoldsAt ρ h := by
  cases F with
  | index k =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    simp only [HoldsAt, hf k (by simp [slots]) t ht]
  | length x n =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨x', hx, n', hn, rfl⟩ := hm
    simp only [HoldsAt, hf x (by simp [slots]) x' hx, hf n (by simp [slots]) n' hn]
  | bound x k =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨x', hx, k', hk, rfl⟩ := hm
    simp only [HoldsAt, hf x (by simp [slots]) x' hx, hf k (by simp [slots]) k' hk]
  | int k =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    simp only [HoldsAt, hf k (by simp [slots]) t ht]
  | linear G =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨G', hG, rfl⟩ := hm
    simp only [HoldsAt]
    have hv : ∀ x ∈ G.vars, ∀ y, f x = some y → valuation ρ' y = valuation ρ x := by
      intro x hx y hy; simp only [valuation, hf x hx y hy]
    rw [Linear.Fact.holds_mapVars hG hv]
    constructor
    · rintro ⟨hi, hh⟩
      refine ⟨fun x hx => ?_, hh⟩
      obtain ⟨y, hy, hfy⟩ := Linear.Fact.mapVars_vars_fwd hG x hx
      rw [← hf x hx y hfy]; exact hi y hy
    · rintro ⟨hi, hh⟩
      refine ⟨fun y hy => ?_, hh⟩
      obtain ⟨x, hx, hfx⟩ := Linear.Fact.mapVars_vars hG y hy
      rw [hf x hx y hfx]; exact hi x hx

/-- A fact reads its slots' values alone. -/
theorem holdsAt_map {F : IndexFact} {f : Nat → Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s ∈ F.slots, ρ' (f s) = ρ s) : (F.map f).HoldsAt ρ' h ↔ F.HoldsAt ρ h := by
  obtain ⟨G, hG⟩ : ∃ G, F.mapM (some ∘ f) = some G := by
    cases F with
    | index k => exact ⟨_, rfl⟩
    | length x n => exact ⟨_, rfl⟩
    | bound x k => exact ⟨_, rfl⟩
    | int k => exact ⟨_, rfl⟩
    | linear G => obtain ⟨G', h⟩ := Linear.Fact.mapVars_some f G; exact ⟨.linear G', by simp [mapM, h]⟩
  simp only [map, hG, Option.getD_some]
  exact holdsAt_mapM hG (fun s hs t ht => by cases ht; exact hf s hs)

/-- A heap extension keeps a fact: the store lies in the old heap. -/
theorem holdsAt_extend {F : IndexFact} {ρ : Env} {h : Heap} (vs : List Val) (hF : F.HoldsAt ρ h) :
    F.HoldsAt ρ (h ++ vs) := by
  cases F with
  | index k => exact hF
  | length x n =>
    obtain ⟨s, ls, hs, hl, hn⟩ := hF
    exact ⟨s, ls, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl, hn⟩
  | bound x k =>
    obtain ⟨s, ls, b, i, hs, hl, hk, hi, hle⟩ := hF
    exact ⟨s, ls, b, i, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl,
      hk, hi, hle⟩
  | int k => exact hF
  | linear G => exact hF

end IndexFact

/-- An index atom: its fact, where the slot `cond`, if stated, holds a truthy
value, or a falsy one where `negated`, as an elements atom's condition. -/
structure IndexAtom where
  fact : IndexFact
  cond : Option Nat := none
  negated : Bool := false
  deriving DecidableEq, Repr, Hashable

structure Knowledge where
  cells : Facts := []
  values : Facts := []
  links : HeapLinks.Links := []
  /-- Which locations differ (`HeapSeparation`), addressed by level. -/
  separation : HeapSeparation.Separation := {}
  /-- The elements facts (`ElemAtom`). -/
  elems : List ElemAtom := []
  /-- The index facts (`IndexAtom`). -/
  indices : List IndexAtom := []
  deriving DecidableEq, Repr

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, f.contents.mem (ρ f.slot) = true

def ElemsHolds (as : List ElemAtom) (ρ : Env) (h : Heap) : Prop :=
  ∀ a ∈ as, (∀ b, a.cond = some b → tagHolds .truthy (ρ b) = !a.negated) → CallEffects.ElemsAt a.pred (ρ a.slot) h

def IndexHolds (as : List IndexAtom) (ρ : Env) (h : Heap) : Prop :=
  ∀ a ∈ as, (∀ b, a.cond = some b → tagHolds .truthy (ρ b) = !a.negated) → a.fact.HoldsAt ρ h

def Holds (k : Knowledge) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ ∧ HeapLinks.Holds k.links ρ h ∧
    HeapSeparation.Holds k.separation ρ ∧ ElemsHolds k.elems ρ h ∧ IndexHolds k.indices ρ h

theorem elemsHolds_nil (ρ h) : ElemsHolds [] ρ h := by simp [ElemsHolds]

theorem indexHolds_nil (ρ h) : IndexHolds [] ρ h := by simp [IndexHolds]

theorem indexHolds_extend {as : List IndexAtom} {ρ h} (vs : List Val) (he : IndexHolds as ρ h) :
    IndexHolds as ρ (h ++ vs) := fun a ha hc => IndexFact.holdsAt_extend vs (he a ha hc)

/-- An atom renamed by a partial map, where it maps every slot the atom names. -/
def mapIndex (f : Nat → Option Nat) (a : IndexAtom) : Option IndexAtom :=
  match a.fact.mapM f, a.cond with
  | some F, none => some { a with fact := F }
  | some F, some c => (f c).map fun c' => { a with fact := F, cond := some c' }
  | none, _ => none

/-- Atoms renamed by a partial map, kept where every slot maps. -/
def mapIndices (f : Nat → Option Nat) (as : List IndexAtom) : List IndexAtom :=
  as.filterMap (mapIndex f)

/-- Renaming keeps the atoms where each renamed slot holds its source slot's value. -/
theorem mapIndices_holds {as : List IndexAtom} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s t, f s = some t → ρ' t = ρ s) (he : IndexHolds as ρ h) :
    IndexHolds (mapIndices f as) ρ' h := by
  intro a ha hc
  obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
  unfold mapIndex at hab
  split at hab
  · rename_i F hF hcb
    cases hab
    exact (IndexFact.holdsAt_mapM hF (fun s _ t ht => hf s t ht)).mpr (he b hb (by simp [hcb]))
  · rename_i F c hF hcb
    simp only [Option.map_eq_some_iff] at hab
    obtain ⟨t, ht, rfl⟩ := hab
    refine (IndexFact.holdsAt_mapM hF (fun s _ t ht => hf s t ht)).mpr (he b hb ?_)
    intro d hd
    rw [hcb] at hd
    cases hd
    rw [← hf c t ht]
    exact hc t rfl
  · cases hab

theorem empty (ρ h) : Holds {} ρ h :=
  ⟨holds_nil ρ h,by simp [ValueHolds],by simp [HeapLinks.Holds],HeapSeparation.empty_holds ρ,elemsHolds_nil ρ h,
    indexHolds_nil ρ h⟩

/-- A heap extension keeps an elements fact: the store and every element
location lie in the old heap. -/
theorem elemsAt_extend {R : CallEffects.ElemPred} {r : Tm} {h : Heap} (vs : List Val)
    (he : CallEffects.ElemsAt R r h) : CallEffects.ElemsAt R r (h ++ vs) := by
  obtain ⟨s, ls, hs, hl, hall⟩ := he
  refine ⟨s, ls, hs, ?_, fun l hm => ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl
  · obtain ⟨v, hv, hr⟩ := hall l hm
    exact ⟨v, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv, hr⟩

theorem elemsHolds_extend {as : List ElemAtom} {ρ h} (vs : List Val) (he : ElemsHolds as ρ h) :
    ElemsHolds as ρ (h ++ vs) := fun a ha hc => elemsAt_extend vs (he a ha hc)

/-- Atoms about slots past the pushed one. -/
def shiftElems (as : List ElemAtom) : List ElemAtom :=
  as.map fun a => { a with slot := a.slot + 1, cond := a.cond.map (· + 1) }

theorem shiftElems_holds {as : List ElemAtom} {ρ h v} (he : ElemsHolds as ρ h) :
    ElemsHolds (shiftElems as) (push v ρ) h := by
  intro a ha hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact he b hb fun c hc' => hc (c + 1) (by simp [hc'])

/-- Atoms about slots below the dropped slot 0, restated one lower. -/
def dropElems (as : List ElemAtom) : List ElemAtom :=
  (as.filter fun a => 0 < a.slot && a.cond.all (0 < ·)).map fun a =>
    { a with slot := a.slot - 1, cond := a.cond.map (· - 1) }

theorem dropElems_holds {as : List ElemAtom} {ρ h v} (he : ElemsHolds as (push v ρ) h) :
    ElemsHolds (dropElems as) ρ h := by
  intro a ha hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hb, hp⟩ := List.mem_filter.mp hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.all_eq_true] at hp
  have hs : push v ρ b.slot = ρ (b.slot - 1) := by
    obtain ⟨i, hi⟩ : ∃ i, b.slot = i + 1 := ⟨b.slot - 1, by omega⟩
    rw [hi]; rfl
  have := he b hb fun c hc' => by
    have hc0 := hp.2 c hc'
    obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
    exact hc i (by simp [hc'])
  simpa [hs] using this

/-- A fresh allocation preserves every assertion about existing cells and aliases. -/
theorem alloc_frame {k ρ h v} (hk : Holds k ρ h) : Holds k ρ (h ++ [v]) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frame hk.2.2.1, hk.2.2.2.1, elemsHolds_extend [v] hk.2.2.2.2.1,
    indexHolds_extend [v] hk.2.2.2.2.2⟩
  intro f hf
  obtain ⟨flds,c,oid,u,he,hr,hm⟩ := hk.1 f hf
  exact ⟨flds,c,oid,u,he,hr.alloc_frames [v],hm⟩

/-- The same across a whole object's worth of fresh locations. -/
theorem alloc_frames {k ρ h} (vs : List Val) (hk : Holds k ρ h) : Holds k ρ (h ++ vs) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frames vs hk.2.2.1, hk.2.2.2.1, elemsHolds_extend vs hk.2.2.2.2.1,
    indexHolds_extend vs hk.2.2.2.2.2⟩
  intro f hf
  obtain ⟨flds,c,oid,u,he,hr,hm⟩ := hk.1 f hf
  exact ⟨flds,c,oid,u,he,hr.alloc_frames vs,hm⟩

/-- What every one of several states establishes: a fact about a slot and
field each of them states, holding what any of them says it holds; the first's
links that appear verbatim in all the others; the separation pairs every
state justifies (`HeapSeparation.meet`). Used by the producer at a merge
that is not a cut, where no requirement is stated; every edge is still
checked, and each state's fact covers the union. Each join is widened
(`ValueSet.widen`), so a merge keeps at most 8 clauses per object. -/
def meet : List Knowledge → Knowledge
  | [] => {}
  | k :: ks =>
    let joined := fun (pick : Knowledge → Facts) =>
      (pick k).filterMap fun f =>
        let others := ks.map fun o => (pick o).filter fun g => g.slot == f.slot && g.field == f.field
        if others.all (!·.isEmpty) then
          some { f with contents := others.flatten.foldl (fun V g => if V = g.contents then V else (V.join g.contents).widen) f.contents }
        else none
    ⟨(joined (·.cells)).eraseDups, (joined (·.values)).eraseDups,
     let others := ks.map fun o => (Std.HashSet.ofList o.links : Std.HashSet HeapLinks.Link)
     k.links.filter (fun g => others.all (·.contains g)),
     HeapSeparation.meet (k.separation :: ks.map (·.separation)),
     k.elems.filter fun a => ks.all (·.elems.contains a),
     k.indices.filter fun a => ks.all (·.indices.contains a)⟩

/-- Whether a target atom follows from a source atom on an edge mapping `m`:
the source's slot holds the mapped target slot's value (`M`), its predicate
is within the target's, and its condition is none or the mapped one's. -/
def elemFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (s t : ElemAtom) : Bool :=
  (M (PointClaims.slot m t.slot)).contains s.slot && s.pred.le t.pred &&
    match s.cond, t.cond with
    | none, _ => true
    | some c, some c' => (M (PointClaims.slot m c')).contains c && s.negated == t.negated
    | some _, none => false

def elemsCheckBy (M : Nat → List Nat) (a b : List ElemAtom) (m : PointClaims.Mapping) : Bool :=
  b.all fun t => a.any fun s => elemFollows M m s t

theorem elemsCheckBy_sound {M : Nat → List Nat} {a b : List ElemAtom} {m ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hc : elemsCheckBy M a b m = true) (ha : ElemsHolds a ρ h) :
    ElemsHolds b (PointClaims.mapEnv m ρ) h := by
  intro t ht hcond
  obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc t ht)
  simp only [elemFollows, Bool.and_eq_true, List.contains_iff_mem] at hf
  obtain ⟨⟨hslot, hle⟩, hcd⟩ := hf
  have hsv : ρ s.slot = PointClaims.mapEnv m ρ t.slot := hM _ _ hslot
  have hsc : ∀ c, s.cond = some c → tagHolds .truthy (ρ c) = !s.negated := by
    intro c hc
    rw [hc] at hcd
    cases htc : t.cond with
    | none => rw [htc] at hcd; cases hcd
    | some c' =>
      rw [htc] at hcd
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hcd
      rw [hM _ _ hcd.1, hcd.2]
      exact hcond c' htc
  have := ha s hs hsc
  rw [hsv] at this
  exact this.mono hle

/-- Whether a target linear form is a source one, term by term, each target
slot mapped to a slot whose value the source slot holds (`M`). -/
def termsFollow (M : Nat → List Nat) (m : PointClaims.Mapping) : Linear.Form → Linear.Form → Bool
  | [], [] => true
  | (x, c) :: t, (y, c') :: t' => c == c' && (M (PointClaims.slot m y)).contains x && termsFollow M m t t'
  | _, _ => false

def formFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : Linear.Fact → Linear.Fact → Bool
  | .le F d, .le F' d' => d == d' && termsFollow M m F F'
  | .ne F d, .ne F' d' => d == d' && termsFollow M m F F'
  | _, _ => false

theorem termsFollow_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) :
    ∀ {F F' : Linear.Form}, termsFollow M m F F' = true →
      Linear.Form.eval (valuation (PointClaims.mapEnv m ρ)) F' = Linear.Form.eval (valuation ρ) F ∧
      ∀ y ∈ F'.map (·.1), ∃ x ∈ F.map (·.1), ρ x = PointClaims.mapEnv m ρ y := by
  intro F
  induction F with
  | nil => intro F' h; cases F' with
    | nil => exact ⟨rfl, by simp⟩
    | cons _ _ => simp [termsFollow] at h
  | cons p t ih =>
    intro F' h
    obtain ⟨x, c⟩ := p
    cases F' with
    | nil => simp [termsFollow] at h
    | cons q t' =>
      obtain ⟨y, c'⟩ := q
      simp only [termsFollow, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
      obtain ⟨⟨rfl, hx⟩, ht⟩ := h
      obtain ⟨he, hv⟩ := ih ht
      have hxy : ρ x = PointClaims.mapEnv m ρ y := hM _ _ hx
      refine ⟨?_, ?_⟩
      · simp only [Linear.Form.eval, he, valuation, ← hxy]
      · intro z hz
        simp only [List.map_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨x, by simp, hxy⟩
        · obtain ⟨w, hw, hwz⟩ := hv z hz
          exact ⟨w, by simp [hw], hwz⟩

theorem formFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {F F' : Linear.Fact}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hf : formFollows M m F F' = true) :
    (F'.Holds (valuation (PointClaims.mapEnv m ρ)) ↔ F.Holds (valuation ρ)) ∧
      ∀ y ∈ F'.vars, ∃ x ∈ F.vars, ρ x = PointClaims.mapEnv m ρ y := by
  cases F <;> cases F' <;> simp only [formFollows, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hf
  all_goals
    obtain ⟨rfl, ht⟩ := hf
    obtain ⟨he, hv⟩ := termsFollow_sound hM ht
    exact ⟨by simp only [Linear.Fact.Holds, he], hv⟩

/-- Whether a target fact follows from a source fact on an edge mapping `m`:
each slot of the source's holds the value of the mapped target slot (`M`). -/
def factFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : IndexFact → IndexFact → Bool
  | .index k, .index k' => (M (PointClaims.slot m k')).contains k
  | .length x n, .length x' n' =>
    (M (PointClaims.slot m x')).contains x && (M (PointClaims.slot m n')).contains n
  | .bound x k, .bound x' k' =>
    (M (PointClaims.slot m x')).contains x && (M (PointClaims.slot m k')).contains k
  | .int k, .int k' => (M (PointClaims.slot m k')).contains k
  | .linear F, .linear F' => formFollows M m F F'
  | _, _ => false

theorem factFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {s t : IndexFact} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hf : factFollows M m s t = true) (hs : s.HoldsAt ρ h) :
    t.HoldsAt (PointClaims.mapEnv m ρ) h := by
  cases s <;> cases t <;> simp only [factFollows, Bool.and_eq_true, List.contains_iff_mem, reduceCtorEq] at hf
  · rename_i k k'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf] using hs
  · rename_i x n x' n'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf.1, hM _ _ hf.2] using hs
  · rename_i x k x' k'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf.1, hM _ _ hf.2] using hs
  · rename_i k k'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf] using hs
  · rename_i F F'
    obtain ⟨hh, hv⟩ := formFollows_sound hM hf
    refine ⟨fun y hy => ?_, hh.mpr hs.2⟩
    obtain ⟨x, hx, hxy⟩ := hv y hy
    have := hs.1 x hx
    rw [hxy] at this
    exact this

/-- Whether a target atom follows from a source atom: its fact follows, and its
condition is none or the mapped one's, at the same answer. -/
def indexFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (s t : IndexAtom) : Bool :=
  factFollows M m s.fact t.fact &&
    match s.cond, t.cond with
    | none, _ => true
    | some c, some c' => (M (PointClaims.slot m c')).contains c && s.negated == t.negated
    | some _, none => false

/-- The linear facts the unconditional atoms state. -/
def linearFacts (as : List IndexAtom) : List Linear.Fact :=
  as.filterMap fun a => if a.cond.isNone then match a.fact with
    | .linear F => some F
    | _ => none else none

/-- Whether an unconditional atom states that the slot `s` holds a safe integer. -/
def intSlot (as : List IndexAtom) (s : Nat) : Bool :=
  as.any fun a => a.cond.isNone && match a.fact with
    | .int k => k == s
    | .linear F => F.vars.contains s
    | _ => false

theorem linearFacts_holds {as : List IndexAtom} {ρ h} (he : IndexHolds as ρ h) :
    ∀ F ∈ linearFacts as, F.Holds (valuation ρ) := by
  intro F hF
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hF
  split at hm
  · rename_i hn
    have hat := he a ha fun b hb => by rw [Option.isNone_iff_eq_none.mp hn] at hb; cases hb
    cases hf : a.fact with
    | linear G => rw [hf] at hm hat; cases hm; exact hat.2
    | index _ | length _ _ | bound _ _ | int _ => rw [hf] at hm; cases hm
  · cases hm

theorem intSlot_sound {as : List IndexAtom} {ρ h s} (he : IndexHolds as ρ h) (hs : intSlot as s = true) :
    (intValue (ρ s)).isSome := by
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp hs
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hn, hf⟩ := hm
  have hat := he a ha fun b hb => by rw [hn] at hb; cases hb
  cases hfa : a.fact with
  | int k => rw [hfa] at hf hat; simp only [beq_iff_eq] at hf; subst hf; exact hat
  | linear G => rw [hfa] at hf hat; exact hat.1 s (List.contains_iff_mem.mp hf)
  | index _ | length _ _ | bound _ _ => rw [hfa] at hf; cases hf

/-- Whether a target atom follows from the source's linear facts: an
unconditional `int` atom of a slot the source states holds a safe integer, or
an unconditional linear atom the source's linear facts entail
(`Linear.entails`), each target slot renamed to the source slot the edge maps
it to. -/
def pickSlot (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom) (y : Nat) : Nat :=
  ((M (PointClaims.slot m y)).find? (intSlot a)).getD (PointClaims.slot m y)

theorem pickSlot_eq {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom} {ρ : Env}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (y : Nat) : ρ (pickSlot M m a y) = PointClaims.mapEnv m ρ y := by
  unfold pickSlot
  cases hf : (M (PointClaims.slot m y)).find? (intSlot a) with
  | none => rfl
  | some x => exact hM _ _ (List.mem_of_find?_eq_some hf)

/-- Whether the source's facts bound slot `k` by the length of slot `x`'s
store: an unconditional length atom of a slot of `x`'s class, both slots
stated safe integers, and the linear facts entailing `0 ≤ k ≤ n` and
`k ≤ 2^32 - 2`. -/
def lengthBound (M : List Nat) (a : List IndexAtom) (k : Nat) : Bool :=
  intSlot a k && a.any fun atom => atom.cond.isNone && match atom.fact with
    | .length y n => M.contains y && intSlot a n &&
        Linear.entails (linearFacts a) (.le [(k, -1)] 0) &&
        Linear.entails (linearFacts a) (.le [(k, 1), (n, -1)] 0) &&
        Linear.entails (linearFacts a) (.le [(k, 1)] (maxArrayLength - 1))
    | _ => false

theorem indexOfBits_safe {b : UInt64} {j : Int} (hb : SafeIntegers.SafeInt b j) (h0 : 0 ≤ j)
    (h1 : j < maxArrayLength) : indexOfBits b = some j.toNat := by
  rcases hb.2 with ⟨-, he⟩ | ⟨hle, he⟩
  · have : b = bitsOfNat j.natAbs := UInt64.toNat_inj.mp he
    have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
    have h1' : j < 4294967295 := by omega
    rw [this, IndexNumbers.indexOfBits_bitsOfNat (by omega)]
    congr 1; omega
  · have hj : j = 0 := by omega
    subst hj
    have : b = 0x8000000000000000 := UInt64.toNat_inj.mp (by rw [he]; simp [SafeIntegers.bitsOfNat_zero])
    subst this; rfl

theorem lengthBound_sound {M : List Nat} {a : List IndexAtom} {k : Nat} {ρ h} {v : Val}
    (hM : ∀ y ∈ M, ρ y = v) (hc : lengthBound M a k = true) (ha : IndexHolds a ρ h) :
    ∃ s ls b idx, Footprints.storeOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
      indexOfBits b = some idx ∧ idx ≤ ls.length := by
  simp only [lengthBound, Bool.and_eq_true] at hc
  obtain ⟨hi, hany⟩ := hc
  obtain ⟨atom, hat0, hm⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hnone, hf⟩ := hm
  have hat := ha atom hat0 fun b hb => by rw [hnone] at hb; cases hb
  have hlin := linearFacts_holds ha
  cases hfact : atom.fact with
  | length y n =>
    rw [hfact] at hf hat
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hf
    obtain ⟨⟨⟨⟨hy, hn⟩, e1⟩, e2⟩, e3⟩ := hf
    obtain ⟨s, ls, hs, hl, hnv, hmax⟩ := hat
    have f1 := Linear.entails_sound e1 hlin
    have f2 := Linear.entails_sound e2 hlin
    have f3 := Linear.entails_sound e3 hlin
    simp only [Linear.Fact.Holds, Linear.Form.eval] at f1 f2 f3
    have hL : SafeIntegers.SafeInt (bitsOfNat ls.length) (ls.length : Int) :=
      ⟨by simp [maxArrayLength] at hmax ⊢; omega, .inl ⟨by omega, by simp⟩⟩
    have hvn : valuation ρ n = ls.length := by simp [valuation, hnv, intValue, SafeIntegers.safeIntOfBits_complete hL]
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (intSlot_sound ha hi)
    obtain ⟨b, hb, hsafe⟩ := intValue_safe hj
    have hvi : valuation ρ k = j := by simp [valuation, hj]
    rw [hvi, hvn] at f2; rw [hvi] at f1 f3
    have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
    refine ⟨s, ls, b, j.toNat, by rw [← hM y hy]; exact hs, hl, hb,
      indexOfBits_safe hsafe (by omega) (by omega), by omega⟩
  | index _ | bound _ _ | int _ | linear _ => rw [hfact] at hf; simp at hf

def linearFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom) (t : IndexAtom) : Bool :=
  t.cond.isNone && match t.fact with
  | .bound x k =>
      lengthBound (M (PointClaims.slot m x)) a (pickSlot M m a k)
  | .int k => intSlot a (pickSlot M m a k)
  | .linear F => match F.mapVars (fun y => some (pickSlot M m a y)) with
    | some F' => F'.vars.all (intSlot a) && Linear.entails (linearFacts a) F'
    | none => false
  | _ => false

theorem linearFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom} {t : IndexAtom} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hf : linearFollows M m a t = true) (ha : IndexHolds a ρ h) :
    t.fact.HoldsAt (PointClaims.mapEnv m ρ) h := by
  simp only [linearFollows, Bool.and_eq_true] at hf
  obtain ⟨-, hf⟩ := hf
  cases ht : t.fact with
  | int k =>
    rw [ht] at hf
    simp only at hf
    have := intSlot_sound ha hf
    rw [pickSlot_eq hM] at this
    exact this
  | linear F =>
    rw [ht] at hf
    simp only at hf
    split at hf
    · rename_i F' hF'
      simp only [Bool.and_eq_true, List.all_eq_true] at hf
      obtain ⟨hv, he⟩ := hf
      have hv' : ∀ x ∈ F.vars, ∀ y, (fun y => some (pickSlot M m a y)) x = some y →
          valuation ρ y = valuation (PointClaims.mapEnv m ρ) x := by
        intro x _ y hy; cases hy; simp only [valuation, pickSlot_eq hM]
      refine ⟨fun x hx => ?_, (Linear.Fact.holds_mapVars hF' hv').mp
        (Linear.entails_sound he (linearFacts_holds ha))⟩
      obtain ⟨y, hy, hxy⟩ := Linear.Fact.mapVars_vars_fwd hF' x hx
      cases hxy
      have := intSlot_sound ha (hv _ hy)
      rw [pickSlot_eq hM] at this
      exact this
    · cases hf
  | bound x k =>
    rw [ht] at hf
    simp only at hf
    obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ :=
      lengthBound_sound (v := PointClaims.mapEnv m ρ x) (fun y hy => hM _ y hy) hf ha
    rw [pickSlot_eq hM] at hb
    exact ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩
  | index _ | length _ _ => rw [ht] at hf; cases hf

def indicesCheckBy (M : Nat → List Nat) (a b : List IndexAtom) (m : PointClaims.Mapping) : Bool :=
  b.all fun t => a.any (fun s => indexFollows M m s t) || linearFollows M m a t

theorem indicesCheckBy_sound {M : Nat → List Nat} {a b : List IndexAtom} {m ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hc : indicesCheckBy M a b m = true) (ha : IndexHolds a ρ h) :
    IndexHolds b (PointClaims.mapEnv m ρ) h := by
  intro t ht hcond
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hc t ht) with hc' | hlin
  case inr => exact linearFollows_sound hM hlin ha
  obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp hc'
  simp only [indexFollows, Bool.and_eq_true] at hf
  obtain ⟨hfact, hcd⟩ := hf
  have hsc : ∀ c, s.cond = some c → tagHolds .truthy (ρ c) = !s.negated := by
    intro c hc
    rw [hc] at hcd
    cases htc : t.cond with
    | none => rw [htc] at hcd; cases hcd
    | some c' =>
      rw [htc] at hcd
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hcd
      rw [hM _ _ hcd.1, hcd.2]
      exact hcond c' htc
  exact factFollows_sound hM hfact (ha s hs hsc)

/-- Atoms about slots past the pushed one. -/
def shiftIndices (as : List IndexAtom) : List IndexAtom := mapIndices (fun i => some (i + 1)) as

theorem shiftIndices_holds {as : List IndexAtom} {ρ h v} (he : IndexHolds as ρ h) :
    IndexHolds (shiftIndices as) (push v ρ) h :=
  mapIndices_holds (fun s t hst => by cases hst; rfl) he

/-- Whether a fact reads the environment alone: `index`, `int` and `linear`. -/
def IndexFact.envOnly : IndexFact → Bool
  | .index _ | .int _ | .linear _ => true
  | .length _ _ | .bound _ _ => false

/-- The atoms whose facts read the environment alone, kept by any heap change. -/
def envIndices (as : List IndexAtom) : List IndexAtom := as.filter (·.fact.envOnly)

theorem envIndices_holds {as : List IndexAtom} {ρ h} (he : IndexHolds as ρ h) (h' : Heap) :
    IndexHolds (envIndices as) ρ h' := by
  intro a ha hc
  obtain ⟨ha, henv⟩ := List.mem_filter.mp ha
  have := he a ha hc
  cases hf : a.fact <;> rw [hf] at this henv <;> simp [IndexFact.envOnly] at henv <;> exact this

/-- Atoms about slots below the dropped slot 0, restated one lower; an atom
naming slot 0 is first restated on a slot the links relate to it. -/
def dropIndices (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  let restated := match HeapLinks.neighbors ls 0 with
    | y :: _ => as ++ mapIndices (fun i => some (if i = 0 then y else i)) as
    | [] => as
  mapIndices (fun i => if i = 0 then none else some (i - 1)) restated

theorem dropIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ h v}
    (hl : HeapLinks.Holds ls (push v ρ) h) (he : IndexHolds as (push v ρ) h) :
    IndexHolds (dropIndices ls as) ρ h := by
  have hr : IndexHolds (match HeapLinks.neighbors ls 0 with
      | y :: _ => as ++ mapIndices (fun i => some (if i = 0 then y else i)) as
      | [] => as) (push v ρ) h := by
    split
    · rename_i y _ hn
      have hy : push v ρ y = push v ρ 0 := HeapLinks.neighbors_eq hl (by rw [hn]; simp)
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact he a ha
      · exact mapIndices_holds (fun s t hst => by
          cases hst; split
          · rename_i hs; rw [hs]; exact hy
          · rfl) he a ha
    · exact he
  refine mapIndices_holds (fun s t hst => ?_) hr
  split at hst
  · cases hst
  · cases hst
    obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
    rfl

/-- The atoms conditional on the observed slot's class, at the observed answer,
made unconditional. -/
def promoteIndices (ls : HeapLinks.Links) (as : List IndexAtom) (slot : Nat) (q : Bool) : List IndexAtom :=
  as ++ (as.filter fun a => a.negated == !q &&
    a.cond.any fun c => (HeapLinks.aliases ls slot).contains c).map ({ · with cond := none })

theorem promoteIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {slot : Nat} {q : Bool} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds as ρ h) (ht : tagHolds .truthy (ρ slot) = q) :
    IndexHolds (promoteIndices ls as slot q) ρ h := by
  intro a ha hc
  rcases List.mem_append.mp ha with ha | ha
  · exact he a ha hc
  · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨b, ⟨hb, hneg, hcb⟩, rfl⟩ := ha
    refine he b hb fun c hc' => ?_
    rw [hc'] at hcb
    simp only [Option.any_some, List.contains_iff_mem] at hcb
    rw [HeapLinks.aliases_eq hl hcb, ht, hneg]
    cases q <;> rfl

def check (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  HeapFacts.check a.cells b.cells m && (HeapFacts.check a.values b.values m &&
    (HeapLinks.check a.links b.links m && (HeapSeparation.check a.separation b.separation m &&
      (elemsCheckBy (fun x => [x]) a.elems b.elems m && indicesCheckBy (fun x => [x]) a.indices b.indices m))))

theorem check_sound {a b m ρ h} (hc : check a b m = true) (ha : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  simp only [check,Bool.and_eq_true] at hc
  refine ⟨HeapFacts.check_sound hc.1 ha.1,?_,HeapLinks.check_sound hc.2.2.1 ha.2.2.1,
    HeapSeparation.check_sound hc.2.2.2.1 ha.2.2.2.1,
    elemsCheckBy_sound (fun x y hy => by rw [List.mem_singleton.mp hy]) hc.2.2.2.2.1 ha.2.2.2.2.1,
    indicesCheckBy_sound (fun x y hy => by rw [List.mem_singleton.mp hy]) hc.2.2.2.2.2 ha.2.2.2.2.2⟩
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc.2.1 f hf)
  simp only [Bool.and_eq_true,beq_iff_eq] at hc
  simpa [PointClaims.mapEnv,hc.1] using ValueSets.ValueSet.le_sound hc.2 (ha.2.1 g hg)

def shift (k : Knowledge) : Knowledge :=
  ⟨HeapFacts.shift k.cells,HeapFacts.shift k.values,HeapLinks.pull k.links (fun i => [i+1]),
    HeapSeparation.shift k.separation, shiftElems k.elems, shiftIndices k.indices⟩

theorem shift_holds {k ρ h v} (hk : Holds k ρ h) : Holds (shift k) (push v ρ) h := by
  refine ⟨HeapFacts.shift_holds hk.1,?_,?_,HeapSeparation.shift_holds hk.2.2.2.1,shiftElems_holds hk.2.2.2.2.1,
    shiftIndices_holds hk.2.2.2.2.2⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hk.2.1 g hg
  · apply HeapLinks.pull_holds (pre := fun i => [i+1]) hk.2.2.1
    intro i j hj
    have hj := List.mem_singleton.mp hj
    subst j
    rfl
/-- Effect-only continuations discard the result slot. Facts about it cannot
be transferred into the old environment. -/
def dropFacts (fs : Facts) : Facts :=
  (fs.filter fun f => 0 < f.slot).map fun f => {f with slot := f.slot - 1}

/-- The facts on slot 0 restated on each of its aliases: what the facts of
its class keep when the slot is dropped. -/
def aliasZero (ls : HeapLinks.Links) (fs : Facts) : Facts :=
  fs ++ (fs.filter (·.slot == 0)).flatMap fun f => (HeapLinks.aliases ls 0).map fun y => { f with slot := y }

def dropResult (k : Knowledge) : Knowledge :=
  ⟨dropFacts (aliasZero k.links k.cells),dropFacts (aliasZero k.links k.values),
    HeapLinks.pull (HeapLinks.bridge k.links (· == 0)) (fun i => if i = 0 then [] else [i-1]),
    HeapSeparation.drop (match HeapLinks.neighbors k.links 0 with
      | y :: _ => HeapSeparation.restate k.separation 0 y
      | [] => k.separation), dropElems k.elems, dropIndices k.links k.indices⟩

theorem aliasZero_mem {ls : HeapLinks.Links} {fs : Facts} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {g : Fact} (hg : g ∈ aliasZero ls fs) : ∃ f ∈ fs, ρ g.slot = ρ f.slot ∧ g.contents = f.contents ∧ g.field = f.field := by
  rcases List.mem_append.mp hg with hg | hg
  · exact ⟨g, hg, rfl, rfl, rfl⟩
  · obtain ⟨f, hf, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hg
    have h0 : f.slot = 0 := by simpa using (List.mem_filter.mp hf).2
    exact ⟨f, (List.mem_filter.mp hf).1, by rw [h0]; exact HeapLinks.aliases_eq hl hy, rfl, rfl⟩

theorem dropResult_holds {k ρ h v} (hk : Holds k (push v ρ) h) :
    Holds (dropResult k) ρ h := by
  constructor
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    have hp : 0 < g.slot := of_decide_eq_true hg.2
    have he : push v ρ g.slot = ρ (g.slot - 1) := by
      cases hs : g.slot with
      | zero => omega
      | succ i => rfl
    obtain ⟨f, hf, hs, hc, hfl⟩ := aliasZero_mem hk.2.2.1 hg.1
    obtain ⟨flds, c, oid, u, hl, hr, hm⟩ := hk.1 f hf
    exact ⟨flds, c, oid, u, by rw [← he, hs]; exact hl, by rw [hfl]; exact hr, by rw [hc]; exact hm⟩
  · constructor
    · intro f hf
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      have hp : 0 < g.slot := of_decide_eq_true hg.2
      have he : push v ρ g.slot = ρ (g.slot - 1) := by
        cases hs : g.slot with
        | zero => omega
        | succ i => rfl
      obtain ⟨f, hf, hs, hc, -⟩ := aliasZero_mem hk.2.2.1 hg.1
      have := hk.2.1 f hf
      rw [← hs, ← hc, he] at this
      exact this
    have hs : HeapSeparation.Holds (match HeapLinks.neighbors k.links 0 with
        | y :: _ => HeapSeparation.restate k.separation 0 y
        | [] => k.separation) (push v ρ) := by
      split
      · rename_i y _ hn
        exact HeapSeparation.restate_holds (HeapLinks.neighbors_eq hk.2.2.1 (by rw [hn]; simp)) hk.2.2.2.1
      · exact hk.2.2.2.1
    refine ⟨?_, HeapSeparation.drop_holds hs, dropElems_holds hk.2.2.2.2.1,
      dropIndices_holds hk.2.2.1 hk.2.2.2.2.2⟩
    · apply HeapLinks.pull_holds (pre := fun i => if i = 0 then [] else [i-1]) (HeapLinks.bridge_holds hk.2.2.1)
      intro i j hj
      split at hj
      · simp at hj
      · have hj := List.mem_singleton.mp hj
        subst j
        cases i with
        | zero => contradiction
        | succ i => rfl

/-- Project facts along an executable slot map. All runtime aliases selected by
that map are retained, and target slots the map takes from one source slot
are related by alias links (`mapped-alias`); a target slot takes the facts
of every alias of its source slot, so a class keeps its facts when the slot
holding them is not selected. -/
def projectFacts (ls : HeapLinks.Links) (facts : Facts) (m : PointClaims.Mapping) (count : Nat) : Facts :=
  (List.range count).flatMap fun i =>
    let ms := HeapLinks.aliases ls (PointClaims.slot m i)
    (facts.filter fun f => ms.contains f.slot).map fun f => { f with slot := i }

def project (k : Knowledge) (m : PointClaims.Mapping) (count : Nat) : Knowledge :=
  -- The target slots each source slot is mapped to, in increasing order.
  let preimages : Std.HashMap Nat (List Nat) := (List.range count).foldr
    (fun j acc => acc.alter (PointClaims.slot m j) fun js => some (j :: js.getD [])) ∅
  -- Every pair of a group, since `HeapLinks.aliases` reads direct links.
  let pairs : List Nat → HeapLinks.Links := fun js =>
    js.zipIdx.flatMap fun (j, n) => (js.drop (n+1)).map fun r => { cell := j, value := r, alias := true }
  let shared : HeapLinks.Links := preimages.fold (fun acc _ js => match js with
    | _ :: _ :: _ => pairs js ++ acc
    | _ => acc) []
  ⟨projectFacts k.links k.cells m count,projectFacts k.links k.values m count,
    HeapLinks.pull (HeapLinks.bridge k.links fun i => (preimages.getD i []).isEmpty)
      (fun i => preimages.getD i []) ++ shared,
    HeapSeparation.project (HeapLinks.aliases k.links) k.separation m count,
    -- Each target slot takes the atoms of every alias of its source slot,
    -- a condition restated at the first target slot holding it.
    (List.range count).flatMap fun i =>
      let ms := HeapLinks.aliases k.links (PointClaims.slot m i)
      (k.elems.filter fun a => ms.contains a.slot).filterMap fun a => match a.cond with
        | none => some { a with slot := i }
        | some c => ((List.range count).find? fun j =>
            (HeapLinks.aliases k.links (PointClaims.slot m j)).contains c).map fun j =>
              { a with slot := i, cond := some j },
    -- Each slot an index atom names, its condition's included, restated at the
    -- first target slot holding its value.
    mapIndices (fun s => (List.range count).find? fun j =>
      (HeapLinks.aliases k.links (PointClaims.slot m j)).contains s) k.indices⟩

/-! ## Queries by class

What a knowledge states of a slot's value, or of the read of a field from
it, gathered from every slot `M` gives as holding the slot's value: the
classes of a closure, or a slot's aliases in links that state every pair of
a class. -/

theorem any_some {α : Type} {o : Option α} {p : α → Bool} (h : o.any p = true) :
    ∃ x, o = some x ∧ p x = true := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

/-- The meet of a nonempty list of value sets. -/
def meetSome : List ValueSets.ValueSet → Option ValueSets.ValueSet
  | [] => none
  | V :: Vs => some (Vs.foldl (fun V W => if V = W then V else V.meet W) V)

theorem meetSome_mem {l : List ValueSets.ValueSet} {V : ValueSets.ValueSet} {v : Tm}
    (h : meetSome l = some V) (hl : ∀ x ∈ l, x.mem v = true) : V.mem v = true := by
  cases l with
  | nil => cases h
  | cons W Ws =>
    cases h
    have hw := hl W (List.mem_cons_self ..)
    have hws : ∀ x ∈ Ws, x.mem v = true := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    clear hl
    induction Ws generalizing W with
    | nil => exact hw
    | cons a Ws ih =>
      simp only [List.foldl_cons]
      refine ih _ ?_ fun x hx => hws x (List.mem_cons_of_mem _ hx)
      split
      · exact hw
      · rw [ValueSets.ValueSet.mem_meet, hw, hws a (List.mem_cons_self ..)]; rfl

/-- The parts of a meet each about the one read from one object: the meet
holds of that read's value. -/
theorem meetSome_read {l : List ValueSets.ValueSet} {V : ValueSets.ValueSet} {o : Tm} {f : PropKey} {h : Heap}
    (hV : meetSome l = some V)
    (hl : ∀ x ∈ l, ∃ flds c oid u, o = .objAt flds c oid ∧ ReadGave flds f h u ∧ x.mem u = true) :
    ∃ flds c oid u, o = .objAt flds c oid ∧ ReadGave flds f h u ∧ V.mem u = true := by
  cases l with
  | nil => cases hV
  | cons W Ws =>
    obtain ⟨flds, c, oid, u, he, hr, -⟩ := hl W (List.mem_cons_self ..)
    refine ⟨flds, c, oid, u, he, hr, meetSome_mem hV fun x hx => ?_⟩
    obtain ⟨flds', c', oid', u', he', hr', hm'⟩ := hl x hx
    rw [he] at he'
    cases he'
    rw [ReadGave.unique hr hr']
    exact hm'

/-- What a knowledge states of the value of slot `s`: the value facts on
the slots `M s`, and the cell facts of each read into them from the slots
of its receiver. -/
def valueBy (a : Knowledge) (M : Nat → List Nat) (s : Nat) : Option ValueSets.ValueSet :=
  let ms := M s
  -- Each receiver and field once: reads restated on every pair of slots of
  -- two classes give one cell.
  let reads := ((a.links.filter fun g => !g.alias && ms.contains g.value).map fun g =>
    ((M g.cell).foldl min g.cell, g.field)).eraseDups
  meetSome ((a.values.filter fun F => ms.contains F.slot).map (·.contents) ++
    reads.flatMap fun (c, f) =>
      let rs := M c
      (a.cells.filter fun F => rs.contains F.slot && F.field == f).map (·.contents))

/-- What a knowledge states of the read of field `f` from slot `s`'s object:
the cell facts on the slots `M s`, and the value facts of each read of `f`
from them. -/
def cellBy (a : Knowledge) (M : Nat → List Nat) (s : Nat) (f : PropKey) : Option ValueSets.ValueSet :=
  let ms := M s
  -- Each read value's class once, by its least slot.
  let dests := ((a.links.filter fun g => !g.alias && g.field == f && ms.contains g.cell).map fun g =>
    (M g.value).foldl min g.value).eraseDups
  meetSome ((a.cells.filter fun F => ms.contains F.slot && F.field == f).map (·.contents) ++
    dests.flatMap fun d =>
      let ds := M d
      (a.values.filter fun F => ds.contains F.slot).map (·.contents))

/-- The value a link reads, as a `ReadGave`. -/
theorem link_readGave {g : HeapLinks.Link} {ρ : Env} {h : Heap} (ha : g.alias = false)
    (hh : HeapLinks.Holds [g] ρ h) :
    ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value) := by
  have := hh g (List.mem_singleton_self g)
  simp only [ha, Bool.false_eq_true, ite_false] at this
  cases ho : g.optional
  · simp only [ho, Bool.false_eq_true, ite_false] at this
    obtain ⟨flds, c, oid, l, he, hl, hv⟩ := this
    exact ⟨flds, c, oid, he, ReadGave.present hl hv⟩
  · simpa [ho] using this

section queries
variable {a : Knowledge} {M : Nat → List Nat} {ρ : Env} {h : Heap}

/-- The least of a slot and slots holding its value holds its value. -/
theorem foldl_min_eq (x : Nat) : ∀ (l : List Nat) (d : Nat), ρ d = ρ x → (∀ y ∈ l, ρ y = ρ x) →
    ρ (l.foldl min d) = ρ x := by
  intro l
  induction l with
  | nil => intro d hd _; exact hd
  | cons y l ih =>
    intro d hd hl
    simp only [List.foldl_cons]
    refine ih _ ?_ fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rcases Nat.le_total d y with hdy | hyd
    · rw [Nat.min_eq_left hdy]; exact hd
    · rw [Nat.min_eq_right hyd]; exact hl y (List.mem_cons_self ..)

theorem valueBy_mem (ha : Holds a ρ h) (hs : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s : Nat} {V : ValueSets.ValueSet}
    (hV : valueBy a M s = some V) : V.mem (ρ s) = true := by
  refine meetSome_mem hV fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hm⟩ := List.mem_filter.mp hF
    rw [← hs s F.slot (List.contains_iff_mem.mp hm)]
    exact ha.2.1 F hF
  · obtain ⟨cf, hcf, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨g, hg, hcf⟩ := List.mem_map.mp (List.mem_eraseDups.mp hcf)
    subst hcf
    obtain ⟨hg, hgs⟩ := List.mem_filter.mp hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hgs
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hk
    obtain ⟨flds, c, oid, u, he, hr, hm⟩ := ha.1 F hF
    obtain ⟨flds', c', oid', he', hr'⟩ := link_readGave hgs.1 fun x hx => by
      rw [List.mem_singleton.mp hx]; exact ha.2.2.1 g hg
    -- The least slot of the receiver's class holds the receiver's value.
    have hmin : ρ ((M g.cell).foldl min g.cell) = ρ g.cell :=
      foldl_min_eq g.cell _ _ rfl fun y hy => hs g.cell y hy
    rw [hs _ F.slot hk.1, hmin, he'] at he
    cases he
    rw [hk.2] at hr
    rw [← hs s g.value hgs.2, ← ReadGave.unique hr hr']
    exact hm

theorem cellBy_holds (ha : Holds a ρ h) (hs : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s : Nat} {f : PropKey}
    {V : ValueSets.ValueSet} (hV : cellBy a M s f = some V) :
    ∃ flds c oid u, ρ s = .objAt flds c oid ∧ ReadGave flds f h u ∧ V.mem u = true := by
  refine meetSome_read hV fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hk
    obtain ⟨flds, c, oid, u, he, hr, hm⟩ := ha.1 F hF
    rw [hs s F.slot hk.1] at he
    rw [hk.2] at hr
    exact ⟨flds, c, oid, u, he, hr, hm⟩
  · obtain ⟨d, hd, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hd)
    obtain ⟨hg, hgs⟩ := List.mem_filter.mp hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hgs
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
    simp only [List.contains_iff_mem] at hk
    obtain ⟨flds, c, oid, he, hr⟩ := link_readGave hgs.1.1 fun x hx => by
      rw [List.mem_singleton.mp hx]; exact ha.2.2.1 g hg
    rw [hs s g.cell hgs.2] at he
    rw [hgs.1.2] at hr
    refine ⟨flds, c, oid, ρ g.value, he, hr, ?_⟩
    have hmin : ρ ((M g.value).foldl min g.value) = ρ g.value :=
      foldl_min_eq g.value _ _ rfl fun y hy => hs g.value y hy
    rw [← hmin, ← hs _ F.slot hk]
    exact ha.2.1 F hF

/-- A slot's aliases hold its value. -/
theorem aliases_class (hl : HeapLinks.Holds a.links ρ h) :
    ∀ x, ∀ y ∈ HeapLinks.aliases a.links x, ρ y = ρ x :=
  fun _ _ hy => HeapLinks.aliases_eq hl hy

end queries

/-- Each cell fact on every alias of its slot: the cells a reader of cells by
slot needs where facts are stored once per class. -/
def aliasCells (k : Knowledge) : Facts :=
  k.cells.flatMap fun F => (HeapLinks.aliases k.links F.slot).map fun y => { F with slot := y }

theorem aliasCells_holds {k : Knowledge} {ρ h} (hk : Holds k ρ h) : HeapFacts.Holds (aliasCells k) ρ h := by
  intro F hF
  obtain ⟨G, hG, hF⟩ := List.mem_flatMap.mp hF
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hF
  obtain ⟨flds, c, oid, u, he, hr, hm⟩ := hk.1 G hG
  exact ⟨flds, c, oid, u, by rw [HeapLinks.aliases_eq hk.2.2.1 hy]; exact he, hr, hm⟩

/-- Every live property-read link transfers the observed result predicate,
including observations admitting undefined. -/
def linkFacts (k : Knowledge) (slot : Nat) (R : ValueSets.ValueSet) : Facts :=
  (k.links.filter (fun g => !g.alias && g.value == slot)).map
    (fun g => ⟨g.cell,R,g.field⟩)

theorem linkFacts_holds {k slot R ρ h} (hk : Holds k ρ h) (hv : R.mem (ρ slot) = true) :
    HeapFacts.Holds (linkFacts k slot R) ρ h := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have hg := List.mem_filter.mp hg
  have hg2 := hg.2
  simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at hg2
  have hl := hk.2.2.1 g hg.1
  simp only [hg2.1,Bool.false_eq_true,ite_false] at hl
  cases ho : g.optional
  · simp only [ho,Bool.false_eq_true,ite_false] at hl
    obtain ⟨flds,c,oid,l,hl,hfd,hh⟩ := hl
    exact ⟨flds,c,oid,ρ g.value,hl,ReadGave.present hfd hh,by simpa [hg2.2] using hv⟩
  · simp only [ho,ite_true] at hl
    obtain ⟨flds,c,oid,hl,hr⟩ := hl
    exact ⟨flds,c,oid,ρ g.value,hl,hr,by simpa [hg2.2] using hv⟩

/-- An observed Boolean outcome refines cells only through current read links.
The ordinary value fact is useful even when no cell link exists. -/
def observeBoolean (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  let R : ValueSets.ValueSet := if q then { tru := true } else { fls := true }
  ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links,k.separation,
    k.elems ++ (k.elems.filter fun a => a.negated == !q &&
      a.cond.any fun c => (HeapLinks.aliases k.links slot).contains c).map ({ · with cond := none }),
    promoteIndices k.links k.indices slot q⟩

theorem observeBoolean_holds {k slot q ρ h} (hk : Holds k ρ h)
    (hq : ρ slot = if q then .tru else .fls) : Holds (observeBoolean k slot q) ρ h := by
  have hv : (if q then ({ tru := true } : ValueSets.ValueSet) else { fls := true }).mem (ρ slot) = true := by
    cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hq ⊢ <;> rw [hq] <;> rfl
  have ht : tagHolds .truthy (ρ slot) = q := by cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hq <;> rw [hq] <;> rfl
  refine ⟨?_,?_,hk.2.2.1,hk.2.2.2.1,?_,promoteIndices_holds hk.2.2.1 hk.2.2.2.2.2 ht⟩
  rotate_left 2
  · intro a ha hc
    rcases List.mem_append.mp ha with ha | ha
    · exact hk.2.2.2.2.1 a ha hc
    · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨b, ⟨hb, hneg, hcb⟩, rfl⟩ := ha
      refine hk.2.2.2.2.1 b hb fun c hc' => ?_
      rw [hc'] at hcb
      simp only [Option.any_some, List.contains_iff_mem] at hcb
      rw [HeapLinks.aliases_eq hk.2.2.1 hcb, hneg, hq]
      cases q <;> rfl
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact linkFacts_holds hk hv f hf
    · exact hk.1 f hf
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hv
    · exact hk.2.1 f hf

/-- A tag narrows a saved primitive predicate, and its still-live read links transfer
that observation to the heap. No link means no assertion about a mutable cell. -/
def observeTag (k : Knowledge) (slot : Nat) (tag : Tag) (q : Bool) : Knowledge :=
  match valueBy k (HeapLinks.aliases k.links) slot with
  | none => k
  | some V =>
    let R := V.meet (ValueSets.ofTag tag q)
    ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links,k.separation,k.elems,k.indices⟩

theorem observeTag_holds {k slot tag q ρ h} (hk : Holds k ρ h)
    (hq' : tagHolds tag (ρ slot) = q ∨ protoFree tag (ρ slot) = false) :
    Holds (observeTag k slot tag q) ρ h := by
  unfold observeTag
  split
  · exact hk
  · rename_i V hV
    have hv : V.mem (ρ slot) = true := valueBy_mem hk (aliases_class hk.2.2.1) hV
    have hR : (V.meet (ValueSets.ofTag tag q)).mem (ρ slot) = true := by
      rw [ValueSets.ValueSet.mem_meet, hv, ValueSets.ofTag_holds (ValueSets.ValueSet.mem_isVal hv) hq']; rfl
    refine ⟨?_,?_,hk.2.2⟩
    · intro f' hf'
      rcases List.mem_append.mp hf' with hf' | hf'
      · exact linkFacts_holds hk hR f' hf'
      · exact hk.1 f' hf'
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hR
      · exact hk.2.1 f' hf'

/-- A truthy answer of the slot `slot` makes the atoms conditional on it
unconditional. -/
def promoteTruthy (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  { k with
    elems := (k.elems ++ (k.elems.filter fun a => a.negated == !q &&
      a.cond.any fun c => (HeapLinks.aliases k.links slot).contains c).map ({ · with cond := none }))
    indices := promoteIndices k.links k.indices slot q }

theorem promoteTruthy_holds {k slot q ρ h} (hk : Holds k ρ h) (ht : tagHolds .truthy (ρ slot) = q) :
    Holds (promoteTruthy k slot q) ρ h := by
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, ?_, promoteIndices_holds hk.2.2.1 hk.2.2.2.2.2 ht⟩
  intro a ha hc
  rcases List.mem_append.mp ha with ha | ha
  · exact hk.2.2.2.2.1 a ha hc
  · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨b, ⟨hb, hneg, hcb⟩, rfl⟩ := ha
    refine hk.2.2.2.2.1 b hb fun c hc' => ?_
    rw [hc'] at hcb
    simp only [Option.any_some, List.contains_iff_mem] at hcb
    rw [HeapLinks.aliases_eq hk.2.2.1 hcb, ht, hneg]
    cases q <;> rfl

def observe (k : Knowledge) (slot : Nat) : BranchRefinement.Observation → Knowledge
  | .boolean q => observeBoolean k slot q
  | .tag t q => if t == .truthy then promoteTruthy (observeTag k slot t q) slot q else observeTag k slot t q

theorem observe_holds {k slot o ρ h} (hk : Holds k ρ h)
    (ho : o.holds (ρ slot)) : Holds (observe k slot o) ρ h := by
  cases o with
  | boolean q => exact observeBoolean_holds hk ho
  | tag t q =>
    simp only [observe]
    split
    · rename_i htq
      simp only [beq_iff_eq] at htq
      subst htq
      have ht : tagHolds .truthy (ρ slot) = q := by
        rcases ho with ho | ho
        · exact ho
        · simp [protoFree] at ho
      exact promoteTruthy_holds (observeTag_holds hk ho) ht
    · exact observeTag_holds hk ho

/-- A finite predicate vocabulary exactly interprets supported primitive clauses. -/
def primitive : List (Clause (Ty ι)) → Option (List Atom)
  | [] => some []
  | .nul :: cs => (primitive cs).map ([.nul] ++ ·)
  | .undef :: cs => (primitive cs).map ([.undef] ++ ·)
  | .bool :: cs => (primitive cs).map ([.tru,.fls] ++ ·)
  | .boolLit b :: cs => (primitive cs).map ([if b then .tru else .fls] ++ ·)
  | .num :: cs => (primitive cs).map ([.num] ++ ·)
  | .numLit b :: cs => (primitive cs).map ([.numLit b] ++ ·)
  | .str :: cs => (primitive cs).map ([.str] ++ ·)
  | .strLit s :: cs => (primitive cs).map ([.strLit s] ++ ·)
  | .numIn bs :: cs => (primitive cs).map (bs.map .numLit ++ ·)
  | .strIn ss :: cs => (primitive cs).map (ss.map .strLit ++ ·)
  | _ => none

/-- A type's members as atoms, when it is of clause rows. -/
def atoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then primitive (expand G A) else none

/-- `atoms`, deciding once that the type is of clause rows: `expand` would
decide it again. The compiler runs it in place of `atoms` (`atoms_eq_once`). -/
def atomsOnce (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then primitive (clausesOf G A) else none

@[csimp] theorem atoms_eq_once : @atoms = @atomsOnce := by
  funext ι G A
  unfold atoms atomsOnce
  split
  · next h => rw [expand_of_plain h]
  · rfl

theorem primitive_sem {G : NormalGraph ι} {cs R} (hc : primitive cs = some R) (n W v) :
    semList (excOf G) (meaning G) (argMeaning G) cs n W v ↔ ∃ a ∈ R, a.holds v := by
  induction cs generalizing R with
  | nil => simp [primitive] at hc; subst R; simp [semList,setSem]
  | cons c cs ih =>
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        simp only [hr,Option.map_some,Option.some.injEq] at hc
        subst R
        have hi := ih hr
        simp only [semList,setSem,List.mem_cons,exists_eq_or_imp] at hi ⊢
        rw [hi]
        simp [semWithArgs,nulT,undefT,boolT,numT,strT,Atom.holds,apply_ite,or_assoc]
        all_goals try (split <;> simp_all [Atom.holds])
        all_goals try (
          constructor
          · rintro (⟨b, hb, rfl⟩ | ⟨a, ha, hh⟩)
            · exact ⟨_, .inl ⟨b, hb, rfl⟩, rfl⟩
            · exact ⟨a, .inr ha, hh⟩
          · rintro ⟨a, (⟨b, hb, rfl⟩ | ha), hh⟩
            · exact .inl ⟨b, hb, hh⟩
            · exact .inr ⟨a, ha, hh⟩)

/-- The built-ins asks nothing of primitive clauses. -/
theorem primitive_plain : ∀ {cs : List (Clause (Ty ι))} {R}, primitive cs = some R →
    ∀ c ∈ cs, c.carriesInvariant = false
  | [], _, _ => by simp
  | c :: cs, R, hc => by
    intro d hd
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        rcases List.mem_cons.mp hd with rfl | hd
        · rfl
        · exact primitive_plain hr d hd

theorem atoms_sem {G : NormalGraph ι} {A R} (h : atoms G A = some R) (n W v) :
    meaning G A n W v ↔ ∃ a ∈ R, a.holds v := by
  unfold atoms at h
  split at h
  · rw [expand_sem G A (by assumption), setSem_row_plain (primitive_plain h)]
    exact primitive_sem h n W v
  · cases h

/-- The atoms a tag's answer leaves a value of `A` among: a string
equality's `true`, the one string; else, where a primitive predicate states
it, the answer's slice of `A`. -/
def observedAtoms (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Option (List Atom) :=
  match tag, q with
  | .strEq s, true => some [.strLit s]
  | _, _ => atoms G (BranchRefinement.tagSlice G A tag q)

theorem observedAtoms_sound {G : NormalGraph ι} {A : Ty ι} {tag q R n W v}
    (h : observedAtoms G A tag q = some R) (hm : meaning G A n W v)
    (ho : (BranchRefinement.Observation.tag tag q).holds v) : ∃ a ∈ R, a.holds v := by
  unfold observedAtoms at h
  split at h
  · rename_i s
    cases h
    have hv := (meaning_value hm).1
    simp only [BranchRefinement.Observation.holds, protoFree, Bool.true_eq_false, or_false] at ho
    cases v <;> simp [tagHolds] at ho
    subst ho
    exact ⟨.strLit _, by simp, rfl⟩
  · exact (atoms_sem h n W v).mp (BranchRefinement.tagSlice_sound hm ho)

/-- Each slot's type as the value set its predicates admit, where it is of
finitely many primitive predicates: each computed when first read, once. -/
def typeSets (G : NormalGraph ι) (Γ : List (Ty ι)) : Array (Thunk (Option ValueSets.ValueSet)) :=
  Γ.toArray.map fun A => Thunk.mk fun _ => (atoms G A).map ValueSets.ofAtoms

/-- The contexts read from computed type sets, slot `i` at index `i - shift`
(below `shift`, none). Kept out of line, so the sets are computed once by
the caller and only read here. -/
@[noinline] def setsCtx (ts : Array (Thunk (Option ValueSets.ValueSet))) (shift : Nat) :
    Nat → Option ValueSets.ValueSet :=
  fun i => if i < shift then none else (ts[i - shift]?).bind (·.get)

theorem typeSets_get (G : NormalGraph ι) (Γ : List (Ty ι)) (i : Nat) :
    ((typeSets G Γ)[i]?).bind (·.get) = (Γ[i]?).bind fun A => (atoms G A).map ValueSets.ofAtoms := by
  simp only [typeSets, Array.getElem?_map, List.getElem?_toArray]
  cases Γ[i]? <;> rfl

theorem typeSets_mem {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W} (he : EnvOk G Γ ρ n W) {i : Nat}
    {C : ValueSets.ValueSet} (h : ((typeSets G Γ)[i]?).bind (·.get) = some C) : C.mem (ρ i) = true := by
  rw [typeSets_get] at h
  cases hA : Γ[i]? with
  | none => rw [hA] at h; cases h
  | some A =>
    rw [hA] at h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ValueSets.ofAtoms_holds ((atoms_sem hR n W (ρ i)).mp (he.2 i A hA))

/-- What every live read link states of its cell where its value's slot has
a type denoting finitely many primitive predicates (`link-fact`,
PROGRAM-TYPING.md, "A call that keeps the heap"): reading the field gives that
value, so it meets one of them. -/
def typedLinkFacts (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Facts :=
  let sets := typeSets G Γ
  linkFactsBy (setsCtx sets 0) k
where
  /-- With each slot's type set read through `t`, each computed once. -/
  linkFactsBy (t : Nat → Option ValueSets.ValueSet) (k : Knowledge) : Facts :=
    k.links.filterMap fun g => if g.alias then none else (t g.value).map fun R => ⟨g.cell, R, g.field⟩

/-- The knowledge with its read links' typed facts (`typedLinkFacts`). -/
def withTypedLinks (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Knowledge :=
  { k with cells := typedLinkFacts G Γ k ++ k.cells }

theorem withTypedLinks_holds {G : NormalGraph ι} {Γ k ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) : Holds (withTypedLinks G Γ k) ρ h := by
  refine ⟨fun f hf => ?_, hk.2.1, hk.2.2⟩
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨g, hg, hf⟩ := List.mem_filterMap.mp hf
    split at hf
    · cases hf
    · rename_i ha
      obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp hf
      have hv := typeSets_mem he (by simpa [setsCtx] using hR)
      exact linkFacts_holds hk hv _ (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, by simp [ha]⟩, rfl⟩)
  · exact hk.1 f hf

/-- A tag observation combines the saved predicate with the tested value's
ordinary type. This retains facts such as a falsy object-or-undefined being
undefined, whose broad saved nullish predicate alone is insufficient. -/
@[nospecialize] def observeTyped (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (slot : Nat) (o : BranchRefinement.Observation) : Knowledge :=
  let out := observe (withTypedLinks G Γ k) slot o
  match o, Γ[slot]? with
  | .tag tag q, some A =>
    match observedAtoms G A tag q with
    | some R => ⟨linkFacts k slot (ValueSets.ofAtoms R) ++ out.cells, ⟨slot,ValueSets.ofAtoms R,valueField⟩ :: out.values,
        out.links, out.separation, out.elems, out.indices⟩
    -- Otherwise the answer itself is a fact of every cell the value was
    -- read from (a separate fact: all of a cell's facts hold). A slice of
    -- objects a test leaves, `x` truthy where `x` is an object or undefined,
    -- also has values neither null nor undefined.
    | none =>
      let out : Knowledge := ⟨linkFacts k slot (ValueSets.ofTag tag q) ++ out.cells, out.values, out.links,
        out.separation, out.elems, out.indices⟩
      if G.plainTy (BranchRefinement.tagSlice G A tag q) && (expand G (BranchRefinement.tagSlice G A tag q)).all
          (fun c => tagClause .isNullish c == some false) then
        ⟨linkFacts k slot (ValueSets.ofAtom .nonNullish) ++ out.cells,
          ⟨slot,ValueSets.ofAtom .nonNullish,valueField⟩ :: out.values, out.links, out.separation, out.elems, out.indices⟩
      else out
  | _, _ => out

theorem observeTyped_holds {G : NormalGraph ι} {Γ k slot o ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (ho : o.holds (ρ slot)) :
    Holds (observeTyped G Γ k slot o) ρ h := by
  have hout := observe_holds (withTypedLinks_holds he hk) ho
  unfold observeTyped
  split
  · rename_i tag q A hi
    split
    · rename_i R hr
      have hv := ValueSets.ofAtoms_holds (observedAtoms_sound hr (he.2 slot A hi) ho)
      refine ⟨?_, ?_, hout.2.2⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact linkFacts_holds hk hv f hf
        · exact hout.1 f hf
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hv
        · exact hout.2.1 f hf
    · have htag : (ValueSets.ofTag tag q).mem (ρ slot) = true :=
        ValueSets.ofTag_holds (meaning_value (he.2 slot A hi)).1 ho
      have hout : Holds ⟨linkFacts k slot (ValueSets.ofTag tag q) ++ (observe (withTypedLinks G Γ k) slot (.tag tag q)).cells,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).values, (observe (withTypedLinks G Γ k) slot (.tag tag q)).links,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).separation,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).elems,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).indices⟩ ρ h := by
        refine ⟨?_, hout.2.1, hout.2.2⟩
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact linkFacts_holds hk htag f hf
        · exact hout.1 f hf
      dsimp only
      by_cases hn : (G.plainTy (BranchRefinement.tagSlice G A tag q) && (expand G (BranchRefinement.tagSlice G A tag q)).all
          (fun c => tagClause .isNullish c == some false)) = true
      · rw [if_pos hn]
        have hm := BranchRefinement.tagSlice_sound (he.2 slot A hi) ho
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hn
        have hq := answers_sound (show Answers G _ .isNullish false from ⟨hn.1, hn.2⟩) hm
        have hval := (meaning_value hm).1
        have hv : (ValueSets.ofAtom .nonNullish).mem (ρ slot) = true := by
          refine ValueSets.ofAtom_holds ⟨hval, ?_, ?_⟩
          · intro h; rw [h] at hq; simp [tagHolds] at hq
          · intro h; rw [h] at hq; simp [tagHolds] at hq
        refine ⟨?_, ?_, hout.2.2⟩
        · intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact linkFacts_holds hk hv f hf
          · exact hout.1 f hf
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hv
          · exact hout.2.1 f hf
      · rw [if_neg hn]; exact hout
  · exact hout

/-- A type's atoms answer no tag: they are primitive predicates. -/
theorem primitive_noTag : ∀ {cs : List (Clause (Ty ι))} {R}, primitive cs = some R → R.all (!·.isTag) = true
  | [], _, h => by simp [primitive] at h; subst h; rfl
  | c :: cs, R, h => by
    cases c <;> simp only [primitive] at h
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at h
      | some rs =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        have := primitive_noTag hr
        simp only [List.all_append, this, Bool.and_true]
        try (rename_i b; cases b)
        all_goals simp [Atom.isTag]

theorem atoms_noTag {G : NormalGraph ι} {A R} (h : atoms G A = some R) : R.all (!·.isTag) = true := by
  unfold atoms at h
  split at h
  · exact primitive_noTag h
  · cases h

end Verification.HeapKnowledge
