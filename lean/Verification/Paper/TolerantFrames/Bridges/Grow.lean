import Verification.Paper.TolerantFrames.Bridges.Transfer
import Verification.Programs.TolerantFramesNamed
import Verification.Paper.TolerantFrames.Instances
import Verification.Paper.TolerantFrames.ParityDerivations

/-! # Tolerant frames: (Grow) and its instances

(Grow), a length lower bound kept by every action of
`{values: any, spines: grow}`, at a variable (`grow`) and along a rigid path
(`grow_path`), by the tolerant frame at the support `{x.spine: grow}`
(`Parity.atom_frame`); its form over names (`named_lowerBound_grow`,
`named_lowerBound_field`); a typed field write keeping every length lower
bound on both exits (`field_write_keeps_bound`); and the loop of
`out[j] = xs[j]`, its aliasing write and its back edge. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom)
open ControlFlow PointClaims

/-! ## (Grow) -/

/-- **(Grow)** `y ≤ |x| ⊢ □_{values: any, spines: grow} (y ≤ |x|)` (the note,
Proposition "Axioms of the atoms"): the tolerant frame at the support
`{x.spine: grow}`, which `{values: any, spines: grow}` respects since `x`
reads an array (`Parity.atom_frame`). -/
theorem grow {y x : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} (hb : LowerBound ε y x ρ m s) :
    Box growEffect.fp (LowerBound ε y x) ρ m s := by
  have hF : ∀ t ∈ (Linear.Fact.le [(HeapKnowledge.Term.value y, 1), (HeapKnowledge.Term.length x, -1)] 0).vars,
      t.atEntry = false := by
    simp [Linear.Fact.vars, HeapKnowledge.Term.value, HeapKnowledge.Term.length]
  have hbox := Parity.atom_frame (m := m)
    (x := .linear (.le [(HeapKnowledge.Term.value y, 1), (HeapKnowledge.Term.length x, -1)] 0))
    (S := [(.spine x [], .grow)]) (Φ := growEffect.fp) (sev := .lengths) (rev := ⟨[.classes (.arrayAt ⟨0⟩) .intrinsic]⟩)
    (by simp [Parity.SupportEvidence.check, Parity.lengthsSupported, Parity.growsWith, Linear.Fact.vars,
      HeapKnowledge.Term.value, HeapKnowledge.Term.length])
    (by
      simp [Parity.RespectEvidence.check, respects, Parity.RespectEvidence.query, Parity.DisjointEvidence.check,
        Parity.ClassWitness.selector, Parity.conjuncts, Parity.arrayNode, growEffect, Footprints.Closed.fp,
        Parity.regionClass, Linear.Fact.vars, Parity.Path.term, HeapKnowledge.Term.length]
      decide)
    ((Parity.linear_holdsAt_iff hF).mp hb)
  exact fun s' ha => (Parity.linear_holdsAt_iff hF).mpr (hbox s' ha)

/-- **(Grow) at a rigid path** (the note, Proposition "Axioms of the
atoms", (Rigid) with (Grow)): along a stable path, `y ≤ |x.p|` survives every
action of `{values: any, spines: grow}`. The path reads its value `v` at every
admissible state; `y ≤ |z|` at a fresh slot `z` holding `v` enters the
modality by (Grow), and the effect reads its classes at no slot. -/
theorem grow_path {y x : Nat} {p : List String} {v : Val} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hp : StableAt x p v ρ m s) (hb : PathLowerBound y x p ρ m s) :
    Box growEffect.fp (PathLowerBound y x p) ρ m s := by
  intro s' ha
  obtain ⟨w, a, len, hw, hy, hl, hle⟩ := hb
  have hwv : w = v := Option.some.inj (hw.symm.trans (hp.read s.pos s.ok))
  subst hwv
  have h0 : LowerBound ⟨ρ, s.h⟩ (y + 1) 0 (push w ρ) m s :=
    pathLowerBound_iff (m := m).mp ⟨w, a, len, rfl, hy, hl, hle⟩
  have ha0 : Action growEffect.fp (push w ρ) s s' :=
    ⟨ha.1, Footprints.Closed.post_iff.mpr (Footprints.Closed.post_iff.mp ha.2)⟩
  obtain ⟨w', a', len', hw', hy', hl', hle'⟩ := pathLowerBound_iff (m := m).mpr (grow h0 s' ha0)
  cases hw'
  exact ⟨w, a', len', ha.1.readPath hp, hy', hl', hle'⟩

/-! ## Named facts an effect keeps -/

/-- **(Grow) as a named fact** (the note, Proposition "Axioms of the
atoms"): a length lower bound over names survives every action of
`{values: any, spines: grow}`: the tolerant frame at `{x.spine: grow}`
(`grow`, `Parity.atom_frame`), the effect reading its classes at no name. -/
theorem named_lowerBound_grow {y x : Nat} {η ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η ρ m s) :
    Box growEffect.fp (Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η) ρ m s := by
  intro s' ha a hm
  simp only [List.mem_singleton] at hm
  subst hm
  intro a' ha' _
  simp only [List.mem_singleton] at ha'
  subst ha'
  have hb : LowerBound ε y x η m s :=
    hS _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) (fun _ h => by cases h)
  exact grow hb s' ⟨ha.1, Footprints.Closed.post_iff.mpr (Footprints.Closed.post_iff.mp ha.2)⟩

/-- (Grow) under the field write's effect, within the element write's. -/
theorem named_lowerBound_field {y x : Nat} {η ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η ρ m s) :
    Box fieldWriteEffect.fp (Named ε [.index ⟨lowerBoundFact y x, none, false⟩] η) ρ m s :=
  fun s' ha => named_lowerBound_grow hS s' (action_le_closed (by decide) ha)

/-! ## A typed field write -/

/-- **A typed field write keeps every length lower bound, on both exits**,
exposing each exit's endpoint: the action of `{values: any, spines: keep}`, the
residual budget, the result's type or the raised value's family, and the
bound. -/
theorem field_write_keeps_bound {ι : Type} [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {Γ} {t : Tm} {Ξ T : Fam} {ρ : Env} {s : IndexedHeap} {y x m k : Nat}
    {h' : Heap} {t' : Tm}
    (hc : ExpressionEffects.fieldWriteWithin G Γ fieldWriteEffect t = true)
    (he : ProgramTyping.EnvOk G Γ ρ s.n s.W) (hs : Safe Ξ T s.n s.W s.h (instantiate 0 ρ t))
    (hst : Steps k s.h (instantiate 0 ρ t) h' t') (hk : k < s.n) (hb : LowerBound ε y x ρ m s) :
    (isVal t' = true → ∃ s' : IndexedHeap, Action fieldWriteEffect.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ T s'.n s'.W t' ∧ LowerBound ε y x ρ m s') ∧
      (∀ e, Raises t' e → ∃ s' : IndexedHeap, Action fieldWriteEffect.fp ρ s s' ∧ s'.h = h' ∧
        s'.n + k = s.n ∧ Scoped 0 e ∧ Ξ s'.n s'.W e ∧ LowerBound ε y x ρ m s') := by
  have hp := HeapObservations.SafePostExc.weaken (Q' := fun h' _ => fieldWriteEffect.Holds s.h h' ∧ True)
    (R' := fun h' => fieldWriteEffect.Holds s.h h' ∧ True) (fun _ _ h => ⟨h, trivial⟩) (fun _ h => ⟨h, trivial⟩)
    (ExpressionEffects.field_write_within_exc hc he s.ok hs)
  have hgrow : ∀ s', Action fieldWriteEffect.fp ρ s s' → LowerBound ε y x ρ m s' :=
    fun s' ha => grow hb s' (action_le_closed (by decide) ha)
  refine ⟨fun hv => ?_, fun e hr => ?_⟩
  · obtain ⟨s', ha, he', hn, hT, -⟩ := action_normal (ρ := ρ) hp hst hv hk
    exact ⟨s', ha, he', hn, hT, hgrow s' ha⟩
  · obtain ⟨s', ha, he', hn, hsc, hΞ, -⟩ := action_throw (ρ := ρ) hp hst hr hk
    exact ⟨s', ha, he', hn, hsc, hΞ, hgrow s' ha⟩

/-! ## The loop of `out[j] = xs[j]`: the aliasing write and the back edge

The note's loop `for (j = from; j < to; j++) out[j] = xs[j]`, its head
holding `0 ≤ j` and `to ≤ |xs|`. The write node's environment is
`v, j, to, xs, out` (slots 0 to 4); the increment binds `j' = j + 1` and the
back edge maps `j', to, xs, out` (slots 0, 3, 4, 5 after the push) to the
head's `j, to, xs, out`. `out` may be `xs`. -/

/-- Slot `j` holds a non-negative integer. It reads no heap. -/
def NonNeg (j : Nat) : Assertion := fun ρ _ _ => ∃ a, HeapKnowledge.intValue (ρ j) = some a ∧ 0 ≤ a

/-- **The aliasing element write keeps the head's facts** for the increment:
an element write at a run-time index, checked within
`{values: any, spines: grow}` whichever array it writes, and `to ≤ |xs|`
retained under that effect; `0 ≤ j` reads no heap. The escaping throw meets
the graph's exception family where the node's family does one level up. -/
theorem loop_write_obligations {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {ρ : Env}
    {m : Nat}
    {s₀ : IndexedHeap} {l : Nat}
    (hinc : ∀ s, NonNeg 1 ρ m s → LowerBound ε 2 3 ρ m s → pre l ρ m s)
    (hΞ : ∀ s e, Above Ξ s e → Ξres s.n s.W e ∧ Rres s.h)
    (hj : NonNeg 1 ρ m s₀) (hb : LowerBound ε 2 3 ρ m s₀) :
    NodeObligations pre Ξres Tres Qres Rres Ξ T growEffect growEffect (fun _ _ => True) (fun _ => True) ρ m s₀
      (.effect ⟨l, none⟩) none :=
  transfer (Kn := [lowerBoundFact 2 3]) (Ke := [])
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun F hF => by simp only [List.mem_singleton] at hF; subst hF; exact grow hb)
    (fun F hF => by simp at hF)
    (fun s _ _ _ _ _ htr => by
      have hb' : LowerBound ε 2 3 ρ m s :=
        htr ρ _ (List.mem_singleton_self _) some _ rfl (fun _ _ _ hg => by cases hg; rfl)
      exact hinc s hj hb')
    (fun s e _ _ hab _ _ => hΞ s e hab)

/-- The write node's local judgment: a typed write checked within
`{values: any, spines: grow}` (`ExpressionEffects.write_within_exc`), in the
form `NodesChecked` takes, with both posts `True`. -/
theorem grow_write_judgment {ι : Type} [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι} {Γ} {t : Tm}
    {Ξ T : Fam} {ρ : Env} {s : IndexedHeap}
    (hc : ExpressionEffects.writeWithin G Γ growEffect t = true) (he : ProgramTyping.EnvOk G Γ ρ s.n s.W)
    (hs : Safe Ξ T s.n s.W s.h (instantiate 0 ρ t)) :
    SafePostExc Ξ T (fun h' _ => growEffect.Holds s.h h' ∧ True) (fun h' => growEffect.Holds s.h h' ∧ True)
      s.n s.W s.h (instantiate 0 ρ t) :=
  HeapObservations.SafePostExc.weaken (fun _ _ h => ⟨h, trivial⟩) (fun _ h => ⟨h, trivial⟩)
    (ExpressionEffects.write_within_exc hc he s.ok hs)

/-- **The back edge with a changed head valuation**: after `j' = j + 1`, the
head holds `0 ≤ j` and `to ≤ |xs|` at its new environment, the head's slot 0
now `j'`. The bound is retained under the increment's empty effect and
renamed (`to, xs` from slots 2, 3 to 1, 2); `0 ≤ j'` follows from `0 ≤ j` and
the increment's post. -/
theorem loop_back_edge {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {ce : Footprints.Closed}
    {Qe : Heap → Prop}
    {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {hd : Nat}
    (hhead : ∀ ρ' s, NonNeg 0 ρ' m s → LowerBound ε 1 2 ρ' m s → pre hd ρ' m s)
    (hΞ : ∀ s e, Above Ξ s e → Ξres s.n s.W e ∧ Rres s.h)
    (hj : NonNeg 1 ρ m s₀) (hb : LowerBound ε 2 3 ρ m s₀) :
    NodeObligations pre Ξres Tres Qres Rres Ξ T Footprints.Closed.empty ce
      (fun _ v => ∃ a, HeapKnowledge.intValue (ρ 1) = some a ∧ HeapKnowledge.intValue v = some (a + 1)) Qe
      ρ m s₀ (.bind ⟨hd, some [0, 3, 4, 5]⟩) none :=
  transfer (Kn := [lowerBoundFact 2 3]) (Ke := [])
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun F hF s ha => by
      simp only [List.mem_singleton] at hF; subst hF
      exact grow hb s (action_le_closed (by decide) ha))
    (fun F hF => by simp at hF)
    (fun s v _ _ _ hq htr => by
      obtain ⟨a, ha, hv⟩ := hq
      obtain ⟨a', ha', hle⟩ := hj
      rw [ha] at ha'; cases ha'
      refine hhead _ s ⟨a + 1, ?_, by omega⟩ ?_
      · simpa [mapEnv, slot, push] using hv
      · refine htr _ _ (List.mem_singleton_self _)
          (fun i => if i = 2 then some 1 else if i = 3 then some 2 else none) (lowerBoundFact 1 2) rfl ?_
        intro i hi j hg
        simp only [lowerBoundFact, HeapKnowledge.IndexFact.slots] at hi
        by_cases h2 : i = 2
        · subst h2; simp at hg; subst hg; simp [mapEnv, slot, push]
        · by_cases h3 : i = 3
          · subst h3; simp at hg; subst hg; simp [mapEnv, slot, push]
          · simp [h2, h3] at hg)
    (fun s e _ _ hab _ _ => hΞ s e hab)

end Verification.TolerantFrames
