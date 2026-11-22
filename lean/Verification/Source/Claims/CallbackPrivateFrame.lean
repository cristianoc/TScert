import Verification.Semantics.Reach.Runs
import Verification.Source.Claims.CallbackInferencePlan

namespace Verification.SourceClaimJson.CallbackInferencePlan
open TolerantFrames TolerantFrames.Reach Footprints HeapObservations

/-- A completed invocation cannot change any old cell outside the transitive
reach of its callee, receiver and arguments, including closure bindings. -/
theorem call_keeps_unreachable {before after : Heap} {t v : Tm} (run : ValRun before t after v)
    {l value} (cell : before[l]? = some value)
    (hidden : ¬ReachesFrom allC before (vals allC Realm.empty true false t) l) :
    after[l]? = some value := by
  induction run with
  | refl => exact cell
  | step hh hs _ ih =>
    have stable := Classical.byContradiction fun changed => by
      obtain ⟨u,hu,a,ha⟩ := step_reach (ofC := allC) (rl := Realm.empty) hs none false rfl cell changed
      exact hidden ⟨u,hu,[a],ha⟩
    apply ih stable
    intro reached
    rcases step_noForge (ofC := allC) (rl := Realm.empty) (nk := false) (fun _ h => by cases h)
      hh hs none rfl l reached with old | fresh
    · exact hidden old
    · exact (Nat.not_lt_of_ge fresh) (List.getElem?_eq_some_iff.mp cell).1

/-- No value stored anywhere contains a handle to the private field,
including handles in nested closure bindings. Direct graph slots may still
hold the object. -/
def hiddenInHeap (h : Heap) (l : Nat) : Prop :=
  ∀ (i : Nat) v, h[i]? = some v → ¬Leaves allC v l

theorem noPathOfHidden {h l} (heap : hiddenInHeap h l) {v} (clean : ¬Leaves allC v l) :
    ¬Reaches allC h v l := by
  rintro ⟨path,hp⟩
  induction path generalizing v with
  | nil => exact hp
  | cons a rest ih =>
    cases rest with
    | nil => exact clean ⟨_,.refl _,a,hp⟩
    | cons b bs =>
      obtain ⟨u, edge, tail⟩ := hp
      rcases edge with ⟨i,_,lookup⟩ | ⟨i,_,lookup⟩
      · exact ih (heap i u lookup) tail
      · exact ih (fun old => clean (Leaves.code (List.mem_of_getElem? lookup) old)) tail

/-- An arbitrary evaluation that starts without a handle to an old
private field cannot publish a handle to it, even through other storage. -/
theorem call_cannot_publish {before after : Heap} {t v : Tm} (run : ValRun before t after v)
    {l} (old : l < before.length) (heap : hiddenInHeap before l)
    (hidden : ¬ReachesFrom allC before (vals allC Realm.empty true false t) l) :
    hiddenInHeap after l ∧ ¬ReachesFrom allC after (vals allC Realm.empty true false v) l := by
  induction run with
  | refl => exact ⟨heap,hidden⟩
  | step hh hs _ ih =>
    apply ih (Nat.lt_of_lt_of_le old (step_length_le hs))
    · intro i u lookup leaf
      rename_i h h₁ h₂ t t₁ t₂ _
      by_cases before : ∃ v, h[i]? = some v ∧ h₁[i]? = some v
      · obtain ⟨v,hb,ha⟩ := before
        rw [lookup] at ha
        cases ha
        exact heap i _ hb leaf
      · have active : ¬Inert allC u := by
          intro inert
          obtain ⟨w,chain,a,edge⟩ := leaf
          cases chain with
          | refl => rw [inert.1 a] at edge; contradiction
          | step hx _ => rw [inert.2] at hx; contradiction
        have inRoots := step_writes (ofC := allC) (rl := Realm.empty) hs none false rfl before lookup active
        exact hidden ⟨u,inRoots,leaf.reaches⟩
    · intro reachable
      rcases step_noForge (ofC := allC) (rl := Realm.empty) (nk := false) (fun _ h => by cases h)
        hh hs none rfl l reachable with reached | fresh
      · exact hidden reached
      · omega

/-- At the field-allocation reduction, every initializer and every old
heap value refers only to previously allocated locations. The returned
object can name the new field, but its heap cannot yet contain a handle
to that field. -/
theorem makeFields_hidden {s : IndexedHeap} {code keys values} (valid : RefsOk s.W (.makeAt code keys values))
    {l} (fresh : s.h.length ≤ l) : hiddenInHeap (s.h ++ values ++ [.nul]) l := by
  intro i v lookup leaf
  have within : RefsOk s.W v := by
    have member := List.mem_of_getElem? lookup
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with (old | init) | rfl
    · obtain ⟨n,hn⟩ := List.getElem?_of_mem old
      exact contents_valid (List.getElem?_eq_some_iff.mp hn).1 hn
    · intro r hr
      apply valid r
      rw [Kinds.refs_makeAt]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨v,init,hr⟩)
    · intro r hr
      cases hr
  exact (Nat.not_lt_of_ge fresh) (Leaves.lt (s := s) (RefsOk.refsOkN within) leaf)

/-- Reading any field of a graph slot can only return a value already in
storage, or undefined, even when lookup follows the prototype chain. -/
theorem readSlot_hidden {before after : Heap} {key receiver v l}
    (run : ValRun before (.readAt key receiver) after v) (recv : isVal receiver = true)
    (heap : hiddenInHeap before l) (value : isVal v = true) :
    after = before ∧ ¬Leaves allC v l := by
  generalize expr : Tm.readAt key receiver = t at run
  induction run generalizing receiver with
  | refl => cases expr; cases value
  | step hh hs tr ih =>
    subst_vars
    cases hs with
    | readC step => exact (value_no_step recv step).elim
    | readProto _ _ lookup =>
      exact ih (hh _ _ lookup) heap value rfl
    | readField _ lookup =>
      cases tr with
      | refl => exact ⟨rfl,heap _ _ lookup⟩
      | step _ step _ => exact (value_no_step (hh _ _ lookup) step).elim
    | readMissing _ _ =>
      cases tr with
      | refl =>
        refine ⟨rfl,?_⟩
        rintro ⟨w,chain,a,edge⟩
        cases chain with
        | refl => cases a <;> cases edge
        | step hx _ => cases hx
      | step _ step _ => exact (value_no_step (by rfl) step).elim

private theorem leafActive {v l} (leaf : Leaves allC v l) : ¬Inert allC v := by
  rintro ⟨f,c⟩
  obtain ⟨w,chain,a,edge⟩ := leaf
  cases chain with
  | refl => rw [f a] at edge; contradiction
  | step hx _ => rw [c] at hx; contradiction

theorem valClean {h l t} (hidden : ¬ReachesFrom allC h (vals allC Realm.empty true false t) l) :
    ¬Leaves allC t l :=
  fun leak => hidden ⟨t,mem_vals_self (leafActive leak),leak.reaches⟩

theorem throwClean {h l t v} (hidden : ¬ReachesFrom allC h (vals allC Realm.empty true false t) l)
    (raised : Raises t v) : ¬Leaves allC v l :=
  fun leak => hidden ⟨v,raises_vals raised (mem_vals_self (leafActive leak)),leak.reaches⟩

/-- A write through a private slot may change the slot's own field. Its
evaluated value cannot publish a handle; if the operand throws, the
handler receives a value with no such handle either. -/
theorem writeSlot_hidden {before after : Heap} {key receiver rhs t l}
    (run : ValRun before (.writeAt key receiver rhs) after t) (recv : isVal receiver = true)
    (old : l < before.length) (heap : hiddenInHeap before l)
    (hidden : ¬ReachesFrom allC before (vals allC Realm.empty true false rhs) l) :
    hiddenInHeap after l ∧ (isVal t = true → ¬Leaves allC t l) ∧ (∀ v, Raises t v → ¬Leaves allC v l) := by
  generalize expr : Tm.writeAt key receiver rhs = u at run
  induction run generalizing receiver rhs with
  | refl =>
    cases expr
    refine ⟨heap, ⟨?_,?_⟩⟩
    · intro hv; cases hv
    intro v raised
    cases raised with
    | writeC1 hr => exact (Bool.noConfusion (recv.symm.trans (raises_not_val hr)))
    | writeC2 _ hr => exact throwClean hidden hr
  | step hh hs tr ih =>
    subst_vars
    cases hs with
    | writeC1 step => exact (value_no_step recv step).elim
    | writeC2 vr step =>
      have state := call_cannot_publish (.step hh step .refl) old heap hidden
      exact ih vr (Nat.lt_of_lt_of_le old (step_length_le step)) state.1 state.2 rfl
    | writeField val found inHeap =>
      cases tr with
      | step _ step _ => exact (value_no_step (by rfl) step).elim
      | refl =>
        refine ⟨?_,?_,?_⟩
        · intro i v hv
          simp only [List.getElem?_set] at hv
          split at hv
          · cases hv
            exact valClean hidden
          · exact heap _ _ hv
        · intro _ leaf
          exact leafActive leaf ⟨by intro a; cases a <;> rfl,rfl⟩
        · intro v raised
          cases raised

end Verification.SourceClaimJson.CallbackInferencePlan
