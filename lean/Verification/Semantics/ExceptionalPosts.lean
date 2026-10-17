import Verification.Semantics.HeapObservations

/-! Safety with a postcondition on a throw as well. `SafePost` states nothing
of the heap a throw leaves; `SafePostExc` states `R` of it, the heap the term
raises in. It uses exactly the same steps, world extensions and heap
invariant, and a thrown value is still of the exception family. -/
namespace Verification.HeapObservations
open Verification

/-- `SafePost` whose throw also meets `R` at the heap it raises in. -/
def SafePostExc (Ξ : Fam) (T : Fam) (Q : Post) (R : Heap → Prop) :
    (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      ((isVal t = true ∧ T (n + 1) W t ∧ Q h t) ∨ (Thrown Ξ (n + 1) W t ∧ R h)) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧
          HeapOk n U h' ∧ SafePostExc Ξ T Q R n U h' t')

/-- Forgetting the throw's postcondition gives `SafePost`. -/
theorem SafePostExc.post {Ξ T Q R} : ∀ {n W h t}, SafePostExc Ξ T Q R n W h t → SafePost Ξ T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (hv | ⟨hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr hr)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih hs⟩

/-- A throw's postcondition that always holds adds nothing to `SafePost`. -/
theorem SafePostExc.of_post {Ξ T Q} {R : Heap → Prop} (hR : ∀ h, R h) :
    ∀ {n W h t}, SafePost Ξ T Q n W h t → SafePostExc Ξ T Q R n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (hv | hr) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ⟨hr, hR h⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih hs⟩

/-- Consequence at the budgets an execution can reach, on both
postconditions. -/
theorem SafePostExc.consequence_below' {Ξ Ξ' T U : Fam} {Q Q' : Post} {R R' : Heap → Prop} : ∀ {n},
    (∀ j, j ≤ n → ∀ W v, Ξ j W v → Ξ' j W v) →
    (∀ j, j ≤ n → ∀ W v, T j W v → U j W v) →
    (∀ h v, Q h v → Q' h v) → (∀ h, R h → R' h) →
    ∀ {W h t}, SafePostExc Ξ T Q R n W h t → SafePostExc Ξ' U Q' R' n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro hexc hsub hpost hr W h t hs
    rcases hs with (⟨hv, ht, hq⟩ | ⟨hth, hR⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hsub _ (Nat.le_refl _) _ _ ht, hpost _ _ hq⟩)
    · exact .inl (.inr ⟨hth.mono (hexc _ (Nat.le_refl _) _), hr _ hR⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh,
        ih (fun j hj => hexc j (by omega)) (fun j hj => hsub j (by omega)) hpost hr hs⟩

theorem SafePostExc.weaken {Ξ T} {Q Q' : Post} {R R' : Heap → Prop}
    (hq : ∀ h v, Q h v → Q' h v) (hr : ∀ h, R h → R' h)
    {n W h t} (hs : SafePostExc Ξ T Q R n W h t) : SafePostExc Ξ T Q' R' n W h t :=
  SafePostExc.consequence_below' (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hq hr hs

theorem SafePostExc.value {Ξ T Q R n W h v} (hv : isVal v = true) (ht : T n W v) (hq : Q h v) :
    SafePostExc Ξ T Q R n W h v := by
  cases n with
  | zero => trivial
  | succ n => exact .inl (.inl ⟨hv, ht, hq⟩)

/-- Overload combination over two executions of the same term: both
postconditions survive, on a normal return and on a throw. -/
theorem SafePostExc.cross_upto {Ξ} {B C D : Fam} {Q Q' : Post} {R R' : Heap → Prop} :
    ∀ (n : Nat), CrossCompatUpTo n B C D →
    ∀ (W W' : WorldT n) (h : Heap) (t : Tm), HeapOk n W h → HeapOk n W' h →
      SafePostExc Ξ B Q R n W h t → SafePostExc Ξ C Q' R' n W' h t →
        SafePostExc Ξ D (fun heap value => Q heap value ∧ Q' heap value) (fun heap => R heap ∧ R' heap)
          n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro hc W W' h t hok hok'
    rintro ((⟨hv1, hBv, hQ⟩ | ⟨hr1, hR1⟩) | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩)
      ((⟨hv2, hCv, hQ2⟩ | ⟨hr2, hR2⟩) | ⟨Z', h2, t2, -, -, hst2, hok2, hcont2⟩)
    · exact .inl (.inl ⟨hv1, hc (p + 1) (Nat.le_refl _) W W' h hok hok' t hBv hCv, hQ, hQ2⟩)
    · rw [hr2.not_val] at hv1; contradiction
    · exact absurd hst2 (value_no_step hv1)
    · rw [hr1.not_val] at hv2; contradiction
    · exact .inl (.inr ⟨hr1, hR1, hR2⟩)
    · exact absurd hst2 hr1.no_step
    · exact absurd hst1 (value_no_step hv2)
    · exact absurd hst1 hr2.no_step
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact .inr ⟨Z, h1, t1, hz, huz, hst1, hok1,
        ih (fun j hj => hc j (by omega)) Z Z' h1 t1 hok1 hok2 hcont1 hcont2⟩

/-- A heap condition that each step keeps, and that holds where the run
starts, holds wherever it raises. -/
theorem SafePostExc.of_invariant {Ξ T Q} {R : Heap → Prop}
    (hstep : ∀ {h t h' t'}, R h → Step h t h' t' → R h') :
    ∀ {n W h t}, R h → SafePost Ξ T Q n W h t → SafePostExc Ξ T Q R n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hR hs
    rcases hs with (hv | hr) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ⟨hr, hR⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih (hstep hR step) hs⟩

/-- Composition through an evaluation context: a throw of the subterm is a
throw of the whole at the same heap, so the subterm's throw postcondition is
the whole's. -/
theorem SafePostExc.bind {Ξ} {A B : Fam} {Q Q' : Post} {R : Heap → Prop} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (raise : ∀ {t v}, Raises t v → Raises (C t) v) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → SafePostExc Ξ A Q R n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Q h' v →
        SafePostExc Ξ B Q' R j U h' (C v)) → SafePostExc Ξ B Q' R n W h (C t) := by
  intro n; induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro W h t hw hh hs hc
    rcases hs with (⟨hv, ha, hq⟩ | ⟨hr, hR⟩) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
    · exact hc (p+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ha hq
    · exact .inl (.inr ⟨hr.lift raise, hR⟩)
    · refine .inr ⟨U, h', C t', hx, hu, lift step, hh', ih U h' t' hu hh' hs' ?_⟩
      intro j hj V he hv h'' v hh'' hval ha hq
      apply hc j (by omega) V _ hv h'' v hh'' hval ha hq
      have he' := WExt_trunc hj hx
      rw [trunc_trunc] at he'
      exact WExt_trans he' he

theorem SafePostExc.bind_value {Ξ T Q R n} {W : WorldT (n+1)} {h b a}
    (hv : isVal a = true) (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : SafePostExc Ξ T Q R n (trunc n (Nat.le_succ n) W) h (subst 0 a b)) :
    SafePostExc Ξ T Q R (n+1) W h (.letE a b) :=
  .inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hw, .letV hv, HeapOk_trunc n W h hh, hs⟩

/-- A term that steps once to a value raises nothing: any throw postcondition
holds of its run. -/
theorem SafePostExc.one_step {Ξ T Q R n W h t h' v} (ht : isVal t = false) (hv : isVal v = true)
    (step : Step h t h' v) (hq : Q h' v) (hs : Safe Ξ T n W h t) :
    SafePostExc Ξ T Q R n W h t := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, _⟩ | hr) | ⟨U, h'', t'', hx, hu, step', hh, hs'⟩
    · simp [ht] at hval
    · exact absurd step hr.no_step
    · obtain ⟨rfl, rfl⟩ := Step_det step step'
      exact .inr ⟨U, h', v, hx, hu, step', hh, by
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs' with (⟨_, ht'⟩ | hr) | ⟨_, _, _, _, _, step'', _, _⟩
          · exact .inl (.inl ⟨hv, ht', hq⟩)
          · exact absurd hr (val_not_thrown hv)
          · exact False.elim (value_no_step hv step'')⟩

end Verification.HeapObservations
