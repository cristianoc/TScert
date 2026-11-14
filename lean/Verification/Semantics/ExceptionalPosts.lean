import Verification.Semantics.HeapObservations

/-! Safety with a postcondition on a throw as well. `SafePost` states nothing
of the heap a throw leaves; `SafePostExc` states `R` of it, the heap the term
raises in. It uses exactly the same steps, world extensions and heap
invariant, and a thrown value is still of the exception family. -/
namespace Verification.HeapObservations
open Verification

/-- A postcondition of an exceptional exit that reads the exit world: the
budget left, the world the safety derivation reached there and the heap the
term raises in. -/
abbrev WExc := (k : Nat) → WorldT k → Heap → Prop

/-- **The lifting** of a heap-only exceptional postcondition: it ignores the
budget and the world. -/
abbrev WExc.lift (R : Heap → Prop) : WExc := fun _ _ h => R h

/-- `SafePostW` whose throw also meets `R` at the world and heap it raises
in. -/
def SafePostExcW (Ξ : Fam) (T : Fam) (Q : WPost) (R : WExc) :
    (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, W, _, t => RefsOk W t
  | n + 1, W, h, t => RefsOk W t ∧
      (((isVal t = true ∧ T (n + 1) W t ∧ Q (n + 1) W h t) ∨ (Thrown Ξ (n + 1) W t ∧ R (n + 1) W h)) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧
          HeapOk n U h' ∧ SafePostExcW Ξ T Q R n U h' t'))

theorem SafePostExcW.refs {Ξ T : Fam} {Q : WPost} {R : WExc} :
    ∀ {n W h t}, SafePostExcW Ξ T Q R n W h t → RefsOk W t
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => h.1

/-- `SafePostExcW` at heap-only postconditions, lifted. -/
abbrev SafePostExc (Ξ : Fam) (T : Fam) (Q : Post) (R : Heap → Prop) :
    (n : Nat) → WorldT n → Heap → Tm → Prop :=
  SafePostExcW Ξ T (WPost.lift Q) (WExc.lift R)

/-- Forgetting the throw's postcondition gives `SafePostW`. -/
theorem SafePostExcW.post {Ξ T} {Q : WPost} {R : WExc} :
    ∀ {n W h t}, SafePostExcW Ξ T Q R n W h t → SafePostW Ξ T Q n W h t := by
  intro n; induction n with
  | zero => intro _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (hv | ⟨hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr hr)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih hs⟩

theorem SafePostExc.post {Ξ T Q R} {n W h t} (hs : SafePostExc Ξ T Q R n W h t) : SafePost Ξ T Q n W h t :=
  SafePostExcW.post hs

/-- A throw's postcondition that always holds adds nothing to `SafePostW`. -/
theorem SafePostExcW.of_post {Ξ T} {Q : WPost} {R : WExc} (hR : ∀ k W h, R k W h) :
    ∀ {n W h t}, SafePostW Ξ T Q n W h t → SafePostExcW Ξ T Q R n W h t := by
  intro n; induction n with
  | zero => intro _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (hv | hr) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ⟨hr, hR _ _ h⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih hs⟩

theorem SafePostExc.of_post {Ξ T Q} {R : Heap → Prop} (hR : ∀ h, R h) {n W h t}
    (hs : SafePost Ξ T Q n W h t) : SafePostExc Ξ T Q R n W h t :=
  SafePostExcW.of_post (fun _ _ h => hR h) hs

/-- Consequence at the budgets an execution can reach, on both
postconditions. -/
theorem SafePostExcW.consequence_below' {Ξ Ξ' T U : Fam} {Q Q' : WPost} {R R' : WExc} : ∀ {n},
    (∀ j, j ≤ n → ∀ W v, Ξ j W v → Ξ' j W v) →
    (∀ j, j ≤ n → ∀ W v, T j W v → U j W v) →
    (∀ j, j ≤ n → ∀ W h v, Q j W h v → Q' j W h v) → (∀ j, j ≤ n → ∀ W h, R j W h → R' j W h) →
    ∀ {W h t}, SafePostExcW Ξ T Q R n W h t → SafePostExcW Ξ' U Q' R' n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro hexc hsub hpost hr W h t hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, ht, hq⟩ | ⟨hth, hR⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hsub _ (Nat.le_refl _) _ _ ht, hpost _ (Nat.le_refl _) _ _ _ hq⟩)
    · exact .inl (.inr ⟨hth.mono (hexc _ (Nat.le_refl _) _), hr _ (Nat.le_refl _) _ _ hR⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh,
        ih (fun j hj => hexc j (by omega)) (fun j hj => hsub j (by omega)) (fun j hj => hpost j (by omega))
          (fun j hj => hr j (by omega)) hs⟩

theorem SafePostExc.consequence_below' {Ξ Ξ' T U : Fam} {Q Q' : Post} {R R' : Heap → Prop} {n}
    (hexc : ∀ j, j ≤ n → ∀ W v, Ξ j W v → Ξ' j W v)
    (hsub : ∀ j, j ≤ n → ∀ W v, T j W v → U j W v)
    (hpost : ∀ h v, Q h v → Q' h v) (hr : ∀ h, R h → R' h)
    {W h t} (hs : SafePostExc Ξ T Q R n W h t) : SafePostExc Ξ' U Q' R' n W h t :=
  SafePostExcW.consequence_below' hexc hsub (fun _ _ _ h v hq => hpost h v hq) (fun _ _ _ h hq => hr h hq) hs

theorem SafePostExcW.weaken {Ξ T} {Q Q' : WPost} {R R' : WExc}
    (hq : ∀ k W h v, Q k W h v → Q' k W h v) (hr : ∀ k W h, R k W h → R' k W h)
    {n W h t} (hs : SafePostExcW Ξ T Q R n W h t) : SafePostExcW Ξ T Q' R' n W h t :=
  SafePostExcW.consequence_below' (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun j _ => hq j) (fun j _ => hr j) hs

theorem SafePostExc.weaken {Ξ T} {Q Q' : Post} {R R' : Heap → Prop}
    (hq : ∀ h v, Q h v → Q' h v) (hr : ∀ h, R h → R' h)
    {n W h t} (hs : SafePostExc Ξ T Q R n W h t) : SafePostExc Ξ T Q' R' n W h t :=
  SafePostExc.consequence_below' (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hq hr hs

theorem SafePostExcW.value {Ξ T} {Q : WPost} {R : WExc} {n W h v} (hv : isVal v = true) (ht : T n W v)
    (hq : Q n W h v) (hr : RefsOk W v) : SafePostExcW Ξ T Q R n W h v := by
  cases n with
  | zero => exact hr
  | succ n => exact ⟨hr, .inl (.inl ⟨hv, ht, hq⟩)⟩

theorem SafePostExc.value {Ξ T Q R n W h v} (hv : isVal v = true) (ht : T n W v) (hq : Q h v)
    (hr : RefsOk W v) : SafePostExc Ξ T Q R n W h v :=
  SafePostExcW.value hv ht hq hr

/-- **Two runs of one term at one world.** The first run's world is kept,
with its world-indexed postconditions; the second run takes the same steps
(`Step_det`), so its heap postconditions hold at the same exits, and its
result type combines with the first's (`CrossCompatUpTo`). -/
theorem SafePostExcW.cross {Ξ Ξ' B C D : Fam} {Q : WPost} {R : WExc} {Q' : Post} {R' : Heap → Prop} :
    ∀ (n : Nat), CrossCompatUpTo n B C D →
    ∀ (W W' : WorldT n) (h : Heap) (t : Tm), HeapOk n W h → HeapOk n W' h →
      SafePostExcW Ξ B Q R n W h t → SafePostExc Ξ' C Q' R' n W' h t →
        SafePostExcW Ξ D (fun k W h v => Q k W h v ∧ Q' h v) (fun k W h => R k W h ∧ R' h) n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ hs _; exact hs
  | succ p ih =>
    intro hc W W' h t hok hok'
    rintro ⟨hrf, hs1⟩ ⟨-, hs2⟩
    refine ⟨hrf, ?_⟩
    rcases hs1 with (⟨hv1, hBv, hQ⟩ | ⟨hr1, hR1⟩) | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩ <;>
    rcases hs2 with (⟨hv2, hCv, hQ2⟩ | ⟨hr2, hR2⟩) | ⟨Z', h2, t2, -, -, hst2, hok2, hcont2⟩
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

/-- Overload combination over two executions of the same term: both
postconditions survive, on a normal return and on a throw. -/
theorem SafePostExc.cross_upto {Ξ} {B C D : Fam} {Q Q' : Post} {R R' : Heap → Prop} (n : Nat)
    (hc : CrossCompatUpTo n B C D) (W W' : WorldT n) (h : Heap) (t : Tm) (hok : HeapOk n W h)
    (hok' : HeapOk n W' h) (h1 : SafePostExc Ξ B Q R n W h t) (h2 : SafePostExc Ξ C Q' R' n W' h t) :
    SafePostExc Ξ D (fun heap value => Q heap value ∧ Q' heap value) (fun heap => R heap ∧ R' heap)
      n W h t :=
  SafePostExcW.cross n hc W W' h t hok hok' h1 h2

/-- **Every execution prefix ends in a well-formed configuration under one
extension of the truncated entry world**: after `k` steps of a term safe at
budget `j + k`, a world at budget `j` extends the entry world truncated to
`j`, the heap meets it in both parts, the term's references are valid in it,
and safety continues there. The budget left may be zero. -/
theorem SafePostExcW.run {Ξ T : Fam} {Q : WPost} {R : WExc} :
    ∀ {k : Nat} {h : Heap} {t : Tm} {h' : Heap} {t' : Tm}, Steps k h t h' t' →
      ∀ {n : Nat} {W : WorldT n}, k ≤ n → WorldAdm W → HeapOk n W h → SafePostExcW Ξ T Q R n W h t →
      ∃ (j : Nat) (hj : j ≤ n) (U : WorldT j), j + k = n ∧ WExt (trunc j hj W) U ∧ WorldAdm U ∧
        HeapOk j U h' ∧ RefsOk U t' ∧ SafePostExcW Ξ T Q R j U h' t' := by
  intro k h t h' t' hst
  induction hst with
  | refl =>
    intro n W _ hadm hok hs
    exact ⟨n, Nat.le_refl n, W, rfl, by rw [trunc_id]; exact WExt_refl _, hadm, hok, hs.refs, hs⟩
  | next st _ ih =>
    intro n W hk hadm hok hs
    cases n with
    | zero => omega
    | succ m =>
      rcases hs.2 with (⟨hv, -, -⟩ | ⟨⟨_, hr, -⟩, -⟩) | ⟨U, h₁, t₁, hx, hu, st', hh, hs'⟩
      · exact absurd st (value_no_step hv)
      · exact absurd st (raises_no_step hr)
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        obtain ⟨j, hj, U', hjk, hx', hu', hh', hr', hs''⟩ := ih (by omega) hu hh hs'
        refine ⟨j, by omega, U', by omega, ?_, hu', hh', hr', hs''⟩
        simpa only [trunc_trunc] using WExt_trans (WExt_trunc hj hx) hx'

/-- Composition through an evaluation context: a throw of the subterm is a
throw of the whole at the same heap, so the subterm's throw postcondition is
the whole's. -/
theorem SafePostExc.bind {Ξ} {A B : Fam} {Q Q' : Post} {R : Heap → Prop} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (raise : ∀ {t v}, Raises t v → Raises (C t) v) (hctx : CtxRefs C) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → RefsOk W (C .undef) → SafePostExc Ξ A Q R n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Q h' v → RefsOk U v →
        SafePostExc Ξ B Q' R j U h' (C v)) → SafePostExc Ξ B Q' R n W h (C t) := by
  intro n; induction n with
  | zero => intro W h t _ _ hC hs _; exact hctx.ok hs hC
  | succ p ih =>
    intro W h t hw hh hC hs hc
    obtain ⟨hrf, hs⟩ := hs
    rcases hs with (⟨hv, ha, hq⟩ | ⟨hr, hR⟩) | ⟨U, h', t', hx, hu, step, hh', hs'⟩
    · exact hc (p+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ha hq hrf
    · exact ⟨hctx.ok hrf hC, .inl (.inr ⟨hr.lift raise, hR⟩)⟩
    · refine ⟨hctx.ok hrf hC, .inr ⟨U, h', C t', hx, hu, lift step, hh',
        ih U h' t' hu hh' (RefsOk_mono hx (RefsOk_trunc _ hC)) hs' ?_⟩⟩
      intro j hj V he hv h'' v hh'' hval ha hq hvr
      apply hc j (by omega) V _ hv h'' v hh'' hval ha hq hvr
      have he' := WExt_trunc hj hx
      rw [trunc_trunc] at he'
      exact WExt_trans he' he

theorem SafePostExc.bind_value {Ξ T Q R n} {W : WorldT (n+1)} {h b a}
    (hv : isVal a = true) (hw : WorldAdm W) (hh : HeapOk (n+1) W h) (href : RefsOk W (.letE a b))
    (hs : SafePostExc Ξ T Q R n (trunc n (Nat.le_succ n) W) h (subst 0 a b)) :
    SafePostExc Ξ T Q R (n+1) W h (.letE a b) :=
  ⟨href, .inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hw, .letV hv, HeapOk_trunc n W h hh, hs⟩⟩

/-- A term that steps once to a value raises nothing: any throw postcondition
holds of its run. -/
theorem SafePostExc.one_step {Ξ T Q R n W h t h' v} (ht : isVal t = false) (hv : isVal v = true)
    (step : Step h t h' v) (hq : Q h' v) (hs : Safe Ξ T n W h t) :
    SafePostExc Ξ T Q R n W h t := by
  cases n with
  | zero => exact hs
  | succ n =>
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hval, _⟩ | hr) | ⟨U, h'', t'', hx, hu, step', hh, hs'⟩
    · simp [ht] at hval
    · exact absurd step hr.no_step
    · obtain ⟨rfl, rfl⟩ := Step_det step step'
      exact .inr ⟨U, h', v, hx, hu, step', hh, by
        cases n with
        | zero => exact hs'
        | succ m =>
          obtain ⟨hrf', hs'⟩ := hs'
          refine ⟨hrf', ?_⟩
          rcases hs' with (⟨_, ht'⟩ | hr) | ⟨_, _, _, _, _, step'', _, _⟩
          · exact .inl (.inl ⟨hv, ht', hq⟩)
          · exact absurd hr (val_not_thrown hv)
          · exact False.elim (value_no_step hv step'')⟩

/-- **A world fact holds at every exit**: a fact of the world that every
extension and every truncation keep, true of the entry world, holds at the
world of each normal and exceptional exit, beside its postcondition. -/
theorem SafePostExcW.world {Ξ T : Fam} {Q : WPost} {R : WExc} {P : (k : Nat) → WorldT k → Prop}
    (hmono : ∀ k (W W' : WorldT k), WExt W W' → P k W → P k W')
    (htrunc : ∀ k j (hj : j ≤ k) (W : WorldT k), P k W → P j (trunc j hj W)) :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}, P n W → SafePostExcW Ξ T Q R n W h t →
      SafePostExcW Ξ T (fun k W h v => Q k W h v ∧ P k W) (fun k W h => R k W h ∧ P k W) n W h t
  | 0, _, _, _, _, hs => hs
  | _ + 1, _, _, _, hp, ⟨hr, hs⟩ => by
    refine ⟨hr, ?_⟩
    rcases hs with (⟨hv, hT, hq⟩ | ⟨ht, hR⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · exact .inl (.inl ⟨hv, hT, hq, hp⟩)
    · exact .inl (.inr ⟨ht, hR, hp⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh,
        SafePostExcW.world hmono htrunc (hmono _ _ _ hx (htrunc _ _ _ _ hp)) hs'⟩

end Verification.HeapObservations
