import Verification.Paper.TolerantFrames.ReadOnlyEnter
import Verification.Paper.TolerantFrames.ReadOnlyTransfer

/-! # Read-only handles: a member's certificate from the charges

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Certificates", `cert_of_charges`).

- **An entering step keeps the heap** (`enter_keeps_heap`): at a reached
  term (`wfS`) a step that changes the heap keeps the path's frames
  (`step_wfS`), so it enters no call.
- **The call it enters, in its context** (`enter_ctx`): the run it pushes
  is the innermost run, of `C`'s code, in an evaluation context whose own
  frames hold the calls active before the step, its top segment outside
  `C`.
- **The call's run stays in its hole** (`hole_ex`): along an execution
  from the entered state while the call is active, the state is the
  context around a run its hole reached, a run of the entered code.
- **The own steps of the call run `C`'s code** (`hole_runsC`): at one call
  more than the context's, a state whose active frame runs `C`'s code has
  every frame of its run on `C`'s code.
- **A member's certificate from the charges** (`ClientFrame.cert_of_charges`):
  at `Ψ_C = componentProtocol`, with no invariant to keep, its entering
  step keeps the heap and its own steps are within the charges
  (`within_member`), where the entered run's values meet the closure of the
  capture sites and `O`. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification HeapObservations Footprints

/-! ## An entering step keeps the heap -/

/-- **An entering step keeps the heap** (proved, `step_wfS`). -/
theorem enter_keeps_heap {F : Family} {C : Nat} {c : ComponentTag} {h h' : Heap} {t t' : Tm}
    (hs : Step h t h' t') (hw : wfS t = true) (hh : HeapFree h) (hd : depthC F C c t < depthC F C c t') :
    h' = h := by
  rcases (step_wfS hs hw hh).2 with e | hst
  · exact e
  · obtain ⟨F₀, F', rest, hP, hP', ht⟩ := hst c
    exfalso
    unfold depthC at hd
    rw [hP, hP'] at hd
    simp [ht] at hd

/-- The tags of a path, at a component. -/
noncomputable abbrev tagsC (F : Family) (C : Nat) (P : List (ComponentTag × Tm)) : List Bool := P.map fun p => F.ofC C p.1

/-- **The call an entering step enters, in its context** (proved, from
`step_runs_wf`'s change of the path): the run the step pushes heads the
path, so the term after the step is that run in an evaluation context
(`path_goto_ctx`); the context's path is the hole's, then frames `S` below
a top segment tagged `c'`, which hold the calls active before the step;
the run's tag is `C`'s and `c'` is not. -/
theorem enter_ctx {F : Family} {C : Nat} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hw : wf t = true)
    (hh : HeapFree h) (hd : depthC F C none t' = depthC F C none t + 1) :
    ∃ K E Kc l L d cc c' g S, EvalCtx K ∧ t' = K (.goto E Kc l L d cc) ∧
      (∀ u, isVal u = false → path none (K u) = wrap g (path c' u) ++ S) ∧
      F.ofC C cc = true ∧ F.ofC C c' = false ∧ blocks (tagsC F C ((c', hole) :: S)) = depthC F C none t := by
  have hp := (step_runs_wf hs hw hh).2.2 none
  -- The pushed run heads the new path.
  have hpush : ∃ x rest', path none t' = x :: rest' ∧ IsGoto x := by
    rcases hp with ⟨new, F₀, F', rest, hP, hP', ht, hn, hg⟩ | ⟨new, F₀, G, G', rest, hP, hP', ht, hn, hg⟩
    · cases new with
      | nil =>
        exfalso; unfold depthC at hd; rw [hP, hP'] at hd; simp [ht.1] at hd
      | cons x xs => exact ⟨x, _, by rw [hP']; rfl, hg x List.mem_cons_self⟩
    · cases new with
      | nil =>
        exfalso; unfold depthC at hd; rw [hP, hP'] at hd
        simp only [List.nil_append, List.map_cons, blocks_cons_cons, ht.1] at hd
        omega
      | cons x xs => exact ⟨x, _, by rw [hP']; rfl, hg x List.mem_cons_self⟩
  obtain ⟨x, rest', hx, m, cc, l, hrh⟩ := hpush
  obtain ⟨E, Kc, L, d, hx2⟩ : ∃ E Kc L d, x.2 = .goto E Kc l L d cc := by
    obtain ⟨xc, xt⟩ := x
    cases xt <;> simp [runHead] at hrh
    obtain ⟨-, rfl, rfl⟩ := hrh
    exact ⟨_, _, _, _, rfl⟩
  have hgo : isGoto x.2 = true := by rw [hx2]; rfl
  obtain ⟨K, hK, ht'⟩ := path_goto_ctx t' none x (by rw [hx]; rfl) hgo
  rw [hx2] at ht'
  obtain ⟨c', g, S, hP⟩ := path_ctx hK none
  have hpt' : path none t' = (cc, .goto E Kc l L d cc) :: (c', g hole) :: S := by
    rw [ht', hP _ rfl]; simp [path, wrap, mapLast]
  refine ⟨K, E, Kc, l, L, d, cc, c', g, S, hK, ht', hP, ?_⟩
  have hdt' : depthC F C none t' = blocks (F.ofC C cc :: tagsC F C ((c', hole) :: S)) := by
    unfold depthC; rw [hpt']; rfl
  rcases hp with ⟨new, F₀, F', rest, hP0, hP', ht, hn, -⟩ | ⟨new, F₀, G, G', rest, hP0, hP', ht, hn, -⟩
  · match new, hn with
    | [], _ =>
      exfalso
      have : depthC F C none t' = depthC F C none t := by
        unfold depthC; rw [hP0, hP']; simp [ht.1]
      omega
    | [y], _ =>
      rw [hpt'] at hP'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hP'
      obtain ⟨-, rfl, rfl⟩ := hP'
      have hdt : depthC F C none t = blocks (tagsC F C ((c', hole) :: S)) := by
        unfold depthC; rw [hP0]; simp [tagsC, ← ht.1]
      rw [hdt', hdt] at hd
      rw [hdt]
      simp only [tagsC, List.map_cons, blocks_cons_cons] at hd ⊢
      revert hd
      cases F.ofC C cc <;> cases F.ofC C c' <;> simp <;> omega
  · match new, hn with
    | [], _ =>
      exfalso
      have : depthC F C none t' ≤ depthC F C none t := by
        unfold depthC; rw [hP0, hP']
        simp only [List.nil_append, List.map_cons, blocks_cons_cons, ht.1]; omega
      omega
    | [y], _ =>
      rw [hpt'] at hP'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hP'
      obtain ⟨-, rfl, rfl⟩ := hP'
      have hdt : depthC F C none t = blocks (F.ofC C F₀.1 :: tagsC F C ((c', hole) :: S)) := by
        unfold depthC; rw [hP0]; simp [tagsC, ← ht.1]
      rw [hdt', hdt] at hd
      rw [hdt]
      simp only [tagsC, List.map_cons, blocks_cons_cons] at hd ⊢
      revert hd
      cases F.ofC C cc <;> cases F.ofC C c' <;> cases F.ofC C F₀.1 <;> simp <;> omega

/-! ## The call's run stays in its hole -/

/-- **A run of the code tagged `cc`**: a run not yet entered or a frame. -/
def RunOf (cc : ComponentTag) (u : Tm) : Prop :=
  (∃ E K l L d, u = .goto E K l L d cc) ∨ ∃ E K t L d k x, u = .frame E K t L d k x cc

theorem RunOf.not_val {cc : ComponentTag} {u : Tm} (h : RunOf cc u) : isVal u = false := by
  rcases h with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ <;> rfl

theorem RunOf.not_spread {cc : ComponentTag} {u : Tm} (h : RunOf cc u) : ∀ a, u ≠ .spread a := by
  rcases h with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ <;> intro a h <;> cases h

theorem RunOf.not_raises {cc : ComponentTag} {u w : Tm} (h : RunOf cc u) : ¬ Raises u w := by
  rcases h with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ <;> intro h <;> cases h

/-- **A step of a run** (proved, by cases): a run of the same code's tag,
a value (a return), or a throw. -/
theorem RunOf.step {cc : ComponentTag} {h h' : Heap} {u u' : Tm} (hr : RunOf cc u) (hs : Step h u h' u') :
    RunOf cc u' ∨ isVal u' = true ∨ ∃ w, Raises u' w := by
  rcases hr with ⟨E, K, l, L, d, rfl⟩ | ⟨E, K, t, L, d, k, x, rfl⟩
  · cases hs with
    | gotoEnter => exact .inl (.inr ⟨_, _, _, _, _, _, _, rfl⟩)
  · cases hs with
    | frameC => exact .inl (.inr ⟨_, _, _, _, _, _, _, rfl⟩)
    | frameRet hv => exact .inr (.inl hv)
    | frameRaise hr =>
      exact .inr (.inr ⟨_, .throwV (sourceVal_isVal (raises_sourceVal hr)) (raises_sourceVal hr)⟩)
    | _ => exact .inl (.inl ⟨_, _, _, _, _, rfl⟩)

/-- The calls of `C` at a term, from its path's tags. -/
theorem depthC_tags {F : Family} {C : Nat} {c : ComponentTag} {t : Tm} :
    depthC F C c t = blocks (((path c t).map Prod.fst).map (F.ofC C)) := by
  simp [depthC, List.map_map, Function.comp_def]

section HoleRun
variable {F : Family} {C : Nat} {K : Tm → Tm} {c' : ComponentTag} {g : Tm → Tm} {S : List (ComponentTag × Tm)}
  (hK : EvalCtx K) (hP : ∀ u, isVal u = false → path none (K u) = wrap g (path c' u) ++ S)
include hK hP

omit hK in
/-- **A term whose path is its top segment holds the context's calls**
(proved). -/
theorem depth_top {u : Tm} (hu : isVal u = false) (h : path c' u = [(c', u)]) :
    depthC F C none (K u) = blocks (tagsC F C ((c', hole) :: S)) := by
  unfold depthC; rw [hP u hu, h]; simp [wrap, mapLast, tagsC]

/-- **A value in the context holds the context's calls** (proved,
`ctx_val_tags`, `depth_top`). -/
theorem depth_val {u v : Tm} (hu : isVal u = false) (hwu : wfS (K u) = true) (hv : isVal v = true)
    (hwv : wfS (K v) = true) : depthC F C none (K v) = blocks (tagsC F C ((c', hole) :: S)) := by
  rw [depthC_tags, ctx_val_tags hK none hu hwu hv hwv, ← depthC_tags]
  exact depth_top hP rfl (by simp [path])

/-- **The call's run stays in its hole** (proved, by induction on the
execution, `EvalCtx.step_hole`, `RunOf.step`): along an execution whose
states hold more calls of `C` than the context, from the context around a
run, each state is the context around a run of the same code's tag its
hole reached: a return or a throw would leave the context's calls
(`depth_val`, `depth_top`). -/
theorem hole_ex {P : Type} {R : Conf × P → Conf × P → Prop} {I : Conf × P → Prop}
    (hR : ∀ a b, I a → R a b → Step a.1.s.h a.1.t b.1.s.h b.1.t) (hI : ∀ a b, I a → R a b → I b)
    (hwf : ∀ a, I a → wfS a.1.t = true) {d : Nat} (hD : blocks (tagsC F C ((c', hole) :: S)) = d)
    {u₁ : Tm} (hu₁ : isVal u₁ = false) (hw₁ : wfS (K u₁) = true) {cc : ComponentTag} :
    ∀ {n : Nat} {a e : Conf × P} {u₀ : Tm}, Ex R (fun x => d + 1 ≤ depthC F C none x.1.t) n a e → I a →
      a.1.t = K u₀ → RunOf cc u₀ → d + 1 ≤ depthC F C none e.1.t →
      (∃ u, Steps n a.1.s.h u₀ e.1.s.h u ∧ e.1.t = K u ∧ RunOf cc u) ∧
      ∀ i h₁ t₁, i ≤ n → Steps i a.1.s.h u₀ h₁ t₁ → ∃ b, I b ∧ b.1.s.h = h₁
  | _, a, _, u₀, .refl _, hIa, ha, hr, _ =>
    ⟨⟨u₀, .refl, ha, hr⟩, fun i h₁ t₁ hi hs => by
      cases Nat.le_zero.mp hi; cases hs; exact ⟨a, hIa, rfl⟩⟩
  | _, a, e, u₀, .next (b := b) _ hab hrest, hIa, ha, hr, he => by
    have hs := hR a b hIa hab
    rw [ha] at hs
    have hIb := hI a b hIa hab
    -- The state after the step holds more calls than the context.
    have hb : d + 1 ≤ depthC F C none b.1.t := by
      cases hrest with
      | refl => exact he
      | next hq _ _ => exact hq
    rcases hK.step_hole hr.not_val hr.not_spread hs with ⟨h₂, u', hs'⟩ | ⟨w, hw⟩
    · obtain ⟨rfl, hbt⟩ := hK.step_inv hs' hs
      rcases hr.step hs' with hr' | hv | ⟨w, hw⟩
      · obtain ⟨⟨u, hu, he', hru⟩, hpre⟩ := hole_ex hR hI hwf hD hu₁ hw₁ hrest hIb hbt hr' he
        refine ⟨⟨u, .next hs' hu, he', hru⟩, fun i h₁ t₁ hi hsi => ?_⟩
        cases hsi with
        | refl => exact ⟨a, hIa, rfl⟩
        | next st hs₂ =>
          obtain ⟨rfl, rfl⟩ := Step_det st hs'
          exact hpre _ _ _ (by omega) hs₂
      · have := depth_val (F := F) (C := C) hK hP hu₁ hw₁ hv (by rw [← hbt]; exact hwf b hIb)
        rw [hbt, this, hD] at hb; omega
      · have := depth_top (F := F) (C := C) hP (raises_not_val hw) (raises_path hw c')
        rw [hbt, this, hD] at hb; omega
    · exact absurd hw hr.not_raises

end HoleRun

/-! ## The own steps of the call run `C`'s code -/

/-- A block of `false` splits the blocks of a list (proved). -/
theorem blocks_split : ∀ (A R : List Bool), blocks (A ++ false :: R) = blocks (A ++ [false]) + blocks R
  | [], R => by simp [blocks]
  | a :: A, R => by
    have ih := blocks_split A R
    have hh : ((A ++ false :: R).head?.getD false) = ((A ++ [false]).head?.getD false) := by
      cases A <;> rfl
    simp only [List.cons_append, blocks, hh, ih]
    omega

/-- **The path of a run** (proved): its frames, its own tag's, above the
top segment. -/
theorem RunOf.path {cc : ComponentTag} {u : Tm} (hr : RunOf cc u) :
    ∃ init s, (∀ c, path c u = init ++ [(cc, s), (c, hole)]) := by
  rcases hr with ⟨E, K, l, L, d, rfl⟩ | ⟨E, K, t, L, d, k, x, rfl⟩
  · exact ⟨[], _, fun c => rfl⟩
  · obtain ⟨init, s, hp⟩ := path_last t cc
    exact ⟨init, _, fun c => by simp only [ReadOnly.path, hp, wrap_snoc, List.append_assoc]; rfl⟩

/-- **At one call more than its context, a run whose active frame runs
`C`'s code runs `C`'s code in every frame** (proved, `blocks_split`,
`blocks_one_all`, `innermost_tag`, as `activeFrame_runsC`). -/
theorem hole_runsC {F : Family} {C : Nat} {K : Tm → Tm} {c' : ComponentTag} {g : Tm → Tm}
    {S : List (ComponentTag × Tm)} (hP : ∀ u, isVal u = false → path none (K u) = wrap g (path c' u) ++ S)
    {cc : ComponentTag} {u : Tm} {d : Nat} (hcc : F.ofC C cc = true) (hc' : F.ofC C c' = false)
    (hD : blocks (tagsC F C ((c', hole) :: S)) = d) (hr : RunOf cc u) (hd : depthC F C none (K u) = d + 1)
    (hin : ¬ OutsideAt F C none (K u)) :
    ∀ key, (activeFrame none u).1 = some key → F.ofC C key.1.2 = true := by
  intro key hkey
  obtain ⟨init, s, hp⟩ := hr.path
  have hpK : path none (K u) = init ++ (cc, s) :: (c', g hole) :: S := by
    rw [hP u hr.not_val, hp c', show init ++ [(cc, s), (c', hole)] = (init ++ [(cc, s)]) ++ [(c', hole)] by simp,
      wrap_snoc]
    simp
  have hDs : blocks (S.map fun p => F.ofC C p.1) = d := by
    rw [← hD]; simp [tagsC, blocks, hc']
  have hb : blocks ((init.map fun p => F.ofC C p.1) ++ [true, false]) = 1 := by
    have e := hd
    unfold depthC at e
    rw [hpK] at e
    simp only [List.map_append, List.map_cons, hcc, hc'] at e
    have := blocks_split ((init.map fun p => F.ofC C p.1) ++ [true]) (S.map fun p => F.ofC C p.1)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    rw [this, hDs] at e
    omega
  have hhead : (init.map fun p => F.ofC C p.1).head?.getD true = true := by
    have ht : F.ofC C (activeTag none (K u)) = true := by
      simpa [OutsideAt, Family.ofC] using hin
    cases init with
    | nil => rfl
    | cons p ps =>
      simp only [activeTag, hpK, List.cons_append, List.head?_cons, Option.map_some, Option.getD_some] at ht
      simpa using ht
  have hall := blocks_one_all _ hb hhead
  obtain ⟨hspec, -⟩ := activeFrame_innermost u none
  rw [hkey] at hspec
  cases hi : innermost u with
  | none => rw [hi] at hspec; simp at hspec
  | some f =>
    rw [hi] at hspec
    have hf : frameOf f = some key := by
      cases e : frameOf f <;> simp_all
    have hmem := innermost_tag u cc hi hf
    rw [hp cc] at hmem
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.map_nil,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | rfl | rfl
    · obtain ⟨p, hpi, hpk⟩ := List.mem_map.mp hmem
      rw [← hpk]; exact hall _ (List.mem_map.mpr ⟨p, hpi, rfl⟩)
    · exact hcc
    · exact hcc

/-! ## A member's certificate from the charges -/

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **Every reached state is a reached term** (proved, `step_wfS` at each
step): where every call the claim is about, at every history the frame
starts from, is one. -/
theorem reached_wfS
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : wfS b.1.t = true := by
  obtain ⟨a, n, hc, hs, hex⟩ := hb
  refine (hex.carry (r := fun x : Conf × Ghost (fr.F.at fr.C) => fr.Entry x.1.s.h x.1.t ∧ wfS x.1.t = true)
    ?_ ⟨hc.1, hst a hc hs⟩).2
  intro x y _ hxy hx
  exact ⟨Entry.step fr hx.1 hxy.1.step, (step_wfS hxy.1.step hx.2 hx.1.2.1.2).1⟩

/-- **A member's certificate from the charges** (proved; the draft's
`cert_of_charges`): at the component's protocol and no invariant to keep,
every member's calls from reached states meet their certificate. The
entering step keeps the heap (`enter_keeps_heap`), so it is within any
protocol; it pushes a run of `C`'s code in a context (`enter_ctx`), whose
run stays in the hole while the call is active (`hole_ex`), and every own
step of the call is a step of that run whose frames run `C`'s code
(`hole_runsC`), within the component's protocol below the entry's heap
(`within_member`), where the entered run's values meet the closure of the
capture sites and `O` (`hroots`). The reached states are reached terms
(`reached_wfS`), meet the flow (`fitsAt_reached`), the residual invariant
(`wok_reached`) and layout provenance (`lay_reached`). -/
theorem cert_of_charges [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {F : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hFa : F.flow.Facts) (hS : fr.FlowSites F.flow) (hE : fr.EntryFits F.flow)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ F lay) a.1.t = true ∧ HeapLay (layQ F lay) a.1.s.h)
    (hT : capClosedB F (tokenCaps F lay) (captureSites F lay ++ F.O)
      (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) = true)
    (htok : tokensSomeB F = true) (hlow : codesLoweredB F = true)
    (hroots : ∀ (a a₁ : Conf × Ghost (fr.F.at fr.C)), fr.Reached a → XStep fr.F fr.C none fr.Θ fr.chkConf a a₁ →
      δ fr.F fr.C none a₁ = δ fr.F fr.C none a + 1 → ∀ (K : Tm → Tm) E Kc l L d cc, EvalCtx K →
      a₁.1.t = K (.goto E Kc l L d cc) → ∀ x ∈ vals allC true (.goto E Kc l L d cc),
        ∃ S', VJ F.flow a₁.2 a₁.1.s.h.length S' x ∧
          Sub S' (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) ∧ layP (layQ F lay) x = true)
    (m : Option Code) :
    TraceCert fr.F fr.C none fr.Θ fr.chkConf fr.Reached (componentProtocol F lay) (fun _ => False) m := by
  -- The entering step keeps the heap.
  have hheap : ∀ a a₁, fr.Reached a → XStep fr.F fr.C none fr.Θ fr.chkConf a a₁ →
      δ fr.F fr.C none a₁ = δ fr.F fr.C none a + 1 → a₁.1.s.h = a.1.s.h := fun a a₁ hA hx hd =>
    enter_keeps_heap (F := fr.F) (C := fr.C) (c := none) hx.1.step (reached_wfS hst hA)
      (Reached.entry hA).2.1.2 (by simp only [δ] at hd; omega)
  refine ⟨fun a a₁ ⟨hA, hx, _, hd⟩ => ?_, fun a a₁ y z ⟨hA, hx, _, hd⟩ ⟨⟨n, hex⟩, hyz, hdy, hoy⟩ => ?_,
    fun _ hG => hG.elim, fun _ hG => hG.elim⟩
  · intro l v _ _ hv
    refine ⟨v, ?_, Change.Holds.refl _ _ _⟩
    simp only [lift] at hv ⊢
    rw [hheap a a₁ hA hx hd]; exact hv
  · have hh := hheap a a₁ hA hx hd
    have hA₁ := Reached.xstep hA hx
    have hent := (Reached.entry hA).2.1
    obtain ⟨K, E, Kc, l, L, d, cc, c', g, S, hK, ht₁, hP, hcc, hc', hD⟩ :=
      enter_ctx (F := fr.F) (C := fr.C) hx.1.step hent.1 hent.2 (by simpa only [δ] using hd)
    have hw₁ : wfS (K (.goto E Kc l L d cc)) = true := by rw [← ht₁]; exact reached_wfS hst hA₁
    have hgo : RunOf cc (.goto E Kc l L d cc) := .inl ⟨_, _, _, _, _, rfl⟩
    obtain ⟨⟨u, hrun, hyt, hru⟩, hpre⟩ := hole_ex (F := fr.F) (C := fr.C) hK hP
      (fun a b _ h => h.1.step) (fun a b h hab => Reached.xstep h hab) (fun a h => reached_wfS hst h) hD
      (u₁ := .goto E Kc l L d cc) rfl hw₁ (a := a₁) (e := y) (n := n) hex hA₁ ht₁ hgo
      (by simp only [δ] at hdy; omega)
    have hyzs := hyz.1.step
    rw [hyt] at hyzs
    obtain ⟨h₂, u', hs'⟩ : ∃ h₂ u', Step y.1.s.h u h₂ u' := by
      rcases hK.step_hole hru.not_val hru.not_spread hyzs with h | ⟨w, hw⟩
      · exact h
      · exact absurd hw hru.not_raises
    obtain ⟨hzh, hzt⟩ := hK.step_inv hs' hyzs
    have hy := Reached.ex hA₁ (Ex.map (fun _ _ _ h => kstep_of_xstep h) hex)
    have hfy := fitsAt_reached hFa hS hE hy
    have hfa := fitsAt_reached hFa hS hE hA₁
    have hwa := wok_reached hwk hA₁
    have hla := lay_reached hly hA₁
    have hdyK : depthC fr.F fr.C none (K u) = depthC fr.F fr.C none a.1.t + 1 := by
      rw [← hyt]; simpa only [δ] using hdy
    have hC := hole_runsC (F := fr.F) (C := fr.C) hP hcc hc' hD hru hdyK (by rw [← hyt]; exact hoy)
    rw [← hh]
    refine within_member (st := lift fr.F fr.C none y.1 y.2) (st' := lift fr.F fr.C none z.1 z.2) hK hrun
      (fun i h₁ t₁ hi hs₁ => ?_) (by simp only [lift]; rw [← hzh] at hs'; exact hs') (by rw [← ht₁]; exact hwa.1)
      (by simp [writesK]) hwa.2 (by simp only [lift]; rw [← hyt]; exact y.1.ok) (by rw [← hyt]; exact hfy.1)
      hC hT htok hlow hfa.2 hla.2 (hroots a a₁ hA hx hd K E Kc l L d cc hK ht₁)
      (ex_sites hS (Ex.map (fun _ _ _ h => kstep_of_xstep h) hex)).2
    obtain ⟨b, hb, hbh⟩ := hpre i h₁ t₁ (Nat.le_of_lt hi) hs₁
    have hfb := fitsAt_reached hFa hS hE hb
    intro l' v hv
    rw [← hbh] at hv
    exact (hfb.2 l' v hv).val

end ClientFrame

end Verification.TolerantFrames.ReadOnly
