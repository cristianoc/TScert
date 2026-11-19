import Verification.Paper.TolerantFrames.ReadOnlyLayouts
import Verification.Paper.TolerantFrames.ReadOnlyIsolate

/-! # Read-only handles: a call's steps within its charges

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Charges", `within_charges`). A call's
run is the run of the call's term in its evaluation context
(`EvalCtx.steps_inv`, the draft's `isolate`): until it returns, every
state's term is the context around a term the call's term reached. The
local lemma reads that run from the call's term alone, whose values are
the callee, the receiver and the arguments, so its held set is the closure
of their sets, not the caller's slots.

- **The active frame through a context** (`activeFrame_ctx`): around a term
  that is not a value, a context fixes the frame the term's active frame is
  read from; the innermost frame inside the term is the whole term's
  (`activeFrame_hole`), so a frame of `C`'s code inside it runs a code of
  the flow where the whole term fits (`Fits.frameIn_hole`).
- **A call's run in its context** (`hole_run`): before its return, an
  execution from the call's state is the call's term's in its context.
- **An execution over heaps of values** (`valRun_of_steps`).
- **Within the charges** (`within_run`, the draft's `within_charges`): a
  step of `C`'s code, or of no frame, of a run of a call's term from `h₀`
  in its context is within the protocol from every code's charges and a
  set passing the closure check that holds the sets of the call's values,
  below `|h₀|`. Its two instances are the depth charges $`W_c`$ at a call
  node's segment (the set $`L(c)`$, `callReach`) and $`\Psi_C`$ at a
  member's call entered from outside code (the closure of the capture sites
  and `O`, `componentProtocol`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification HeapObservations

/-! ## The active frame through a context -/

/-- **A context around a term that is not a value is not a value**
(proved). -/
theorem _root_.Verification.HeapObservations.EvalCtx.not_val {K : Tm → Tm} (hK : EvalCtx K) {u : Tm} (hu : isVal u = false) : isVal (K u) = false := by
  cases hK <;> first | exact hu | rfl

/-- **A context fixes the frame its hole's active frame is read from**
(proved, by induction on the context): around a term that is not a value,
the active frame of the whole term is the term's, read from the frame the
context puts around it. -/
theorem activeFrame_ctx {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ cur, ∃ c', ∀ u, isVal u = false → activeFrame cur (K u) = activeFrame c' u := by
  induction hK with
  | hole => exact fun cur => ⟨cur, fun _ _ => rfl⟩
  | frameC E Kc L d k x comp hK ih =>
    intro _
    obtain ⟨c', hc'⟩ := ih (some (((E, Kc), comp), (k, x)))
    exact ⟨c', fun u hu => by simp only [activeFrame]; exact hc' u hu⟩
  | callArg hf hr hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc'⟩ := ih cur
    refine ⟨c', fun u hu => ?_⟩
    simp only [activeFrame, hf, hr, Bool.true_eq_false, if_false]
    rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
    exact hc' u hu
  | constructArg hf hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc'⟩ := ih cur
    refine ⟨c', fun u hu => ?_⟩
    simp only [activeFrame, hf, Bool.true_eq_false, if_false]
    rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
    exact hc' u hu
  | makeArg hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc'⟩ := ih cur
    refine ⟨c', fun u hu => ?_⟩
    simp only [activeFrame]
    rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
    exact hc' u hu
  | arrArg hi hpre hK ih =>
    intro cur
    obtain ⟨c', hc'⟩ := ih cur
    refine ⟨c', fun u hu => ?_⟩
    simp only [activeFrame]
    rw [activeArgs_at (List.getElem?_set_self hi) (set_prefix hpre) (hK.not_val hu)]
    exact hc' u hu
  | _ =>
    rename_i hK ih
    intro cur
    obtain ⟨c', hc'⟩ := ih cur
    refine ⟨c', fun u hu => ?_⟩
    simp only [activeFrame, hK.not_val hu, *, if_true, if_false, Bool.true_eq_false]

/-- **The innermost frame inside a term is the whole term's** (proved,
`activeFrame_ctx`, `activeFrame_innermost`): where the term's active frame
read from no frame is a frame, the whole term's is that frame. -/
theorem activeFrame_hole {K : Tm → Tm} (hK : EvalCtx K) {u : Tm} (hu : isVal u = false) {key : FrameKey}
    (hk : (activeFrame none u).1 = some key) (cur : Option FrameKey) : (activeFrame cur (K u)).1 = some key := by
  obtain ⟨c', hc'⟩ := activeFrame_ctx hK cur
  rw [hc' u hu, (activeFrame_innermost u c').1]
  have := (activeFrame_innermost u none).1
  rw [hk] at this
  cases hx : (innermost u).bind frameOf <;> simp_all

/-- **A frame of `C`'s code inside a fitting term runs a code of the flow**
(proved, `Fits.frameIn`, `activeFrame_hole`). -/
theorem Fits.frameIn_hole {P : Package} {Fl : Flow P} {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)}
    {a : FrameAt P} {o : Bool} {S : Sites P} {K : Tm → Tm} (hK : EvalCtx K) {u : Tm} (hu : isVal u = false)
    (hf : Fits Fl V Γ a o S (K u)) : FrameIn Fl (activeFrame none u).1 := by
  intro m comp kx he hc
  have hw := hf.frameIn none (fun _ _ _ h => by cases h)
  rw [activeFrame_hole hK hu he none] at hw
  exact hw m comp kx rfl hc

/-! ## The call's term in its context -/

/-- **The hole's references are the whole term's** (proved, by induction on
the context). -/
theorem _root_.Verification.HeapObservations.EvalCtx.refs_hole {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {u : Tm}, ∀ r ∈ refs u, r ∈ refs (K u) := by
  induction hK with
  | hole => exact fun _ hr => hr
  | callArg _ _ hi _ _ ih =>
    intro u r hr
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, List.mem_of_getElem? (List.getElem?_set_self hi), ih r hr⟩
  | constructArg _ hi _ _ ih =>
    intro u r hr
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, List.mem_of_getElem? (List.getElem?_set_self hi), ih r hr⟩
  | @makeArg _ c _ _ _ hi _ _ ih =>
    intro u r hr
    cases c <;> simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap, List.mem_cons]
    all_goals first
      | exact .inr ⟨_, List.mem_of_getElem? (List.getElem?_set_self hi), ih r hr⟩
      | exact ⟨_, List.mem_of_getElem? (List.getElem?_set_self hi), ih r hr⟩
  | arrArg hi _ _ ih =>
    intro u r hr
    simp only [refs, refsArgs_eq, List.mem_flatMap]
    exact ⟨_, List.mem_of_getElem? (List.getElem?_set_self hi), ih r hr⟩
  | _ =>
    rename_i ih
    intro u r hr
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    have := ih r hr
    grind

/-- **The hole meets the residual invariant where the whole term does**
(proved, by induction on the context). -/
theorem _root_.Verification.HeapObservations.EvalCtx.wok_hole {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {u : Tm}, WOk (K u) → WOk u := by
  induction hK with
  | hole => exact fun h => h
  | callArg _ _ hi _ _ ih =>
    intro u h
    simp only [WOk, wOks_iff] at h
    exact ih (h.2.2 _ (List.mem_of_getElem? (List.getElem?_set_self hi)))
  | constructArg _ hi _ _ ih =>
    intro u h
    simp only [WOk, wOks_iff] at h
    exact ih (h.2 _ (List.mem_of_getElem? (List.getElem?_set_self hi)))
  | @makeArg _ c _ _ _ hi _ _ ih =>
    intro u h
    cases c <;> simp only [WOk, wOks_iff] at h
    all_goals first
      | exact ih (h _ (List.mem_of_getElem? (List.getElem?_set_self hi)))
      | exact ih (h.2 _ (List.mem_of_getElem? (List.getElem?_set_self hi)))
  | arrArg hi _ _ ih =>
    intro u h
    simp only [WOk, wOks_iff] at h
    exact ih (h _ (List.mem_of_getElem? (List.getElem?_set_self hi)))
  | _ =>
    rename_i ih
    intro u h
    simp only [WOk] at h
    grind

/-- **The residual invariant along an execution** (proved, `step_wok` at
each step): the term reached meets it at a heap of plain values, its
writes among the first term's. -/
theorem wok_steps : ∀ {j : Nat} {h h' : Heap} {t t' : Tm}, Steps j h t h' t' → HeapW h → WOk t →
    WOk t' ∧ HeapW h' ∧ writesK t' ⊆ writesK t
  | 0, _, _, _, _, .refl, hh, ht => ⟨ht, hh, List.Subset.refl _⟩
  | _ + 1, _, _, _, _, .next st hrest, hh, ht =>
    have h₁ := step_wok st hh ht
    have h₂ := wok_steps hrest h₁.2.1 h₁.1
    ⟨h₂.1, h₂.2.1, h₂.2.2.trans h₁.2.2⟩

/-! ## Within the charges -/

/-- **A heap of values.** -/
def HeapVals (h : Heap) : Prop := ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true

/-- **An execution over heaps of values is a run** (proved). -/
theorem valRun_of_steps : ∀ {j : Nat} {h h' : Heap} {t t' : Tm}, Steps j h t h' t' →
    (∀ i h₁ t₁, i < j → Steps i h t h₁ t₁ → HeapVals h₁) → ValRun h t h' t'
  | 0, _, _, _, _, .refl, _ => .refl
  | _ + 1, _, _, _, _, .next st hrest, hv =>
    .step (hv 0 _ _ (Nat.zero_lt_succ _) .refl) st
      (valRun_of_steps hrest fun i h₁ t₁ hi hs => hv (i + 1) h₁ t₁ (by omega) (.next st hs))

/-- **A call's run before its return is its term's run in its context**
(proved, `EvalCtx.steps_inv`, the draft's `isolate` at the calculus): an
execution from `K[u₀]` along which the term `u₀` reached keeps stepping is
an execution of `u₀`, in `K`. -/
theorem hole_run {K : Tm → Tm} (hK : EvalCtx K) {j : Nat} {h h' : Heap} {u₀ w : Tm} (hs : Steps j h (K u₀) h' w)
    (hgo : ∀ i h₁ t₁, i < j → Steps i h u₀ h₁ t₁ → ∃ h₂ t₂, Step h₁ t₁ h₂ t₂) :
    ∃ u, Steps j h u₀ h' u ∧ w = K u := by
  rcases hK.steps_inv hs with hl | ⟨i, h₁, t₁, hi, hs₁, hn, -⟩
  · exact hl
  · obtain ⟨h₂, t₂, hst⟩ := hgo i h₁ t₁ hi hs₁
    exact absurd hst (hn h₂ t₂)

/-- **A step of a call's run is within the charges** (proved, the draft's
`within_charges`, by `stepWithin_reach`, `heapDeep_of_checks`,
`deepIn_of_checks` and `Fits.frameIn_hole`): let `u₀`, a term performing
no write, be a call's term at `h₀` in the context `K`, the whole term
meeting the residual invariant at a heap of plain values, and `u` the term
its run reached over heaps of values (`hole_run`), the whole term `K u`
fitting with valid references. A step of `u` whose innermost frame is no
frame or one of `C`'s code changes each location of `R_P` below `|h₀|`
within the protocol from every code's charges and a set `T` passing the
closure check, where `T` holds the sets of `u₀`'s values (each meeting the
flow and layout provenance), `h₀` meets the flow and layout provenance, the
flow's tokens are sites and its codes lowered, and the step's history
keeps the sites of `h₀`'s locations. -/
theorem within_run {P : Package} [DecidableEq P.Site] [Hashable P.Site] [LawfulHashable (Option P.Site)]
    {F : FFlow P} {lay : List Layout} {S₀ T : Sites P} {g₀ : Ghost P} {n : Nat} {V : Sites P → Val → Prop}
    {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {Sx : Sites P} {K : Tm → Tm} (hK : EvalCtx K)
    {h₀ : Heap} {u₀ u u' : Tm} {j : Nat} {st st' : St P}
    (hrun : Steps j h₀ u₀ st.s.h u) (hvals : ∀ i h₁ t₁, i < j → Steps i h₀ u₀ h₁ t₁ → HeapVals h₁)
    (hs : Step st.s.h u st'.s.h u') (hw₀ : WOk (K u₀)) (hk₀ : writesK u₀ = []) (hW₀ : HeapW h₀)
    (hrefs : RefsOk st.s.W (K u)) (hfit : Fits F.flow V Γ a o Sx (K u))
    (hC : ∀ key, (activeFrame none u).1 = some key → P.ofC key.1.2 = true)
    (hT : capClosedB F (tokenCaps F lay) S₀ T = true) (htok : tokensSomeB F = true)
    (hlow : codesLoweredB F = true) (hH : HeapInv F.flow g₀ h₀) (hl : HeapLay (layQ F lay) h₀)
    (hroots : ∀ x ∈ vals allC true u₀, ∃ S', VJ F.flow g₀ n S' x ∧ Sub S' T ∧ layP (layQ F lay) x = true)
    (hsite : ∀ l, l < h₀.length → st.g.site l = g₀.site l) :
    StepWithin (probeProtocol (flowKinds F) T) h₀.length st st' := by
  have hu : isVal u = false := by
    cases e : isVal u
    · rfl
    · exact absurd hs (value_no_step e)
  have hfr : frameKinds [] (activeFrame none u).1 ⊆ flowKinds F := by
    have := frameKinds_flow (K₀ := []) (Fits.frameIn_hole hK hu hfit) hC
    simpa using this
  have hwu := wok_steps hrun hW₀ (hK.wok_hole hw₀)
  refine stepWithin_reach (K₀ := []) (valRun_of_steps hrun hvals) hs hwu.1 (by rw [← hk₀]; exact hwu.2.2)
    (hrefs.sub fun r hr => hK.refs_hole r hr) hfr
    (heapDeep_of_checks hT htok hlow hH hl) (fun x hx => ?_) hsite
  obtain ⟨S', hv, hS, hlx⟩ := hroots x hx
  exact deepIn_of_checks hT htok hlow hv hS hlx

/-- **At a call node's segment, within its depth charges** (proved,
`within_run` at `L(c)`): where the closure of the callee's, receiver's and
arguments' sets passes the closure check, and the call's values meet sets
within it. -/
theorem within_depth {P : Package} [DecidableEq P.Site] [Hashable P.Site] [LawfulHashable (Option P.Site)]
    {F : FFlow P} {lay : List Layout} {Sf Sr : Sites P} {args : List (Sites P)} {g₀ : Ghost P} {n : Nat}
    {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {Sx : Sites P}
    {K : Tm → Tm} (hK : EvalCtx K) {h₀ : Heap} {u₀ u u' : Tm} {j : Nat} {st st' : St P}
    (hrun : Steps j h₀ u₀ st.s.h u) (hvals : ∀ i h₁ t₁, i < j → Steps i h₀ u₀ h₁ t₁ → HeapVals h₁)
    (hs : Step st.s.h u st'.s.h u') (hw₀ : WOk (K u₀)) (hk₀ : writesK u₀ = []) (hW₀ : HeapW h₀)
    (hrefs : RefsOk st.s.W (K u)) (hfit : Fits F.flow V Γ a o Sx (K u))
    (hC : ∀ key, (activeFrame none u).1 = some key → P.ofC key.1.2 = true)
    (hT : capClosedB F (tokenCaps F lay) (Sf ++ Sr ++ args.flatten) (callReach F lay Sf Sr args) = true)
    (htok : tokensSomeB F = true) (hlow : codesLoweredB F = true) (hH : HeapInv F.flow g₀ h₀)
    (hl : HeapLay (layQ F lay) h₀)
    (hroots : ∀ x ∈ vals allC true u₀, ∃ S', VJ F.flow g₀ n S' x ∧ Sub S' (callReach F lay Sf Sr args) ∧
      layP (layQ F lay) x = true)
    (hsite : ∀ l, l < h₀.length → st.g.site l = g₀.site l) :
    StepWithin (depthCharges F (callReach F lay Sf Sr args)) h₀.length st st' :=
  within_run hK hrun hvals hs hw₀ hk₀ hW₀ hrefs hfit hC hT htok hlow hH hl hroots hsite

/-- **At a member's call entered from outside code, within `Ψ_C`** (proved,
`within_run` at the closure of the capture sites and `O`): where that
closure passes the closure check, and the call's values meet sets within
it. -/
theorem within_member {P : Package} [DecidableEq P.Site] [Hashable P.Site] [LawfulHashable (Option P.Site)]
    {F : FFlow P} {lay : List Layout} {g₀ : Ghost P} {n : Nat}
    {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {Sx : Sites P}
    {K : Tm → Tm} (hK : EvalCtx K) {h₀ : Heap} {u₀ u u' : Tm} {j : Nat} {st st' : St P}
    (hrun : Steps j h₀ u₀ st.s.h u) (hvals : ∀ i h₁ t₁, i < j → Steps i h₀ u₀ h₁ t₁ → HeapVals h₁)
    (hs : Step st.s.h u st'.s.h u') (hw₀ : WOk (K u₀)) (hk₀ : writesK u₀ = []) (hW₀ : HeapW h₀)
    (hrefs : RefsOk st.s.W (K u)) (hfit : Fits F.flow V Γ a o Sx (K u))
    (hC : ∀ key, (activeFrame none u).1 = some key → P.ofC key.1.2 = true)
    (hT : capClosedB F (tokenCaps F lay) (captureSites F lay ++ F.O)
      (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) = true)
    (htok : tokensSomeB F = true) (hlow : codesLoweredB F = true) (hH : HeapInv F.flow g₀ h₀)
    (hl : HeapLay (layQ F lay) h₀)
    (hroots : ∀ x ∈ vals allC true u₀, ∃ S', VJ F.flow g₀ n S' x ∧
      Sub S' (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O)) ∧ layP (layQ F lay) x = true)
    (hsite : ∀ l, l < h₀.length → st.g.site l = g₀.site l) :
    StepWithin (componentProtocol F lay) h₀.length st st' :=
  within_run hK hrun hvals hs hw₀ hk₀ hW₀ hrefs hfit hC hT htok hlow hH hl hroots hsite

end Verification.TolerantFrames.ReadOnly
