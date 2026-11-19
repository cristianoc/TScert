import Verification.Source.Claims.FramedBinding
import Verification.Paper.TolerantFrames.ReadOnlyRealize

/-! # The realization of a framed plan's request

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Realization", `prologue_sim` and
`chk_sim`). A receiverless module function's realized code
(`realizedCode`) is its request's tables (`requestCode`) with one prologue
node past the body. Where the request's nodes target only its own labels
(`bodyTargetsB`), the two codes agree on the body (`realized_agree`):

- **The prologue** (`prologue_steps`): from the realized code's run at the
  prologue's label, two steps (entering its node, `undefined`, and its
  continuation) reach the realized code's run at the request's start, its
  slots the receiver's dropped.
- **The simulation** (`prologue_sim`): from there, every execution of the
  realized code is the same execution of the request's, on the same heaps,
  to related terms (`TabRel`), and where one takes no step the other takes
  none.
- **The same sites and crossings out** (`chk_site_sim`, `chk_actual_sim`,
  the site and crossings-out parts of `chk_sim`): in any context, related
  runs allocate at the same site, the flow holding both codes and their
  sites one per body allocation (`allocB`), and a step of related runs
  crosses out the same values. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly HeapObservations

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

instance (n : Nat) : DecidablePred (ContBelow n) := fun k => by cases k <;> unfold ContBelow <;> infer_instance

/-- **A code's nodes target its own labels**, decided: each continuation's
and handler's target is a label of the code's first `n` nodes. -/
def bodyTargetsB (m : Code) (n : Nat) : Bool :=
  m.2.all fun (k, x) => decide (ContBelow n k) && x.all (·.label < n)

/-- **The targets check is sound** (proved). -/
theorem bodyTargetsB_sound {m : Code} {n : Nat} (h : bodyTargetsB m n = true) :
    ∀ (l : Nat) k x, m.2[l]? = some (k, x) → ContBelow n k ∧ HandlerBelow n x := by
  intro l k x hl
  simp only [bodyTargetsB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hx⟩ := h (k, x) (List.mem_of_getElem? hl)
  refine ⟨hk, fun t ht => ?_⟩
  subst ht
  simpa using hx

/-- **The realized code and its request's agree on the body** (proved): the
realized code's tables are the request's with one node appended. -/
theorem realized_agree {r : SourceRequest σ ι} (h : bodyTargetsB (requestCode r) r.program.length = true) :
    BodyAgree (realizedCode r) (requestCode r) r.program.length := by
  refine ⟨fun l hl => ⟨?_, ?_⟩, fun l _ k x hk => bodyTargetsB_sound h l k x hk⟩
  · simp only [realizedCode, requestCode]
    rw [List.getElem?_append_left (by simpa using hl)]
  · simp only [realizedCode, requestCode]
    rw [List.getElem?_append_left (by simpa using hl)]

/-- The prologue's target: the request's start, the slots past the
receiver. -/
def prologueTarget (r : SourceRequest σ ι) : Target :=
  ⟨r.start, some ((List.range (r.inputs.length + 1)).map (· + 1))⟩

/-- **The prologue's steps** (proved): the realized code's run at the
prologue's label enters its node, which evaluates `undefined`, and continues
at the request's start with the slots the target maps. -/
theorem prologue_steps (r : SourceRequest σ ι) (h : Heap) (L : List Tm) (d : Tm) (c : ComponentTag) :
    Steps 2 h (.goto (realizedCode r).1 (realizedCode r).2 r.program.length L d c) h
      (.goto (realizedCode r).1 (realizedCode r).2 r.start (envMap (prologueTarget r).mapping L d).1
        (envMap (prologueTarget r).mapping L d).2 c) := by
  have he : (realizedCode r).1[r.program.length]? = some .undef := by
    simp [realizedCode]
  have hk : (realizedCode r).2[r.program.length]? = some (.effect (prologueTarget r), none) := by
    simp [realizedCode, prologueTarget]
  refine .next (.gotoEnter he hk) (.next ?_ .refl)
  have hi : instantiate 0 (envOf L d) Tm.undef = .undef := by simp [instantiate]
  rw [hi]
  exact .frameEffect rfl

/-- **The prologue's simulation** (proved, `prologue_steps`, `tabRel_steps`,
`tabRel_stuck`; the draft's `prologue_sim`): where the request's nodes
target its own labels and its start is one of them, two steps from the
realized code's run at the prologue's label reach a run related to the
request's run at its start, at the slots the prologue maps; every
execution from there is the same execution of the request's code, to
related terms, and where one takes no step the other takes none. -/
theorem prologue_sim {r : SourceRequest σ ι} (ht : bodyTargetsB (requestCode r) r.program.length = true)
    (hs : r.start < r.program.length) (h : Heap) (L : List Tm) (d : Tm) (c : ComponentTag) :
    let L' := (envMap (prologueTarget r).mapping L d).1
    let d' := (envMap (prologueTarget r).mapping L d).2
    Steps 2 h (.goto (realizedCode r).1 (realizedCode r).2 r.program.length L d c) h
        (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) ∧
      TabRel (realizedCode r) (requestCode r) r.program.length
        (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) (PassUnit.gotoOf r.program r.start L' d' c) ∧
      (∀ {j h₁ h₂ t₁}, Steps j h₁ (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) h₂ t₁ →
        ∃ t₂, Steps j h₁ (PassUnit.gotoOf r.program r.start L' d' c) h₂ t₂ ∧
          TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂ ∧
          ((∀ h₃ t₃, ¬ Step h₂ t₁ h₃ t₃) → ∀ h₃ t₃, ¬ Step h₂ t₂ h₃ t₃)) := by
  intro L' d'
  have hA := realized_agree ht
  have hrel : TabRel (realizedCode r) (requestCode r) r.program.length
      (.goto (realizedCode r).1 (realizedCode r).2 r.start L' d' c) (PassUnit.gotoOf r.program r.start L' d' c) := by
    rw [gotoOf_requestCode]; exact .goto hs
  refine ⟨prologue_steps r h L d c, hrel, fun hst => ?_⟩
  obtain ⟨t₂, hs₂, hr₂⟩ := tabRel_steps hA hrel hst
  exact ⟨t₂, hs₂, hr₂, tabRel_stuck hA hr₂⟩

/-- **Related runs allocate at the same site** (proved, `stepSite_tabRel`
and `allocB_realized`; the site part of the draft's `chk_sim`): where the
flow holds both codes at their entry and numbers their allocation sites by
the body (`allocB`), a step of related terms in any context reads the same
site. -/
theorem chk_site_sim {P : TolerantFrames.ReadOnly.Package} [DecidableEq P.Site] {num : P.Site → Nat}
    (hnum : ∀ a b, num a = num b → a = b) {F : FFlow P} {r : SourceRequest σ ι} {base : Nat}
    {bodies : List Code} (hb : allocB num F r base bodies = true)
    (h₁ : (F.at (realizedCode r) entryCx).isSome = true) (h₂ : (F.at (requestCode r) entryCx).isSome = true)
    {K : Tm → Tm} (hK : EvalCtx K) {t₁ t₂ : Tm} (hr : TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂) :
    stepSite F.flow none (K t₁) = stepSite F.flow none (K t₂) := by
  refine stepSite_tabRel hK hr fun comp l _ kx hkx => ?_
  obtain ⟨f₁, hf₁⟩ := Option.isSome_iff_exists.mp h₁
  obtain ⟨f₂, hf₂⟩ := Option.isSome_iff_exists.mp h₂
  have hs := allocB_realized hnum hb hf₁ hf₂ (List.mem_of_getElem? hkx)
  simp only [allocOf, FFlow.flow, hf₁, hf₂, Option.map_some, Option.getD_some, FCode.flow, hs]

/-- The prologue's node holds no value, so the realized code's node
expressions hold its request's (proved). -/
theorem realized_vals (ofC : ComponentTag → Bool) (r : SourceRequest σ ι) :
    valsArgs ofC true (realizedCode r).1 = valsArgs ofC true (requestCode r).1 := by
  simp [realizedCode, requestCode, vals]

/-- **Related steps cross the same values out** (proved, `vals_tabRel`,
`vals_ctx`, `actualXs_congr`; the crossings-out part of the draft's
`chk_sim`): in any context, a step of related runs to related runs crosses
out the same values at the same type. -/
theorem chk_actual_sim {F : TolerantFrames.ReadOnly.Family} {C : Nat} {tv : TypeView} (T : tv.Ty) (h h' : Heap)
    {r : SourceRequest σ ι} {K : Tm → Tm} (hK : EvalCtx K) {t₁ t₂ t₁' t₂' : Tm}
    (hr : TabRel (realizedCode r) (requestCode r) r.program.length t₁ t₂)
    (hr' : TabRel (realizedCode r) (requestCode r) r.program.length t₁' t₂') :
    actualXs F C T h (K t₁) h' (K t₁') = actualXs F C T h (K t₂) h' (K t₂') :=
  actualXs_congr T h h' (vals_ctx hK (vals_tabRel (realized_vals _ r) hr))
    (vals_ctx hK (vals_tabRel (realized_vals _ r) hr'))

end
end Verification.SourceClaimJson
