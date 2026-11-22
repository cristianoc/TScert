import Verification.Semantics.Support
import Verification.Semantics.SafeRet
import Verification.Paper.TolerantFrames.ReadOnlyLocalReach

/-! # Support-parametric callback demands: semantic foundation

Core general definitions and proved theorems for verifying higher-order
functions whose loops preserve heap facts across callback invocations,
without requiring `readonly` handles or a component-wide client obligation
`Θ_C`:

- `SupportedAt`: outer-entry support preservation — every location selected
  by `S` at `(ρ₀, h₀)` undergoes at most its allowed change from `h₁` to
  `h₂` (`supportedAt_self`, `supportedAt_refl`, `supportedAt_trans`,
  `supportedAt_of_mem_agree`).
- `CallbackDemand`: a callback parameter position `param` and the support
  `support` rooted at outer call positions (`callEnv`).
- **Operational local confinement** (`valRun_preserves_unreachable`,
  `valRun_preserves_ge_of_deep`): built directly on `ReadOnly.valRun_noForge`,
  `ReadOnly.step_changed_reached`, and `ReadOnly.reach_deep`. Any location
  unreachable from the call's values is preserved unconditionally across
  every step of the call's run.
- **Path-provenance freshness** (`region_mem_lt_length`,
  `supportedAt_of_write_ge`): in any well-formed heap (`HeapOk`, `RootsOk`),
  every location selected by ANY `Footprints.Region` — direct field, nested
  path, path spine, or path cells — lies strictly below `h.length`. Thus any
  write to a fresh location `l ≥ h.length` (such as `walked.push(w)` on a
  freshly allocated array) preserves every pre-existing region regardless of
  path nesting depth.
- **`SafeRet` collapse** (`SafeRet.toSafePostExcW`): collapses `SafeRet` into
  ordinary `SafePostExcW` (with zero client obligation `K` / `Θ_C`) whenever
  an execution invariant discharges `RetAt` at every step.
- **Transitive / adapting-closure preservation** (`supportedAt_of_steps`):
  any multi-step execution whose individual steps each preserve `SupportedAt`
  (either via fresh writes or via calls to a forwarding callback parameter)
  preserves `SupportedAt` across the whole run. -/

namespace Verification.CallbackDemands
open Verification Footprints HeapObservations

/-! ## Outer-entry support preservation -/

/-- **Outer-entry support preservation**: every location selected by `S` at
`(ρ₀, h₀)` undergoes at most its allowed change from `h₁` to `h₂`. -/
def SupportedAt (S : Footprint) (ρ₀ : Env) (h₀ h₁ h₂ : Heap) : Prop :=
  ∀ e ∈ S, ∀ l v, e.1.mem ρ₀ h₀ l = true → h₁[l]? = some v →
    ∃ v', h₂[l]? = some v' ∧ e.2.Holds h₁.length v v'

theorem supportedAt_self (S : Footprint) (ρ : Env) (h h' : Heap) :
    SupportedAt S ρ h h h' ↔ Supported S ρ h h' := Iff.rfl

theorem supportedAt_refl (S : Footprint) (ρ₀ : Env) (h₀ h : Heap) :
    SupportedAt S ρ₀ h₀ h h :=
  fun _ _ _ v _ hv => ⟨v, hv, Change.Holds.refl _ _ _⟩

theorem supportedAt_nil (ρ₀ : Env) (h₀ h₁ h₂ : Heap) :
    SupportedAt [] ρ₀ h₀ h₁ h₂ :=
  fun _ he => by cases he

theorem supportedAt_sub {S T : Footprint} {ρ₀ : Env} {h₀ h₁ h₂ : Heap}
    (hS : SupportedAt S ρ₀ h₀ h₁ h₂) (hsub : ∀ e ∈ T, e ∈ S) :
    SupportedAt T ρ₀ h₀ h₁ h₂ :=
  fun e he => hS e (hsub e he)

theorem supportedAt_trans {S : Footprint} {ρ₀ : Env} {h₀ h₁ h₂ h₃ : Heap}
    (hle : h₁.length ≤ h₂.length)
    (h12 : SupportedAt S ρ₀ h₀ h₁ h₂) (h23 : SupportedAt S ρ₀ h₀ h₂ h₃) :
    SupportedAt S ρ₀ h₀ h₁ h₃ := by
  intro e he l v hm hv1
  obtain ⟨v', hv2, hc1⟩ := h12 e he l v hm hv1
  obtain ⟨v'', hv3, hc2⟩ := h23 e he l v' hm hv2
  exact ⟨v'', hv3, hc1.trans hle hc2⟩

theorem supportedAt_of_prefix {S : Footprint} {ρ₀ : Env} {h₀ h₁ h₂ : Heap}
    (hp : h₁.IsPrefix h₂) : SupportedAt S ρ₀ h₀ h₁ h₂ := by
  intro e _ l v _ hv1
  obtain ⟨extra, rfl⟩ := hp
  have hlt : l < h₁.length := (List.getElem?_eq_some_iff.mp hv1).1
  exact ⟨v, by rw [List.getElem?_append_left hlt]; exact hv1, Change.Holds.refl _ _ _⟩

/-- **Outer-entry preservation gives call-site `Supported`** whenever every
region of `S` selects at `(ρ₀, h₁)` only locations it already selected at
`(ρ₀, h₀)` (automatic for `.field` and `.fields`; holds for `.path` and
`.spine` whenever prefix fields agree between `h₀` and `h₁`). -/
theorem supportedAt_to_supported {S : Footprint} {ρ₀ : Env} {h₀ h₁ h₂ : Heap}
    (hagree : ∀ e ∈ S, ∀ l, e.1.mem ρ₀ h₁ l = true → e.1.mem ρ₀ h₀ l = true)
    (hsup : SupportedAt S ρ₀ h₀ h₁ h₂) :
    Supported S ρ₀ h₁ h₂ :=
  fun e he l v hm hv => hsup e he l v (hagree e he l hm) hv

/-- **Renaming along a slot map**: if `σ` maps each region's slots into `ρ₀`
and `hagree` relates `r` at `(ρ, h₁)` to `r'` at `(ρ₀, h₀)`, `SupportedAt`
transfers cleanly to the renamed support. -/
theorem supportedAt_transfer {S T : Footprint} {ρ₀ ρ : Env} {h₀ h₁ h₂ : Heap}
    (hcov : ∀ e ∈ T, ∃ e' ∈ S, e'.2.le e.2 = true ∧
      ∀ l, e.1.mem ρ h₁ l = true → e'.1.mem ρ₀ h₀ l = true)
    (hsup : SupportedAt S ρ₀ h₀ h₁ h₂) :
    Supported T ρ h₁ h₂ := by
  intro e he l v hm hv
  obtain ⟨e', he', hle, hmem⟩ := hcov e he
  obtain ⟨v', hv', hc⟩ := hsup e' he' l v (hmem l hm) hv
  exact ⟨v', hv', hc.mono hle⟩

/-! ## Callback demand specification -/

/-- **A callback demand on a function**: parameter `param` (in `callEnv`
positions: `0` receiver, `1 + i` the `i`-th actual) must preserve `support`
(evaluated at outer entry `(callEnv r args, h₀)`). -/
structure CallbackDemand where
  param : Nat
  support : Footprint
  deriving Repr, DecidableEq

/-- Whether demand `a` is implied by demand `b` (same callback parameter, and
every entry of `a.support` is covered by an entry of `b.support` with at
least as strong a change). -/
def CallbackDemand.coveredBy (a b : CallbackDemand) : Bool :=
  a.param == b.param &&
    a.support.all fun e => b.support.any fun e' => e'.1 == e.1 && e'.2.le e.2

theorem CallbackDemand.coveredBy_sound {a b : CallbackDemand} (hc : a.coveredBy b = true)
    {ρ₀ : Env} {h₀ h₁ h₂ : Heap} (hb : SupportedAt b.support ρ₀ h₀ h₁ h₂) :
    SupportedAt a.support ρ₀ h₀ h₁ h₂ := by
  simp only [CallbackDemand.coveredBy, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hc
  intro e he l v hm hv
  obtain ⟨e', he', hreg, hle⟩ := hc.2 e he
  obtain ⟨v', hv', hch⟩ := hb e' he' l v (hreg ▸ hm) hv
  exact ⟨v', hv', hch.mono hle⟩

/-! ## Operational local confinement (Form (a)) -/

/-- **Operational local confinement**: any location unreachable from the
values of `t` in `h` is unchanged across every step of any `ValRun` starting
from `(h, t)`. Built directly on `ReadOnly.valRun_noForge` and
`ReadOnly.step_changed_reached`. -/
theorem valRun_preserves_unreachable {h h' : Heap} {t t' : Tm}
    (hr : TolerantFrames.ReadOnly.ValRun h t h' t')
    {l : Nat} {v : Val} (hv : h[l]? = some v)
    (hun : ¬ TolerantFrames.ReadOnly.ReachesFrom TolerantFrames.ReadOnly.allC h
      (TolerantFrames.ReadOnly.vals TolerantFrames.ReadOnly.allC TolerantFrames.ReadOnly.Realm.empty true false t) l) :
    h'[l]? = some v := by
  induction hr with
  | refl => exact hv
  | @step h₀ h₁ h₂ t₀ t₁ t₂ hh hs hrest ih =>
    have h1 : h₁[l]? = some v := by
      by_cases h1 : h₁[l]? = some v
      · exact h1
      · exact (hun (TolerantFrames.ReadOnly.step_changed_reached hs hv h1)).elim
    have hun1 : ¬ TolerantFrames.ReadOnly.ReachesFrom TolerantFrames.ReadOnly.allC h₁
        (TolerantFrames.ReadOnly.vals TolerantFrames.ReadOnly.allC TolerantFrames.ReadOnly.Realm.empty true false t₁) l := by
      intro hreach
      have hlt : l < h₀.length := (List.getElem?_eq_some_iff.mp hv).1
      rcases TolerantFrames.ReadOnly.step_noForge (ofC := TolerantFrames.ReadOnly.allC)
        (rl := TolerantFrames.ReadOnly.Realm.empty) (nk := false) (fun _ h => by cases h) hh hs none rfl l hreach with
        hpre | hge
      · exact hun hpre
      · omega
    exact ih h1 hun1

/-- **Fresh-region confinement corollary**: when every location `< b` holds
values reaching only locations `< b` (`HeapDeep (· < b) [true] h`), and every
value of term `t` reaches only locations `< b` (`DeepIn (· < b) [true]`),
then EVERY location `l ≥ b` is unchanged across any `ValRun` from `(h, t)`. -/
theorem valRun_preserves_ge_of_deep {b : Nat} {h h' : Heap} {t t' : Tm}
    (hr : TolerantFrames.ReadOnly.ValRun h t h' t')
    (hH : TolerantFrames.ReadOnly.HeapDeep (fun l => decide (l < b)) [true] h)
    (ht : ∀ u ∈ TolerantFrames.ReadOnly.vals TolerantFrames.ReadOnly.allC
      TolerantFrames.ReadOnly.Realm.empty true false t,
      TolerantFrames.ReadOnly.DeepIn (fun l => decide (l < b)) [true] u)
    {l : Nat} {v : Val} (hge : b ≤ l) (hv : h[l]? = some v) :
    h'[l]? = some v := by
  refine valRun_preserves_unreachable hr hv fun hreach => ?_
  obtain ⟨u, hu, π, hfol⟩ := hreach
  have hlt := TolerantFrames.ReadOnly.reach_deep hH π (ht u hu) hfol
  simp only [List.mem_singleton, decide_eq_true_eq] at hlt
  omega

/-! ## Path-provenance freshness (Form (b)) -/

private theorem roleAt_lt_of_shaped {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) {l : Nat} {r : Role} (hr : roleAt W l = some r) :
    l < h.length := by
  obtain ⟨u, hu, -⟩ := hsh l r hr
  exact (List.getElem?_eq_some_iff.mp hu).1

private theorem slot_roleAt_of_refsOk {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    {c : CallCode} {oid : Nat} (href : RefsOk W (.objAt fs c oid))
    {k : PropKey} {l : Nat} (hl : fs.lookup k = some l) :
    ∃ r, roleAt W l = some r := by
  have hpair : (k, l) ∈ fs := Footprints.lookup_mem_pair hl
  have hmem : Ref.slot k l ∈ objRefs fs oid :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(k, l), hpair, rfl⟩)
  have href' : Ref.slot k l ∈ refs (.objAt fs c oid) := by
    cases c <;> simp [refs, hmem]
  have hok := href (.slot k l) href'
  simp only [RefOk] at hok
  cases hr : roleAt W l with
  | none => rw [hr] at hok; exact hok.elim
  | some r => exact ⟨r, rfl⟩

private theorem refsOk_readPath {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) :
    ∀ (p : List String) {v u : Val}, RefsOk W v → HeapKnowledge.readPath h v p = some u →
      RefsOk W u
  | [], v, u, hv, hr => by
    simp only [HeapKnowledge.readPath, Option.some.injEq] at hr
    exact hr ▸ hv
  | f :: p, v, u, hv, hr => by
    cases v with
    | objAt fs c oid =>
      simp only [HeapKnowledge.readPath] at hr
      cases hlu : fs.lookup (.str f) with
      | none => simp only [hlu] at hr; cases hr
      | some l =>
        obtain ⟨r, hrw⟩ := slot_roleAt_of_refsOk hv hlu
        obtain ⟨w, hwl, hshape⟩ := hsh l r hrw
        simp only [hlu, hwl] at hr
        exact refsOk_readPath hsh p hshape.2 hr
    | _ => simp [HeapKnowledge.readPath] at hr

private theorem entriesAt_elem_lt {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) {s : Nat} {r : Role} (hrw : roleAt W s = some r) {l : Nat}
    (hm : some l ∈ Footprints.entriesAt h (some s)) : l < h.length := by
  obtain ⟨w, hws, hshape⟩ := hsh s r hrw
  simp only [Footprints.entriesAt, hws, Option.bind_some] at hm
  cases w with
  | arr ls =>
    simp only [spineEntries, Option.getD_some] at hm
    have href : Ref.elem l ∈ refs (.arr ls) := by
      simp only [refs, spineRefs, List.mem_filterMap]
      exact ⟨some l, hm, rfl⟩
    exact roleAt_lt_of_shaped hsh (hshape.2 (.elem l) href)
  | viewSpine f cs =>
    simp only [spineEntries, Option.getD_some, List.mem_map, Option.some.injEq] at hm
    obtain ⟨l', hl', rfl⟩ := hm
    have href : Ref.elem l' ∈ refs (.viewSpine f cs) := by
      simp only [refs, List.mem_map]
      exact ⟨l', hl', rfl⟩
    exact roleAt_lt_of_shaped hsh (hshape.2 (.elem l') href)
  | _ => simp [spineEntries] at hm

private theorem elem_lt_of_spineCells {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) {v : Val} (hv : RefsOk W v) {l : Nat}
    (hc : (Footprints.spineCells h v).contains (some l) = true) :
    l < h.length := by
  simp only [List.contains_iff_mem, Footprints.spineCells, List.mem_append] at hc
  rcases hc with hl | hr
  · cases v with
    | objAt fs c oid =>
      simp only [Footprints.fieldsOf] at hl
      cases hlu : fs.lookup arraySpineKey with
      | none => simp [hlu, Footprints.entriesAt] at hl
      | some s =>
        rw [hlu] at hl
        obtain ⟨r, hrw⟩ := slot_roleAt_of_refsOk hv hlu
        exact entriesAt_elem_lt hsh hrw hl
    | _ => simp [Footprints.fieldsOf, Footprints.entriesAt] at hl
  · cases v with
    | objAt fs c oid =>
      cases c with
      | view s f len =>
        simp only [HeapKnowledge.descriptorSpine] at hr
        have hmem : Ref.view s f len (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view s f len) oid) := by
          simp [refs]
        have hok := hv _ hmem
        simp only [RefOk] at hok
        exact entriesAt_elem_lt hsh hok.2 hr
      | _ => simp [HeapKnowledge.descriptorSpine, Footprints.entriesAt] at hr
    | _ => simp [HeapKnowledge.descriptorSpine, Footprints.entriesAt] at hr

private theorem elementsOf_lt {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) {v : Val} (hv : RefsOk W v) {l : Nat}
    (he : HeapKnowledge.elementsOf v = some l) :
    l < h.length := by
  cases v with
  | objAt fs c oid =>
    simp only [HeapKnowledge.elementsOf] at he
    cases hlu : fs.lookup arraySpineKey with
    | some s =>
      rw [hlu] at he
      cases he
      obtain ⟨r, hrw⟩ := slot_roleAt_of_refsOk hv hlu
      exact roleAt_lt_of_shaped hsh hrw
    | none =>
      rw [hlu] at he
      cases c with
      | view s f len =>
        simp only [Option.some.injEq] at he
        subst he
        have hmem : Ref.view s f len (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view s f len) oid) := by
          simp [refs]
        have hok := hv _ hmem
        simp only [RefOk] at hok
        exact roleAt_lt_of_shaped hsh hok.2
      | _ => cases he
  | _ => simp [HeapKnowledge.elementsOf] at he

private theorem fieldLocs_lt {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) {v : Val} (hv : RefsOk W v) {l : Nat}
    (hc : (Footprints.fieldLocs v).contains l = true) :
    l < h.length := by
  simp only [List.contains_iff_mem] at hc
  cases v with
  | objAt fs c oid =>
    simp only [Footprints.fieldLocs, Footprints.fieldsOf, List.mem_map, List.mem_filter] at hc
    obtain ⟨⟨k, l'⟩, ⟨hpair, -⟩, rfl⟩ := hc
    have hmem : Ref.slot k l' ∈ objRefs fs oid :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(k, l'), hpair, rfl⟩)
    have href' : Ref.slot k l' ∈ refs (.objAt fs c oid) := by
      cases c <;> simp [refs, hmem]
    have hok := hv (.slot k l') href'
    simp only [RefOk] at hok
    cases hr : roleAt W l' with
    | none => rw [hr] at hok; exact hok.elim
    | some r => exact roleAt_lt_of_shaped hsh hr
  | _ => simp [Footprints.fieldLocs, Footprints.fieldsOf] at hc

private theorem lookup_field_lt {n : Nat} {W : WorldT n} {h : Heap}
    (hsh : Shaped W h) {v : Val} (hv : RefsOk W v) {k : PropKey} {l : Nat}
    (hlu : (Footprints.fieldsOf v).lookup k = some l) :
    l < h.length := by
  cases v with
  | objAt fs c oid =>
    obtain ⟨r, hrw⟩ := slot_roleAt_of_refsOk hv hlu
    exact roleAt_lt_of_shaped hsh hrw
  | _ => simp [Footprints.fieldsOf] at hlu

/-- **Universal path-provenance bound**: in any well-formed heap (`HeapOk`,
`RootsOk`), EVERY location selected by ANY `Footprints.Region` — direct field,
nested path, nested path spine, or nested path cells — lies strictly below
`h.length`. -/
theorem region_mem_lt_length {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) :
    ∀ {r : Region} {l : Nat}, r.mem ρ h l = true → l < h.length
  | .field x k, l, hm => by
    simp only [Region.mem, beq_iff_eq] at hm
    exact lookup_field_lt hok.2 (hρ x) hm
  | .fields x, l, hm =>
    fieldLocs_lt hok.2 (hρ x) hm
  | .cells x, l, hm =>
    elem_lt_of_spineCells hok.2 (hρ x) hm
  | .cls _, l, hm => by
    simp only [Region.mem] at hm
    cases hget : h[l]? with
    | none => rw [hget] at hm; cases hm
    | some _ => exact (List.getElem?_eq_some_iff.mp hget).1
  | .all, l, hm => by
    simpa [Region.mem] using hm
  | .path x p k, l, hm => by
    simp only [Region.mem] at hm
    cases hr : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hr] at hm; cases hm
    | some v =>
      rw [hr] at hm
      simp only [beq_iff_eq] at hm
      exact lookup_field_lt hok.2 (refsOk_readPath hok.2 p (hρ x) hr) hm
  | .pathFields x p, l, hm => by
    simp only [Region.mem] at hm
    cases hr : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hr] at hm; cases hm
    | some v =>
      rw [hr] at hm
      exact fieldLocs_lt hok.2 (refsOk_readPath hok.2 p (hρ x) hr) hm
  | .pathCells x p, l, hm => by
    simp only [Region.mem] at hm
    cases hr : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hr] at hm; cases hm
    | some v =>
      rw [hr] at hm
      exact elem_lt_of_spineCells hok.2 (refsOk_readPath hok.2 p (hρ x) hr) hm
  | .inCls r _, l, hm => by
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact region_mem_lt_length hok hρ hm.1
  | .spine x p, l, hm => by
    simp only [Region.mem] at hm
    cases hr : HeapKnowledge.readPath h (ρ x) p with
    | none => rw [hr] at hm; cases hm
    | some v =>
      rw [hr] at hm
      simp only [beq_iff_eq] at hm
      exact elementsOf_lt hok.2 (refsOk_readPath hok.2 p (hρ x) hr) hm

/-- **Fresh-write preservation at arbitrary path depth**: if every location
modified between `h₁` and `h₂` lies at or above `b` (such as a freshly
allocated array `walked` created at heap length `b`), and every region of `S`
evaluated at `(ρ₀, h₀)` selects only locations `< b` (from `region_mem_lt_length`),
then `SupportedAt S ρ₀ h₀ h₁ h₂` holds unconditionally. -/
theorem supportedAt_of_write_ge {b : Nat} {S : Footprint} {ρ₀ : Env} {h₀ h₁ h₂ : Heap}
    (hSlt : ∀ e ∈ S, ∀ l, e.1.mem ρ₀ h₀ l = true → l < b)
    (hmod : ∀ l v, l < b → h₁[l]? = some v → h₂[l]? = some v) :
    SupportedAt S ρ₀ h₀ h₁ h₂ := by
  intro e he l v hm hv1
  exact ⟨v, hmod l v (hSlt e he l hm) hv1, Change.Holds.refl _ _ _⟩

/-! ## Collapsing `SafeRet` without client trust `Θ_C` -/

/-- **`SafeRet` collapses to ordinary `SafePostExcW`** (zero `ClientFrame`,
zero `Θ_C`) whenever an invariant `I` of the pending framed evaluation and
state discharges `RetAt` at every step and is preserved across every step. -/
theorem safeRet_to_safePostExcW {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : WPost} {R : WExc}
    {F : Nat → Bool} {Ret RetE : Nat → Env → Heap → Heap → Prop}
    {I : Option (Nat × Heap) → (k : Nat) → WorldT k → Heap → Tm → Prop}
    (hinv : ∀ p (k : Nat) (W : WorldT (k + 1)) h t (U : WorldT k) h' t',
      I p (k + 1) W h t → Step h t h' t' →
      WExt (trunc k (Nat.le_succ k) W) U → WorldAdm U → HeapOk k U h' →
      RetAt Ret RetE p h' t t' ∧ (RefsOk U t' → I (framedPend F p h t t') k U h' t')) :
    ∀ {n : Nat} {W : WorldT n} {p : Option (Nat × Heap)} {h : Heap} {t : Tm},
      I p n W h t → SafeRet J Ξ T Q R F Ret RetE n W p h t →
      SafePostExcW Ξ T Q R n W h t ∧
        (∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → Steps j h t h' t' → J h' t') := by
  intro n
  induction n with
  | zero =>
    intro W p h t _ hs
    exact ⟨hs, fun hj _ => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro W p h t hi hs
    obtain ⟨hrf, hJ, hs⟩ := hs
    rcases hs with hv | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · refine ⟨⟨hrf, .inl hv⟩, fun hj hsteps => ?_⟩
      cases hsteps with
      | refl => exact hJ
      | next st' _ =>
        rcases hv with ⟨hval, _, _⟩ | ⟨⟨v, hr, _, _⟩, _⟩
        · exact absurd hval (by simp [not_val_of_step st'])
        · exact absurd st' (raises_no_step hr)
    · obtain ⟨hret, hi'⟩ := hinv p n W h t U h' t' hi st hx hu hh
      have hs' := hs hret
      obtain ⟨hpost', hreach'⟩ := ih (hi' (SafeRet.refs hs')) hs'
      refine ⟨⟨hrf, .inr ⟨U, h', t', hx, hu, st, hh, hpost'⟩⟩, fun hj hsteps => ?_⟩
      cases hsteps with
      | refl => exact hJ
      | next st' hrest =>
        obtain ⟨rfl, rfl⟩ := Step_det st st'
        exact hreach' (Nat.lt_of_succ_lt_succ hj) hrest

/-! ## Multi-step preservation for adapting / forwarding closures -/

/-- **Transitivity across `Steps`**: if every individual step along a run
from `(h, t)` preserves `SupportedAt S ρ₀ h₀`, then the entire run preserves
`SupportedAt S ρ₀ h₀`. -/
theorem supportedAt_of_steps {S : Footprint} {ρ₀ : Env} {h₀ : Heap}
    {P : Heap → Tm → Prop}
    (hstep : ∀ {h t h' t'}, P h t → Step h t h' t' →
      SupportedAt S ρ₀ h₀ h h' ∧ P h' t') :
    ∀ {k : Nat} {h t h' t'}, P h t → Steps k h t h' t' →
      SupportedAt S ρ₀ h₀ h h'
  | 0, h, _, _, _, _, .refl => supportedAt_refl S ρ₀ h₀ h
  | _ + 1, _, _, _, _, hP, .next st hrest =>
    let ⟨hs1, hP'⟩ := hstep hP st
    supportedAt_trans (Footprints.step_length_le st) hs1 (supportedAt_of_steps hstep hP' hrest)

/-- **A callback-demand plan's specification**:
- `framed`: each callback call node `l` in the main graph and the supports kept
  across it (passed directly to `SinglePass` and `run_sound_framed`);
- `calls`: each framed call node `l` paired with the `callEnv` parameter
  position (`1 + i`) of the callback it invokes;
- `confined`: allocation nodes whose fresh local objects are confined to the
  function body (never passed out or stored into pre-existing storage);
- `demands`: the published `CallbackDemand`s required of callers. -/
structure CallbackDemandSpec where
  framed : List (Nat × List Footprint) := []
  calls : List (Nat × Nat) := []
  confined : List Nat := []
  demands : List CallbackDemand := []
  deriving Repr, DecidableEq

/-! ## Pure read-only / fresh-allocating operational soundness -/

mutual
/-- Whether a term performs no writes to existing heap storage (only values,
reads, arithmetic, conditionals, lets, or fresh allocations), so every `Step`
keeps `h.IsPrefix h'`. -/
def isReadOnlyOrAlloc : Tm → Bool
  | .var _ | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _
  | .objAt .. | .arr _ | .viewSpine .. => true
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => isReadOnlyOrAlloc a
  | .indexAt a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
      isReadOnlyOrAlloc a && isReadOnlyOrAlloc b
  | .ite c a b => isReadOnlyOrAlloc c && isReadOnlyOrAlloc a && isReadOnlyOrAlloc b
  | .letE a b => isReadOnlyOrAlloc a && isReadOnlyOrAlloc b
  | .makeAt .absent _ xs | .arrLit xs => isReadOnlyOrAllocList xs
  | .makeAt (.graph _ _ _ _ _ _ _ _) _ xs => isReadOnlyOrAllocList xs
  | _ => false
termination_by structural t => t

def isReadOnlyOrAllocList : List Tm → Bool
  | [] => true
  | x :: xs => isReadOnlyOrAlloc x && isReadOnlyOrAllocList xs
termination_by structural xs => xs
end

theorem isReadOnlyOrAllocList_eq_all (xs : List Tm) :
    isReadOnlyOrAllocList xs = xs.all isReadOnlyOrAlloc := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [isReadOnlyOrAllocList, ih]

theorem isReadOnlyOrAlloc_of_isVal {v : Tm} (hv : isVal v = true) : isReadOnlyOrAlloc v = true := by
  cases v <;> simp_all [isVal, isReadOnlyOrAlloc]

theorem isReadOnlyOrAlloc_makeAt_absent (ns : List PropKey) (xs : List Tm) :
    isReadOnlyOrAlloc (.makeAt .absent ns xs) = xs.all isReadOnlyOrAlloc := by
  simp [isReadOnlyOrAlloc, isReadOnlyOrAllocList_eq_all]

theorem isReadOnlyOrAlloc_makeAt_graph (ar : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (s : Nat) (caps : List Tm)
    (k : Invoke) (r : Bool) (c : ComponentTag) (ns : List PropKey) (xs : List Tm) :
    isReadOnlyOrAlloc (.makeAt (.graph ar E K s caps k r c) ns xs) = xs.all isReadOnlyOrAlloc := by
  simp [isReadOnlyOrAlloc, isReadOnlyOrAllocList_eq_all]

theorem isReadOnlyOrAlloc_arrLit (xs : List Tm) :
    isReadOnlyOrAlloc (.arrLit xs) = xs.all isReadOnlyOrAlloc := by
  simp [isReadOnlyOrAlloc, isReadOnlyOrAllocList_eq_all]

mutual
theorem isReadOnlyOrAlloc_subst {a : Tm} (ha : isReadOnlyOrAlloc a = true) :
    ∀ (t : Tm) (j : Nat), isReadOnlyOrAlloc t = true → isReadOnlyOrAlloc (subst j a t) = true
  | .var i, j, _ => by
    simp only [subst]
    split
    · exact ha
    · split <;> rfl
  | .nul, _, _ | .undef, _, _ | .tru, _, _ | .fls, _, _ | .num _, _, _ | .str _, _, _
  | .bigint _, _, _ | .sym _, _, _ | .arr _, _, _ | .viewSpine .., _, _ => rfl
  | .objAt _ c _, _, _ => by cases c <;> rfl
  | .readAt _ x, j, ht => isReadOnlyOrAlloc_subst ha x j ht
  | .test _ x, j, ht => isReadOnlyOrAlloc_subst ha x j ht
  | .lenOf x, j, ht => isReadOnlyOrAlloc_subst ha x j ht
  | .spread x, j, ht => isReadOnlyOrAlloc_subst ha x j ht
  | .throw x, j, ht => isReadOnlyOrAlloc_subst ha x j ht
  | .indexAt x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isReadOnlyOrAlloc_subst ha y j ht.2⟩
  | .arith _ x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isReadOnlyOrAlloc_subst ha y j ht.2⟩
  | .elemAt x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isReadOnlyOrAlloc_subst ha y j ht.2⟩
  | .merge _ x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isReadOnlyOrAlloc_subst ha y j ht.2⟩
  | .makeKey x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isReadOnlyOrAlloc_subst ha y j ht.2⟩
  | .ite c x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨⟨isReadOnlyOrAlloc_subst ha c j ht.1.1, isReadOnlyOrAlloc_subst ha x j ht.1.2⟩,
      isReadOnlyOrAlloc_subst ha y j ht.2⟩
  | .letE x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [subst, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isReadOnlyOrAlloc_subst ha y (j + 1) ht.2⟩
  | .makeAt .absent _ xs, j, ht => isReadOnlyOrAllocList_subst ha xs j ht
  | .makeAt (.graph ..) _ xs, j, ht => isReadOnlyOrAllocList_subst ha xs j ht
  | .arrLit xs, j, ht => isReadOnlyOrAllocList_subst ha xs j ht
  | .makeAt (.bound ..) _ _, _, ht | .makeAt (.view ..) _ _, _, ht
  | .invoke .., _, ht | .construct .., _, ht | .writeAt .., _, ht
  | .setElem .., _, ht | .goto .., _, ht | .frame .., _, ht => by simp [isReadOnlyOrAlloc] at ht
termination_by structural t => t

theorem isReadOnlyOrAllocList_subst {a : Tm} (ha : isReadOnlyOrAlloc a = true) :
    ∀ (xs : List Tm) (j : Nat), isReadOnlyOrAllocList xs = true → isReadOnlyOrAllocList (substArgs j a xs) = true
  | [], _, _ => rfl
  | x :: xs, j, h => by
    simp only [isReadOnlyOrAllocList, Bool.and_eq_true] at h
    simp only [substArgs, isReadOnlyOrAllocList, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j h.1, isReadOnlyOrAllocList_subst ha xs j h.2⟩
termination_by structural xs => xs
end

mutual
theorem isReadOnlyOrAlloc_instantiate {ρ : Env} (hρ : ∀ i, isReadOnlyOrAlloc (ρ i) = true) :
    ∀ (t : Tm) (j : Nat), isReadOnlyOrAlloc t = true → isReadOnlyOrAlloc (instantiate j ρ t) = true
  | .var i, j, _ => by
    simp only [instantiate]
    split
    · rfl
    · exact hρ (i - j)
  | .nul, _, _ | .undef, _, _ | .tru, _, _ | .fls, _, _ | .num _, _, _ | .str _, _, _
  | .bigint _, _, _ | .sym _, _, _ | .arr _, _, _ | .viewSpine .., _, _ => rfl
  | .objAt _ c _, _, _ => by cases c <;> rfl
  | .readAt _ x, j, ht => isReadOnlyOrAlloc_instantiate hρ x j ht
  | .test _ x, j, ht => isReadOnlyOrAlloc_instantiate hρ x j ht
  | .lenOf x, j, ht => isReadOnlyOrAlloc_instantiate hρ x j ht
  | .spread x, j, ht => isReadOnlyOrAlloc_instantiate hρ x j ht
  | .throw x, j, ht => isReadOnlyOrAlloc_instantiate hρ x j ht
  | .indexAt x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isReadOnlyOrAlloc_instantiate hρ y j ht.2⟩
  | .arith _ x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isReadOnlyOrAlloc_instantiate hρ y j ht.2⟩
  | .elemAt x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isReadOnlyOrAlloc_instantiate hρ y j ht.2⟩
  | .merge _ x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isReadOnlyOrAlloc_instantiate hρ y j ht.2⟩
  | .makeKey x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isReadOnlyOrAlloc_instantiate hρ y j ht.2⟩
  | .ite c x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨⟨isReadOnlyOrAlloc_instantiate hρ c j ht.1.1, isReadOnlyOrAlloc_instantiate hρ x j ht.1.2⟩,
      isReadOnlyOrAlloc_instantiate hρ y j ht.2⟩
  | .letE x y, j, ht => by
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isReadOnlyOrAlloc_instantiate hρ y (j + 1) ht.2⟩
  | .makeAt .absent _ xs, j, ht => isReadOnlyOrAllocList_instantiate hρ xs j ht
  | .makeAt (.graph ..) _ xs, j, ht => isReadOnlyOrAllocList_instantiate hρ xs j ht
  | .arrLit xs, j, ht => isReadOnlyOrAllocList_instantiate hρ xs j ht
  | .makeAt (.bound ..) _ _, _, ht | .makeAt (.view ..) _ _, _, ht
  | .invoke .., _, ht | .construct .., _, ht | .writeAt .., _, ht
  | .setElem .., _, ht | .goto .., _, ht | .frame .., _, ht => by simp [isReadOnlyOrAlloc] at ht
termination_by structural t => t

theorem isReadOnlyOrAllocList_instantiate {ρ : Env} (hρ : ∀ i, isReadOnlyOrAlloc (ρ i) = true) :
    ∀ (xs : List Tm) (j : Nat), isReadOnlyOrAllocList xs = true → isReadOnlyOrAllocList (instantiateArgs j ρ xs) = true
  | [], _, _ => rfl
  | x :: xs, j, h => by
    simp only [isReadOnlyOrAllocList, Bool.and_eq_true] at h
    simp only [instantiateArgs, isReadOnlyOrAllocList, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j h.1, isReadOnlyOrAllocList_instantiate hρ xs j h.2⟩
termination_by structural xs => xs
end

private theorem readElems_isVal {h : Heap} :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs →
      (∀ (l : Nat) v, h[l]? = some v → isVal v = true) → ∀ v ∈ vs, isVal v = true
  | [], _, hr, _ => by simp [readElems] at hr; subst hr; intro _ h; cases h
  | none :: ls, vs, hr, hh => by
    simp only [readElems] at hr
    cases hrest : readElems h ls with
    | none => simp [hrest] at hr
    | some rest =>
      simp only [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rfl
      · exact readElems_isVal hrest hh v hv
  | some l :: ls, vs, hr, hh => by
    simp only [readElems] at hr
    cases hv0 : h[l]? with
    | none => simp [hv0] at hr
    | some v0 =>
      simp only [hv0, Option.bind_some] at hr
      cases hrest : readElems h ls with
      | none => simp [hrest] at hr
      | some rest =>
        simp only [hrest, Option.map_some, Option.some.injEq] at hr
        subst hr
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hh l v hv0
        · exact readElems_isVal hrest hh v hv

private theorem list_all_set {α : Type} : ∀ {xs : List α} {p : α → Bool} {i : Nat} {a : α},
    xs.all p = true → p a = true → (xs.set i a).all p = true
  | [], _, _, _, _, _ => rfl
  | _ :: xs, p, 0, a, hall, ha => by
    simp only [List.set, List.all_cons, Bool.and_eq_true] at hall ⊢
    exact ⟨ha, hall.2⟩
  | x :: xs, p, i + 1, a, hall, ha => by
    simp only [List.set, List.all_cons, Bool.and_eq_true] at hall ⊢
    exact ⟨hall.1, list_all_set hall.2 ha⟩

private theorem binop_isVal {op : Arith} {a b v : Tm} (h : binop op a b = some v) : isVal v = true := by
  obtain ⟨-, -, hv⟩ := binop_result h
  rcases hv with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

private theorem mergeParts_isVal {h : Heap} {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hp : mergeParts h d a b = some ps) : ∀ p ∈ ps, isVal p.2 = true := by
  intro p hmem
  rcases mergeParts_vals hp p hmem with h1 | ⟨_, h2⟩ | ⟨_, h3⟩
  · rw [h1]; rfl
  · exact h2
  · rw [h3]; rfl

private theorem vals_append {h xs : Heap}
    (hh : ∀ (l : Nat) v, h[l]? = some v → isVal v = true)
    (hxs : ∀ v ∈ xs, isVal v = true) :
    ∀ (l : Nat) v, (h ++ xs)[l]? = some v → isVal v = true := by
  intro l v hget
  rcases List.mem_append.mp (List.mem_of_getElem? hget) with hm | hm
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm; exact hh j v hj
  · exact hxs v hm

/-- **Read-only / fresh-allocating step soundness**: every `Step` of a term
satisfying `isReadOnlyOrAlloc` extends the heap as a prefix (`h.IsPrefix h'`),
preserves `isReadOnlyOrAlloc`, and keeps every heap entry a value. -/
theorem isReadOnlyOrAlloc_step {h h' : Heap} {t t' : Tm} (st : Step h t h' t')
    (hh : ∀ (l : Nat) v, h[l]? = some v → isVal v = true)
    (ht : isReadOnlyOrAlloc t = true) :
    h.IsPrefix h' ∧ isReadOnlyOrAlloc t' = true ∧ (∀ (l : Nat) v, h'[l]? = some v → isVal v = true) := by
  induction st with
  | letC _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ha', ht.2], hh'⟩
  | letV hv =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    exact ⟨List.prefix_rfl, isReadOnlyOrAlloc_subst (isReadOnlyOrAlloc_of_isVal hv) _ 0 ht.2, hh⟩
  | spreadC _ ih => exact ih hh ht
  | @makeArg c ns inits i _ _ a a' hi _ _ ih =>
    cases c with
    | absent =>
      rw [isReadOnlyOrAlloc_makeAt_absent] at ht ⊢
      obtain ⟨hp, ha', hh'⟩ := ih hh (List.all_eq_true.mp ht a (List.mem_of_getElem? hi))
      exact ⟨hp, list_all_set ht ha', hh'⟩
    | graph ar E K s caps k r comp =>
      rw [isReadOnlyOrAlloc_makeAt_graph] at ht ⊢
      obtain ⟨hp, ha', hh'⟩ := ih hh (List.all_eq_true.mp ht a (List.mem_of_getElem? hi))
      exact ⟨hp, list_all_set ht ha', hh'⟩
    | _ => simp [isReadOnlyOrAlloc] at ht
  | @makeFields _ _ vs _ hvs _ =>
    exact ⟨⟨vs ++ [.nul], by simp [List.append_assoc]⟩, by simp [isReadOnlyOrAlloc],
      vals_append (vals_append hh hvs) (by simp [isVal])⟩
  | readC _ ih => exact ih hh ht
  | readField _ hget => exact ⟨List.prefix_rfl, isReadOnlyOrAlloc_of_isVal (hh _ _ hget), hh⟩
  | readProto _ _ hget => exact ⟨List.prefix_rfl, by simpa [isReadOnlyOrAlloc] using isReadOnlyOrAlloc_of_isVal (hh _ _ hget), hh⟩
  | readMissing _ _ => exact ⟨List.prefix_rfl, rfl, hh⟩
  | indexC1 _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ha', ht.2], hh'⟩
  | indexC2 _ _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.2
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ht.1, ha'], hh'⟩
  | indexField _ _ hget => exact ⟨List.prefix_rfl, isReadOnlyOrAlloc_of_isVal (hh _ _ hget), hh⟩
  | indexProto _ _ _ hget =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    exact ⟨List.prefix_rfl, by simp [isReadOnlyOrAlloc, isReadOnlyOrAlloc_of_isVal (hh _ _ hget), ht.2], hh⟩
  | indexMissing _ _ _ => exact ⟨List.prefix_rfl, rfl, hh⟩
  | testC _ ih => exact ih hh ht
  | testV _ => exact ⟨List.prefix_rfl, by split <;> rfl, hh⟩
  | iteC _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, hc', hh'⟩ := ih hh ht.1.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, hc', ht.1.2, ht.2], hh'⟩
  | iteT =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    exact ⟨List.prefix_rfl, ht.1.2, hh⟩
  | iteF =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    exact ⟨List.prefix_rfl, ht.2, hh⟩
  | arithC1 _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ha', ht.2], hh'⟩
  | arithC2 _ _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, hb', hh'⟩ := ih hh ht.2
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ht.1, hb'], hh'⟩
  | arithV hbin =>
    exact ⟨List.prefix_rfl, isReadOnlyOrAlloc_of_isVal (binop_isVal hbin), hh⟩
  | arithThrow _ => exact ⟨⟨[.nul], rfl⟩, rfl, vals_append hh (by simp [isVal])⟩
  | arrArg hi _ _ ih =>
    rw [isReadOnlyOrAlloc_arrLit] at ht ⊢
    obtain ⟨hp, ha', hh'⟩ := ih hh (List.all_eq_true.mp ht _ (List.mem_of_getElem? hi))
    exact ⟨hp, list_all_set ht ha', hh'⟩
  | arrSpread heq _ hread =>
    rw [isReadOnlyOrAlloc_arrLit] at ht ⊢
    rw [heq, List.all_append, List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at ht
    rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨List.prefix_rfl, ⟨⟨ht.1, List.all_eq_true.mpr fun v hv =>
      isReadOnlyOrAlloc_of_isVal (readElems_isVal hread hh v hv)⟩, ht.2.2⟩, hh⟩
  | arrAlloc hvs _ => exact ⟨⟨_, rfl⟩, rfl, vals_append hh hvs⟩
  | arrAllocThrow _ _ => exact ⟨⟨[.nul], rfl⟩, rfl, vals_append hh (by simp [isVal])⟩
  | elemC1 _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ha', ht.2], hh'⟩
  | elemC2 _ _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, hb', hh'⟩ := ih hh ht.2
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ht.1, hb'], hh'⟩
  | elemRead _ hget => exact ⟨List.prefix_rfl, isReadOnlyOrAlloc_of_isVal (hh _ _ hget), hh⟩
  | elemAbsent _ => exact ⟨List.prefix_rfl, rfl, hh⟩
  | elemStr => exact ⟨List.prefix_rfl, by unfold codeUnitAt; split <;> rfl, hh⟩
  | lenC _ ih => exact ih hh ht
  | lenV => exact ⟨List.prefix_rfl, rfl, hh⟩
  | lenStr _ => exact ⟨List.prefix_rfl, rfl, hh⟩
  | lenStrThrow _ => exact ⟨⟨[.nul], rfl⟩, rfl, vals_append hh (by simp [isVal])⟩
  | throwC _ ih => exact ih hh ht
  | mergeC1 _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ha', ht.2], hh'⟩
  | mergeC2 _ _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, hb', hh'⟩ := ih hh ht.2
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ht.1, hb'], hh'⟩
  | mergeV _ _ hmp =>
    refine ⟨List.prefix_rfl, ?_, hh⟩
    rw [isReadOnlyOrAlloc_makeAt_absent, List.all_map, List.all_eq_true]
    intro p hp
    exact isReadOnlyOrAlloc_of_isVal (mergeParts_isVal hmp p hp)
  | makeKeyC1 _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, ha', hh'⟩ := ih hh ht.1
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ha', ht.2], hh'⟩
  | makeKeyC2 _ _ ih =>
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at ht
    obtain ⟨hp, hb', hh'⟩ := ih hh ht.2
    exact ⟨hp, by simp [isReadOnlyOrAlloc, ht.1, hb'], hh'⟩
  | makeKeyV hv _ =>
    exact ⟨List.prefix_rfl, by rw [isReadOnlyOrAlloc_makeAt_absent]; simp [isReadOnlyOrAlloc_of_isVal hv], hh⟩
  | _ => simp [isReadOnlyOrAlloc] at ht

/-- Multi-step read-only / fresh-allocating prefix soundness. -/
theorem isReadOnlyOrAlloc_steps {k : Nat} {h h' : Heap} {t t' : Tm}
    (hh : ∀ (l : Nat) v, h[l]? = some v → isVal v = true)
    (ht : isReadOnlyOrAlloc t = true) (hs : Steps k h t h' t') :
    h.IsPrefix h' ∧ isReadOnlyOrAlloc t' = true := by
  induction hs with
  | refl => exact ⟨List.prefix_rfl, ht⟩
  | @next _ h₀ h₁ h₂ t₀ t₁ t₂ st _ ih =>
    obtain ⟨hpre01, ht1, hh1⟩ := isReadOnlyOrAlloc_step st hh ht
    obtain ⟨hpre12, ht2⟩ := ih hh1 ht1
    exact ⟨hpre01.trans hpre12, ht2⟩

/-- A value whose own allocated field and spine locations all lie at or above `b`. -/
def FreshValueAt (b : Nat) : Tm → Prop
  | .objAt fs .absent _ => ∀ k l, (k, l) ∈ fs → b ≤ l
  | .arr ls => ∀ l, some l ∈ ls → b ≤ l
  | _ => False

theorem FreshValueAt.mono {b₁ b₂ : Nat} {v : Tm} (hle : b₁ ≤ b₂) (h : FreshValueAt b₂ v) :
    FreshValueAt b₁ v := by
  cases v with
  | objAt fs c _ =>
    cases c with
    | absent => exact fun k l hm => Nat.le_trans hle (h k l hm)
    | _ => exact h
  | arr ls => exact fun l hm => Nat.le_trans hle (h l hm)
  | _ => exact h

/-- Whether a term is a pure fresh plain-object or array allocation (possibly
wrapped in `.letE` bindings of read-only / allocating expressions, as array
literals lower to `.letE (.arrLit ...) (.makeAt .absent ...)`). -/
def isFreshAlloc : Tm → Bool
  | .makeAt .absent _ xs => isReadOnlyOrAllocList xs
  | .arrLit xs => isReadOnlyOrAllocList xs
  | .letE a b => isReadOnlyOrAlloc a && isFreshAlloc b
  | _ => false

theorem isFreshAlloc_isReadOnlyOrAlloc : ∀ {t : Tm}, isFreshAlloc t = true → isReadOnlyOrAlloc t = true
  | .makeAt .absent _ xs, ht => by simpa [isFreshAlloc, isReadOnlyOrAlloc] using ht
  | .arrLit xs, ht => by simpa [isFreshAlloc, isReadOnlyOrAlloc] using ht
  | .letE a b, ht => by
    simp only [isFreshAlloc, Bool.and_eq_true] at ht
    simp only [isReadOnlyOrAlloc, Bool.and_eq_true]
    exact ⟨ht.1, isFreshAlloc_isReadOnlyOrAlloc ht.2⟩
  | .var _, ht | .nul, ht | .undef, ht | .tru, ht | .fls, ht | .num _, ht | .str _, ht
  | .bigint _, ht | .sym _, ht | .objAt .., ht | .arr _, ht | .viewSpine .., ht
  | .readAt .., ht | .indexAt .., ht | .writeAt .., ht | .test .., ht | .ite .., ht
  | .arith .., ht | .elemAt .., ht | .setElem .., ht | .lenOf _, ht | .spread _, ht
  | .throw _, ht | .merge .., ht | .makeKey .., ht | .invoke .., ht | .construct .., ht
  | .goto .., ht | .frame .., ht => by simp [isFreshAlloc] at ht
  | .makeAt (.graph ..) _ _, ht | .makeAt (.bound ..) _ _, ht | .makeAt (.view ..) _ _, ht => by
    simp [isFreshAlloc] at ht

theorem isFreshAlloc_subst {a : Tm} (ha : isReadOnlyOrAlloc a = true) :
    ∀ {t : Tm} (j : Nat), isFreshAlloc t = true → isFreshAlloc (subst j a t) = true
  | .makeAt .absent ns xs, j, ht => by
    have ht' : isReadOnlyOrAlloc (.makeAt .absent ns xs) = true := isFreshAlloc_isReadOnlyOrAlloc ht
    have hsub := isReadOnlyOrAlloc_subst ha (.makeAt .absent ns xs) j ht'
    simpa [subst, isFreshAlloc, isReadOnlyOrAlloc] using hsub
  | .arrLit xs, j, ht => by
    have ht' : isReadOnlyOrAlloc (.arrLit xs) = true := isFreshAlloc_isReadOnlyOrAlloc ht
    have hsub := isReadOnlyOrAlloc_subst ha (.arrLit xs) j ht'
    simpa [subst, isFreshAlloc, isReadOnlyOrAlloc] using hsub
  | .letE x b, j, ht => by
    simp only [isFreshAlloc, Bool.and_eq_true] at ht
    simp only [subst, isFreshAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_subst ha x j ht.1, isFreshAlloc_subst ha (j + 1) ht.2⟩
  | .var _, _, ht | .nul, _, ht | .undef, _, ht | .tru, _, ht | .fls, _, ht | .num _, _, ht
  | .str _, _, ht | .bigint _, _, ht | .sym _, _, ht | .objAt .., _, ht | .arr _, _, ht
  | .viewSpine .., _, ht | .readAt .., _, ht | .indexAt .., _, ht | .writeAt .., _, ht
  | .test .., _, ht | .ite .., _, ht | .arith .., _, ht | .elemAt .., _, ht | .setElem .., _, ht
  | .lenOf _, _, ht | .spread _, _, ht | .throw _, _, ht | .merge .., _, ht | .makeKey .., _, ht
  | .invoke .., _, ht | .construct .., _, ht | .goto .., _, ht | .frame .., _, ht
  | .makeAt (.graph ..) _ _, _, ht | .makeAt (.bound ..) _ _, _, ht | .makeAt (.view ..) _ _, _, ht => by
    simp [isFreshAlloc] at ht

theorem isFreshAlloc_instantiate {ρ : Env} (hρ : ∀ i, isReadOnlyOrAlloc (ρ i) = true) :
    ∀ {t : Tm} (j : Nat), isFreshAlloc t = true → isFreshAlloc (instantiate j ρ t) = true
  | .makeAt .absent ns xs, j, ht => by
    have hinst := isReadOnlyOrAlloc_instantiate hρ (.makeAt .absent ns xs) j (isFreshAlloc_isReadOnlyOrAlloc ht)
    simpa [instantiate, isFreshAlloc, isReadOnlyOrAlloc] using hinst
  | .arrLit xs, j, ht => by
    have hinst := isReadOnlyOrAlloc_instantiate hρ (.arrLit xs) j (isFreshAlloc_isReadOnlyOrAlloc ht)
    simpa [instantiate, isFreshAlloc, isReadOnlyOrAlloc] using hinst
  | .letE x b, j, ht => by
    simp only [isFreshAlloc, Bool.and_eq_true] at ht
    simp only [instantiate, isFreshAlloc, Bool.and_eq_true]
    exact ⟨isReadOnlyOrAlloc_instantiate hρ x j ht.1, isFreshAlloc_instantiate hρ (j + 1) ht.2⟩
  | .var _, _, ht | .nul, _, ht | .undef, _, ht | .tru, _, ht | .fls, _, ht | .num _, _, ht
  | .str _, _, ht | .bigint _, _, ht | .sym _, _, ht | .objAt .., _, ht | .arr _, _, ht
  | .viewSpine .., _, ht | .readAt .., _, ht | .indexAt .., _, ht | .writeAt .., _, ht
  | .test .., _, ht | .ite .., _, ht | .arith .., _, ht | .elemAt .., _, ht | .setElem .., _, ht
  | .lenOf _, _, ht | .spread _, _, ht | .throw _, _, ht | .merge .., _, ht | .makeKey .., _, ht
  | .invoke .., _, ht | .construct .., _, ht | .goto .., _, ht | .frame .., _, ht
  | .makeAt (.graph ..) _ _, _, ht | .makeAt (.bound ..) _ _, _, ht | .makeAt (.view ..) _ _, _, ht => by
    simp [isFreshAlloc] at ht

private theorem slots_ge (base : Nat) : ∀ (ns : List PropKey) k l, (k, l) ∈ slots base ns → base ≤ l
  | [], _, _, hm => by cases hm
  | _ :: ns, k, l, hm => by
    rcases List.mem_cons.mp hm with h | h
    · cases h; exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ base) (slots_ge (base + 1) ns k l h)

private theorem elemSlots_ge (base n : Nat) {l : Nat} (hm : some l ∈ elemSlots base n) : base ≤ l := by
  simp only [elemSlots, List.mem_map, Option.some.injEq] at hm
  obtain ⟨i, _, rfl⟩ := hm
  omega

private theorem throw_val_never_val {k : Nat} {h h' : Heap} {u v : Tm}
    (hu : isVal u = true) (hs : Steps k h (.throw u) h' v) (hv : isVal v = true) : False := by
  cases hs with
  | refl => simp [isVal] at hv
  | next st _ =>
    cases st with
    | throwC st' => exact absurd st' (value_no_step hu)

/-- **Fresh allocation step soundness**: any normal evaluation of a term with
`isFreshAlloc t = true` extends the heap as a prefix (`h.IsPrefix h'`) and
returns a value whose allocated locations all lie at or above `h.length`. -/
theorem isFreshAlloc_steps {k : Nat} {h h' : Heap} {t v : Tm}
    (hh : ∀ (l : Nat) u, h[l]? = some u → isVal u = true)
    (ht : isFreshAlloc t = true) (hs : Steps k h t h' v) (hv : isVal v = true) :
    h.IsPrefix h' ∧ FreshValueAt h.length v := by
  induction hs with
  | @refl h_r t_r =>
    cases t_r <;> simp [isFreshAlloc, isVal] at ht hv
  | @next m h₀ h₁ h₂ t₀ t₁ t₂ st hrest ih =>
    have hro := isFreshAlloc_isReadOnlyOrAlloc ht
    obtain ⟨hpre01, hro1, hh1⟩ := isReadOnlyOrAlloc_step st hh hro
    cases st with
    | @makeArg c ns inits i _ _ a a' hi _ _ =>
      cases c with
      | absent =>
        have ht1 : isFreshAlloc (.makeAt .absent ns (inits.set i a')) = true := by
          simpa [isFreshAlloc, isReadOnlyOrAlloc] using hro1
        obtain ⟨hpre12, hfr⟩ := ih hh1 ht1 hv
        exact ⟨hpre01.trans hpre12, hfr.mono hpre01.length_le⟩
      | _ => simp [isFreshAlloc] at ht
    | @makeFields c ns vs _ _ _ =>
      cases c with
      | absent =>
        cases hrest with
        | refl =>
          exact ⟨hpre01, fun k l hm => slots_ge _ ns k l hm⟩
        | next st' _ => exact absurd st' (value_no_step rfl)
      | _ => simp [isFreshAlloc] at ht
    | arrArg _ _ _ =>
      obtain ⟨hpre12, hfr⟩ := ih hh1 (by simpa [isFreshAlloc, isReadOnlyOrAlloc] using hro1) hv
      exact ⟨hpre01.trans hpre12, hfr.mono hpre01.length_le⟩
    | arrSpread _ _ _ =>
      obtain ⟨hpre12, hfr⟩ := ih hh1 (by simpa [isFreshAlloc, isReadOnlyOrAlloc] using hro1) hv
      exact ⟨hpre01.trans hpre12, hfr.mono hpre01.length_le⟩
    | @arrAlloc vs _ _ _ =>
      cases hrest with
      | refl =>
        exact ⟨hpre01, fun l hm => elemSlots_ge _ vs.length hm⟩
      | next st' _ => exact absurd st' (value_no_step rfl)
    | arrAllocThrow _ _ =>
      exact (throw_val_never_val (by simp [thrownError, isVal]) hrest hv).elim
    | letC _ =>
      simp only [isFreshAlloc, Bool.and_eq_true] at ht
      simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at hro1
      obtain ⟨hpre12, hfr⟩ := ih hh1 (by simp [isFreshAlloc, hro1.1, ht.2]) hv
      exact ⟨hpre01.trans hpre12, hfr.mono hpre01.length_le⟩
    | letV hva =>
      simp only [isFreshAlloc, Bool.and_eq_true] at ht
      obtain ⟨hpre12, hfr⟩ := ih hh1 (isFreshAlloc_subst (isReadOnlyOrAlloc_of_isVal hva) 0 ht.2) hv
      exact ⟨hpre01.trans hpre12, hfr.mono hpre01.length_le⟩
    | _ => simp [isFreshAlloc] at ht

/-- A fresh object's own field locations and spine slot all lie at or above `b`. -/
theorem freshValueAt_field_ge {b : Nat} {v : Tm} (hf : FreshValueAt b v)
    {k : PropKey} {l : Nat} (hl : (Footprints.fieldsOf v).lookup k = some l) : b ≤ l := by
  cases v with
  | objAt fs c _ =>
    cases c with
    | absent => exact hf k l (Footprints.lookup_mem_pair hl)
    | _ => cases hf
  | _ => simp [Footprints.fieldsOf] at hl

theorem freshValueAt_fieldLocs_ge {b : Nat} {v : Tm} (hf : FreshValueAt b v)
    {l : Nat} (hl : (Footprints.fieldLocs v).contains l = true) : b ≤ l := by
  cases v with
  | objAt fs c _ =>
    cases c with
    | absent =>
      simp only [Footprints.fieldLocs, Footprints.fieldsOf, List.contains_iff_mem,
        List.mem_map, List.mem_filter] at hl
      obtain ⟨⟨k, l'⟩, ⟨hmem, _⟩, rfl⟩ := hl
      exact hf k l' hmem
    | _ => cases hf
  | _ => simp [Footprints.fieldLocs, Footprints.fieldsOf] at hl

theorem freshValueAt_elementsOf_ge {b : Nat} {v : Tm} (hf : FreshValueAt b v)
    {l : Nat} (hl : HeapKnowledge.elementsOf v = some l) : b ≤ l := by
  cases v with
  | objAt fs c _ =>
    cases c with
    | absent =>
      simp only [HeapKnowledge.elementsOf] at hl
      cases hlu : fs.lookup arraySpineKey with
      | some s' =>
        rw [hlu] at hl; cases hl
        exact hf arraySpineKey l (Footprints.lookup_mem_pair hlu)
      | none => rw [hlu] at hl; cases hl
    | _ => cases hf
  | _ => simp [HeapKnowledge.elementsOf] at hl

end Verification.CallbackDemands
