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

end Verification.CallbackDemands
