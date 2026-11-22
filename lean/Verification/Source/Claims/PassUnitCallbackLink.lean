import Verification.Semantics.CallbackDemands
import Verification.Source.Claims.PassUnitFile

/-! # Support-parametric callback demands: demanded interfaces and module linking

Generalizes the module-level linking theorem (`PassUnitRealize.approx_meets` /
`PassUnitFile.passFile_safe`) to modules containing internal higher-order
functions with inferred callback demands (`CallbackDemand`), with zero client
trust `Θ_C`:

- `CallbackPreserves`: step-indexed, world-monotone predicate stating that a
  callback argument `cb` of type `cbTy` preserves `SupportedAt S ρ₀ h₀` across
  every normal-returning invocation in any future reachable world/heap.
- `DemandsMet`: every callback demand `d ∈ ds` is met by the actual callback
  argument at `callEnv r args d.param`.
- `DemandedMeaning`: identical to `meaning G F k W v` when `ds = []`
  (`demandedMeaning_nil`), and otherwise requires `DemandsMet` as an additional
  precondition on each arrow invocation (`DemandedPromiseWith`).
- `DemandedEnvOk` / `DemandedRowSpec` / `closure_meets_below_demanded` /
  `approx_meets_demanded`: step-indexed unfolding induction proving that every
  closed unit meets its demanded interface (`DemandedMeaning`) at every budget
  and every world above `W₀`.
- **`approx_meets_exported`** (headline linking corollary): every exported /
  non-demanded unit (`dem x = []`, e.g. `sumAndTrace`, `collectDirect`,
  `collectAdapted`) unconditionally meets its plain TypeScript interface
  `meaning G (iface x) m W (approx code n x)` — to the exact same extent as
  `PassUnitFile.passFile_safe` in the original verifier. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean Verification ProgramTyping RequestJson SourceElaboration ControlFlow
open PositiveGraphs PositiveRules LabelStore HeapObservations CallbackDemands

section DemandedSemantics
variable {ι : Type}

/-! ## Callback preservation and demanded arrow meanings -/

/-- **A callback preserves a support** (`CallbackPreserves`): at every future
reachable world `(k, V)` extending `trunc k hk W` with `HeapOk k V h₁` and
`h₀.length ≤ h₁.length`, whenever `cb` is invoked at a signature `p` of `cbTy`
with receiver/arguments meeting `p`'s contract and terminates normally in
`j < k` steps at `(h₂, v)`, the heap transition satisfies
`SupportedAt S ρ₀ h₀ h₁ h₂`. -/
def CallbackPreserves (G : NormalGraph ι) (cbTy : Ty ι)
    (S : Footprints.Footprint) (ρ₀ : Env) (h₀ : Heap) (n : Nat) (W : WorldT n) (cb : Tm) : Prop :=
  ∀ (L : List (CallEffects.Arrow (Ty ι))) (Sg : List (CallEffects.RestArrow (Ty ι))),
    Represents G cbTy (.arrs L Sg) →
    ∀ p ∈ L,
      ∀ (k : Nat) (hk : k ≤ n) (V : WorldT k), WExt (trunc k hk W) V → WorldAdm V →
        ∀ (h₁ : Heap), HeapOk k V h₁ → h₀.length ≤ h₁.length →
          ∀ (r_cb : Tm), isVal r_cb = true → meaning G p.receiver k V r_cb → RefsOk V r_cb →
          ∀ (args_cb : List Tm), CallArguments.Values args_cb → (∀ a ∈ args_cb, RefsOk V a) →
            ArgsShort (p.arguments.map (meaning G)) k V args_cb →
            p.effect.Requires r_cb args_cb h₁ →
            ∀ (j : Nat) (h₂ : Heap) (v : Tm), j < k →
              Steps j h₁ (.invoke cb r_cb args_cb) h₂ v → isVal v = true →
              SupportedAt S ρ₀ h₀ h₁ h₂

theorem CallbackPreserves.down {G : NormalGraph ι} {cbTy : Ty ι} {S : Footprints.Footprint}
    {ρ₀ : Env} {h₀ : Heap} {n m : Nat} (hmn : m ≤ n) {W : WorldT n} {U : WorldT m}
    (hx : WExt (trunc m hmn W) U) {cb : Tm}
    (h : CallbackPreserves G cbTy S ρ₀ h₀ n W cb) :
    CallbackPreserves G cbTy S ρ₀ h₀ m U cb := by
  intro L Sg hrep p hp k hk V hy hV h₁ hh₁ hlen r_cb hr_v hr_m hr_r args_cb ha_v ha_r ha_s hreq j h₂ v hj hst hv
  refine h L Sg hrep p hp k (Nat.le_trans hk hmn) V ?_ hV h₁ hh₁ hlen r_cb hr_v hr_m hr_r args_cb ha_v ha_r ha_s hreq j h₂ v hj hst hv
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc hk hx) hy

theorem CallbackPreserves.mono {G : NormalGraph ι} {cbTy : Ty ι} {S : Footprints.Footprint}
    {ρ₀ : Env} {h₀ : Heap} {n : Nat} {W W' : WorldT n} (hx : WExt W W') {cb : Tm}
    (h : CallbackPreserves G cbTy S ρ₀ h₀ n W cb) :
    CallbackPreserves G cbTy S ρ₀ h₀ n W' cb :=
  h.down (Nat.le_refl n) (by simpa only [trunc_id] using hx)

theorem CallbackPreserves.of_sub {G : NormalGraph ι} {cbTy : Ty ι} {S T : Footprints.Footprint}
    {ρ₀ : Env} {h₀ : Heap} {n : Nat} {W : WorldT n} {cb : Tm}
    (h : CallbackPreserves G cbTy S ρ₀ h₀ n W cb) (hsub : ∀ e ∈ T, e ∈ S) :
    CallbackPreserves G cbTy T ρ₀ h₀ n W cb := by
  intro L Sg hrep p hp k hk V hy hV h₁ hh₁ hlen r_cb hr_v hr_m hr_r args_cb ha_v ha_r ha_s hreq j h₂ v hj hst hv
  exact supportedAt_sub (h L Sg hrep p hp k hk V hy hV h₁ hh₁ hlen r_cb hr_v hr_m hr_r args_cb ha_v ha_r ha_s hreq j h₂ v hj hst hv) hsub

/-- Deterministic extraction of a normal postcondition from `SafePostExcV`. -/
theorem safePostExcV_normal_post {Ξ R : Fam} {Q : WPost} {E : WExcV} :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t : Tm} {j : Nat} {h' : Heap} {v : Tm},
      j < n → Steps j h t h' v → isVal v = true → SafePostExcV Ξ R Q E n W h t →
      ∃ (m : Nat) (U : WorldT m), Q m U h' v := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ hj; omega
  | succ n ih =>
    intro W h t j h' v hj hst hv hs
    obtain ⟨-, hs⟩ := hs
    cases hst with
    | refl =>
      rcases hs with (⟨_, _, hq⟩ | ⟨_, hth, _, _, _⟩) | ⟨_, _, _, _, _, st, _, _⟩
      · exact ⟨n + 1, W, hq⟩
      · exact absurd hv (by simp [raises_not_val hth])
      · exact absurd st (value_no_step hv)
    | next st₁ hrest =>
      rcases hs with (⟨hv0, _, _⟩ | ⟨_, hth, _, _, _⟩) | ⟨U, h₁, t₁, _, _, st₂, _, hs₁⟩
      · exact absurd st₁ (value_no_step hv0)
      · exact absurd st₁ (raises_no_step hth)
      · obtain ⟨rfl, rfl⟩ := Step_det st₁ st₂
        exact ih (Nat.lt_of_succ_lt_succ hj) hrest hv hs₁

/-- **Every demand of `ds` is met** at a call `(r, args)` against signature `p`
in `(G, n, W, h₀)`. Empty demand list holds vacuously (`demandsMet_nil`). -/
def DemandsMet (G : NormalGraph ι) (p : CallEffects.Arrow (Ty ι))
    (ds : List CallbackDemand) (r : Tm) (args : List Tm) (h₀ : Heap) (n : Nat) (W : WorldT n) : Prop :=
  ∀ d ∈ ds, ∃ cbTy, 1 ≤ d.param ∧ p.arguments[d.param - 1]? = some cbTy ∧
    CallbackPreserves G cbTy d.support (CallEffects.callEnv r args) h₀ n W (CallEffects.callEnv r args d.param)

theorem demandsMet_nil (G : NormalGraph ι) (p : CallEffects.Arrow (Ty ι))
    (r : Tm) (args : List Tm) (h₀ : Heap) (n : Nat) (W : WorldT n) :
    DemandsMet G p [] r args h₀ n W :=
  fun _ hd => by cases hd

theorem DemandsMet.down {G : NormalGraph ι} {p : CallEffects.Arrow (Ty ι)}
    {ds : List CallbackDemand} {r : Tm} {args : List Tm} {h₀ : Heap}
    {n m : Nat} (hmn : m ≤ n) {W : WorldT n} {U : WorldT m} (hx : WExt (trunc m hmn W) U)
    (h : DemandsMet G p ds r args h₀ n W) :
    DemandsMet G p ds r args h₀ m U := by
  intro d hd
  obtain ⟨cbTy, hge, harg, hcb⟩ := h d hd
  exact ⟨cbTy, hge, harg, hcb.down hmn hx⟩

/-- **Demand-guarded fixed-arity callable contract**: identical to
`CallEffects.PromiseWith`, with the additional precondition
`DemandsMet G p ds r args heap j U` on every invocation. -/
def DemandedPromiseWith (G : NormalGraph ι) (p : CallEffects.Arrow (Ty ι))
    (ds : List CallbackDemand) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ r, isVal r = true → meaning G p.receiver j U r → RefsOk U r →
      ∀ args, CallArguments.Values args → (∀ a ∈ args, RefsOk U a) →
        ArgsShort (p.arguments.map (meaning G)) j U args →
        p.effect.Requires r args heap →
        DemandsMet G p ds r args heap j U →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafePostExcV (excOf G) (p.effect.result (meaning G p.result) (p.effect.promised args))
            (p.effect.schema.exitPostW .normal r args U heap)
            (p.effect.schema.exitPostW .exceptional r args U heap) j U heap result

/-- **Demand-guarded variadic callable contract**: identical to
`CallEffects.PromiseWith` on `s.fixed` with `ArgsRest`, plus `DemandsMet` on
the fixed prefix actuals. -/
def DemandedRestPromiseWith (G : NormalGraph ι) (s : CallEffects.RestArrow (Ty ι))
    (ds : List CallbackDemand) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ r, isVal r = true → meaning G s.receiver j U r → RefsOk U r →
      ∀ args, CallArguments.Values args → (∀ a ∈ args, RefsOk U a) →
        ArgsRest (s.arguments.1.map (meaning G)) (argMeaning G s.arguments.2) j U args →
        s.fixed.effect.Requires r args heap →
        DemandsMet G s.fixed ds r (args.take s.arguments.1.length) heap j U →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafePostExcV (excOf G) (s.fixed.effect.result (meaning G s.result) (s.fixed.effect.promised args))
            (s.fixed.effect.schema.exitPostW .normal r args U heap)
            (s.fixed.effect.schema.exitPostW .exceptional r args U heap) j U heap result

theorem DemandedPromiseWith.down {G : NormalGraph ι} {p : CallEffects.Arrow (Ty ι)}
    {ds : List CallbackDemand} {k j : Nat} (hjk : j ≤ k) {W : WorldT k} {U : WorldT j}
    (hx : WExt (trunc j hjk W) U) {v : Val}
    (h : DemandedPromiseWith G p ds k W v) : DemandedPromiseWith G p ds j U v := by
  intro i hi V hy hu heap hh hvr r hrv hrm hrr args hav har has hreq hdem
  refine h i (by omega) V ?_ hu heap hh hvr r hrv hrm hrr args hav har has hreq hdem
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_of_lt hi) hx) hy

theorem DemandedRestPromiseWith.down {G : NormalGraph ι} {s : CallEffects.RestArrow (Ty ι)}
    {ds : List CallbackDemand} {k j : Nat} (hjk : j ≤ k) {W : WorldT k} {U : WorldT j}
    (hx : WExt (trunc j hjk W) U) {v : Val}
    (h : DemandedRestPromiseWith G s ds k W v) : DemandedRestPromiseWith G s ds j U v := by
  intro i hi V hy hu heap hh hvr r hrv hrm hrr args hav har has hreq hdem
  refine h i (by omega) V ?_ hu heap hh hvr r hrv hrm hrr args hav har has hreq hdem
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_of_lt hi) hx) hy

/-- **Demand-guarded meaning of a value at type `F`**:
- When `ds = []`, this IS the ordinary semantic meaning `meaning G F k W v`.
- When `ds ≠ []`, `v` is a closed value that, for every arrow clause
  representing `F`, is invocable and satisfies `DemandedPromiseWith` (and
  `DemandedRestPromiseWith`). -/
def DemandedMeaning (G : NormalGraph ι) (F : Ty ι) (ds : List CallbackDemand)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  if ds = [] then meaning G F k W v
  else isVal v = true ∧ Scoped 0 v ∧
    ∀ L Sg, Represents G F (.arrs L Sg) →
      Invocable v ∧
      (∀ p ∈ L, DemandedPromiseWith G p ds k W v) ∧
      (∀ s ∈ Sg, DemandedRestPromiseWith G s ds k W v)

/-- **Empty demands collapse identically to ordinary `meaning`** (proved). -/
theorem demandedMeaning_nil (G : NormalGraph ι) (F : Ty ι) (k : Nat) (W : WorldT k) (v : Val) :
    DemandedMeaning G F [] k W v ↔ meaning G F k W v := by
  simp [DemandedMeaning]

/-- **Ordinary `meaning` implies `DemandedMeaning` for any demand list** (proved). -/
theorem demandedMeaning_of_meaning {G : NormalGraph ι} {F : Ty ι} {ds : List CallbackDemand}
    {k : Nat} {W : WorldT k} {v : Val} (h : meaning G F k W v) :
    DemandedMeaning G F ds k W v := by
  unfold DemandedMeaning
  split
  · exact h
  · refine ⟨(meaning_value h).1, (meaning_value h).2, fun L Sg hrep => ?_⟩
    have hraw := represents_raw hrep k W v h
    refine ⟨hraw.1.1, fun p hp => ?_, fun s hs => ?_⟩
    · intro j hj U hx hu heap hh hvr r hrv hrm hrr args hav har has hreq _
      exact hraw.1.2 _ (List.mem_map_of_mem hp) j hj U hx hu heap hh hvr r hrv hrm hrr args hav har has hreq
    · intro j hj U hx hu heap hh hvr r hrv hrm hrr args hav har has hreq _
      exact hraw.2.2 _ (List.mem_map_of_mem hs) j hj U hx hu heap hh hvr r hrv hrm hrr args hav har has hreq

theorem DemandedMeaning.down {G : NormalGraph ι} {F : Ty ι} {ds : List CallbackDemand}
    {k j : Nat} (hjk : j ≤ k) {W : WorldT k} {U : WorldT j} (hx : WExt (trunc j hjk W) U) {v : Val}
    (h : DemandedMeaning G F ds k W v) : DemandedMeaning G F ds j U v := by
  by_cases hnil : ds = []
  · simp only [DemandedMeaning, hnil, ↓reduceIte] at h ⊢
    exact (meaning_adm G F).transfer h j hjk U hx
  · simp only [DemandedMeaning, hnil, ↓reduceIte] at h ⊢
    refine ⟨h.1, h.2.1, fun L Sg hrep => ?_⟩
    obtain ⟨hinv, hL, hSg⟩ := h.2.2 L Sg hrep
    exact ⟨hinv, fun p hp => (hL p hp).down hjk hx, fun s hs => (hSg s hs).down hjk hx⟩

theorem DemandedMeaning.mono {G : NormalGraph ι} {F : Ty ι} {ds : List CallbackDemand}
    {k : Nat} {W W' : WorldT k} (hx : WExt W W') {v : Val}
    (h : DemandedMeaning G F ds k W v) : DemandedMeaning G F ds k W' v :=
  h.down (Nat.le_refl k) (by simpa only [trunc_id] using hx)

theorem DemandedMeaning.value {G : NormalGraph ι} {F : Ty ι} {ds : List CallbackDemand}
    {k : Nat} {W : WorldT k} {v : Val} (h : DemandedMeaning G F ds k W v) :
    isVal v = true ∧ Scoped 0 v := by
  unfold DemandedMeaning at h
  split at h
  · exact meaning_value h
  · exact ⟨h.1, h.2.1⟩

/-! ## Demand-guarded capture environments and module rows -/

/-- **Demand-guarded `EnvOk`**: every slot `i` has a closed value, and for every
typed slot `Γ[i]? = some A`, its value satisfies `DemandedMeaning G A (demAt i)`.
When `demAt i = []`, this is identically `meaning G A n W (ρ i)`. -/
def DemandedEnvOk (G : NormalGraph ι) (Γ : List (Ty ι)) (demAt : Nat → List CallbackDemand)
    (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  (∀ i, Scoped 0 (ρ i)) ∧ ∀ i A, Γ[i]? = some A → DemandedMeaning G A (demAt i) n W (ρ i)

theorem demandedEnvOk_nil_iff {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n} :
    DemandedEnvOk G Γ (fun _ => []) ρ n W ↔ EnvOk G Γ ρ n W := by
  simp [DemandedEnvOk, EnvOk, demandedMeaning_nil]

theorem DemandedEnvOk.of_envOk {G : NormalGraph ι} {Γ : List (Ty ι)} {demAt : Nat → List CallbackDemand}
    {ρ : Env} {n : Nat} {W : WorldT n} (he : EnvOk G Γ ρ n W) :
    DemandedEnvOk G Γ demAt ρ n W :=
  ⟨he.1, fun i A hA => demandedMeaning_of_meaning (he.2 i A hA)⟩

theorem DemandedEnvOk.down {G : NormalGraph ι} {Γ : List (Ty ι)} {demAt : Nat → List CallbackDemand}
    {ρ : Env} {n m : Nat} (hmn : m ≤ n) {W : WorldT n} {U : WorldT m} (hx : WExt (trunc m hmn W) U)
    (he : DemandedEnvOk G Γ demAt ρ n W) :
    DemandedEnvOk G Γ demAt ρ m U :=
  ⟨he.1, fun i A hA => (he.2 i A hA).down hmn hx⟩

theorem DemandedEnvOk.withSelf {G : NormalGraph ι} {Cs : List (Ty ι)} {demAt : Nat → List CallbackDemand}
    {vs : List Tm} {self : Tm} {n : Nat} {W : WorldT n}
    (hvs : DemandedEnvOk G Cs demAt (envOf vs .nul) n W) (hlen : Cs.length ≤ vs.length)
    (hself : Scoped 0 self) :
    DemandedEnvOk G Cs demAt (envOf (vs ++ [self]) .nul) n W := by
  refine ⟨fun i => ?_, fun i A hA => ?_⟩
  · by_cases hi : i < vs.length
    · simpa [envOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi] using hvs.1 i
    · by_cases hi' : i = vs.length
      · subst hi'
        simpa [envOf, List.getD_eq_getElem?_getD] using hself
      · have hgt : (vs ++ [self]).length ≤ i := by simp; omega
        simp [envOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt, Scoped]
  · have hi : i < Cs.length := (List.getElem?_eq_some_iff.mp hA).1
    have hlt : i < vs.length := Nat.lt_of_lt_of_le hi hlen
    have heq : envOf (vs ++ [self]) .nul i = envOf vs .nul i := by
      simp [envOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [heq]
    exact hvs.2 i A hA

/-- Demand assignment for a call frame `r :: parameters arity args ++ captures`:
receiver and parameters have no sibling demands (`[]`), while capture slot
`1 + arity + k` inherits `capDem k`. -/
def frameDem (arity : Nat) (capDem : Nat → List CallbackDemand) (i : Nat) : List CallbackDemand :=
  if i < 1 + arity then [] else capDem (i - (1 + arity))

theorem frame_demandedEnvOk {G : NormalGraph ι} {arity : Nat} {row : CallEffects.Arrow (Ty ι)}
    {Cs : List (Ty ι)} {capDem : Nat → List CallbackDemand} {vs : List Tm}
    (har : arity ≤ row.arguments.length) {j : Nat} {U : WorldT j}
    (hvs : DemandedEnvOk G Cs capDem (envOf vs .nul) j U)
    {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args) :
    DemandedEnvOk G (codeFrame arity row Cs none) (frameDem arity capDem)
      (envOf (r :: CallArguments.parameters arity args ++ vs) .nul) j U := by
  have hparamsLen : (CallArguments.parameters arity args).length = arity :=
    CallEffects.Effect.parameters_length arity args
  have hbase : EnvOk G (codeFrame arity row [] none) (envOf (r :: CallArguments.parameters arity args ++ []) .nul) j U :=
    frame_envOk har ⟨fun _ => by simp [envOf, Scoped], fun _ _ h => by simp at h⟩
      (Nat.le_refl j) (by rw [trunc_id]; exact WExt_refl U) hr ha
  refine ⟨fun i => ?_, fun i A hA => ?_⟩
  · cases i with
    | zero => exact (meaning_value hr).2
    | succ k =>
      by_cases hk : k < arity
      · have heq : envOf (r :: CallArguments.parameters arity args ++ vs) .nul (k + 1) =
            envOf (r :: CallArguments.parameters arity args ++ []) .nul (k + 1) := by
          simp only [envOf, List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
        rw [heq]
        exact hbase.1 (k + 1)
      · have heq : envOf (r :: CallArguments.parameters arity args ++ vs) .nul (k + 1) =
            envOf vs .nul (k - arity) := by
          simp only [envOf, List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_right (by omega), hparamsLen]
        rw [heq]
        exact hvs.1 (k - arity)
  · cases i with
    | zero =>
      simp only [codeFrame, bodyFrame, List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hA
      subst hA
      have hframe : frameDem arity capDem 0 = [] := by simp [frameDem]
      rw [hframe, demandedMeaning_nil]
      exact hr
    | succ k =>
      by_cases hk : k < arity
      · have hframe : frameDem arity capDem (k + 1) = [] := by simp [frameDem]; omega
        rw [hframe, demandedMeaning_nil]
        have hlt : k < (row.arguments.take arity).length := by simp; omega
        have hA' : (codeFrame arity row [] none)[k + 1]? = some A := by
          simp only [codeFrame, bodyFrame, List.cons_append, List.getElem?_cons_succ, List.append_nil] at hA ⊢
          rwa [List.getElem?_append_left hlt] at hA
        have heq : envOf (r :: CallArguments.parameters arity args ++ vs) .nul (k + 1) =
            envOf (r :: CallArguments.parameters arity args ++ []) .nul (k + 1) := by
          simp only [envOf, List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
        rw [heq]
        exact hbase.2 (k + 1) A hA'
      · have hframe : frameDem arity capDem (k + 1) = capDem (k - arity) := by
          simp only [frameDem, show ¬ (k + 1 < 1 + arity) by omega, ↓reduceIte]
          congr 1; omega
        rw [hframe]
        have htakeLen : (row.arguments.take arity).length = arity := by simp; omega
        simp only [codeFrame, bodyFrame, List.cons_append, List.getElem?_cons_succ] at hA
        rw [List.getElem?_append_right (by omega), htakeLen] at hA
        have heq : envOf (r :: CallArguments.parameters arity args ++ vs) .nul (k + 1) =
            envOf vs .nul (k - arity) := by
          simp only [envOf, List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_right (by omega), hparamsLen]
        rw [heq]
        exact hvs.2 (k - arity) A hA

/-- **A module function's demand-guarded row specification** (`DemandedRowSpec`):
identical to `RowSpec`, with captures typed under `DemandedEnvOk` (using
`capDem`) and entry calls required to meet `ds` (`DemandsMet`). -/
def DemandedRowSpec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (capDem : Nat → List CallbackDemand) (row : CallEffects.Arrow (Ty ι))
    (sep : HeapSeparation.Separation) (ds : List CallbackDemand) : Prop :=
  arity ≤ row.arguments.length ∧ row.effect.belowRow arity = true ∧
  ∀ n W h L comp,
    DemandedEnvOk G (codeFrame arity row Cs none) (frameDem arity capDem) (envOf L .nul) n W →
    WorldAdm W → HeapOk n W h → RefsOk W (.goto E K start L .nul comp) → CallArguments.Values L →
    PreAt row.effect (none : Option (Ty ι)) L h → HeapSeparation.Holds sep (envOf L .nul) →
    ∀ r args, FrameValues arity (none : Option (Ty ι)) L r args →
      DemandsMet G row ds r args h n W →
      HeapObservations.SafePostExcV (excOf G)
        (row.effect.result (meaning G row.result) (framePromised row.effect (frameOffset (none : Option (Ty ι))) L))
        (row.effect.schema.exitPostW .normal r args W h) (row.effect.schema.exitPostW .exceptional r args W h)
        n W h (.goto E K start L .nul comp)

/-- Any unconditional `RowSpec` (with no demanded siblings in its captures) is a
`DemandedRowSpec` for any `ds` (proved). -/
theorem demandedRowSpec_of_rowSpec {G : NormalGraph ι} {arity E K start Cs row sep ds}
    (h : RowSpec G arity E K start Cs row sep) :
    DemandedRowSpec G arity E K start Cs (fun _ => []) row sep ds := by
  refine ⟨h.1, h.2.1, fun n W heap L comp he hw hh hgo hv hpre hsep r args hf _ => ?_⟩
  have hnil : frameDem arity (fun _ => []) = fun _ => [] := by
    funext i; unfold frameDem; split <;> rfl
  rw [hnil, demandedEnvOk_nil_iff] at he
  exact h.2.2 n W heap L comp he hw hh hgo hv hpre hsep r args hf

/-- Invoking a demand-guarded module row's code from a frame at the call's level. -/
theorem demandedRow_invoke_at {G : NormalGraph ι} {arity E K start Cs capDem row vs sep ds} {comp : ComponentTag}
    (hs : DemandedRowSpec G arity E K start Cs capDem row sep ds) {j : Nat} {U : WorldT j}
    (hvs : DemandedEnvOk G Cs capDem (envOf vs .nul) j U) (hvalues : CallArguments.Values vs)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args)
    (hq : ∀ F ∈ row.effect.pre, F.HoldsAt ⟨CallEffects.callEnv r args, heap⟩ (CallEffects.callEnv r args) heap)
    (hsep : HeapSeparation.Holds sep (envOf (r :: CallArguments.parameters arity args ++ vs) .nul))
    (hgo : RefsOk U (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul comp))
    (hdem : DemandsMet G row ds r args heap j U) :
    HeapObservations.SafePostExcV (excOf G) (row.effect.result (meaning G row.result) (row.effect.promised args))
      (row.effect.schema.exitPostW .normal r args U heap) (row.effect.schema.exitPostW .exceptional r args U heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul comp) := by
  have hb := CallEffects.Effect.belowRow_entry hs.2.1
  have hsafe := hs.2.2 j U heap _ comp (frame_demandedEnvOk hs.1 hvs hr ha) hu hh hgo (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (meaning_value hr).1
    · rcases List.mem_append.mp hv with hv | hv
      · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl
          (ArgsT_values (fun A hA => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hA); exact meaning_valOnly G a) ha.2.1) v hv
      · exact hvalues v hv)
    (fun _ F hF => (CallEffects.Effect.pre_frame hb (F := F) hF r args vs .nul heap).mp (hq F hF))
    hsep r args ⟨[], vs, rfl, rfl⟩ hdem
  have hp := framePromised_params hb [r] args vs
  simp only [List.length_singleton, List.singleton_append] at hp
  have hp' : framePromised row.effect 1 (r :: CallArguments.parameters arity args ++ vs) =
      row.effect.promised args := hp
  rw [show frameOffset (none : Option (Ty ι)) = 1 from rfl, hp'] at hsafe
  exact hsafe

/-- Demand-guarded offers of a module function's code. -/
def DemandedRowOffers (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (capDem : Nat → List CallbackDemand)
    (L : List (CallEffects.Arrow (Ty ι))) (S : List (CallEffects.RestArrow (Ty ι)))
    (sep : HeapSeparation.Separation) (ds : List CallbackDemand) : Prop :=
  ∀ p ∈ offerRows L S, DemandedRowSpec G arity E K start Cs capDem p sep ds

/-- **A closure meets its demand-guarded arrow from captures meeting theirs
below the budget** (proved): exact generalization of `closure_meets_below`.
When `ds = []`, this yields ordinary `meaning G F n W (.objAt ...)`. -/
theorem closure_meets_below_demanded {G : NormalGraph ι} {arity E K start Cs capDem vs} {kind : Invoke}
    {comp : ComponentTag} {F : Ty ι} {L : List (CallEffects.Arrow (Ty ι))}
    {S : List (CallEffects.RestArrow (Ty ι))} (fs : List (PropKey × Nat)) {oid : Nat}
    {sep : HeapSeparation.Separation} {ds : List CallbackDemand}
    (hr : Represents G F (.arrs L S)) (hk : KindOffers G kind L S)
    (ho : DemandedRowOffers G arity E K start Cs capDem L S sep ds)
    (hlen : Cs.length ≤ vs.length) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs)
    (hsep : ∀ r args more, HeapSeparation.Holds sep (envOf (r :: CallArguments.parameters arity args ++ (vs ++ more)) .nul))
    {n : Nat} (W : WorldT n)
    (hcaps : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      DemandedEnvOk G Cs capDem (envOf vs .nul) j U) :
    DemandedMeaning G F ds n W (.objAt fs (.graph arity E K start vs kind false comp) oid) := by
  obtain ⟨hkind, hrows⟩ := hk
  have hbL : ∀ p ∈ L, KindBinds G kind p.receiver :=
    fun p hp => kindOffers_binds (hrows p (List.mem_append_left _ hp))
  have hbS : ∀ s ∈ S, KindBinds G kind s.receiver :=
    fun s hs => kindOffers_binds (hrows _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)))
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind false comp) oid) := by simpa [Scoped] using hsc
  have hinv : Invocable (.objAt fs (.graph arity E K start vs kind false comp) oid) :=
    ⟨fs, _, oid, rfl, callable_of_kind hkind, hself⟩
  have hfixed : ∀ p ∈ L, DemandedPromiseWith G p ds n W (.objAt fs (.graph arity E K start vs kind false comp) oid) := by
    intro p hp j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq hdem
    have henv := (hcaps j hj U hx).withSelf hlen hself
    exact ⟨_, .graph hrv hvals (hbL p hp j U r hrr),
      demandedRow_invoke_at (ho p (List.mem_append_left _ hp)) henv
        (Values.withSelf hvalues rfl) hu hh hrr ha (fun F hF => hreq.2 F hF) (hsep r args _)
        (goto_entry_refs (graph_code_refs hvr).1 (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact (graph_code_refs hvr).2 a ha
          · rw [List.mem_singleton.mp ha]; exact hvr) hrref har) hdem⟩
  have hrest : ∀ s ∈ S, DemandedRestPromiseWith G s ds n W (.objAt fs (.graph arity E K start vs kind false comp) oid) := by
    intro s hsm j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq hdem
    have hspec := ho _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hsm, rfl⟩))
    have hle : arity ≤ s.arguments.1.length := hspec.1
    have hrow : s.fixed.effect.belowRow arity = true := hspec.2.1
    have hbelow := CallEffects.Effect.belowRow_entry hrow
    have henv := (hcaps j hj U hx).withSelf hlen hself
    have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
        CallArguments.parameters arity args := by
      rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
        Nat.min_eq_left hle, CallArguments.parameters_take]
    have hsafe := demandedRow_invoke_at (comp := comp) hspec henv (Values.withSelf hvalues rfl) hu hh
      (args := args.take s.arguments.1.length) hrr
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using ha.1)
      (fun F hF => (CallEffects.Effect.pre_take hbelow hle (F := F) hF r args heap).mpr (hreq.2 F hF))
      (by rw [hp]; exact hsep r args _)
      (goto_entry_refs (graph_code_refs hvr).1 (fun a ha => by
        rcases List.mem_append.mp ha with ha | ha
        · exact (graph_code_refs hvr).2 a ha
        · rw [List.mem_singleton.mp ha]; exact hvr) hrref (fun a ha => har a (List.mem_of_mem_take ha)))
      hdem
    have hpr : s.fixed.effect.promised (args.take s.arguments.1.length) = s.fixed.effect.promised args :=
      CallEffects.Effect.promised_take hbelow hle args
    rw [hp, hpr] at hsafe
    exact ⟨_, .graph hrv hvals (hbS s hsm j U r hrr), CallEffects.Effect.safe_exits_take hrow hle hu hh hsafe⟩
  unfold DemandedMeaning
  split
  · rename_i hnil
    subst hnil
    apply (represents_back hr n W _)
    refine ⟨⟨hinv, ?_⟩, ⟨hinv, ?_⟩⟩
    · intro q hq j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hfixed p hp j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq (demandsMet_nil G p r args heap j U)
    · intro q hq j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq
      obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
      exact hrest s hsm j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq (demandsMet_nil G s.fixed r (args.take s.arguments.1.length) heap j U)
  · refine ⟨rfl, hself, fun L' S' hr' => ?_⟩
    have heq : ([.arrs L S] : List (PositiveNormalization.Clause (Ty ι))) = [.arrs L' S'] :=
      hr.symm.trans hr'
    injection heq with hcl
    injection hcl with hL hS
    subst hL; subst hS
    exact ⟨hinv, hfixed, hrest⟩

/-! ## Module-level step-indexed linking with callback demands -/

/-- Demand list for capture slot `k` of a module function `c`, reading `dem d`
for every linked sibling `Slot.linked d` and `[]` for every outside slot. -/
def slotDem {ι U : Type} (c : ModuleCode ι U) (dem : U → List CallbackDemand) (k : Nat) :
    List CallbackDemand :=
  match c.slots[k]? with
  | some (.linked d) => dem d
  | _ => []

/-- **What a unit of a callback-demand module must meet to be realized**
(`DemandedRealizes`): exact generalization of `Realizes` (`PassUnitRealize.lean`)
where each unit `u` carries a demand list `dem u` (`[]` for every exported /
public function), its code offers `DemandedRowOffers` under `slotDem (code u) dem`,
and its captures agree with `iface` and `OutsideContracts`. -/
def DemandedRealizes {U : Type} (G : NormalGraph ι) (code : U → ModuleCode ι U) (iface : U → Ty ι)
    (dem : U → List CallbackDemand) (S : U → Prop) {N : Nat} (W₀ : WorldT N) (u : U) : Prop :=
  ∃ (L : List (CallEffects.Arrow (Ty ι))) (Sg : List (CallEffects.RestArrow (Ty ι))),
    Represents G (iface u) (.arrs L Sg) ∧ KindOffers G (code u).kind L Sg ∧
    DemandedRowOffers G (code u).arity (code u).exprs (code u).conts (code u).start
      (code u).captures (slotDem (code u) dem) L Sg (code u).sep (dem u) ∧
    (code u).captures.length = (code u).slots.length ∧
    (∀ (k : Nat) d, (code u).slots[k]? = some (Slot.linked d) → (code u).captures[k]? = some (iface d) ∧ S d) ∧
    (∀ (k : Nat) v A, (code u).slots[k]? = some (Slot.outside v) → (code u).captures[k]? = some A →
      ∀ i, ∀ j ≤ i, ∀ V : WorldT j, Above W₀ V → meaning G A j V (v i)) ∧
    CapturesApart code u

/-- The captures of a demand-realized unit meet `DemandedEnvOk` at `j` in a
world above `W₀`, where every linked sibling `d` meets `DemandedMeaning` for
`dem d`. -/
theorem captures_demandedEnvOk {U : Type} {G : NormalGraph ι} {code : U → ModuleCode ι U}
    {iface : U → Ty ι} {dem : U → List CallbackDemand} {S : U → Prop} {N : Nat} {W₀ : WorldT N}
    {u : U} (hr : DemandedRealizes G code iface dem S W₀ u) (ho : OutsideValues code) {f : U → Tm}
    (hf : ∀ d, isVal (f d) = true ∧ Scoped 0 (f d)) {i j : Nat} (hji : j ≤ i) {V : WorldT j}
    (hV : Above W₀ V) (hm : ∀ d, S d → DemandedMeaning G (iface d) (dem d) j V (f d)) :
    DemandedEnvOk G (code u).captures (slotDem (code u) dem) (envOf ((code u).captured f i) .nul) j V := by
  obtain ⟨L, Sg, -, -, -, hlen, hagree, hout, -⟩ := hr
  refine ⟨fun k => ?_, fun k A hA => ?_⟩
  · by_cases hk : k < ((code u).captured f i).length
    · have hget : ((code u).captured f i)[k]? = some ((code u).captured f i)[k] := List.getElem?_eq_getElem hk
      have hsc := (captured_values ho hf u i _ (List.getElem_mem hk)).2
      simpa [envOf, List.getD_eq_getElem?_getD, hget] using hsc
    · have hnone : ((code u).captured f i)[k]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hk)
      simp [envOf, List.getD_eq_getElem?_getD, hnone, Scoped]
  · have hk : k < (code u).slots.length := by
      have := (List.getElem?_eq_some_iff.mp hA).1; omega
    have hs : (code u).slots[k]? = some (code u).slots[k] := List.getElem?_eq_getElem hk
    have hv : envOf ((code u).captured f i) .nul k = ((code u).slots[k]).valueAt f i := by
      simp [envOf, List.getD_eq_getElem?_getD, captured_get hs]
    rw [hv]
    cases hsk : (code u).slots[k] with
    | linked d =>
      rw [hsk] at hs
      obtain ⟨hty, hd⟩ := hagree k d hs
      rw [hty] at hA; injection hA with hA; subst hA
      have hsd : slotDem (code u) dem k = dem d := by simp [slotDem, hs]
      rw [hsd]
      exact hm d hd
    | outside w =>
      rw [hsk] at hs
      have hsd : slotDem (code u) dem k = [] := by simp [slotDem, hs]
      rw [hsd, demandedMeaning_nil]
      exact hout k w A hs hA i j hji V hV

/-- **Module linking with callback demands** (proved): over a closed set `S`
where every unit is demand-realized at base world `W₀`, every unfolding `n` of
every unit `u ∈ S` meets `DemandedMeaning G (iface u) (dem u)` at every budget
`m ≤ n` in every world above `W₀`. -/
theorem approx_meets_demanded {U : Type} {G : NormalGraph ι} {code : U → ModuleCode ι U}
    {iface : U → Ty ι} {dem : U → List CallbackDemand} {S : U → Prop} {N : Nat} {W₀ : WorldT N}
    (hreal : ∀ u, S u → DemandedRealizes G code iface dem S W₀ u) (ho : OutsideValues code) :
    ∀ n u, S u → ∀ m ≤ n, ∀ W : WorldT m, Above W₀ W →
      DemandedMeaning G (iface u) (dem u) m W (approx code n u) := by
  intro n
  induction n with
  | zero =>
    intro u hu m hm W _
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -, hsep⟩ := hreal u hu
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    exact closure_meets_below_demanded (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u 0 v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u 0 v hv).1)
      (hsep _ 0) W (fun j hj => absurd hj (Nat.not_lt_zero j))
  | succ n ih =>
    intro u hu m hm W hW
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -, hsep⟩ := hreal u hu
    exact closure_meets_below_demanded (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u (n + 1) v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u (n + 1) v hv).1)
      (hsep _ (n + 1)) W (fun j hj V hx => captures_demandedEnvOk (hreal u hu) ho (approxEnv_value ho (n + 1))
        (by omega) (hW.below _ hx) (fun d hd => ih d hd j (by omega) V (hW.below _ hx)))

/-- **Headline linking corollary for exported / non-demanded functions**
(proved, zero `Θ_C`): every unit `x ∈ S` with `dem x = []` (every exported
function such as `sumAndTrace`, `collectDirect`, `collectAdapted`) meets its
plain TypeScript interface `meaning G (iface x) m W (approx code n x)`
**unconditionally**, at every unfolding depth `n`, every budget `m ≤ n`, and
every world above `W₀` — identical to `PassUnitFile.passFile_safe`. -/
theorem approx_meets_exported {U : Type} {G : NormalGraph ι} {code : U → ModuleCode ι U}
    {iface : U → Ty ι} {dem : U → List CallbackDemand} {S : U → Prop} {N : Nat} {W₀ : WorldT N}
    (hreal : ∀ u, S u → DemandedRealizes G code iface dem S W₀ u) (ho : OutsideValues code) :
    ∀ n x, S x → dem x = [] → ∀ m ≤ n, ∀ W : WorldT m, Above W₀ W →
      meaning G (iface x) m W (approx code n x) := by
  intro n x hx hnil m hm W hW
  have h := approx_meets_demanded hreal ho n x hx m hm W hW
  rwa [hnil, demandedMeaning_nil] at h

end DemandedSemantics

end Verification.SourceClaimJson.PassUnit

