import Verification.Source.Claims.FramedStarts

/-! # The initial configurations, from the checks the pass makes

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The initialization in the flow").
An initial configuration of a framed plan's program runs the
initialization's code at the realm's identities in front of a client of
lowered outside source. The checks of the frame's flow (`frameFlowB`, its
`initFlowB`) establish both premises the framed claim reads of them:

- **The realm's identities meet the initialization's slots**
  (`realmSlot_vj`): at the history before any entry, every location outside
  storage, an identity passing `realmSlotB` meets its slot's set, and is a
  closure of the signature its slot names.
- **The initialization's run fits the flow** (`init_fits`, by `gotoC` at
  its proposal): its slots by `realmSlot_vj`, the default `undefined` a
  primitive, its returns within the set.
- **Every initial configuration fits the flow** (`FramedSpec.initialFits`):
  the run at `O`, the client by `fits_lowered` (lowered source is lowered
  code), the realm's heap of primitives.
- **Every initial configuration is an entry** (`FramedSpec.initialEntry`):
  code provenance (`prov_mono` from `codeOkB`, the client's closures of
  outside code, `prov_loweredSrc`), the call discipline (the run free of
  runs, the client lowered source), outside code lowered source (every code
  the run holds carries a tag of `C`) and closed values. -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow
open Verification.SourceClaimJson (realmSlotB initFlowB codeOkB)

/-! ## Provenance -/

/-- **Provenance at a weaker test** (proved, by induction on the term). -/
theorem prov_mono {ok ok' : Code → ComponentTag → Bool} (hok : ∀ m c, ok m c = true → ok' m c = true) :
    ∀ t, prov ok t = true → prov ok' t = true := by
  intro t
  induction t using Tm.induct with
  | _ =>
    intro h
    simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at h ⊢
    try grind

/-- A part of a closure's code in lowered code holds no code (proved). -/
theorem codePart_prov {ok : Code → ComponentTag → Bool} {t : Tm} (h : CodePart t) : prov ok t = true := by
  rcases h with ⟨i, rfl⟩ | hp
  · simp [prov]
  · cases t <;> simp_all [primVal, prov]

/-- **Lowered source meets every test passing outside code's lowered
codes** (proved, by induction on the term): every code it holds is outside
code's, its node expressions lowered source. -/
theorem prov_loweredSrc {ofC : ComponentTag → Bool} {ok : Code → ComponentTag → Bool}
    (hok : ∀ m c, ofC c = false → (∀ e ∈ m.1, LoweredSrc ofC e) → ok m c = true) :
    ∀ t, LoweredSrc ofC t → prov ok t = true := by
  intro t
  induction t using Tm.induct with
  | makeBound t r pre ns args _ _ _ iha =>
    intro h
    simp only [LoweredSrc, loweredSrcArgs_iff] at h
    simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨codePart_prov h.1, codePart_prov h.2.1⟩, fun x hx => codePart_prov (h.2.2.1 x hx)⟩,
      fun x hx => iha x hx (h.2.2.2 x hx)⟩
  | makeGraph n E K s caps k r comp ns args ihE _ iha =>
    intro h
    simp only [LoweredSrc, loweredSrcArgs_iff] at h
    simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨hok _ _ h.1 h.2.1, fun x hx => ihE x hx (h.2.1 x hx)⟩, fun x hx => codePart_prov (h.2.2.1 x hx)⟩,
      fun x hx => iha x hx (h.2.2.2 x hx)⟩
  | _ =>
    intro h
    simp only [LoweredSrc, loweredSrcArgs_iff, prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at h ⊢
    try grind

theorem map_self_iff {f : Tm → Tm} : ∀ {l : List Tm}, l.map f = l ↔ ∀ x ∈ l, f x = x
  | [] => by simp
  | x :: xs => by simp [map_self_iff]

/-- **Instantiation keeps a term scoped below its depth** (proved, by
induction on the term): it replaces no variable. -/
theorem instantiate_of_scoped (ρ : Env) : ∀ (t : Tm) (d : Nat), Scoped d t → instantiate d ρ t = t := by
  intro t
  induction t using Tm.induct with
  | _ =>
    intro d h
    simp only [Scoped, scopedArgs_iff] at h
    simp [instantiate, instantiateArgs_eq_map, map_self_iff]
    try grind

/-! ## The realm's identities -/

section
variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

/-- **A realm's identity passing its slot's check meets the slot**
(proved): an object with no field, which holds no location, or a closure of `C`'s code with no field and no capture
whose code holds no value, open at its entry where its token lies in `O`
and naming only its own slot at every context, meets the slot's set, and
is a closure of the signature the slot names. -/
theorem realmSlot_vj {F : FFlow P} {c : FCode P} {i : Nat} {v : Tm} (h : realmSlotB F c i v = true)
    (g : Ghost P) (n : Nat) :
    VJ F.flow g n (c.flow.env 0 i) v ∧ ∀ σ, c.flow.fn 0 i = some σ → FnIs P σ v := by
  unfold realmSlotB at h
  split at h
  · rename_i loc
    simp only [Option.isNone_iff_eq_none] at h
    refine ⟨VJ.thrown (Fl := F.flow) (g := g) (n := n) loc, fun σ hσ => ?_⟩
    rw [h] at hσ; cases hσ
  · rename_i ar E K s k rest comp loc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true, Option.all_eq_true,
      Option.any_eq_true] at h
    obtain ⟨⟨⟨⟨hC, hvals⟩, ⟨c', hc', htok, hop⟩⟩, hself⟩, hfn⟩ := h
    have hcode : codeVals P.ofC (.objAt [] (.graph ar E K s [] k rest comp) loc) = [] := by
      simp [codeVals, hC]
    have hnext : ∀ a, next (.objAt [] (.graph ar E K s [] k rest comp) loc) a = none := by
      intro a; cases a <;> rfl
    have hleaves : ∀ l, ¬ Leaves P.ofC (.objAt [] (.graph ar E K s [] k rest comp) loc) l := by
      rintro l ⟨x, hx, a, hn⟩
      cases hx with
      | refl => rw [hnext a] at hn; cases hn
      | step hm _ => rw [hcode] at hm; cases hm
    have hreach : ∀ x, CodeReach P.ofC (.objAt [] (.graph ar E K s [] k rest comp) loc) x →
        x = .objAt [] (.graph ar E K s [] k rest comp) loc := by
      intro x hx
      cases hx with
      | refl => rfl
      | step hm _ => rw [hcode] at hm; cases hm
    have hwithin : ∀ w, Within P (.objAt [] (.graph ar E K s [] k rest comp) loc) w →
        w = .objAt [] (.graph ar E K s [] k rest comp) loc := by
      intro w hw
      cases hw with
      | refl => rfl
      | cap hu _ => cases hu
      | code hu _ => rw [hvals] at hu; cases hu
    have hπ : F.flow.code (E, K) entryCx = some c'.flow := by simp [FFlow.flow, hc']
    have hcapfn : ∀ cx π, F.flow.code (E, K) cx = some π → CapFn π ar E K s [] rest := by
      intro cx π hcx
      obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hcx
      exact (selfFnB_sound (hself _ (FFlow.at_ctxs hfc))).capFn
    refine ⟨⟨rfl, Scoped.closed (by simp [Scoped]), fun l hl => (hleaves l hl).elim, fun l hl => (hleaves l hl).elim,
      ?_, ?_⟩, ?_⟩
    · intro x hx fs ar' E' K' s' caps' k' rest' comp' oid he
      rw [hreach x hx] at he
      simp only [Tm.objAt.injEq, CallCode.graph.injEq] at he
      obtain ⟨-, ⟨rfl, rfl, rfl, rfl, -, -, -, rfl⟩, -⟩ := he
      exact ⟨fun _ => ⟨c'.flow, hπ, htok⟩, fun hc => by rw [hC] at hc; cases hc⟩
    · intro w hw
      rw [hwithin w hw]
      refine ⟨rfl, ?_, ?_, fun x hx => by rw [hcode] at hx; cases hx⟩
      · intro fs ar' E' K' s' caps' k' rest' comp' oid he _
        simp only [Tm.objAt.injEq, CallCode.graph.injEq] at he
        obtain ⟨-, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, -⟩ := he
        refine ⟨⟨c'.flow, hπ, fun ht => ?_⟩, fun j u hu => (by simp at hu), fun cx π hcx =>
          ⟨fun j u hu => (by simp at hu), hcapfn cx π hcx⟩⟩
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hop
        rcases hop with hn | hop
        · exact absurd (show c'.tok ∈ F.O from ht) hn
        · exact openB_sound F hop
      · intro fs ar' E' K' s' caps' k' rest' comp' oid he hc
        simp only [Tm.objAt.injEq, CallCode.graph.injEq] at he
        obtain ⟨-, ⟨-, -, -, -, -, -, -, rfl⟩, -⟩ := he
        rw [hC] at hc; cases hc
    · intro σ hσ
      have := hfn σ hσ
      subst this
      exact ⟨[], [], k, comp, loc, rfl, rfl, hC⟩
  · cases h

/-- **A realm's identity passing its slot's check is closed** (proved). -/
theorem realmSlot_scoped {F : FFlow P} {c : FCode P} {i : Nat} {v : Tm} (h : realmSlotB F c i v = true) :
    Scoped 0 v := by
  unfold realmSlotB at h
  split at h
  · simp [Scoped]
  · simp [Scoped]
  · cases h

/-- **The initialization's run fits the flow** (proved, by `gotoC` at its
proposal at its entry context): each slot holds a realm's identity meeting
it (`realmSlot_vj`) or the default `undefined`, a primitive; a slot naming
a signature is one below the identities, holding a closure of it; its
returns lie within `O`. -/
theorem init_fits {F : FFlow P} {initE : List Tm} {initK : List (Continuation × Option Target)} {initL : List Tm}
    (hI : initFlowB F initE initK initL = true) {tag : ComponentTag} (hC : P.ofC tag = true) (g : Ghost P) (n : Nat)
    {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} :
    Fits F.flow (VJ F.flow g n) Γ a o F.flow.O (.goto initE initK 0 initL .undef tag) := by
  simp only [initFlowB, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq, List.all_eq_true] at hI
  obtain ⟨⟨⟨⟨⟨c, hc, ⟨hret, hsize⟩, hslots⟩, -⟩, -⟩, -⟩, -⟩ := hI
  have hslot : ∀ i, i < initL.length → VJ F.flow g n (c.flow.env 0 i) (envOf initL .undef i) ∧
      ∀ σ, c.flow.fn 0 i = some σ → FnIs P σ (envOf initL .undef i) := by
    intro i hi
    have hm : (initL[i], i) ∈ initL.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
    have hv : envOf initL .undef i = initL[i] := by simp [envOf, List.getD_eq_getElem?_getD, hi]
    rw [hv]
    exact realmSlot_vj (hslots _ hm) g n
  refine .gotoC entryCx c.flow hC (by simp [FFlow.flow, hc]) (fun i => .inl ?_) (fun i σ hσ => ?_) hret
    (fun _ => Sub.refl _)
  · rcases Nat.lt_or_ge i initL.length with hi | hi
    · exact (hslot i hi).1
    · have hv : envOf initL .undef i = .undef := by simp [envOf, List.getD_eq_getElem?_getD, hi]
      rw [hv]; exact VJ.prim rfl
  · exact (hslot i (Nat.lt_of_lt_of_le (FCode.fn_lt hσ) hsize)).2 σ hσ
end

end Verification.TolerantFrames.ReadOnly

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

namespace FramedSpec
variable (spec : FramedSpec ι)

omit [Labels ι] in
/-- **The component's checks at the frame's flow** (proved, by
`frame_transport` from the check `componentBindingRefusal` runs at the
flow with the frame's sites and decided tags). -/
theorem frameFlow_checks (h : spec.componentRefusal.val = none) :
    frameFlowB spec.fflow spec.lay spec.realm spec.initE spec.initK spec.initL = true :=
  frame_transport spec.C spec.checked
    (fun _ Fl => frameFlowB Fl spec.lay spec.realm spec.initE spec.initK spec.initL = true)
    (componentBindingRefusal_none (spec.componentRefusal_none h)).2.2.2.2.2.2.2

omit [Labels ι] in
/-- **What the checks give of the initialization**, at the frame's flow
(proved, `frameFlowB_sound` at `frameFlow_checks`). -/
theorem init_checks (h : spec.componentRefusal.val = none) :
    spec.fflow.flow.Facts ∧ (∀ e ∈ spec.initE, free false e = true) ∧ (∀ v ∈ spec.realm, primVal v = true) ∧
      (∀ v ∈ spec.initL, layP (layQ spec.fflow spec.lay) v = true ∧ Plain v ∧ free false v = true) ∧
      initFlowB spec.fflow spec.initE spec.initK spec.initL = true := by
  obtain ⟨hFa, -, -, -, -, -, -, -, -, hEf, hprim, hLi, hI⟩ := frameFlowB_sound (spec.frameFlow_checks h)
  exact ⟨hFa, hEf, hprim, hLi, hI⟩

/-- **Every initial configuration fits the flow** (proved, from the
component's checks): the initialization's run fits `O` (`init_fits`), the
client fits `O` with its variable bound to `O` (`fits_lowered`, lowered
source being lowered code), and the realm's heap of primitives meets the
flow. -/
theorem initialFits (r : SourceRequest σ ι) (h : spec.componentRefusal.val = none) : spec.InitialFits r := by
  obtain ⟨hFa, -, hprim, -, hI⟩ := spec.init_checks h
  intro x hx
  obtain ⟨client, hh, ht, hlow, hsc⟩ := hx
  refine ⟨?_, fun w u hu => ?_⟩
  · show Fits spec.fflow.flow _ _ _ _ _ x.t
    rw [ht]
    refine .letE (init_fits hI (spec.init_ofC r) _ _) ?_ (fun _ => Sub.refl _)
    have := fits_lowered (Fl := spec.fflow.flow)
      (g := bareStart (spec.core r).F (spec.core r).C (.letE (.goto spec.initE spec.initK 0 spec.initL .undef
        (some spec.C)) client))
      (n := x.s.h.length) hFa (fun _ => .undef) (fun _ => VJ.prim rfl) (o := true) client 1
      (consSites spec.fflow.flow.O fun _ => none) (LoweredSrc.lowered spec.fflow.flow hlow) (fun i hi => by
        obtain rfl : i = 0 := by omega
        rfl)
    rw [instantiate_of_scoped _ client 1 hsc] at this
    exact this
  · rw [hh] at hu
    exact VJ.prim (hprim u (List.mem_of_getElem? hu))

/-- A code the flow proposes for at a tag of `C` is one of the frame's codes
(proved). -/
theorem codeOk_ok (r : SourceRequest σ ι) {m : Code} {c : ComponentTag} (h : codeOkB spec.fflow m c = true) :
    (spec.frame r).ok m c = true := by
  simp only [codeOkB, Bool.or_eq_true, Bool.not_eq_true', Option.isSome_iff_exists] at h
  simp only [ClientFrame.ok, decide_eq_true_eq]
  intro hruns
  have hruns' : spec.F.Runs c spec.C := hruns
  rcases h with hc | ⟨fc, hfc⟩
  · have : (spec.F.at spec.C).ofC c = true := by simpa [Family.at, Family.ofC] using hruns'
    rw [this] at hc; cases hc
  · exact ⟨entryCx, fc.flow, by simp [flow, FFlow.flow, hfc]⟩

/-- **Every initial configuration is an entry** (proved, from the
component's checks): code provenance (the initialization's code and every
code its node expressions and slots hold at a tag of `C` among the flow's,
`codeOkB`; the client's codes outside code's), the call discipline (the run
and the realm free of runs, the client lowered source), outside code
lowered source (every code the run holds carries a tag of `C`) and closed
values (the identities, `Scoped 1 client`, the realm's primitives). -/
theorem initialEntry (r : SourceRequest σ ι) (h : spec.componentRefusal.val = none) : spec.InitialEntry r := by
  obtain ⟨-, hEf, hprim, hLi, hI⟩ := spec.init_checks h
  have hI' := hI
  simp only [initFlowB, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq, List.all_eq_true,
    provs_eq] at hI'
  obtain ⟨⟨⟨⟨⟨c, hc, -, hslots⟩, hpE⟩, hpL⟩, hsE⟩, hsL⟩ := hI'
  have hmemL : ∀ v ∈ spec.initL, ∃ i, realmSlotB spec.fflow c i v = true := by
    intro v hv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hv
    exact ⟨i, hslots (v, i) (List.mem_zipIdx_iff_getElem?.mpr hi)⟩
  have hRun : (spec.frame r).F.Runs (some spec.C) (spec.frame r).C := by
    simpa [Family.ofC] using spec.init_ofC r
  have hpv : ∀ v, primVal v = true → ∀ ok, prov ok v = true := by
    intro v hp ok; cases v <;> simp_all [primVal, prov]
  intro x hx
  obtain ⟨client, hh, ht, hlow, hsc⟩ := hx
  rw [ht, hh]
  refine ⟨⟨?_, fun v hv => hpv v (hprim v hv) _⟩, ⟨?_, fun v hv => ?_⟩, ⟨?_, fun v hv => hpv v (hprim v hv) _⟩,
    ⟨?_, fun v hv => ?_⟩⟩
  · -- provenance
    simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, fun e he => prov_mono (fun m c h => spec.codeOk_ok r h) e (hpE e he)⟩,
      fun v hv => prov_mono (fun m c h => spec.codeOk_ok r h) v (hpL v hv)⟩, trivial⟩, ?_⟩
    · simp only [ClientFrame.ok, decide_eq_true_eq]
      exact fun _ => ⟨entryCx, c.flow, by simp [flow, FFlow.flow, hc]⟩
    · refine prov_loweredSrc (fun m cc hcc _ => ?_) client hlow
      simp only [ClientFrame.ok, decide_eq_true_eq]
      intro hr
      have hr' : spec.F.Runs cc spec.C := hr
      have : (spec.F.at spec.C).ofC cc = true := by simpa [Family.at, Family.ofC] using hr'
      have hcc' : (spec.F.at spec.C).ofC cc = false := hcc
      rw [this] at hcc'; cases hcc'
  · -- the discipline
    simp only [wf, isVal, ↓reduceIte, runParts, frees_eq, List.all_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨hEf, fun v hv => (hLi v hv).2.2⟩, rfl⟩, loweredSrc_free hlow true⟩
  · have := hprim v hv
    cases v <;> simp_all [primVal, TolerantFrames.ReadOnly.free]
  · -- outside code lowered source
    simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true]
    have hC : ∀ m cc, (spec.F.at spec.C).ofC cc = true → srcOk (spec.F.ofC spec.C) m cc = true := by
      intro m cc hcc
      simp only [srcOk, decide_eq_true_eq]
      intro hf
      have hf' : (spec.F.at spec.C).ofC cc = false := hf
      rw [hcc] at hf'; cases hf'
    refine ⟨⟨⟨⟨hC _ _ (spec.init_ofC r), fun e he => prov_mono (fun m cc h => hC m cc h) e (hsE e he)⟩,
      fun v hv => prov_mono (fun m cc h => hC m cc h) v (hsL v hv)⟩, trivial⟩, ?_⟩
    refine prov_loweredSrc (fun m cc _ hE => ?_) client hlow
    simp only [srcOk, decide_eq_true_eq]
    exact fun _ => hE
  · -- closed values
    simp only [Scoped, scopedArgs_iff]
    refine ⟨⟨fun v hv => ?_, trivial⟩, hsc⟩
    obtain ⟨i, hi⟩ := hmemL v hv
    exact realmSlot_scoped hi
  · have := hprim v hv
    cases v <;> simp_all [primVal, Scoped]
end FramedSpec
end
end Verification.SourceClaimJson

