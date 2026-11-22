import Verification.Source.Claims.CallbackDemandSpec
import Verification.Source.Claims.PassUnitCallbackLink

/-! # Soundness of callback-demand origin tracking, projection, and write checks

Proves the semantic correctness of the decidable checks in
`CallbackDemandSpec.lean` (zero `sorry`, zero axioms):

- `mentionsDemandedSibling_false_instantiate`: any expression not mentioning a
  demanded sibling instantiates identically under `ρ₁` and `ρ₂` whenever they
  agree on all non-demanded slots.
- `OriginValueHolds` / `EnvOriginHolds` / `originsLe_sound` /
  `applyTargetMap_sound`: one step of forward slot-origin soundness, the
  steps of the fixpoint witness check `originsValid`.
- `projectEntry_demand_mem` & `projectEntry_confined_ge`: projecting a
  node-local support entry either maps every selected location into the outer
  `callEnv` demand region (under prefix agreement) or selects only locations
  at or above the owner's allocation bound `bOwn`.
- `supportedAt_of_post_fresh`: universal path-provenance disjointness between
  a fresh allocation's writes (`FreshValueAt b`) and any pre-existing
  parameter/path region (`l < b` by `CallbackDemands.region_mem_lt_length`). -/

namespace Verification.SourceClaimJson
open Lean Verification ControlFlow ProgramTyping PositiveGraphs PositiveRules LabelStore
open HeapObservations CallbackDemands

/-! ## Non-mention of demanded siblings preserves instantiation -/

private theorem mentionsDemandedSibling_false_list {env : List SlotOrigin} {ds : List String}
    {xs : List Tm} (h : xs.any (mentionsDemandedSibling env ds) = false) :
    ∀ x ∈ xs, mentionsDemandedSibling env ds x = false := by
  intro x hx
  cases hm : mentionsDemandedSibling env ds x with
  | false => rfl
  | true =>
    have : xs.any (mentionsDemandedSibling env ds) = true := List.any_eq_true.mpr ⟨x, hx, hm⟩
    rw [h] at this; cases this

/-- If `mentionsDemandedSibling env ds t = false`, and `ρ₁`, `ρ₂` agree on
every slot whose origin is not `.sibling nm` (`nm ∈ ds`), then `t` instantiates
identically under `ρ₁` and `ρ₂` at any binder depth `j`. -/
theorem mentionsDemandedSibling_false_instantiate {ds : List String} :
    ∀ (t : Tm) (env : List SlotOrigin) (j : Nat) (ρ₁ ρ₂ : Env),
      mentionsDemandedSibling (List.replicate j .unknown ++ env) ds t = false →
      (∀ s, (∀ nm ∈ ds, originAt env s ≠ .sibling nm) → ρ₁ s = ρ₂ s) →
      instantiate j ρ₁ t = instantiate j ρ₂ t
  | .var i, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [instantiate]
    split
    · rfl
    · rename_i hge
      have hge' : j ≤ i := Nat.le_of_not_lt hge
      apply hag (i - j)
      intro nm hnm heq
      have hrep : originAt (List.replicate j .unknown ++ env) i = originAt env (i - j) := by
        simp only [originAt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp; omega), List.length_replicate]
      simp only [mentionsDemandedSibling, hrep, heq] at hm
      have hc : ds.contains nm = true := List.contains_iff_mem.mpr hnm
      rw [hc] at hm; cases hm
  | .nul, _, _, _, _, _, _ | .undef, _, _, _, _, _, _ | .tru, _, _, _, _, _, _
  | .fls, _, _, _, _, _, _ | .num _, _, _, _, _, _, _ | .str _, _, _, _, _, _, _
  | .bigint _, _, _, _, _, _, _ | .sym _, _, _, _, _, _, _ | .arr _, _, _, _, _, _, _
  | .viewSpine .., _, _, _, _, _, _ => rfl
  | .objAt _ .absent _, _, _, _, _, _, _ | .objAt _ (.view ..) _, _, _, _, _, _, _ => rfl
  | .objAt _ (.bound ..) _, _, _, _, _, hm, _ | .objAt _ (.graph ..) _, _, _, _, _, hm, _
  | .makeAt (.bound ..) _ _, _, _, _, _, hm, _ | .goto .., _, _, _, _, hm, _
  | .frame .., _, _, _, _, hm, _ => by simp [mentionsDemandedSibling] at hm
  | .invoke f r args, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate, instantiateArgs_eq_map]
    congr 1
    · exact mentionsDemandedSibling_false_instantiate f env j ρ₁ ρ₂ hm.1.1 hag
    · exact mentionsDemandedSibling_false_instantiate r env j ρ₁ ρ₂ hm.1.2 hag
    · refine List.map_congr_left fun a ha => ?_
      exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂
        (mentionsDemandedSibling_false_list hm.2 a ha) hag
  | .construct f args, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate, instantiateArgs_eq_map]
    congr 1
    · exact mentionsDemandedSibling_false_instantiate f env j ρ₁ ρ₂ hm.1 hag
    · refine List.map_congr_left fun a ha => ?_
      exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂
        (mentionsDemandedSibling_false_list hm.2 a ha) hag
  | .letE a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]
    congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · have hrep : .unknown :: (List.replicate j .unknown ++ env) = List.replicate (j + 1) .unknown ++ env := by
        simp [List.replicate_succ]
      rw [hrep] at hm
      exact mentionsDemandedSibling_false_instantiate b env (j + 1) ρ₁ ρ₂ hm.2 hag
  | .makeAt .absent ns xs, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate, instantiateArgs_eq_map]
    congr 1
    exact List.map_congr_left fun x hx =>
      mentionsDemandedSibling_false_instantiate x env j ρ₁ ρ₂ (mentionsDemandedSibling_false_list hm x hx) hag
  | .makeAt (.view ..) ns xs, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate, instantiateArgs_eq_map]
    congr 1
    exact List.map_congr_left fun x hx =>
      mentionsDemandedSibling_false_instantiate x env j ρ₁ ρ₂ (mentionsDemandedSibling_false_list hm x hx) hag
  | .makeAt (.graph ..) ns xs, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate, instantiateArgs_eq_map]
    congr 1
    · congr 1
      exact List.map_congr_left fun c hc =>
        mentionsDemandedSibling_false_instantiate c env j ρ₁ ρ₂ (mentionsDemandedSibling_false_list hm.1 c hc) hag
    · exact List.map_congr_left fun x hx =>
        mentionsDemandedSibling_false_instantiate x env j ρ₁ ρ₂ (mentionsDemandedSibling_false_list hm.2 x hx) hag
  | .arrLit xs, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate, instantiateArgs_eq_map]
    congr 1
    exact List.map_congr_left fun x hx =>
      mentionsDemandedSibling_false_instantiate x env j ρ₁ ρ₂ (mentionsDemandedSibling_false_list hm x hx) hag
  | .readAt _ a, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate]; congr 1
    exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm hag
  | .test _ a, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate]; congr 1
    exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm hag
  | .lenOf a, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate]; congr 1
    exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm hag
  | .spread a, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate]; congr 1
    exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm hag
  | .throw a, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling] at hm
    simp only [instantiate]; congr 1
    exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm hag
  | .indexAt a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .writeAt _ a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .arith _ a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .elemAt a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .merge _ a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .makeKey a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .ite c a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate c env j ρ₁ ρ₂ hm.1.1 hag
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1.2 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
  | .setElem c a b, env, j, ρ₁, ρ₂, hm, hag => by
    simp only [mentionsDemandedSibling, Bool.or_eq_false_iff] at hm
    simp only [instantiate]; congr 1
    · exact mentionsDemandedSibling_false_instantiate c env j ρ₁ ρ₂ hm.1.1 hag
    · exact mentionsDemandedSibling_false_instantiate a env j ρ₁ ρ₂ hm.1.2 hag
    · exact mentionsDemandedSibling_false_instantiate b env j ρ₁ ρ₂ hm.2 hag
termination_by t => sizeOf t

/-! ## Forward slot-origin soundness -/

/-- **A path of named data fields misses in `h` from `v`**: following its
fields, an object owns no field of the next name, so a read of it goes to the
object's prototype or gives `undefined` (`Step.readProto`, `Step.readMissing`)
and `readPath` gives none. -/
def PathMiss (h : Heap) : Val → List String → Prop
  | _, [] => False
  | .objAt fs _ _, f :: p => match fs.lookup (.str f) with
    | none => True
    | some l => match h[l]? with
      | some v => PathMiss h v p
      | none => False
  | _, _ :: _ => False

/-- Semantic meaning of a `SlotOrigin` for a runtime value `v` in heap `h`,
relative to outer `callEnv` `ρ₀` (so parameter `p` is `ρ₀ (p + 1)`), sibling
map `sibVal`, own-entry allocation floor `bOwn`, and caller allocation floor
`bCaller`. A path holds the value its own data fields lead to in `h`, or
misses there (`PathMiss`): a field read past a missing own field reads the
prototype's, which no own path names. -/
def OriginValueHolds {ι : Type} (codes : List (RequestJson.CodeRequest ι))
    (ρ₀ : Env) (sibVal : String → Tm) (bOwn bCaller : Nat) (h : Heap) : SlotOrigin → Tm → Prop
  | .param p, v => v = ρ₀ (p + 1)
  | .fresh _, v => FreshValueAt bOwn v
  | .callerFresh _, v => FreshValueAt bCaller v
  | .sibling nm, v => v = sibVal nm
  | .path p fs, v => HeapKnowledge.readPath h (ρ₀ (p + 1)) fs = some v ∨ PathMiss h (ρ₀ (p + 1)) fs
  | .closure ci caps, v =>
      ∃ q fs ar E K s capVals kind rest comp oid,
        codes[ci]? = some q ∧ q.entry.arity = ar ∧ q.entry.exprs = E ∧ q.entry.conts = K ∧
        q.entry.start = s ∧ v = .objAt fs (.graph ar E K s capVals kind rest comp) oid ∧
        caps.length = capVals.length ∧
        ∀ i, i < caps.length → OriginValueHolds codes ρ₀ sibVal bOwn bCaller h (caps.getD i .unknown) (capVals.getD i .nul)
  | .prim, _ => True
  | .unknown, _ => True
termination_by o => sizeOf o
decreasing_by
  rename_i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  simp only [SlotOrigin.closure.sizeOf_spec]
  omega

private theorem originValueHolds_param {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h : Heap} {p : Nat} {v : Tm} :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h (.param p) v ↔ v = ρ₀ (p + 1) := by
  rw [OriginValueHolds]

private theorem originValueHolds_fresh {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h : Heap} {a : Nat} {v : Tm} :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h (.fresh a) v ↔ FreshValueAt bOwn v := by
  rw [OriginValueHolds]

private theorem originValueHolds_path {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h : Heap} {p : Nat} {fs : List String} {v : Tm} :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h (.path p fs) v ↔
      HeapKnowledge.readPath h (ρ₀ (p + 1)) fs = some v ∨ PathMiss h (ρ₀ (p + 1)) fs := by
  rw [OriginValueHolds]

private theorem originValueHolds_unknown {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h : Heap} {v : Tm} :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h .unknown v := by
  rw [OriginValueHolds]; trivial

/-- Every slot in `env` holds a value meeting its `SlotOrigin`. -/
def EnvOriginHolds {ι : Type} (codes : List (RequestJson.CodeRequest ι))
    (ρ₀ : Env) (sibVal : String → Tm) (bOwn bCaller : Nat) (h : Heap)
    (env : List SlotOrigin) (ρ : Env) : Prop :=
  ∀ s, OriginValueHolds codes ρ₀ sibVal bOwn bCaller h (originAt env s) (ρ s)

/-- `originsLe stored next = true` preserves `EnvOriginHolds` (proved). -/
theorem originsLe_sound {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h : Heap}
    {stored next : List SlotOrigin} {ρ : Env}
    (hle : originsLe stored next = true)
    (hnext : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h next ρ) :
    EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h stored ρ := by
  intro s
  unfold originAt
  rw [List.getD_eq_getElem?_getD]
  by_cases hs : s < stored.length
  · have hall := List.all_eq_true.mp hle s (List.mem_range.mpr hs)
    have hget : stored[s]? = some stored[s] := List.getElem?_eq_getElem hs
    rw [hget] at hall ⊢
    simp only [Option.getD_some]
    cases hst : stored[s] with
    | unknown => exact originValueHolds_unknown
    | _ =>
      rw [hst] at hall
      simp only [beq_iff_eq] at hall
      have hns := hnext s
      simpa [originAt, List.getD_eq_getElem?_getD, hall] using hns
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hs)]
    exact originValueHolds_unknown

/-- `applyTargetMap` preserves `EnvOriginHolds` across `PointClaims.mapEnv`
(proved). -/
theorem applyTargetMap_sound {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h : Heap}
    {env : List SlotOrigin} {ρ : Env} {pushed : Option SlotOrigin} {v : Tm} {tgt : Target}
    (henv : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h env ρ)
    (hpush : ∀ o, pushed = some o → OriginValueHolds codes ρ₀ sibVal bOwn bCaller h o v) :
    EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h (applyTargetMap env pushed tgt)
      (PointClaims.mapEnv tgt.mapping (match pushed with | some _ => push v ρ | none => ρ)) := by
  have hsrc : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h
      (match pushed with | some o => o :: env | none => env)
      (match pushed with | some _ => push v ρ | none => ρ) := by
    cases pushed with
    | none => exact henv
    | some o =>
      intro s
      cases s with
      | zero => simpa [originAt, push] using hpush o rfl
      | succ k => simpa [originAt, push] using henv k
  intro s
  unfold applyTargetMap PointClaims.mapEnv
  cases hm : tgt.mapping with
  | none =>
    simp only [PointClaims.slot]
    cases pushed with
    | none => exact hsrc s
    | some _ => exact hsrc s
  | some m =>
    simp only [originAt, List.getD_eq_getElem?_getD, List.getElem?_map, PointClaims.slot]
    cases hms : m[s]? with
    | none => exact originValueHolds_unknown
    | some idx =>
      simp only [Option.map_some, Option.getD_some]
      cases pushed with
      | none => exact hsrc idx
      | some _ => exact hsrc idx

/-! ## Region projection soundness -/

private theorem readPath_append (h : Heap) :
    ∀ (p₁ p₂ : List String) (v : Tm),
      HeapKnowledge.readPath h v (p₁ ++ p₂) =
        (HeapKnowledge.readPath h v p₁).bind (fun u => HeapKnowledge.readPath h u p₂)
  | [], _, _ => rfl
  | f :: p₁, p₂, v => by
    cases v with
    | objAt fs _ _ =>
      simp only [List.cons_append, HeapKnowledge.readPath]
      cases hlu : fs.lookup (.str f) with
      | none => rfl
      | some l =>
        cases hget : h[l]? with
        | none => simp only [hget]; rfl
        | some u => simp only [hget]; exact readPath_append h p₁ p₂ u
    | _ => rfl

/-- **Demand projection soundness** (proved): if `projectEntry env confined (r, δ) = .demand (r', δ')`,
`EnvOriginHolds` holds at `(ρ, h₁)`, every slot of a path origin holds the
value its own data fields lead to in `h₁` (`hown`: no read of it went to a
prototype or missed, which `EnvOriginHolds` admits), and every path read from
outer `ρ₀` in `h₁` agrees with `h₀`, then `δ' = δ` and every location selected
by `r` at `(ρ, h₁)` is selected by `r'` at `(ρ₀, h₀)`. -/
theorem projectEntry_demand_mem {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ ρ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h₀ h₁ : Heap}
    {env : List SlotOrigin} {confined : List Nat}
    (henv : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ)
    (hown : ∀ x p fs, originAt env x = .path p fs → HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs = some (ρ x))
    (hagree : ∀ p fs, HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs = HeapKnowledge.readPath h₀ (ρ₀ (p + 1)) fs)
    (hcells_agree : ∀ p fs l,
      (((HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs).map (Footprints.spineCells h₁)).getD []).contains (some l) = true →
      (((HeapKnowledge.readPath h₀ (ρ₀ (p + 1)) fs).map (Footprints.spineCells h₀)).getD []).contains (some l) = true) :
    ∀ {r r' : Footprints.Region} {δ δ' : Footprints.Change},
      projectEntry env confined (r, δ) = .demand (r', δ') →
      δ' = δ ∧ ∀ l, r.mem ρ h₁ l = true → r'.mem ρ₀ h₀ l = true
  | .inCls r _, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    obtain ⟨rfl, hmem⟩ := projectEntry_demand_mem henv hown hagree hcells_agree hp
    exact ⟨rfl, fun l hl => by
      simp only [Footprints.Region.mem, Bool.and_eq_true] at hl
      exact hmem l hl.1⟩
  | .field x k, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param p =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      simpa [Footprints.Region.mem, hx] using hl
    | path p fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho; rw [hagree p fs] at hx
      simpa [Footprints.Region.mem, hx] using hl
    | fresh a => simp only [ho] at hp; split at hp <;> simp at hp
    | _ => rw [ho] at hp; cases hp
  | .fields x, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param p =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      simpa [Footprints.Region.mem, hx] using hl
    | path p fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho; rw [hagree p fs] at hx
      simpa [Footprints.Region.mem, hx] using hl
    | fresh a => simp only [ho] at hp; split at hp <;> simp at hp
    | _ => rw [ho] at hp; cases hp
  | .cells x, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param p =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      have h0 : (((HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) []).map (Footprints.spineCells h₁)).getD []).contains (some l) = true := by
        simpa [HeapKnowledge.readPath, Footprints.Region.mem, hx] using hl
      simpa [HeapKnowledge.readPath, Footprints.Region.mem] using hcells_agree p [] l h0
    | path p fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho
      have h0 : (((HeapKnowledge.readPath h₁ (ρ₀ (p + 1)) fs).map (Footprints.spineCells h₁)).getD []).contains (some l) = true := by
        simpa [hx, Footprints.Region.mem] using hl
      have h1 := hcells_agree p fs l h0
      simp only [Footprints.Region.mem]
      cases hrp : HeapKnowledge.readPath h₀ (ρ₀ (p + 1)) fs with
      | none => simp [hrp] at h1
      | some v => simpa [hrp] using h1
    | _ => rw [ho] at hp; cases hp
  | .path x p k, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param q =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      simp only [Footprints.Region.mem] at hl
      rw [hx] at hl
      cases p with
      | nil => simpa [Footprints.Region.mem, HeapKnowledge.readPath] using hl
      | cons f rest =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Footprints.Region.mem]
        rwa [hagree q (f :: rest)] at hl
    | path q fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho
      simp only [Footprints.Region.mem] at hl ⊢
      rw [← hagree q (fs ++ p), readPath_append h₁ fs p (ρ₀ (q + 1)), hx]
      exact hl
    | fresh a => simp only [ho] at hp; split at hp <;> simp at hp
    | _ => rw [ho] at hp; cases hp
  | .pathFields x p, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param q =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      simp only [Footprints.Region.mem] at hl
      rw [hx] at hl
      cases p with
      | nil => simpa [Footprints.Region.mem, HeapKnowledge.readPath] using hl
      | cons f rest =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Footprints.Region.mem]
        rwa [hagree q (f :: rest)] at hl
    | path q fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho
      simp only [Footprints.Region.mem] at hl ⊢
      rw [← hagree q (fs ++ p), readPath_append h₁ fs p (ρ₀ (q + 1)), hx]
      exact hl
    | fresh a => simp only [ho] at hp; split at hp <;> simp at hp
    | _ => rw [ho] at hp; cases hp
  | .pathCells x p, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param q =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      simp only [Footprints.Region.mem] at hl
      rw [hx] at hl
      have h0 : (((HeapKnowledge.readPath h₁ (ρ₀ (q + 1)) p).map (Footprints.spineCells h₁)).getD []).contains (some l) = true := by
        cases hrp : HeapKnowledge.readPath h₁ (ρ₀ (q + 1)) p with
        | none => simp [hrp] at hl
        | some v => simpa [hrp] using hl
      have h1 := hcells_agree q p l h0
      cases p with
      | nil => simpa [Footprints.Region.mem, HeapKnowledge.readPath] using h1
      | cons f rest =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Footprints.Region.mem]
        cases hrp : HeapKnowledge.readPath h₀ (ρ₀ (q + 1)) (f :: rest) with
        | none => simp [hrp] at h1
        | some v => simpa [hrp] using h1
    | path q fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho
      have h0 : (((HeapKnowledge.readPath h₁ (ρ₀ (q + 1)) (fs ++ p)).map (Footprints.spineCells h₁)).getD []).contains (some l) = true := by
        rw [readPath_append h₁ fs p (ρ₀ (q + 1)), hx, Option.bind_some]
        cases hrp : HeapKnowledge.readPath h₁ (ρ x) p with
        | none => simp [Footprints.Region.mem, hrp] at hl
        | some v => simpa [Footprints.Region.mem, hrp] using hl
      have h1 := hcells_agree q (fs ++ p) l h0
      cases hrp : HeapKnowledge.readPath h₀ (ρ₀ (q + 1)) (fs ++ p) with
      | none => simp [hrp] at h1
      | some v => simpa [Footprints.Region.mem, hrp] using h1
    | _ => rw [ho] at hp; cases hp
  | .spine x p, r', δ, δ', hp => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | param q =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      rw [originValueHolds_param] at hx
      simp only [Footprints.Region.mem] at hl ⊢
      rwa [hx, hagree q p] at hl
    | path q fs =>
      rw [ho] at hp hx; cases hp
      refine ⟨rfl, fun l hl => ?_⟩
      replace hx := hown x _ _ ho
      simp only [Footprints.Region.mem] at hl ⊢
      rw [← hagree q (fs ++ p), readPath_append h₁ fs p (ρ₀ (q + 1)), hx]
      exact hl
    | fresh a => simp only [ho] at hp; split at hp <;> simp at hp
    | _ => rw [ho] at hp; cases hp
  | .cls _, _, _, _, hp | .all, _, _, _, hp => by simp [projectEntry] at hp

/-- **Confined projection bound** (proved): any support entry projecting to
`.confined` selects exclusively locations `≥ bOwn` (allocated after producer entry). -/
theorem projectEntry_confined_ge {ι : Type} {codes : List (RequestJson.CodeRequest ι)}
    {ρ₀ ρ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h₁ : Heap}
    {env : List SlotOrigin} {confined : List Nat}
    (henv : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ) :
    ∀ {r : Footprints.Region} {δ : Footprints.Change},
      projectEntry env confined (r, δ) = .confined →
      ∀ l, r.mem ρ h₁ l = true → bOwn ≤ l
  | .inCls r _, δ, hp, l, hl => by
    simp only [projectEntry] at hp
    simp only [Footprints.Region.mem, Bool.and_eq_true] at hl
    exact projectEntry_confined_ge (r := r) henv hp l hl.1
  | .field x k, δ, hp, l, hl => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | fresh a =>
      rw [ho, originValueHolds_fresh] at hx
      simp only [Footprints.Region.mem, beq_iff_eq] at hl
      exact freshValueAt_field_ge hx hl
    | _ => rw [ho] at hp; cases hp
  | .fields x, δ, hp, l, hl => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | fresh a =>
      rw [ho, originValueHolds_fresh] at hx
      exact freshValueAt_fieldLocs_ge hx hl
    | _ => rw [ho] at hp; cases hp
  | .path x p k, δ, hp, l, hl => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | fresh a =>
      rw [ho] at hp
      rw [ho, originValueHolds_fresh] at hx
      cases p with
      | nil =>
        simp only [Footprints.Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hl
        exact freshValueAt_field_ge hx hl
      | cons _ _ => simp at hp
    | _ => rw [ho] at hp; cases hp
  | .pathFields x p, δ, hp, l, hl => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | fresh a =>
      rw [ho] at hp
      rw [ho, originValueHolds_fresh] at hx
      cases p with
      | nil =>
        simp only [Footprints.Region.mem, HeapKnowledge.readPath] at hl
        exact freshValueAt_fieldLocs_ge hx hl
      | cons _ _ => simp at hp
    | _ => rw [ho] at hp; cases hp
  | .spine x p, δ, hp, l, hl => by
    simp only [projectEntry] at hp
    have hx := henv x
    cases ho : originAt env x with
    | fresh a =>
      rw [ho] at hp
      rw [ho, originValueHolds_fresh] at hx
      cases p with
      | nil =>
        simp only [Footprints.Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hl
        exact freshValueAt_elementsOf_ge hx hl
      | cons _ _ => simp at hp
    | _ => rw [ho] at hp; cases hp
  | .cells x, _, hp, _, _ => by
    simp only [projectEntry] at hp
    cases ho : originAt env x <;> simp [ho] at hp
  | .pathCells x _, _, hp, _, _ => by
    simp only [projectEntry] at hp
    cases ho : originAt env x <;> simp [ho] at hp
  | .cls _, _, hp, _, _ | .all, _, hp, _, _ => by simp [projectEntry] at hp

/-! ## Universal path-provenance fresh-write disjointness -/

/-- **Fresh-write preservation from a `Footprints.Post` effect** (proved):
whenever a call/step satisfies `Footprints.Post Φ ρ h₁ h₂` and every location
selected by any `(r, δ) ∈ Φ` either satisfies `b ≤ l` (freshly allocated at or
after `b`) or has `δ = .keep`, while every region of `S` at `(ρ₀, h₀)` lies
strictly below `b` (from `CallbackDemands.region_mem_lt_length`), then
`SupportedAt S ρ₀ h₀ h₁ h₂` holds unconditionally. -/
theorem supportedAt_of_post_fresh {b : Nat} {Φ S : Footprints.Footprint}
    {ρ ρ₀ : Env} {h₀ h₁ h₂ : Heap}
    (hSlt : ∀ e ∈ S, ∀ l, e.1.mem ρ₀ h₀ l = true → l < b)
    (hpost : Footprints.Post Φ ρ h₁ h₂)
    (hΦ : ∀ e ∈ Φ, ∀ l, e.1.mem ρ h₁ l = true → b ≤ l ∨ e.2 = .keep) :
    SupportedAt S ρ₀ h₀ h₁ h₂ := by
  refine supportedAt_of_write_ge hSlt fun l v hlt hv => ?_
  obtain ⟨v', hv', hch⟩ := hpost.2 l v hv
  rcases hch with rfl | ⟨e, he, hm, hhold⟩
  · exact hv'
  · have hkeep : e.2 = .keep := (hΦ e he l hm).resolve_left (by omega)
    rw [hkeep] at hhold
    cases hhold
    exact hv'

end Verification.SourceClaimJson
