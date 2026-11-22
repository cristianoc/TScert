import Verification.Source.Claims.CallbackPreservation
import Verification.Semantics.FootprintRebase

/-! Exact projection, forwarding, and the callback demand check at a concrete
heap transition. The root and actual-slot correspondences are semantic premises. -/
namespace Verification.SourceClaimJson.CallbackPreservation
open Footprints HeapKnowledge

def RealizesRoots (roots : RootMap) (src dst : Env) (h : Heap) : Prop :=
  ∀ x y p, roots x = some (y, p) → readPath h (dst y) p = some (src x)

theorem projectRegion_mem_exact {roots : RootMap} {src dst : Env} {h : Heap}
    (ok : RealizesRoots roots src dst h) (r : Region) {s : Region}
    (proj : projectRegion roots r = some s) (l : Nat) :
    r.mem src h l = s.mem dst h l := by
  induction r generalizing s with
  | cls | all => cases proj; rfl
  | inCls r c ih =>
    cases hr : projectRegion roots r with
    | none => simp [projectRegion, hr] at proj
    | some t =>
      simp [projectRegion, hr] at proj
      subst s
      simp [Region.mem, ih hr]
  | spine x p =>
    cases hr : roots x with
    | none => simp [projectRegion, hr] at proj
    | some t =>
      rcases t with ⟨y,q⟩
      simp [projectRegion, hr] at proj
      subst s
      simp [Region.mem, readPath_append, ok x y q hr]
  | field x k | fields x | cells x | path x p k | pathFields x p | pathCells x p =>
    all_goals try cases p
    all_goals cases hr : roots x with
    | none => simp [projectRegion, hr] at proj
    | some t =>
      rcases t with ⟨y,q⟩
      have eqv := ok x y q hr
      cases q with
      | nil =>
        have e : dst y = src x := Option.some.inj eqv
        simp [projectRegion, hr] at proj
        subst s
        simp [Region.mem, e]
        all_goals rfl
      | cons a q =>
        simp [projectRegion, hr, -List.cons_append] at proj
        subst s
        simp [Region.mem, eqv]
        all_goals try rfl
        all_goals
          have suffix (p : List String) : readPath h (dst y) (a :: (q ++ p)) = readPath h (src x) p := by
            change readPath h (dst y) ((a :: q) ++ p) = _
            rw [readPath_append, eqv]; rfl
          rw [suffix]

theorem project_supported_iff {roots : RootMap} {src dst : Env} {h h' : Heap}
    (ok : RealizesRoots roots src dst h) (S : Footprint) {T : Footprint}
    (proj : project roots S = some T) :
    Supported S src h h' ↔ Supported T dst h h' := by
  induction S generalizing T with
  | nil =>
    cases proj
    simp [Supported]
  | cons e tail ih =>
    rcases e with ⟨r, c⟩
    simp only [project, List.mapM_cons] at proj
    change (do
      let entry ← (projectRegion roots r).map (·, c)
      let rest ← project roots tail
      pure (entry :: rest)) = some T at proj
    cases hr : projectRegion roots r with
    | none => simp [hr] at proj
    | some s =>
      cases ht : project roots tail with
      | none => simp [hr, ht] at proj
      | some rest =>
        simp [hr, ht] at proj
        subst T
        have cons_rule (a : Region) (es : Footprint) (env : Env) :
            Supported ((a,c) :: es) env h h' ↔
              (∀ l v, a.mem env h l = true → h[l]? = some v →
                ∃ v', h'[l]? = some v' ∧ c.Holds h.length v v') ∧ Supported es env h h' := by
          simp [Supported]
        rw [cons_rule, cons_rule, ih ht]
        simp only [projectRegion_mem_exact ok r hr]

open CallEffects

theorem Demand.check_supported {d : Demand} {roots : RootMap} {callbacks : Nat → Option Callback}
    {ev : SepEvidence} {cb : Callback} {src dst closure : Env} {h h' : Heap}
    {n : Nat} {W : WorldT n} {μ} (exit : Completion)
    (accept : d.check roots callbacks ev = true) (lookup : callbacks d.parameter = some cb)
    (rootsOK : RealizesRoots roots src dst h)
    (actualsOK : ∀ i j, cb.actuals i = some j → dst j = closure i)
    (evidenceOK : ev.Holds μ dst h) (heapOK : HeapOk n W h) (envOK : RootsOk W dst)
    (effect : Post (cb.effects.get exit) closure h h') :
    Supported (d.support.get exit) src h h' := by
  simp only [Demand.check, lookup, Bool.and_eq_true] at accept
  have checked : (match project roots (d.support.get exit) with
    | some S => stable ev S ((cb.effects.get exit).renameM cb.actuals)
    | none => false) = true := by
    cases exit
    · exact accept.1
    · exact accept.2
  cases hp : project roots (d.support.get exit) with
  | none => simp [hp] at checked
  | some S =>
    simp only [hp] at checked
    exact (project_supported_iff rootsOK _ hp).mpr
      (stable_sound checked evidenceOK heapOK envOK (effect.renameM actualsOK))


theorem Demand.forward_supported_iff {d forwarded : Demand} {roots : RootMap} {p : Nat}
    {src dst : Env} {h h' : Heap}
    (ok : RealizesRoots roots src dst h) (hf : d.forward p roots = some forwarded)
    (exit : Completion) :
    Supported (d.support.get exit) src h h' ↔ Supported (forwarded.support.get exit) dst h h' := by
  cases hn : project roots d.support.normal with
  | none => simp [Demand.forward, hn] at hf
  | some normal =>
    cases he : project roots d.support.exceptional with
    | none => simp [Demand.forward, hn, he] at hf
    | some exceptional =>
      simp [Demand.forward, hn, he] at hf
      subst forwarded
      cases exit
      · exact project_supported_iff ok _ hn
      · exact project_supported_iff ok _ he

theorem RealizesRoots.comp {r s : RootMap} {ρ σ τ : Env} {h : Heap}
    (hr : RealizesRoots r ρ σ h) (hs : RealizesRoots s σ τ h) :
    RealizesRoots (fun x => do
      let (y, p) ← r x
      let (z, q) ← s y
      pure (z, q ++ p)) ρ τ h := by
  intro x z path he
  cases hx : r x with
  | none => simp [hx] at he
  | some yp =>
    obtain ⟨y,p⟩ := yp
    cases hy : s y with
    | none => simp [hx,hy] at he
    | some zq =>
      obtain ⟨z',q⟩ := zq
      simp [hx,hy] at he
      obtain ⟨rfl,rfl⟩ := he
      rw [readPath_append, hs _ _ _ hy]
      exact hr _ _ _ hx

/-- The producer selects the whole support for replay, removes its private
entries from the published demand, and strengthens each remaining change to
`keep`. A concrete local frame and the projected published demand together
establish the full support of the call in the producer's environment. -/
theorem supported_of_private_and_published {roots : RootMap} {body iface : Env}
    {before after : Heap} (rootsOK : RealizesRoots roots body iface before)
    (S : Footprint) (isPrivate : Region → Bool) {projected : Footprint}
    (hp : project roots (S.filter fun e => !isPrivate e.1) = some projected)
    (localFrame : Supported (S.filter fun e => isPrivate e.1) body before after)
    (published : Supported (projected.map fun e => (e.1, .keep)) iface before after) :
    Supported S body before after := by
  have residual : Supported (S.filter fun e => !isPrivate e.1) body before after := by
    apply (project_supported_iff rootsOK _ hp).mpr
    intro e he l v hm hv
    obtain ⟨v',hv',unchanged⟩ := published (e.1, .keep)
      (List.mem_map.mpr ⟨e, he, rfl⟩) l v hm hv
    change v' = v at unchanged
    subst v'
    exact ⟨v,hv',Change.Holds.refl _ _ _⟩
  intro e he
  by_cases priv : isPrivate e.1 = true
  · exact localFrame e (List.mem_filter.mpr ⟨he, priv⟩)
  · exact residual e (List.mem_filter.mpr ⟨he, by simpa using priv⟩)

end Verification.SourceClaimJson.CallbackPreservation
