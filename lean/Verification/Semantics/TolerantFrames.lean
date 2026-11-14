import Verification.Semantics.ArgumentStoreRegions

/-! # Tolerant frames over indexed states

The states of the note "Tolerant frames" read in the indexed model. A
**state** is a budget, a world at that budget and a heap meeting it, the
budget positive: the safety predicates state nothing at budget zero
(`Safe Ξ T 0 W h t` is `True`), so no assertion is read there. An
**admissible transition** drops the budget and extends the truncated world;
heap growth and the contents of every location whose contract admits one value
follow from it. A **safe run** of a term from a state, to a point with budget
left, ends in a state an admissible transition reaches, its intermediate
worlds the ones the safety derivation supplies (`run`). An **action** of a
footprint `Φ` at a name valuation `ρ` is an admissible transition whose heaps
meet `Post Φ ρ`, and `Box Φ F` holds where `F` holds after every action of
`Φ`: the weakest liberal precondition of one arbitrary such action. The name
valuation and the entry mark are parameters of every assertion and stay fixed
across the modality. A fact whose support an effect respects enters the
modality (`tolerant_frame`), and two atoms, a length lower bound and density,
enter that of `{values: any, stores: grow}`. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations

/-! ## States and admissible transitions -/

/-- A state: budget `n`, positive, a world at `n` whose contracts survive
allocation, and a heap meeting the world. -/
structure IndexedHeap where
  n : Nat
  W : WorldT n
  h : Heap
  pos : 0 < n
  adm : WorldAdm W
  ok : HeapOk n W h

/-- An assertion, read at a name valuation, an entry mark and a state. -/
abbrev Assertion := Env → Nat → IndexedHeap → Prop

/-- `s'` is reachable from `s` by what safe code may do: its budget is at
most `s`'s, and its world extends `s`'s world truncated to its budget. -/
def Admissible (s s' : IndexedHeap) : Prop :=
  ∃ hle : s'.n ≤ s.n, WExt (trunc s'.n hle s.W) s'.W

namespace Admissible

theorem refl (s : IndexedHeap) : Admissible s s :=
  ⟨Nat.le_refl _, by rw [trunc_id]; exact WExt_refl _⟩

/-- Composition through the intermediate state's world. -/
theorem trans {s₁ s₂ s₃ : IndexedHeap} (h₁ : Admissible s₁ s₂) (h₂ : Admissible s₂ s₃) :
    Admissible s₁ s₃ := by
  obtain ⟨hle₁, hx₁⟩ := h₁
  obtain ⟨hle₂, hx₂⟩ := h₂
  refine ⟨Nat.le_trans hle₂ hle₁, ?_⟩
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc hle₂ hx₁) hx₂

/-- The heap grows: each heap is as long as its world, and the world only
grows. -/
theorem length_le {s s' : IndexedHeap} (ha : Admissible s s') : s.h.length ≤ s'.h.length := by
  obtain ⟨hle, tail, ht⟩ := ha
  rw [s.ok.1.1, s'.ok.1.1, toList_length, toList_length, ht]
  simp

/-- Every location of `s`'s world keeps its contract, restricted to the lower
budget. -/
theorem lookup_ext {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {c : Ctr s.n}
    (hl : lookup s.W l = some c) :
    ∃ hle : s'.n ≤ s.n, lookup s'.W l = some (fun i hi w => c i (Nat.lt_of_lt_of_le hi hle) w) := by
  obtain ⟨hle, hx⟩ := ha
  exact ⟨hle, WExt_lookup hx (lookup_trunc hle s.W l c hl)⟩

/-- **A location whose contract admits one value holds it after every
admissible transition** (at the positive budget every state has). -/
theorem stable_value {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} {c : Ctr s.n} {v : Val}
    (hl : lookup s.W l = some c) (hc : CtrStable c v) : s'.h[l]? = some v := by
  obtain ⟨hle, hx⟩ := ha
  exact s'.ok.stable_value s'.pos (WExt_lookup hx (lookup_trunc hle s.W l c hl)) (hc.restrict hle)

/-- A path through locations with single-value contracts stays one. -/
theorem stablePath {s s' : IndexedHeap} (ha : Admissible s s') {x : Val} {p : List String} {v : Val}
    (hp : StablePath s.W x p v) : StablePath s'.W x p v := by
  obtain ⟨hle, hx⟩ := ha
  exact hp.transfer hle hx

/-- **A stable path reads its value after every admissible transition.** -/
theorem readPath {s s' : IndexedHeap} (ha : Admissible s s') {x : Val} {p : List String} {v : Val}
    (hp : StablePath s.W x p v) : HeapKnowledge.readPath s'.h x p = some v :=
  (ha.stablePath hp).read s'.pos s'.ok

end Admissible

theorem IndexedHeap.stable_value (s : IndexedHeap) {l : Nat} {c : Ctr s.n} {v : Val}
    (hl : lookup s.W l = some c) (hc : CtrStable c v) : s.h[l]? = some v :=
  s.ok.stable_value s.pos hl hc

/-! ## Adequacy: safe runs are admissible -/

/-- **A run that a safety derivation covers, with budget left, ends in a
state an admissible transition reaches**, the safety derivation continuing
there. The intermediate worlds are those the derivation supplies at each
step; determinism of the step relation matches them to the run. -/
theorem run {Ξ T : Fam} {Q : Post} {R : Heap → Prop} :
    ∀ {k h t h' t'}, Steps k h t h' t' → ∀ (s : IndexedHeap), s.h = h → k < s.n →
      SafePostExc Ξ T Q R s.n s.W s.h t →
      ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
        SafePostExc Ξ T Q R s'.n s'.W s'.h t' := by
  intro k h t h' t' hst
  induction hst with
  | refl => intro s hs _ hsafe; exact ⟨s, Admissible.refl s, hs, rfl, hsafe⟩
  | next st _ ih =>
    intro s hs hk hsafe
    obtain ⟨n, W, h₀, pos, adm, ok⟩ := s
    simp only at hs hk hsafe ⊢
    subst hs
    cases n with
    | zero => omega
    | succ m =>
      rcases hsafe.2 with (⟨hv, -, -⟩ | ⟨hr, -⟩) | ⟨U, h₁, t₁, hx, hu, st', hh, hs'⟩
      · exact absurd st (value_no_step hv)
      · exact absurd st hr.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        obtain ⟨s', ha, he, hn, hsafe'⟩ :=
          ih ⟨m, U, _, by omega, hu, hh⟩ rfl (by simp only; omega) hs'
        exact ⟨s', Admissible.trans ⟨Nat.le_succ m, hx⟩ ha, he, by simp only at hn; omega, hsafe'⟩

/-- At positive budget, a value's safety gives its type and the
postcondition. -/
theorem exit_value {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {n : Nat} {W : WorldT n} {h : Heap} {v : Tm}
    (hn : 0 < n) (hv : isVal v = true) (hs : SafePostExc Ξ T Q R n W h v) : T n W v ∧ Q h v := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ j =>
    rcases hs.2 with (⟨-, hT, hQ⟩ | ⟨hr, -⟩) | ⟨_, _, _, _, _, st, _, _⟩
    · exact ⟨hT, hQ⟩
    · exact absurd hv (by rw [hr.not_val]; simp)
    · exact absurd st (value_no_step hv)

/-- At positive budget, a raise's safety gives a thrown value of the
exception family and the throw's postcondition. -/
theorem exit_raise {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {n : Nat} {W : WorldT n} {h : Heap} {t e : Tm}
    (hn : 0 < n) (hr : Raises t e) (hs : SafePostExc Ξ T Q R n W h t) : Thrown Ξ n W t ∧ R h := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ j =>
    rcases hs.2 with (⟨hv, -, -⟩ | ⟨hth, hR⟩) | ⟨_, _, _, _, _, st, _, _⟩
    · rw [raises_not_val hr] at hv; cases hv
    · exact ⟨hth, hR⟩
    · exact absurd st (raises_no_step hr)

/-- The normal exit: a run to a value, with budget left, ends in an
admissible state where the value meets its type and the postcondition. -/
theorem run_normal {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {s : IndexedHeap} {t v : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T Q R s.n s.W s.h t) (hst : Steps k s.h t h' v) (hv : isVal v = true)
    (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ T s'.n s'.W v ∧ Q h' v := by
  obtain ⟨s', ha, he, hn, hs'⟩ := run hst s rfl hk hsafe
  exact ⟨s', ha, he, hn, he ▸ exit_value s'.pos hv hs'⟩

/-- The exceptional exit: a run to a raise, with budget left, ends in an
admissible state where the thrown value is of the exception family and the
throw's postcondition holds. -/
theorem run_throw {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {s : IndexedHeap} {t t' e : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T Q R s.n s.W s.h t) (hst : Steps k s.h t h' t') (hr : Raises t' e)
    (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ Thrown Ξ s'.n s'.W t' ∧ R h' := by
  obtain ⟨s', ha, he, hn, hs'⟩ := run hst s rfl hk hsafe
  exact ⟨s', ha, he, hn, he ▸ exit_raise s'.pos hr hs'⟩

/-- Plain safety: a run with budget left ends in an admissible state, safety
continuing there. -/
theorem safe_run {Ξ T : Fam} {s : IndexedHeap} {t t' : Tm} {h' : Heap} {k : Nat}
    (hsafe : Safe Ξ T s.n s.W s.h t) (hst : Steps k s.h t h' t') (hk : k < s.n) :
    ∃ s' : IndexedHeap, Admissible s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ Safe Ξ T s'.n s'.W s'.h t' := by
  have hp : SafePostExc Ξ T (fun _ _ => True) (fun _ => True) s.n s.W s.h t :=
    SafePostExc.of_post (fun _ => trivial) (of_value_property (fun _ _ _ _ _ => trivial) hsafe)
  obtain ⟨s', ha, he, hn, hs'⟩ := run hst s rfl hk hp
  exact ⟨s', ha, he, hn, erase hs'.post⟩

/-! ## Actions and the modality -/

/-- An action of the footprint `Φ` at the name valuation `ρ`: an admissible
transition whose heaps meet `Φ`'s postcondition, its regions read at the
heap it starts from. -/
def Action (Φ : Footprint) (ρ : Env) (s s' : IndexedHeap) : Prop :=
  Admissible s s' ∧ Post Φ ρ s.h s'.h

theorem Action.refl (Φ : Footprint) (ρ : Env) (s : IndexedHeap) : Action Φ ρ s s :=
  ⟨Admissible.refl s, Post.refl Φ ρ s.h⟩

/-- `Box Φ F`: `F` holds after every action of `Φ`, at the same name
valuation and entry mark. -/
def Box (Φ : Footprint) (F : Assertion) : Assertion :=
  fun ρ m s => ∀ s', Action Φ ρ s s' → F ρ m s'

def Entails (F G : Assertion) : Prop := ∀ ρ m s, F ρ m s → G ρ m s

/-- An assertion is invariant when every admissible transition keeps it. -/
def Invariant (g : Assertion) : Prop := ∀ ρ m s s', Admissible s s' → g ρ m s → g ρ m s'

/-- An effect is rigid at `ρ` when its action is transitive. -/
def Rigid (Φ : Footprint) (ρ : Env) : Prop :=
  ∀ s₁ s₂ s₃, Action Φ ρ s₁ s₂ → Action Φ ρ s₂ s₃ → Action Φ ρ s₁ s₃

/-! ## The laws -/

section Laws
variable {Φ Ψ : Footprint} {F G g : Assertion} {ρ : Env} {m : Nat} {s : IndexedHeap}

/-- (a) Reflexive elimination. -/
theorem box_elim (hb : Box Φ F ρ m s) : F ρ m s := hb s (Action.refl Φ ρ s)

/-- (b) Conjunction. -/
theorem box_and : Box Φ (fun ρ m s => F ρ m s ∧ G ρ m s) ρ m s ↔ Box Φ F ρ m s ∧ Box Φ G ρ m s :=
  ⟨fun hb => ⟨fun s' ha => (hb s' ha).1, fun s' ha => (hb s' ha).2⟩,
    fun ⟨hf, hg⟩ s' ha => ⟨hf s' ha, hg s' ha⟩⟩

/-- (b) Monotonicity. -/
theorem box_mono (hfg : Entails F G) (hb : Box Φ F ρ m s) : Box Φ G ρ m s :=
  fun s' ha => hfg ρ m s' (hb s' ha)

/-- (c) Antitonicity in the effect, for inclusion of actions from `s`. -/
theorem box_anti (hle : ∀ s', Action Φ ρ s s' → Action Ψ ρ s s') (hb : Box Ψ F ρ m s) :
    Box Φ F ρ m s :=
  fun s' ha => hb s' (hle s' ha)

/-- Footprint inclusion gives inclusion of actions from a state where its
class evidence holds. -/
theorem action_le {cl : ClassEvidence} (hle : Footprint.le cl Φ Ψ = true) (hc : ClassOk cl ρ s.h)
    {s' : IndexedHeap} (ha : Action Φ ρ s s') : Action Ψ ρ s s' :=
  ⟨ha.1, Post.mono hle hc ha.2⟩

/-- Closed footprints are included as their entries are, from every state. -/
theorem action_le_closed {a b : Footprints.Closed} (hle : a.le b = true) {s' : IndexedHeap}
    (ha : Action a.fp ρ s s') : Action b.fp ρ s s' :=
  ⟨ha.1, Footprints.Closed.post_mono hle ha.2⟩

/-- (d) Disjunction with an invariant guard. -/
theorem box_or (hg : Invariant g) (h : g ρ m s ∨ Box Φ F ρ m s) :
    Box Φ (fun ρ m s => g ρ m s ∨ F ρ m s) ρ m s := by
  intro s' ha
  rcases h with hg' | hb
  · exact .inl (hg ρ m s s' ha.1 hg')
  · exact .inr (hb s' ha)

/-- (e) Idempotence for a rigid effect. -/
theorem box_idem (hr : Rigid Φ ρ) (hb : Box Φ F ρ m s) : Box Φ (Box Φ F) ρ m s :=
  fun s₁ ha₁ s₂ ha₂ => hb s₂ (hr s s₁ s₂ ha₁ ha₂)

end Laws

/-- Every admissible transition is an action of the closed footprint letting
everything change. -/
theorem action_top {ρ : Env} {s s' : IndexedHeap} (ha : Admissible s s') : Action Footprints.Closed.top.fp ρ s s' :=
  ⟨ha, Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (Footprints.Closed.holds_top.mpr ha.length_le))⟩

/-- **Invariance is the note's `F ⊢ □_⊤ F`.** -/
theorem invariant_iff_top {g : Assertion} : Invariant g ↔ Entails g (Box Footprints.Closed.top.fp g) :=
  ⟨fun hg ρ m s hs s' ha => hg ρ m s s' ha.1 hs,
    fun hb ρ m s s' ha hs => hb ρ m s hs s' (action_top ha)⟩

/-- **Closed footprints are rigid**: a run within one followed by another is
within it (`Closed.Holds.trans_on`). -/
theorem closed_rigid (c : Footprints.Closed) (ρ : Env) : Rigid c.fp ρ := by
  intro s₁ s₂ s₃ ha₁ ha₂
  refine ⟨ha₁.1.trans ha₂.1, ?_⟩
  have h₁ : c.Holds s₁.h s₂.h := Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha₁.2)
  have h₂ : c.Holds s₂.h s₃.h := Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha₂.2)
  exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (h₁.trans_on (h₂.on _)))

/-! ## An effect that is not rigid

`x[∗]`, the store of `x` with the cells it lists, both at `any`: a first
action may make the store list an old cell, and a second may then change that
cell, which the first heap's region does not cover. -/

/-- A contract admitting every value. -/
def anyCtr : Ctr 1 := fun _ _ _ v => isVal v = true

/-- A world of three locations admitting every value: an array store, then
two element cells. -/
def anyWorld : WorldT 1 := ofEntries [(.store .array, anyCtr), (.elem, anyCtr), (.elem, anyCtr)]

theorem anyWorld_lookup {l : Nat} {c : Ctr 1} (hl : lookup anyWorld l = some c) : l < 3 ∧ c = anyCtr := by
  simp only [lookup, anyWorld, toList, entries_ofEntries] at hl
  rcases l with _ | _ | _ | l <;> simp at hl
  all_goals exact ⟨by omega, hl.symm⟩

theorem anyWorld_adm : WorldAdm anyWorld := by
  intro l c hl
  obtain ⟨-, rfl⟩ := anyWorld_lookup hl
  exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩

/-- A heap of `anyWorld`: a store listing its element cells, and two source
values without references. -/
theorem anyWorld_ok {ls : List (Option Nat)} {a b : Val} (hls : ∀ l, some l ∈ ls → l = 1 ∨ l = 2)
    (ha : isSourceVal a = true) (hb : isSourceVal b = true) (hra : refs a = []) (hrb : refs b = []) :
    HeapOk 1 anyWorld [.arr ls, a, b] := by
  have hvals : ∀ v ∈ [Tm.arr ls, a, b], isVal v = true := by
    intro v hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rfl
    · exact sourceVal_isVal ha
    · exact sourceVal_isVal hb
  refine ⟨⟨by simp [anyWorld, toList], fun l c hc => ?_⟩, fun l r hr => ?_⟩
  · obtain ⟨hlt, rfl⟩ := anyWorld_lookup hc
    have hlh : l < [Tm.arr ls, a, b].length := by simpa using hlt
    exact ⟨_, List.getElem?_eq_getElem hlh, fun _ _ => hvals _ (List.getElem_mem hlh)⟩
  · simp only [roleAt, roles, anyWorld, entries_ofEntries] at hr
    rcases l with _ | _ | _ | l <;> simp at hr <;> subst hr
    · refine ⟨_, rfl, ⟨ls, rfl⟩, RefsOk_arr_iff.mpr fun l hl => ?_⟩
      rcases hls l hl with rfl | rfl <;> simp [roleAt, roles, anyWorld]
    · exact ⟨_, rfl, ha, RefsOk_of_nil hra⟩
    · exact ⟨_, rfl, hb, RefsOk_of_nil hrb⟩

/-- A state of `anyWorld` at budget 1. -/
def anyState (h : Heap) (ok : HeapOk 1 anyWorld h) : IndexedHeap :=
  ⟨1, anyWorld, h, Nat.one_pos, anyWorld_adm, ok⟩

theorem anyState_admissible {h h' : Heap} {ok ok'} :
    Admissible (anyState h ok) (anyState h' ok') :=
  ⟨Nat.le_refl 1, by show WExt (trunc 1 (Nat.le_refl 1) anyWorld) anyWorld; rw [trunc_id]; exact WExt_refl _⟩

/-- **`x[∗] : any` is not rigid.** -/
theorem elems_not_rigid :
    ¬ Rigid [(.field 0 arrayStoreKey, .any), (.elems 0, .any)]
      (fun _ => .objAt [(arrayStoreKey, 0)] .absent 0) := by
  intro hr
  let s₁ := anyState [.arr [some 1], .nul, .nul] (anyWorld_ok (by simp) rfl rfl rfl rfl)
  let s₂ := anyState [.arr [some 2], .nul, .nul] (anyWorld_ok (by simp) rfl rfl rfl rfl)
  let s₃ := anyState [.arr [some 2], .nul, .tru] (anyWorld_ok (by simp) rfl rfl rfl rfl)
  have a₁ : Action [(.field 0 arrayStoreKey, .any), (.elems 0, .any)]
      (fun _ => .objAt [(arrayStoreKey, 0)] .absent 0) s₁ s₂ := by
    refine ⟨anyState_admissible, by simp [s₁, s₂, anyState], fun l v hl => ?_⟩
    rcases l with _ | _ | _ | l <;> simp [s₁, s₂, anyState] at hl ⊢
    · exact .inr ⟨_, List.mem_cons_self .., by decide, trivial⟩
    · exact .inl hl
    · exact .inl hl
  have a₂ : Action [(.field 0 arrayStoreKey, .any), (.elems 0, .any)]
      (fun _ => .objAt [(arrayStoreKey, 0)] .absent 0) s₂ s₃ := by
    refine ⟨anyState_admissible, by simp [s₂, s₃, anyState], fun l v hl => ?_⟩
    rcases l with _ | _ | _ | l <;> simp [s₂, s₃, anyState] at hl ⊢
    · exact .inl hl
    · exact .inl hl
    · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by decide, trivial⟩
  obtain ⟨-, -, hp⟩ := hr s₁ s₂ s₃ a₁ a₂
  obtain ⟨v', hv', ha⟩ := hp 2 .nul (by simp [s₁, anyState])
  simp [s₃, anyState] at hv'
  subst hv'
  rcases ha with he | ⟨e, he, hm, -⟩
  · cases he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [s₁, anyState, Region.mem, storeElems, fieldsOf] at hm

/-! ## Adequacy: effect judgments give actions -/

/-- **The normal exit of a run is an action of the normal footprint**: a
judgment whose normal exit meets `cn` and `Qn` from the run's first heap, and
whose exceptional exit meets `ce` and `Qe`, and a run to a value with budget
left. The endpoint exposes the action, the residual budget, the value's type
and the exact post. -/
theorem action_normal {Ξ T : Fam} {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {ρ : Env}
    {s : IndexedHeap} {t v : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
      s.n s.W s.h t)
    (hst : Steps k s.h t h' v) (hv : isVal v = true) (hk : k < s.n) :
    ∃ s' : IndexedHeap, Action cn.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ T s'.n s'.W v ∧ Qn h' v := by
  obtain ⟨s', ha, he, hn, hT, hc, hq⟩ := run_normal hsafe hst hv hk
  subst he
  exact ⟨s', ⟨ha, Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp hc)⟩, rfl, hn, hT, hq⟩

/-- **The exceptional exit of a run is an action of the exceptional
footprint**, the raised value exposed: it is closed and of the exception
family at the endpoint, and the exact exceptional post holds. -/
theorem action_throw {Ξ T : Fam} {cn ce : Footprints.Closed} {Qn : Post} {Qe : Heap → Prop} {ρ : Env}
    {s : IndexedHeap} {t t' e : Tm} {h' : Heap} {k : Nat}
    (hsafe : SafePostExc Ξ T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ Qe h')
      s.n s.W s.h t)
    (hst : Steps k s.h t h' t') (hr : Raises t' e) (hk : k < s.n) :
    ∃ s' : IndexedHeap, Action ce.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
      Scoped 0 e ∧ Ξ s'.n s'.W e ∧ Qe h' := by
  obtain ⟨s', ha, he, hn, ⟨e', hr', hsc, hΞ⟩, hc, hq⟩ := run_throw hsafe hst hr hk
  cases Raises_det hr hr'
  subst he
  exact ⟨s', ⟨ha, Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp hc)⟩, rfl, hn, hsc, hΞ, hq⟩

/-- A normal-only judgment (`SafePost`) leaves the exceptional exit at
`{values: any, stores: any}`: its throw is an action of `Closed.top`, the
raised value exposed. -/
theorem action_throw_top {Ξ T : Fam} {Q : Post} {ρ : Env} {s : IndexedHeap} {t t' e : Tm} {h' : Heap}
    {k : Nat} (hsafe : SafePost Ξ T Q s.n s.W s.h t) (hst : Steps k s.h t h' t') (hr : Raises t' e)
    (hk : k < s.n) :
    ∃ s' : IndexedHeap, Action Footprints.Closed.top.fp ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧
      Scoped 0 e ∧ Ξ s'.n s'.W e := by
  obtain ⟨s', ha, he, hn, ⟨e', hr', hsc, hΞ⟩, -⟩ :=
    run_throw (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) hsafe) hst hr hk
  cases Raises_det hr hr'
  exact ⟨s', action_top ha, he, hn, hsc, hΞ⟩

/-! ## Invariant and rigid assertions -/

/-- An assertion reading no state is invariant: a fact about the name
valuation and the entry mark alone. -/
theorem invariant_const (P : Env → Nat → Prop) : Invariant (fun ρ m _ => P ρ m) :=
  fun _ _ _ _ _ hp => hp

/-- The store of `x` was allocated at or after the entry mark: `fresh(x)`. It
reads no heap. -/
def Fresh (x : Nat) : Assertion := fun ρ m _ => FreshAt m (ρ x)

theorem fresh_invariant (x : Nat) : Invariant (Fresh x) := invariant_const _

/-- The path `p` from `x` passes only locations whose contracts admit one
value, reading `v`: a fact of the world. -/
def StableAt (x : Nat) (p : List String) (v : Val) : Assertion :=
  fun ρ _ s => StablePath s.W (ρ x) p v

theorem stableAt_invariant (x : Nat) (p : List String) (v : Val) : Invariant (StableAt x p v) :=
  fun _ _ _ _ ha hp => ha.stablePath hp

/-- The path `p` from `x` reads `v`: `π ≐ v`. -/
def ReadsAs (x : Nat) (p : List String) (v : Val) : Assertion :=
  fun ρ _ s => HeapKnowledge.readPath s.h (ρ x) p = some v

/-- **A stable path is rigid**: `rigid(π)` with its witness the path's
value, under every effect. -/
theorem stable_rigid {Φ : Footprint} {x : Nat} {p : List String} {v : Val} {ρ : Env} {m : Nat}
    {s : IndexedHeap} (hp : StableAt x p v ρ m s) : Box Φ (ReadsAs x p v) ρ m s :=
  fun _ ha => ha.1.readPath hp

/-! ## Rigidity on a domain

`box_idem` needs transitivity of the action from every state; a footprint
whose region is read along a path composes only where the path resolves to
the same value in both heaps. Rigidity on a domain asks transitivity from the
domain's states, and the domain carries the evidence: a stable path, a fact
of the world every admissible transition keeps. -/

/-- `Φ`'s action is transitive from every state of `D`. -/
def RigidOn (Φ : Footprint) (ρ : Env) (m : Nat) (D : Assertion) : Prop :=
  ∀ s₁ s₂ s₃, D ρ m s₁ → Action Φ ρ s₁ s₂ → Action Φ ρ s₂ s₃ → Action Φ ρ s₁ s₃

/-- (e) on a domain: idempotence from a state of the domain. -/
theorem box_idem_on {Φ : Footprint} {F D : Assertion} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hr : RigidOn Φ ρ m D) (hD : D ρ m s) (hb : Box Φ F ρ m s) : Box Φ (Box Φ F) ρ m s :=
  fun s₁ ha₁ s₂ ha₂ => hb s₂ (hr s s₁ s₂ hD ha₁ ha₂)

/-- A rigid domain that is invariant stays one along every action: the
domain holds at every state an action reaches, so idempotence iterates. -/
theorem rigidOn_domain {Φ : Footprint} {D : Assertion} {ρ : Env} {m : Nat} {s s' : IndexedHeap}
    (hinv : Invariant D) (hD : D ρ m s) (ha : Action Φ ρ s s') : D ρ m s' :=
  hinv ρ m s s' ha.1 hD

/-- The region of the field `k` of the value the path `p` reads from `x` is
the same at every heap where the path reads `v`. -/
theorem path_mem_eq {ρ : Env} {x : Nat} {p : List String} {k : PropKey} {v : Val} {h h' : Heap} {l : Nat}
    (hv : HeapKnowledge.readPath h (ρ x) p = some v) (hv' : HeapKnowledge.readPath h' (ρ x) p = some v) :
    (Region.path x p k).mem ρ h l = (Region.path x p k).mem ρ h' l := by
  simp only [Region.mem, hv, hv']

/-- **A store region at a stable path is rigid on the domain of the path's
stability**: `{x.p.k: δ}` composes from every state where the path from `x`
is stable, whatever the change `δ`. -/
theorem path_rigid_on (x : Nat) (p : List String) (k : PropKey) (δ : Change) (v : Val) (ρ : Env) (m : Nat) :
    RigidOn [(.path x p k, δ)] ρ m (StableAt x p v) := by
  intro s₁ s₂ s₃ hD ha₁ ha₂
  have hv₁ := hD.read s₁.pos s₁.ok
  have hv₂ := ha₁.1.readPath hD
  refine ⟨ha₁.1.trans ha₂.1, Nat.le_trans ha₁.2.1 ha₂.2.1, fun l v₀ h₀ => ?_⟩
  obtain ⟨v₁, h₁, a₁⟩ := ha₁.2.2 l v₀ h₀
  obtain ⟨v₂, h₂, a₂⟩ := ha₂.2.2 l v₁ h₁
  have hb : s₁.h.length ≤ s₂.h.length := ha₁.2.1
  refine ⟨v₂, h₂, ?_⟩
  have single : ∀ {e}, e ∈ [(Region.path x p k, δ)] → e = (Region.path x p k, δ) := fun he => by simpa using he
  rcases a₁ with rfl | ⟨e₁, he₁, hm₁, hh₁⟩
  · rcases a₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inl rfl
    · obtain rfl := single he₂
      exact .inr ⟨_, List.mem_singleton_self _, (path_mem_eq hv₁ hv₂).trans hm₂, hh₂.lower hb⟩
  · obtain rfl := single he₁
    rcases a₂ with rfl | ⟨e₂, he₂, -, hh₂⟩
    · exact .inr ⟨_, List.mem_singleton_self _, hm₁, hh₁⟩
    · obtain rfl := single he₂
      exact .inr ⟨_, List.mem_singleton_self _, hm₁, hh₁.trans hb hh₂⟩

/-! ## Entering the modality -/

/-- **The tolerant frame theorem as a modal law**: a fact whose support the
effect respects, under knowledge holding at the state, holds after every
action of the effect (`stable_sound`, `FactKind.support_sound`). -/
theorem tolerant_frame {K : SepKnowledge} {F : FactKind} {Φ : Footprint} {μ : Nat → Nat} {ρ : Env}
    {m : Nat} {s : IndexedHeap} (hc : stable K F.support Φ = true) (hK : K.Holds μ ρ s.h)
    (hF : F.Holds ρ s.h) : Box Φ (fun ρ _ s => F.Holds ρ s.h) ρ m s :=
  fun _ ha => FactKind.support_sound hF (stable_sound hc hK ha.2)

/-- **The tolerant frame theorem, over any assertion**: an assertion with a
support in a context every action of the effect meets, and an effect
respecting that support under a query sound at the state, holds after every
action of the effect: `K ∧ F ⊢ □_Φ F` (`keeps_sound`). -/
theorem tolerant_frame_supports {C : Env → Heap → Heap → Prop} {P : Env → Heap → Prop} {S Φ : Footprint}
    {q : SepQuery} {ρ : Env} {m : Nat} {s : IndexedHeap} (hs : Supports C P S) (hr : respects q S Φ = true)
    (hq : q.Sound ρ s.h) (hc : ∀ s', Action Φ ρ s s' → C ρ s.h s'.h) (hP : P ρ s.h) :
    Box Φ (fun ρ _ s => P ρ s.h) ρ m s :=
  fun s' ha => keeps_sound hs hr hq ha.2 (hc s' ha) hP

open HeapKnowledge in
/-- **An index fact a closed footprint's change keeps holds after every
action of the footprint** (`holdsAt_kept`, `Changes.ofClosed_holds`). -/
theorem kept_box (c : Footprints.Closed) {F : IndexFact} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hk : F.keptBy (Changes.ofClosed c) (fun _ _ => false) = true) (hF : F.HoldsAt ε ρ s.h) :
    Box c.fp (fun ρ _ s => F.HoldsAt ε ρ s.h) ρ m s := by
  intro s' ha
  have hc : (Changes.ofClosed c).Holds s.h s'.h :=
    Changes.ofClosed_holds (Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha.2))
  exact IndexFact.holdsAt_kept hc (fun _ _ _ _ _ _ _ hf => by simp at hf) hk hF

/-! ## Two atoms -/

/-- `{values: any, stores: grow}`: the effect of an element write whose
target is unknown. -/
def growEffect : Footprints.Closed := ⟨.any, .grow⟩

open HeapKnowledge in
/-- `y ≤ |x|`: slot `y` holds an integer at most the length of `x`'s store. -/
def lowerBoundFact (y x : Nat) : IndexFact := .linear (.le [(.value y, 1), (.length x, -1)] 0)

/-- `y ≤ |x|` as an assertion. -/
def LowerBound (ε : HeapKnowledge.EntryState) (y x : Nat) : Assertion := fun ρ _ s => (lowerBoundFact y x).HoldsAt ε ρ s.h

/-- **(Grow)** `y ≤ |x| ⊢ □_{values: any, stores: grow} (y ≤ |x|)`. -/
theorem grow {y x : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} (hb : LowerBound ε y x ρ m s) :
    Box growEffect.fp (LowerBound ε y x) ρ m s :=
  kept_box growEffect rfl hb

/-- `y ≤ |x.p|`: the value the path `p` reads from `x` has a store at least as
long as the integer slot `y` holds. -/
def PathLowerBound (y x : Nat) (p : List String) : Assertion := fun ρ _ s =>
  ∃ w a len, HeapKnowledge.readPath s.h (ρ x) p = some w ∧ HeapKnowledge.intValue (ρ y) = some a ∧
    HeapKnowledge.lengthOf s.h w = some len ∧ a ≤ len

/-- **(Grow) at a rigid path**: along a stable path, `y ≤ |x.p|` survives
every action of `{values: any, stores: grow}`. The path's rigidity is a fact
of the world, kept by every admissible transition. -/
theorem grow_path {y x : Nat} {p : List String} {v : Val} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hp : StableAt x p v ρ m s) (hb : PathLowerBound y x p ρ m s) :
    Box growEffect.fp (PathLowerBound y x p) ρ m s := by
  intro s' ha
  obtain ⟨w, a, len, hw, ha', hl, hle⟩ := hb
  have hv : HeapKnowledge.readPath s.h (ρ x) p = some v := hp.read s.pos s.ok
  rw [hw] at hv; cases hv
  obtain ⟨st, ls, hst, hls, rfl, hm⟩ := HeapKnowledge.lengthOf_store hl
  have hc : (HeapKnowledge.Changes.ofClosed growEffect).Holds s.h s'.h :=
    HeapKnowledge.Changes.ofClosed_holds (Footprints.Closed.holds_iff.mpr (Footprints.Closed.post_iff.mp ha.2))
  obtain ⟨ls', hls', hlen, hmax⟩ := hc.2.2 rfl st ls hls
  exact ⟨v, a, ls'.length, ha.1.readPath hp, ha', HeapKnowledge.lengthOf_of_store hst hls' (hmax hm),
    by omega⟩

open HeapKnowledge in
/-- `y ≤ |x.p|` as the pass states it: a linear index fact over the value of
slot `y` and the length term at `x`'s path `p`. -/
def pathLowerBoundFact (y x : Nat) (p : List String) : IndexFact :=
  .linear (.le [(.value y, 1), ((HeapKnowledge.Term.now .length x p), -1)] 0)

/-- **`PathLowerBound` is the pass's path-term index fact.** -/
theorem pathLowerBound_iff {y x : Nat} {p : List String} {ρ : Env} {m : Nat} {s : IndexedHeap} :
    PathLowerBound y x p ρ m s ↔ (pathLowerBoundFact y x p).HoldsAt ε ρ s.h := by
  have e1 : HeapKnowledge.termValue ε ρ s.h (.value y) = HeapKnowledge.intValue (ρ y) := rfl
  have e2 : HeapKnowledge.termValue ε ρ s.h (HeapKnowledge.Term.now .length x p) =
      (HeapKnowledge.readPath s.h (ρ x) p).bind (HeapKnowledge.lengthOf s.h) := rfl
  simp only [PathLowerBound, pathLowerBoundFact, HeapKnowledge.IndexFact.HoldsAt, Linear.Fact.vars,
    Linear.Fact.Holds, Linear.Form.eval, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, HeapKnowledge.termValuation, e1, e2]
  constructor
  · rintro ⟨w, a, len, hw, ha, hl, hle⟩
    rw [ha, hw]
    simp only [Option.bind_some, hl, Option.isSome_some, Option.getD_some, true_and]
    omega
  · rintro ⟨⟨hy, hx⟩, hle⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hy
    obtain ⟨len, hl⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨w, hw, hl'⟩ := Option.bind_eq_some_iff.mp hl
    rw [ha, hl] at hle
    simp only [Option.getD_some] at hle
    exact ⟨w, a, len, hw, ha, hl', by omega⟩

/-- (Grow) at a rigid path for the pass's path-term fact. -/
theorem grow_path_fact {y x : Nat} {p : List String} {v : Val} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hp : StableAt x p v ρ m s) (hb : (pathLowerBoundFact y x p).HoldsAt ε ρ s.h) :
    Box growEffect.fp (fun ρ _ s => (pathLowerBoundFact y x p).HoldsAt ε ρ s.h) ρ m s :=
  fun s' ha => pathLowerBound_iff.mp (grow_path hp (pathLowerBound_iff.mpr hb) s' ha)

/-- `dense(x, k)`: the first `k` indices of `x`'s store are present. -/
def DenseAt (x k : Nat) : Assertion := fun ρ _ s => Dense x k ρ s.h

/-- **(Dense)** `dense(x, k) ⊢ □_{values: any, stores: grow} dense(x, k)`. -/
theorem dense {x k : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} (hd : DenseAt x k ρ m s) :
    Box growEffect.fp (DenseAt x k) ρ m s :=
  fun _ ha => stableDenseClosed_sound (by decide) hd ha.2

end Verification.TolerantFrames
