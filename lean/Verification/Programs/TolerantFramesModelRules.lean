import Verification.Programs.TolerantFramesModelTyped
import Verification.Programs.TolerantFramesModelLoop
import Verification.Programs.TolerantFramesElems

/-! # Tolerant frames: the note's remaining atoms and rules in the model

Each atom or rule of the note "Tolerant frames" not stated elsewhere, as a
theorem with the hypotheses the indexed model forces, or a counter-model
where the note's statement does not hold:

- (View): a linear fact whose current terms are slots' integers and
  typed-array lengths holds after every admissible transition where each
  view's length location is single-valued (`view_box`), which a type stating
  `viewLengthKey` stable gives (`viewStable_of_typed`); without it the length
  may change (`view_not_invariant`); an entry term reads the entry state,
  which no transition changes;
- (Init): every linear fact whose current terms are no string lengths
  survives every action of `{values: init, stores: keep}` (`init_box`), with
  no condition on its paths, its entry terms of every kind;
- Call: a callee's run is an action of its renamed regional effect at the
  caller's slots, its post holds, and the caller's facts it keeps are named
  at the result's fresh name (`call_rule`);
- Alloc: an allocated array is fresh, empty and apart from every older array
  whose cells are allocated (`alloc_post`); a later change of the fresh store
  at `any` can break that separation even though the store stays fresh
  (`apart_not_kept_fresh`);
- Seq-Eff: rebasing keeps each entry's change (`rebaseAll_labels`) and
  widens what it cannot rebase to every location (`rebase_elems`); the rule
  holds with class evidence at the entry (`seq_eff`);
- Fresh-Eff: a fresh store's entry in a step's effect covers no location of
  the entry heap (`fresh_eff`, `fresh_eff_bound`); its listed cells are not
  erased (`fresh_cells_not_erased`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations ControlFlow PointClaims
open ProgramTyping PositiveGraphs PositiveRules ExpressionEffects HeapExpressionRules

/-! ## (View) -/

/-- `w`'s view length is read at a location whose contract admits one value
(or `w` owns no such key and has no prototype): a fact of the world. -/
def ViewStable (w : Nat) : Assertion := fun ρ _ s =>
  ∃ fs cd o, ρ w = .objAt fs cd o ∧ Verification.StableAt s.W fs viewLengthKey

/-- A stable view's length reads the same after every admissible transition. -/
theorem viewLengthOf_kept {fs : List (PropKey × Nat)} {cd : CallCode} {o : Nat} {s s' : IndexedHeap}
    (hst : Verification.StableAt s.W fs viewLengthKey) (ha : Admissible s s') :
    HeapKnowledge.viewLengthOf s'.h (.objAt fs cd o) = HeapKnowledge.viewLengthOf s.h (.objAt fs cd o) := by
  unfold Verification.StableAt at hst
  cases hl : fs.lookup viewLengthKey with
  | none => simp [HeapKnowledge.viewLengthOf, hl]
  | some l =>
    rw [hl] at hst
    obtain ⟨c, value, hc, hcs⟩ := hst
    simp [HeapKnowledge.viewLengthOf, hl, s.stable_value hc hcs, ha.stable_value hc hcs]

theorem viewStable_invariant (w : Nat) : Invariant (ViewStable w) := by
  intro ρ m s s' ha ⟨fs, cd, o, hv, hst⟩
  refine ⟨fs, cd, o, hv, ?_⟩
  unfold Verification.StableAt at hst ⊢
  split at hst
  · rename_i l hl
    obtain ⟨c, value, hc, hcs⟩ := hst
    obtain ⟨hle, hc'⟩ := ha.lookup_ext hc
    exact ⟨_, value, hc', hcs.restrict hle⟩
  · exact hst

/-- **(View)**: a linear fact whose current terms are slots' integers and
stable views' lengths holds after every admissible transition: `a(view(w)) ⊢
□_⊤ a(view(w))`; its entry terms, of any kind and path, read the entry state
(`termValue_entry_invariant`). -/
theorem view_box {F : Linear.Fact HeapKnowledge.Term} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hv : ∀ t ∈ F.vars, t.atEntry = false →
      t.path = [] ∧ (t.kind = .value ∨ (t.kind = .view ∧ ViewStable t.slot ρ m s)))
    (hF : (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) :
    Box Footprints.Closed.top.fp (fun ρ _ s => (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) ρ m s := by
  intro s' ha
  have he : ∀ t ∈ F.vars, HeapKnowledge.termValue ε ρ s'.h t = HeapKnowledge.termValue ε ρ s.h t := by
    intro t ht
    obtain ⟨k, slot, p, e⟩ := t
    cases e
    case true => exact HeapKnowledge.termValue_entry_invariant rfl
    obtain ⟨hp, hk⟩ := hv _ ht rfl
    simp only at hp hk
    subst hp
    rcases hk with rfl | ⟨rfl, fs, cd, o, hw, hst⟩
    · rfl
    · simp only [HeapKnowledge.termValue_nil, HeapKnowledge.kindValue, hw]
      exact viewLengthOf_kept hst ha.1
  obtain ⟨hd, hh⟩ := hF
  refine ⟨fun t ht => by rw [he t ht]; exact hd t ht, ?_⟩
  refine (Linear.Fact.holds_congr fun t ht => ?_).mpr hh
  simp only [HeapKnowledge.termValuation, he t ht]

/-- A type stating `viewLengthKey` stable gives the view's stability. -/
theorem viewStable_of_typed {ι : Type} {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {w : Nat} {A : Ty ι} (he : EnvOk G Γ ρ s.n s.W) (hw : Γ[w]? = some A)
    (hs : stableField G A viewLengthKey = true) : ViewStable w ρ m s := by
  obtain ⟨flds, oid, hv, hst⟩ := stableField_at hs (he.2 w A hw)
  exact ⟨flds, .absent, oid, hv, hst⟩

/-- A typed array of length 1, its length at location 1. -/
def viewObj : Val := .objAt [(hostKey, 0), (viewLengthKey, 1)] .absent 2

theorem viewObj_length {b : UInt64} {n : Int} (hb : SafeIntegers.SafeInt b n) (h0 : 0 ≤ n) :
    HeapKnowledge.viewLengthOf [.nul, .num b, .nul] viewObj = some n := by
  have hl : SafeIntegers.safeIntOfBits b = some n := SafeIntegers.safeIntOfBits_complete hb
  have hne : (PropKey.str "[[viewLength]]" == PropKey.str "[[host]]") = false := by decide
  simp [HeapKnowledge.viewLengthOf, viewObj, List.lookup, hostKey, viewLengthKey, hne, hl, h0]

/-- **(View) needs the view's stability**: in a world whose locations admit
every value, a transition changes a typed array's length from 1 to 2. -/
theorem view_not_invariant :
    ¬ ∀ (ρ : Env) (m : Nat) (s : IndexedHeap), HeapKnowledge.viewLengthOf s.h (ρ 0) = some 1 →
      Box Footprints.Closed.top.fp (fun ρ _ s => HeapKnowledge.viewLengthOf s.h (ρ 0) = some 1) ρ m s := by
  intro hall
  have two : SafeIntegers.SafeInt (bitsOfNat 2) 2 := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
  let s₁ := anyState [.nul, .num oneBits, .nul] rfl (vals3 rfl rfl rfl)
  let s₂ := anyState [.nul, .num (bitsOfNat 2), .nul] rfl (vals3 rfl rfl rfl)
  have h₁ := viewObj_length oneBits_safe (by decide)
  have h₂ := viewObj_length two (by decide)
  have := hall (fun _ => viewObj) 0 s₁ h₁ s₂ (action_top anyState_admissible)
  simp only [s₂, anyState] at this
  rw [h₂] at this
  cases this

/-! ## (Init) -/

theorem initTerm_kept (t : HeapKnowledge.Term) (hk : t.atEntry = false → t.kind ≠ .strLength) :
    t.keptBy (HeapKnowledge.Changes.ofClosed initEffect) (fun _ _ => false) = true := by
  obtain ⟨k, slot, p, e⟩ := t
  cases e
  case true => simp [HeapKnowledge.Term.keptBy]
  have hk := hk rfl
  cases k <;> cases p <;>
    simp_all [HeapKnowledge.Term.keptBy, HeapKnowledge.Term.pathKeptBy, HeapKnowledge.Changes.ofClosed,
      initEffect, HeapKnowledge.Changes.keepsLength, Footprints.Change.le, Footprints.Change.rank,
      Footprints.Change.onStore]

/-- **(Init)**: a linear fact whose current terms are integers, lengths and
view lengths at any paths holds after every action of the initialisation
write's `{values: init, stores: keep}`; its entry terms are of any kind. The
note's side condition, paths through fields holding objects, is what a
defined path read already is. -/
theorem init_box {F : Linear.Fact HeapKnowledge.Term} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hk : ∀ t ∈ F.vars, t.atEntry = false → t.kind ≠ .strLength) (hF : (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) :
    Box initEffect.fp (fun ρ _ s => (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) ρ m s :=
  kept_box initEffect (by
    simp only [HeapKnowledge.IndexFact.keptBy, Bool.or_eq_true, List.all_eq_true]
    exact .inl fun t ht => initTerm_kept t (hk t ht)) hF

/-- (Init) for the length lower bound along a path. -/
theorem init_path {y x : Nat} {p : List String} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hb : PathLowerBound y x p ρ m s) : Box initEffect.fp (PathLowerBound y x p) ρ m s := by
  intro s' ha
  refine pathLowerBound_iff.mpr (init_box (ε := ⟨ρ, s.h⟩) (m := m) (F := .le [(.value y, 1), (⟨.length, x, p, false⟩, -1)] 0)
    (fun t ht _ => ?_) (pathLowerBound_iff.mp hb) s' ha)
  simp only [Linear.Fact.vars, List.map, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp [HeapKnowledge.Term.value]

/-! ## Call -/

/-- **The Call rule.** A callee graph checked from its entry assertion at the
callee's environment `ρc`, its normal exit post bounding the heap by a
regional effect `Φ` read at `ρc`; each callee position `i` holding the
caller's slot `σ i`. A run of the callee to its result `v`, with budget left,
is an action of `Φ[x⃗/p⃗]` (`Φ` renamed by `σ`) at the caller's environment;
the result is of the callee's type and the callee's post holds; every named
fact of the caller under `□_{Φ[x⃗/p⃗]}` at the entry holds at the exit,
the result named by a name `y` no fact mentions. -/
theorem call_rule {P : Program} {pre : Nat → Assertion} {Ξres Tres : Fam} {Qres Rres : Heap → Prop} {m : Nat}
    (hnodes : NodesChecked P pre Ξres Tres Qres Rres m) (hdown : AdminClosed pre m) {l : Nat}
    {ρc ρ : Env} {s : IndexedHeap} (hpre : pre l ρc m s) {Φ : Footprint} {σ : Nat → Nat}
    (hQ : ∀ h, Qres h → Post Φ ρc s.h h) (hσ : ∀ i, ρ (σ i) = ρc i)
    {S : List SinglePass.Atom} {η : Env} {y : Nat} (hy : ∀ a ∈ S, y ∉ a.names)
    (hR : Box (Φ.rename σ) (Named ε S η) ρ m s)
    {k : Nat} {h' : Heap} {v : Tm} (hrun : Transitions P k s.h (.at l ρc) h' (.done v)) (hk : k < s.n) :
    ∃ s' : IndexedHeap, Action (Φ.rename σ) ρ s s' ∧ s'.h = h' ∧ s'.n + k = s.n ∧ isVal v = true ∧
      Tres s'.n s'.W v ∧ Qres h' ∧ Named ε S (Env.set η y v) ρ m s' := by
  obtain ⟨s', ha, he, hn, hv, hT, hq⟩ := invocation_done hnodes hdown hpre hrun hk
  have hact : Action (Φ.rename σ) ρ s s' := ⟨ha, Post.rename hσ (he ▸ hQ h' hq)⟩
  exact ⟨s', hact, he, hn, hv, hT, hq, named_set v hy (hR s' hact)⟩

/-! ## Alloc -/

/-- The allocation of an empty array: one object whose store field holds the
empty store. -/
def allocTerm : Tm := .makeAt .absent [arrayStoreKey] [.arr []]

/-- The array the allocation steps to at a heap. -/
def allocated (h : Heap) : Val := .objAt [(arrayStoreKey, h.length)] .absent (h.length + 1)

theorem alloc_step (h : Heap) : Step h allocTerm (h ++ [.arr []] ++ [.nul]) (allocated h) :=
  .makeFields (by simp [isVal]) rfl

/-- **Alloc**: the allocated array is fresh against the heap it was
allocated in, has length 0, and is apart from every value whose store is
below that heap's length and lists only cells below it, at the heap after
the allocation. -/
theorem alloc_post (h : Heap) :
    FreshAt h.length (allocated h) ∧
      HeapKnowledge.lengthOf (h ++ [.arr []] ++ [.nul]) (allocated h) = some 0 ∧
      ∀ (u : Val) (sy : Nat) (ys : List (Option Nat)), storeOf u = some sy → h[sy]? = some (.arr ys) →
        HeapKnowledge.ElementsBelow h.length ys →
        HeapKnowledge.RegionsApart (h ++ [.arr []] ++ [.nul]) (allocated h) u := by
  have hst : storeOf (allocated h) = some h.length := by simp [storeOf, fieldsOf, allocated]
  have hget : (h ++ [.arr []] ++ [.nul])[h.length]? = some (.arr []) := by simp
  refine ⟨⟨_, hst, Nat.le_refl _⟩, HeapKnowledge.lengthOf_of_store hst hget (by decide), ?_⟩
  intro u sy ys hsy hys hbelow
  have hlt : sy < h.length := (List.getElem?_eq_some_iff.mp hys).1
  exact alloc_apart hst hget (Nat.le_refl _) (fun _ hm => by simp at hm) hsy
    (by rw [List.append_assoc, List.getElem?_append_left hlt]; exact hys) hlt hbelow

/-- A world-free counter-model: the fresh array `x` (store at location 2)
and `y` (store at 0, listing cell 1). -/
def apartEnv : Env := fun i => if i = 0 then .objAt [(arrayStoreKey, 2)] .absent 0
  else .objAt [(arrayStoreKey, 0)] .absent 0

theorem apartEnv_store₀ : storeOf (apartEnv 0) = some 2 := by
  simp [apartEnv, storeOf, fieldsOf]

theorem apartEnv_store₁ : storeOf (apartEnv 1) = some 0 := by
  simp [apartEnv, storeOf, fieldsOf]

/-- **Alloc's separations are not kept by freshness**: `x` fresh against the
mark 2, `y`'s cells allocated, `apart(x, y)`, and an action changing only
`x`'s store, at `any`, after which `x` lists `y`'s cell. -/
theorem apart_not_kept_fresh :
    ¬ ∀ (ρ : Env) (m : Nat) (s : IndexedHeap), Fresh 0 ρ m s → RootCells 1 ρ m s → ApartAt 0 1 ρ m s →
      Box [(.field 0 arrayStoreKey, .any)] (ApartAt 0 1) ρ m s := by
  intro hall
  let s₁ := anyState [.arr [some 1], .nul, .arr []] rfl (vals3 rfl rfl rfl)
  let s₂ := anyState [.arr [some 1], .nul, .arr [some 1]] rfl (vals3 rfl rfl rfl)
  have hfresh : Fresh 0 apartEnv 2 s₁ := ⟨2, apartEnv_store₀, Nat.le_refl _⟩
  have hcells : RootCells 1 apartEnv 2 s₁ := by
    intro st ls hst hv
    rw [apartEnv_store₁] at hst; cases hst
    simp only [s₁, anyState] at hv
    simp at hv; subst hv
    intro l hl; simp at hl; subst hl; simp [s₁, anyState]
  have hap : ApartAt 0 1 apartEnv 2 s₁ := by
    refine ⟨some 2, [], some 0, [some 1], .inr ⟨2, rfl, apartEnv_store₀, rfl⟩,
      .inr ⟨0, rfl, apartEnv_store₁, rfl⟩, ?_⟩
    intro l hl l' hl' he
    subst he
    simp only [HeapKnowledge.InRegion, Option.some.injEq, List.mem_singleton, List.not_mem_nil, or_false] at hl hl'
    omega
  have hact : Action [(.field 0 arrayStoreKey, .any)] apartEnv s₁ s₂ := by
    refine ⟨anyState_admissible, by simp [s₁, s₂, anyState], fun l v hl => ?_⟩
    rcases l with _ | _ | _ | l <;> simp [s₁, s₂, anyState] at hl ⊢
    · exact .inl hl
    · exact .inl hl
    · exact .inr (by simp [Region.mem, apartEnv, fieldsOf, Footprints.Change.Holds])
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := hall apartEnv 2 s₁ hfresh hcells hap s₂ hact
  have hxr : xs = [some 1] := by
    rcases hx with ⟨-, hv⟩ | ⟨st, -, hst, hv⟩
    · simp [apartEnv] at hv
    · rw [apartEnv_store₀] at hst; cases hst
      simp [s₂, anyState] at hv; exact hv.symm
  have hyr : ys = [some 1] := by
    rcases hy with ⟨-, hv⟩ | ⟨st, -, hst, hv⟩
    · simp [apartEnv] at hv
    · rw [apartEnv_store₁] at hst; cases hst
      simp [s₂, anyState] at hv; exact hv.symm
  subst hxr hyr
  exact hab 1 (.inr (by simp)) 1 (.inr (by simp)) rfl

/-! ## Seq-Eff -/

/-- **Rebasing keeps change labels**: every entry of a rebased effect has the
change of an entry of the step's effect. -/
theorem rebaseAll_labels {ev : RebaseEvidence} {Ψ : Footprint} {e : Region × Change}
    (he : e ∈ rebaseAll ev Ψ) : ∃ e' ∈ Ψ, e.2 = e'.2 := by
  obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp he
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
  exact ⟨e', he', rfl⟩

/-- What rebasing cannot place, it widens to every location: a step's
element cells, whatever their class. -/
theorem rebase_elems (ev : RebaseEvidence) (x : Nat) : rebase ev (.elems x) = [.all] := rfl

/-- **Seq-Eff**: the entry effect so far, a step's effect at its own
positions, its rebasing to the entry, and `Φ ∪ Ψ' ⊑_cl Φ` with the class
evidence `cl` holding at the entry heap give the entry effect after the step. -/
theorem seq_eff {Φ Ψ : Footprint} {cl : ClassEvidence} {ρ₀ σ : Env} {ev : RebaseEvidence}
    {sI s₀ s : IndexedHeap} (hp : Action Φ ρ₀ sI s₀) (hn : Action Ψ σ s₀ s) (hk : RebaseOk ev σ ρ₀ sI.h s₀.h)
    (hle : Footprint.le cl (Φ ++ rebaseAll ev Ψ) Φ = true) (hc : ClassOk cl ρ₀ sI.h) : Action Φ ρ₀ sI s :=
  action_compose_at hp hn hk hle hc

/-! ## Fresh-Eff -/

/-- **Fresh-Eff**: a step's effect with an entry for `x`'s store, `x`'s store
allocated at or after `b`: on every location below `b`, the step is within
the rest of its effect. -/
theorem fresh_eff {Φ : Footprint} {x : Nat} {δ : Change} {ρ : Env} {h h' : Heap} {b : Nat}
    (hp : Post (Φ ++ [(.field x arrayStoreKey, δ)]) ρ h h') (hf : FreshAt b (ρ x)) :
    ∀ l v, l < b → h[l]? = some v → ∃ v', h'[l]? = some v' ∧ Allowed Φ ρ h l v v' := by
  intro l v hl hv
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with h | ⟨e, he, hm, hh⟩
  · exact .inl h
  · rcases List.mem_append.mp he with he | he
    · exact .inr ⟨e, he, hm, hh⟩
    · simp only [List.mem_singleton] at he
      subst he
      obtain ⟨st, hst, hle⟩ := hf
      simp only [Region.mem, beq_iff_eq] at hm
      simp only [storeOf] at hst
      rw [hst] at hm
      cases hm
      omega

/-- Fresh-Eff for the invocation's bound: a closed bound so far from the
entry heap `h₀`, and a step within the bound beside an entry for a store
allocated during the invocation, keep the bound from `h₀`. -/
theorem fresh_eff_bound {c : Footprints.Closed} {x : Nat} {δ : Change} {ρ : Env} {h₀ h h' : Heap}
    (hI : c.Holds h₀ h) (hp : Post (c.fp ++ [(.field x arrayStoreKey, δ)]) ρ h h')
    (hf : FreshAt h₀.length (ρ x)) : c.Holds h₀ h' := by
  refine bound_step_fresh hI ⟨hp.1, fun l v hl hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := fresh_eff hp hf l v hl hv
  exact ⟨v', hv', (Footprints.Closed.allowed_iff hv).mp ha⟩

/-- **A fresh store's cells are not erased**: a store allocated at 2 may list
the old cell 1, and a change of its cells changes that old location. -/
theorem fresh_cells_not_erased :
    ¬ ∀ (ρ : Env) (h h' : Heap) (b : Nat), Post [(.elems 0, .any)] ρ h h' → FreshAt b (ρ 0) →
      ∀ l v, l < b → h[l]? = some v → h'[l]? = some v := by
  intro hall
  let ρ : Env := fun _ => .objAt [(arrayStoreKey, 2)] .absent 0
  have hp : Post [(.elems 0, .any)] ρ [.nul, .nul, .arr [some 1]] [.nul, .tru, .arr [some 1]] := by
    refine ⟨by simp, fun l v hl => ?_⟩
    rcases l with _ | _ | _ | l <;> simp at hl ⊢
    · exact .inl hl
    · refine .inr ?_
      simp [Region.mem, storeElems, ρ, fieldsOf, Footprints.Change.Holds]
    · exact .inl hl
  have := hall ρ _ _ 2 hp ⟨2, by simp [storeOf, fieldsOf, ρ], Nat.le_refl _⟩ 1 .nul (by omega) rfl
  simp at this

end Verification.TolerantFrames
