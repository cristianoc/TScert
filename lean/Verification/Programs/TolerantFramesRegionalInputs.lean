import Verification.Programs.SinglePass
import Verification.Programs.TolerantFramesDriverSummaries

/-! # Regional incoming tables along a visit -/
namespace Verification.TolerantFrames
open Verification SinglePass ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open ProgramTyping LabelStore GraphCode
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- Type checking leaves the regional input table intact. -/
theorem exitTypes_regionIn {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {out : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {store : SinglePass.Store} {pushed handler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {a b : SinglePass.ExitsDone ι G} {et : SinglePass.ExitTyped ι}
    (h : SinglePass.exitTypes G I env l en sd out t tc Γ names store pushed handler observed first diff a = .ok (b, et)) :
    b.regionIn = a.regionIn := by
  unfold SinglePass.exitTypes at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The head check leaves the regional input table intact. -/
theorem headExit_regionIn {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {store : SinglePass.Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {a b : SinglePass.ExitsDone ι G}
    (h : SinglePass.headExit G I env l t tc Γ names store pushed vacuous carried a = .ok b) :
    b.regionIn = a.regionIn := by
  unfold SinglePass.headExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- The assertion check leaves the regional input table intact. -/
theorem assertionExit_regionIn {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (ProgramTyping.Ty ι))} {names : List Nat} {store : SinglePass.Store} {pushed vacuous : Bool}
    {observed : Option BranchRefinement.Observation} {a b : SinglePass.ExitsDone ι G}
    (h : SinglePass.assertionExit G env l t tc Γe names store pushed observed vacuous a = .ok b) :
    b.regionIn = a.regionIn := by
  unfold SinglePass.assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals cases h <;> rfl

/-- A successful exit preserves the complete regional input table. -/
theorem exitStep_regionIn {env : WalkEnv ι G I} {l : Nat} {en : Entered ι}
    {sd : StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    {a b : ExitsDone ι G} {e : Exit × Nat}
    (h : exitStep G I env l en sd ys out a e = .ok b) : b.regionIn = a.regionIn := by
  unfold exitStep at h
  extract_lets ex first node c width entry st t pushed observed handler pushedNames tr a0 Γ names store unsatΓ vacuous Γe read Γr at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets diff u a2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i a1 et
  simp only [typed] at ht
  have hp : a2.regionIn = a.regionIn := by
    dsimp only [a2, a0]
    split <;> split <;> rfl
  have hp1 : a1.regionIn = a.regionIn := by
    split at ht
    · cases ht; exact hp
    · exact (exitTypes_regionIn ht).trans hp
  extract_lets freshImpl record at h
  split at h
  · simp only [Except.map] at h
    split at h
    · cases h
    · rename_i a3 hhead
      cases h
      exact (headExit_regionIn hhead).trans hp1
  · split at h
    · cases h
    rename_i a3 ha
    split at h
    cases h
    exact (assertionExit_regionIn ha).trans hp1

/-- Every exit in the fold preserves the regional input table. -/
theorem exitsFold_regionIn {env : WalkEnv ι G I} {l : Nat} {en : Entered ι}
    {sd : StepDone ι G} {ys : List (PromiseCalls.Yield ι)} {out : Thunk HeapKnowledge.Knowledge}
    (es : List (Exit × Nat)) (a b : ExitsDone ι G)
    (h : es.foldlM (exitStep G I env l en sd ys out) a = .ok b) : b.regionIn = a.regionIn := by
  induction es generalizing a with
  | nil => cases h; rfl
  | cons e es ih =>
    rw [List.foldlM_cons] at h
    cases he : exitStep G I env l en sd ys out a e with
    | error stop => rw [he] at h; cases h
    | ok a' =>
      rw [he] at h
      exact (ih a' h).trans (exitStep_regionIn he)


/-- Adding one predecessor retains every incoming regional state. -/
theorem regionIn_modify_mono (a : Array (List RegionState)) (l t : Nat) (r e : RegionState)
    (he : e ∈ a[t]!) : e ∈ (a.modify l (r :: ·))[t]! := by
  by_cases hlt : l = t
  · subst t
    cases h : a[l]? with
    | none => simpa [getElem!_def, h, Array.getElem?_modify] using he
    | some xs =>
      simpa [getElem!_def, Array.getElem?_modify, h] using
        (List.mem_cons_of_mem r (show e ∈ xs by simpa [getElem!_def, h] using he))
  · simpa only [getElem!_def, Array.getElem?_modify, if_neg hlt] using he

/-- The regional target fold only adds incoming states, at its targets. -/
theorem regionalFold_inputs (heads : Nat → Bool) (given : Nat → RegionState)
    (established : Target → Bool → RegionState) (ts : List (Target × Bool))
    (acc : List (Nat × RegionState) × Array (List RegionState)) :
    let out := ts.foldl (fun acc (t, h) =>
      if heads t.label then (acc.1 ++ [(t.label, given t.label)], acc.2)
      else (acc.1 ++ [(t.label, established t h)], acc.2.modify t.label (established t h :: ·))) acc
    (∀ (t : Nat) (e : RegionState), e ∈ acc.2[t]! → e ∈ out.2[t]!) ∧
    (∀ (t : Nat), (∀ x ∈ ts, x.1.label ≠ t) → out.2[t]? = acc.2[t]?) := by
  induction ts generalizing acc with
  | nil => exact ⟨fun _ _ h => h, fun _ _ => rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · let next := (acc.1 ++ [(x.1.label, given x.1.label)], acc.2)
      exact ⟨(ih next).1, fun t ht => (ih next).2 t (fun y hy => ht y (List.mem_cons_of_mem _ hy))⟩
    · refine ⟨fun t e he => (ih _).1 t e (regionIn_modify_mono _ _ _ _ _ he), ?_⟩
      intro t ht
      rw [(ih _).2 t (fun y hy => ht y (List.mem_cons_of_mem _ hy))]
      simp only [Array.getElem?_modify, if_neg (ht x (List.mem_cons_self ..))]

/-- The target fold appends precisely one sparse-table entry per target. -/
theorem regionalFold_entries (heads : Nat → Bool) (given : Nat → RegionState)
    (established : Target → Bool → RegionState) (ts : List (Target × Bool))
    (acc : List (Nat × RegionState) × Array (List RegionState)) :
    (ts.foldl (fun acc (t, h) =>
      if heads t.label then (acc.1 ++ [(t.label, given t.label)], acc.2)
      else (acc.1 ++ [(t.label, established t h)], acc.2.modify t.label (established t h :: ·))) acc).1 =
    acc.1 ++ ts.map (fun (t, h) => (t.label, if heads t.label then given t.label else established t h)) := by
  induction ts generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    split <;> rw [ih] <;> simp_all [List.append_assoc]

/-- Entries for other labels preserve a sparse table's entry at `l`. -/
theorem sparseFold_frame {α : Type} (xs : List (Nat × α)) (table : List α) (l : Nat)
    (hne : ∀ x ∈ xs, x.1 ≠ l) :
    (xs.foldl (fun acc (j, x) => acc.set j x) table)[l]? = table[l]? := by
  induction xs generalizing table with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih _ (fun y hy => hne y (List.mem_cons_of_mem _ hy))]
    simp only [List.getElem?_set, if_neg (hne x (List.mem_cons_self ..))]

/-- A sparse table keeps its initial own entry when no target shares the label. -/
theorem sparse_own {α : Type} (n l : Nat) (empty value : α) (xs : List (Nat × α))
    (hl : l < n) (hne : ∀ x ∈ xs, x.1 ≠ l) :
    (sparse n empty ((l, value) :: xs))[l]? = some value := by
  rw [sparse, List.foldl_cons, sparseFold_frame xs _ l hne]
  simp [hl]

/-- The regional target fold preserves the incoming array's allocation. -/
theorem regionalFold_size (heads : Nat → Bool) (given : Nat → RegionState)
    (established : Target → Bool → RegionState) (ts : List (Target × Bool))
    (acc : List (Nat × RegionState) × Array (List RegionState)) :
    (ts.foldl (fun acc (t, h) =>
      if heads t.label then (acc.1 ++ [(t.label, given t.label)], acc.2)
      else (acc.1 ++ [(t.label, established t h)], acc.2.modify t.label (established t h :: ·))) acc).2.size = acc.2.size := by
  induction ts generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split <;> rw [ih] <;> simp

/-- Regional checking preserves the input array's size. -/
theorem regionalAt_size {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) :
    done.regionIn.size = incoming.size := by
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere cEv t0 F C Fs origins pushes outR outF outC outFs established targets n at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hi := regionalFold_size (fun t => env.isHead[t]!)
      (fun t => ((rg.heads[t]?).join).getD {}) established targets
      ([(l, { here with cells := C, fields := Fs })], incoming)
    simp_all only

/-- Exits preserve the regional input array's allocation. -/
theorem visitExits_regionSize {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) : ex.regionIn.size = σ.regionIn.size := by
  unfold visitExits at h
  cases hr : env.regional with
  | none =>
    simp only [hr] at h
    rw [exitsFold_regionIn _ _ _ h]
  | some rg =>
    simp only [hr] at h
    cases hd : regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 σ.regionIn with
    | error why => simp [hd, Except.map] at h
    | ok done =>
      simp only [hd, Except.map] at h
      rw [exitsFold_regionIn _ _ _ h]
      exact regionalAt_size hd

/-- A successful regional check retains incoming states and changes only
its successors' and handler's entries. -/
theorem regionalAt_inputs {env : WalkEnv ι G I} {l : Nat} {en : Entered ι} {sd : StepDone ι G}
    {rg : Regional} {a : Answered G} {incoming : Array (List RegionState)} {done : RegionalDone ι}
    (h : regionalAt G I env l en sd rg a incoming = .ok done) :
    (∀ (t : Nat) (e : RegionState), e ∈ incoming[t]! → e ∈ done.regionIn[t]!) ∧
    (∀ t, (∀ x ∈ successors env.nodes[l]!.continuation, x.label ≠ t) →
      (∀ x, env.nodes[l]!.handler = some x → x.label ≠ t) → done.regionIn[t]? = incoming[t]?) := by
  unfold regionalAt at h
  extract_lets node c width st here sums ordinaryEv kHere cEv t0 F C Fs origins pushes outR outF outC outFs established targets n at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | cases h | skip
  all_goals
    have hi := regionalFold_inputs (fun t => env.isHead[t]!)
      (fun t => ((rg.heads[t]?).join).getD {}) established targets
      ([(l, { here with cells := C, fields := Fs })], incoming)
    simp_all only
    refine ⟨fun _ _ _ => trivial, fun t hs hh => hi.2 t ?_⟩
    intro x hx
    simp only [targets, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact hs y hy
    · exact hh y (by simpa using hy)

/-- The exits carry precisely the incoming table computed before their fold. -/
theorem visitExits_inputs {env : WalkEnv ι G I} {σ : WalkState ι G} {l : Nat}
    {en : Entered ι} {sd : StepDone ι G} {ex : ExitsDone ι G}
    (h : visitExits G I env σ l en sd = .ok ex) :
    (∀ (t : Nat) (e : RegionState), e ∈ σ.regionIn[t]! → e ∈ ex.regionIn[t]!) ∧
    (∀ t, (∀ x ∈ successors env.nodes[l]!.continuation, x.label ≠ t) →
      (∀ x, env.nodes[l]!.handler = some x → x.label ≠ t) → ex.regionIn[t]? = σ.regionIn[t]?) := by
  unfold visitExits at h
  cases hr : env.regional with
  | none =>
    simp only [hr] at h
    have he := exitsFold_regionIn _ _ _ h
    rw [he]
    exact ⟨fun _ _ h => h, fun _ _ _ => rfl⟩
  | some rg =>
    simp only [hr] at h
    cases hd : regionalAt G I env l en sd rg (exitsYields G I env l en sd).2 σ.regionIn with
    | error why => simp [hd, Except.map] at h
    | ok done =>
      simp only [hd, Except.map] at h
      have he := exitsFold_regionIn _ _ _ h
      rw [he]
      exact regionalAt_inputs hd

end Verification.TolerantFrames
