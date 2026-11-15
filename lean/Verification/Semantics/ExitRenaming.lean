import Verification.Semantics.ExitConjunction
import Verification.Semantics.AssertionScopes

/-! # Binding: a schema at a call that saves its first actuals

Binding (the note *Tolerant frames*, §6, rule Call at a bound function)
saves a receiver and the first `k` actuals; the bound call passes the rest.
A schema of the longer call is a schema of the bound call where it names no
saved value: each entry position `i > k` of the longer call is position
`i - k` of the bound call (`dropBefore`), each exit position past the result
likewise (`dropAfter`), and the result stays. `Exits.drop k` substitutes
these positions in every frame and every formula and refuses a schema
naming a saved position (`Exits.drop`); its exits at the bound call are
exactly the schema's at the longer call (`Exits.exitPost_drop`).

The substitution is stated once for every two-state formula
(`FormulaF.renameHolds`): renamed by partial maps of entry and exit
positions, a formula holds at a two-state interpretation exactly where the
original holds at one agreeing with it on every renamed position
(`Renaming.Agrees`). A transport's equations at the saved positions are
those of a call (`TwoState.Shifted`) and hold at every call; it is
substituted where its default image is the next exit slot and no
replacement names a saved position. -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge Parity TolerantFrames

/-! ## Renaming positions -/

/-- **A renaming of positions**: entry positions by `before`, exit positions
by `after`, each partial. -/
structure Renaming where
  before : Nat → Option Nat
  after : Nat → Option Nat

/-- The map of a phase's positions. -/
def Renaming.at (R : Renaming) : Phase → Nat → Option Nat
  | .before => R.before
  | .after => R.after

/-- **Two two-state interpretations agreeing on a renaming**: `s'` reads at
each renamed position what `s` reads at the original, at the same states and
mark. -/
structure Renaming.Agrees (R : Renaming) (s s' : TwoState) : Prop where
  before : ∀ i j, R.before i = some j → s'.beforeEnv j = s.beforeEnv i
  after : ∀ i j, R.after i = some j → s'.afterEnv j = s.afterEnv i
  mark : s'.mark = s.mark
  pre : s'.before = s.before
  post : s'.after = s.after

theorem Renaming.Agrees.env {R : Renaming} {s s' : TwoState} (h : R.Agrees s s') (p : Phase) :
    ∀ i j, R.at p i = some j → s'.env p j = s.env p i := by
  cases p
  · exact h.before
  · exact h.after

theorem Renaming.Agrees.state {R : Renaming} {s s' : TwoState} (h : R.Agrees s s') (p : Phase) :
    s'.state p = s.state p := by
  cases p
  · exact h.pre
  · exact h.post

/-- A path with its root renamed. -/
def renamePath (f : Nat → Option Nat) (p : Path) : Option Path := (f p.root).map fun j => ⟨j, p.fields⟩

theorem read_renamePath {f : Nat → Option Nat} {p p' : Path} (hp : renamePath f p = some p') {η η' : Env}
    (he : ∀ i j, f i = some j → η' j = η i) (h : Heap) : p'.read η' h = p.read η h := by
  simp only [renamePath, Option.map_eq_some_iff] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  simp only [Path.read, he _ _ hj]

/-- A witness with its root renamed. -/
def renameWitness (f : Nat → Option Nat) : Witness → Option Witness
  | .path p => (renamePath f p).map .path
  | .literal v => some (.literal v)

theorem value_renameWitness {f : Nat → Option Nat} {w w' : Witness} (hw : renameWitness f w = some w') {η η' : Env}
    (he : ∀ i j, f i = some j → η' j = η i) (h : Heap) : w'.value η' h = w.value η h := by
  cases w with
  | path p =>
    simp only [renameWitness, Option.map_eq_some_iff] at hw
    obtain ⟨p', hp, rfl⟩ := hw
    exact read_renamePath hp he h
  | literal v => simp only [renameWitness, Option.some.injEq] at hw; subst hw; rfl

theorem heapFree_renameWitness {f : Nat → Option Nat} {w w' : Witness} (hw : renameWitness f w = some w') :
    w'.heapFree = w.heapFree := by
  cases w with
  | path p =>
    simp only [renameWitness, renamePath, Option.map_map, Option.map_eq_some_iff] at hw
    obtain ⟨j, -, rfl⟩ := hw
    rfl
  | literal v => simp only [renameWitness, Option.some.injEq] at hw; subst hw; rfl

/-- A term's slot renamed, in whichever namespace it reads. -/
def termRename (f : Nat → Option Nat) (t : Term) : Option Term :=
  t.reroot (fun s => (f s).map (·, [])) (fun s => (f s).map (·, []))

theorem termAt_termRename {f : Nat → Option Nat} {t t' : Term} (ht : termRename f t = some t') {η η' : Env}
    (he : ∀ i j, f i = some j → η' j = η i) (h : Heap) : termAt η' h t' = termAt η h t := by
  simp only [termRename, Term.reroot] at ht
  split at ht <;>
  · simp only [Option.map_map, Option.map_eq_some_iff] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    simp only [termAt, Function.comp, List.nil_append, he _ _ hj]

/-- A two-state variable renamed in its phase. -/
def renameStepVar (R : Renaming) : StepVar → Option StepVar
  | .before t => (termRename R.before t).map .before
  | .after t => (termRename R.after t).map .after

theorem value_renameStepVar {R : Renaming} {s s' : TwoState} (hs : R.Agrees s s') {x x' : StepVar}
    (hx : renameStepVar R x = some x') : stepValue s' x' = stepValue s x := by
  cases x with
  | before t =>
    simp only [renameStepVar, Option.map_eq_some_iff] at hx
    obtain ⟨t', ht, rfl⟩ := hx
    simp only [stepValue, hs.pre]
    exact termAt_termRename ht hs.before _
  | after t =>
    simp only [renameStepVar, Option.map_eq_some_iff] at hx
    obtain ⟨t', ht, rfl⟩ := hx
    simp only [stepValue, hs.post]
    exact termAt_termRename ht hs.after _

/-- An effect with its roots renamed, where every root is renamed. -/
def renameFootprint (f : Nat → Option Nat) (Φ : Footprint) : Option Footprint :=
  if Φ.all (fun e => (regionRoots e.1).all fun x => (f x).isSome) then
    some (Footprints.Footprint.rename (fun x => (f x).getD 0) Φ) else none

theorem action_renameFootprint {f : Nat → Option Nat} {Φ Φ' : Footprint} (hΦ : renameFootprint f Φ = some Φ')
    {η η' : Env} (he : ∀ i j, f i = some j → η' j = η i) {s s' : IndexedHeap} :
    EffectAction Φ' η' s s' ↔ EffectAction Φ η s s' := by
  unfold renameFootprint at hΦ
  split at hΦ
  · rename_i hall
    cases hΦ
    rw [EffectAction.rename_iff]
    refine EffectAction.congr_roots fun x ⟨e, he', hx⟩ => ?_
    have hs := List.all_eq_true.mp (List.all_eq_true.mp hall e he') x hx
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
    simp only [hj, Option.getD_some]
    exact he x j hj
  · cases hΦ

/-! ## Operation posts -/

private theorem bind_some {α β : Type} {o : Option α} {g : α → Option β} {b : β} (h : o.bind g = some b) :
    ∃ a, o = some a ∧ g a = some b := Option.bind_eq_some_iff.mp h

/-- **An operation post with its positions renamed**, each read in its phase:
the push's arguments by `seq`. -/
def renameOperation {S S' : Type} (R : Renaming) (seq : S → Option S') :
    OperationPostF S → Option (OperationPostF S')
  | .arith op l r y => do pure (.arith op (← renameWitness R.after l) (← renameWitness R.after r) (← renamePath R.after y))
  | .stringLength x y => do pure (.stringLength (← renamePath R.after x) (← renamePath R.after y))
  | .stringRead x i y => do pure (.stringRead (← renamePath R.after x) (← renameWitness R.after i) (← renamePath R.after y))
  | .lengthsKept x x' => do pure (.lengthsKept (← R.before x) (← R.after x'))
  | .boundedWrite x i x' => do pure (.boundedWrite (← R.before x) (← R.before i) (← R.after x'))
  | .push x x' args => do pure (.push (← R.before x) (← R.after x') (← seq args))
  | .fact p l F => do pure (.fact p 0 (← F.reframe (fun i => R.at p (i + l)) R.before))
  | .freshStore x => (R.after x).map .freshStore
  | .freshObject x => (R.after x).map .freshObject
  | .elementsWhen x v y P => do pure (.elementsWhen (← R.after x) v (← R.after y) P)
  | .storeExtends x => (R.before x).map .storeExtends
  | .viewWrite x i v g => do pure (.viewWrite (← R.before x) (← R.before i) (← R.before v) g)

/-- **A renamed operation post holds where the original does**, at agreeing
interpretations, its push arguments denoting the same values. -/
theorem holds_renameOperation {R : Renaming} {s s' : TwoState} (hs : R.Agrees s s') {S S' : Type}
    {iS : S → List Witness} {iS' : S' → List Witness} {seq : S → Option S'}
    (hseq : ∀ a a', seq a = some a' →
      (iS' a').mapM (·.value s'.beforeEnv s'.before.h) = (iS a).mapM (·.value s.beforeEnv s.before.h))
    {q : OperationPostF S} {q' : OperationPostF S'}
    (hq : renameOperation R seq q = some q') : (q'.map iS').Holds s' ↔ (q.map iS).Holds s := by
  have hb := hs.before
  have ha := hs.after
  cases q with
  | arith op l r y =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨l', hl, hq⟩ := bind_some hq; obtain ⟨r', hr, hq⟩ := bind_some hq
    obtain ⟨y', hy, hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.post, value_renameWitness hl ha, value_renameWitness hr ha,
      read_renamePath hy ha]
  | stringLength x y =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨x', hx, hq⟩ := bind_some hq; obtain ⟨y', hy, hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.post, read_renamePath hx ha, read_renamePath hy ha]
  | stringRead x i y =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨x', hx, hq⟩ := bind_some hq; obtain ⟨i', hi, hq⟩ := bind_some hq
    obtain ⟨y', hy, hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.post, read_renamePath hx ha, value_renameWitness hi ha,
      read_renamePath hy ha]
  | lengthsKept x x' =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨a, hx, hq⟩ := bind_some hq; obtain ⟨b, hx', hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.pre, hs.post, hb _ _ hx, ha _ _ hx']
  | boundedWrite x i x' =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨a, hx, hq⟩ := bind_some hq; obtain ⟨b, hi, hq⟩ := bind_some hq
    obtain ⟨c, hx', hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.pre, hs.post, hb _ _ hx, hb _ _ hi, ha _ _ hx']
  | push x x' args =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨a, hx, hq⟩ := bind_some hq; obtain ⟨b, hx', hq⟩ := bind_some hq
    obtain ⟨c, hc, hq⟩ := bind_some hq; cases hq
    have hc' := hseq _ _ hc
    rw [hs.pre] at hc'
    simp only [OperationPostF.map, OperationPostF.Holds, hc', hs.pre, hs.post, hb _ _ hx, ha _ _ hx']
  | fact p l F =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨F', hF, hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, Nat.add_zero, hs.state p]
    refine IndexFact.holdsAt_reframe hF (fun i _ t ht => hs.env p _ _ ht) (by simp [hs.pre]) ?_
    exact fun i j hj => hb i j hj
  | freshStore x =>
    simp only [renameOperation, Option.map_eq_some_iff] at hq
    obtain ⟨a, hx, rfl⟩ := hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.pre, ha _ _ hx]
  | freshObject x =>
    simp only [renameOperation, Option.map_eq_some_iff] at hq
    obtain ⟨a, hx, rfl⟩ := hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.pre, ha _ _ hx]
  | elementsWhen x v y P =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨a, hx, hq⟩ := bind_some hq; obtain ⟨b, hy, hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.post, ha _ _ hx, ha _ _ hy]
  | storeExtends x =>
    simp only [renameOperation, Option.map_eq_some_iff] at hq
    obtain ⟨a, hx, rfl⟩ := hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.pre, hs.post, hb _ _ hx]
  | viewWrite x i v g =>
    simp only [renameOperation, Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨a, hx, hq⟩ := bind_some hq; obtain ⟨b, hi, hq⟩ := bind_some hq
    obtain ⟨c, hv, hq⟩ := bind_some hq; cases hq
    simp only [OperationPostF.map, OperationPostF.Holds, hs.pre, hs.post, hb _ _ hx, hb _ _ hi, hb _ _ hv]

/-! ## Formulas -/

/-- **A two-state formula with its positions renamed**, its appends'
arguments by `seq` and its transports by `tr`; an arena node is refused. -/
def renameFormula {S S' T T' : Type} (R : Renaming) (seq : S → Option S') (tr : T → Option T') :
    FormulaF S T → Option (FormulaF S' T')
  | .at .. => none
  | .transition Φ => (renameFootprint R.before Φ).map .transition
  | .operation q => (renameOperation R seq q).map .operation
  | .linear F => (F.mapVars (renameStepVar R)).map .linear
  | .defined v => (renameStepVar R v).map .defined
  | .transport θ => (tr θ).map .transport
  | .and F G => do pure (.and (← renameFormula R seq tr F) (← renameFormula R seq tr G))
  | .truth => some .truth
  | .falsity => some .falsity

/-- **Substitution of positions in a two-state formula** (proved, every
formula): renamed, interpreted at a two-state interpretation agreeing with
another on the renaming, it holds exactly where the original holds there,
where the renamed appends' arguments denote the same values and the renamed
transports hold alike. -/
theorem holds_renameFormula {R : Renaming} {s s' : TwoState} (hs : R.Agrees s s') {S S' T T' : Type}
    {iS : S → List Witness} {iS' : S' → List Witness} {iT : T → Substitution} {iT' : T' → Substitution}
    {seq : S → Option S'} {tr : T → Option T'}
    (hseq : ∀ a a', seq a = some a' →
      (iS' a').mapM (·.value s'.beforeEnv s'.before.h) = (iS a).mapM (·.value s.beforeEnv s.before.h))
    (htr : ∀ θ θ', tr θ = some θ' →
      ((iT' θ').HoldsAt s'.beforeEnv s'.afterEnv s'.after ↔ (iT θ).HoldsAt s.beforeEnv s.afterEnv s.after))
    (arena : AssertionArena) :
    ∀ {F : FormulaF S T} {F' : FormulaF S' T'}, renameFormula R seq tr F = some F' →
      (Holds arena s' (F'.map iS' iT') ↔ Holds arena s (F.map iS iT))
  | .at .., _, h => by cases h
  | .transition Φ, F', h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨Φ', hΦ, rfl⟩ := h
    simp only [FormulaF.map, Holds, hs.pre, hs.post]
    exact action_renameFootprint hΦ hs.before
  | .operation q, F', h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨q', hq, rfl⟩ := h
    exact holds_renameOperation hs hseq hq
  | .linear F, F', h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨G, hG, rfl⟩ := h
    exact factAt_mapVars hG fun x _ y hy => value_renameStepVar hs hy
  | .defined v, F', h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨v', hv, rfl⟩ := h
    simp only [FormulaF.map, Holds, value_renameStepVar hs hv]
  | .transport θ, F', h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨θ', hθ, rfl⟩ := h
    exact htr θ θ' hθ
  | .and F G, F', h => by
    simp only [renameFormula, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨A, hA, h⟩ := bind_some h
    obtain ⟨B, hB, h⟩ := bind_some h
    cases h
    exact and_congr (holds_renameFormula hs hseq htr arena hA) (holds_renameFormula hs hseq htr arena hB)
  | .truth, F', h => by cases h; exact Iff.rfl
  | .falsity, F', h => by cases h; exact Iff.rfl

/-! ## Binding `k` actuals -/

/-- An entry position of the longer call at the bound call: past the receiver
and the `k` saved actuals. -/
def dropBefore (k i : Nat) : Option Nat := if k < i then some (i - k) else none

/-- An exit position of the longer call at the bound call: the result, then
the entry positions one higher. -/
def dropAfter (k i : Nat) : Option Nat :=
  if i = 0 then some 0 else (dropBefore k (i - 1)).map (· + 1)

/-- The renaming of binding `k` actuals. -/
def dropRenaming (k : Nat) : Renaming := ⟨dropBefore k, dropAfter k⟩

/-- **A call's interpretation agrees with the bound call's** on the
renaming: the bound call passes the actuals after the `k` saved ones. -/
theorem dropRenaming_agrees {k : Nat} {pre : List Tm} (hp : pre.length = k) (r r₀ : Tm) (args : List Tm) (v : Tm)
    (m : Nat) (s s' : IndexedHeap) :
    (dropRenaming k).Agrees (callState r₀ (pre ++ args) v m s s') (callState r args v m s s') := by
  have hb : ∀ i j, dropBefore k i = some j → callEnv r args j = callEnv r₀ (pre ++ args) i := by
    intro i j h
    simp only [dropBefore] at h
    split at h
    · cases h
      rename_i hk
      simp only [callEnv, List.getD_eq_getElem?_getD]
      rw [if_neg (by omega), if_neg (by omega), List.getElem?_append_right (by omega), hp]
      congr 2; omega
    · cases h
  refine ⟨hb, fun i j h => ?_, rfl, rfl, rfl⟩
  change dropAfter k i = some j at h
  simp only [dropAfter] at h
  split at h
  · cases h; subst_vars; rfl
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨j', hj', rfl⟩ := h
    show ensuresEnv v r args (j' + 1) = ensuresEnv v r₀ (pre ++ args) i
    simp only [ensuresEnv, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    rw [if_neg (by assumption)]
    exact hb _ _ hj'

/-- **The arguments of an append at the bound call**: fixed witnesses
renamed, and the actuals from a position past the saved ones. -/
def seqDrop (k : Nat) : WitnessSeq → Option WitnessSeq
  | .fixed xs => (xs.mapM (renameWitness (dropBefore k))).map .fixed
  | .restFrom first => if k < first then some (.restFrom (first - k)) else none
  | .append a b => do pure (.append (← seqDrop k a) (← seqDrop k b))

private theorem mapM_rename_values {f : Nat → Option Nat} {η η' : Env} (he : ∀ i j, f i = some j → η' j = η i)
    (h : Heap) : ∀ {xs ys : List Witness}, xs.mapM (renameWitness f) = some ys →
      ys.mapM (·.value η' h) = xs.mapM (·.value η h)
  | [], ys, hm => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm; subst hm; rfl
  | x :: xs, ys, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hm
    obtain ⟨y, hy, hm⟩ := bind_some hm
    obtain ⟨ys', hys, hm⟩ := bind_some hm
    cases hm
    simp only [List.mapM_cons, value_renameWitness hy he h, mapM_rename_values he h hys]

private theorem mapM_paths (η : Env) (h : Heap) (l : List Nat) :
    (l.map fun i => Witness.path ⟨i, []⟩).mapM (·.value η h) = some (l.map η) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.mapM_cons, ih]
    show (Witness.value η h (.path ⟨i, []⟩)).bind _ = _
    rw [show Witness.value η h (.path ⟨i, []⟩) = some (η i) from Path.read_nil rfl]
    rfl

private theorem restFrom_eq (n first : Nat) : (WitnessSeq.restFrom first).instantiate n =
    (((List.range n).map (· + 1)).filter (first ≤ ·)).map fun i => Witness.path ⟨i, []⟩ := rfl

/-- **The bound call's append arguments denote the longer call's.** -/
theorem seqDrop_values {k : Nat} {s s' : TwoState} (hs : (dropRenaming k).Agrees s s') (n : Nat) :
    ∀ {a a' : WitnessSeq}, seqDrop k a = some a' →
      (a'.instantiate n).mapM (·.value s'.beforeEnv s'.before.h) =
        (a.instantiate (k + n)).mapM (·.value s.beforeEnv s.before.h)
  | .fixed xs, a', h => by
    simp only [seqDrop, Option.map_eq_some_iff] at h
    obtain ⟨ys, hys, rfl⟩ := h
    simp only [WitnessSeq.instantiate, hs.pre]
    exact mapM_rename_values hs.before _ hys
  | .restFrom first, a', h => by
    simp only [seqDrop] at h
    split at h
    · cases h
      rename_i hk
      rw [restFrom_eq, restFrom_eq, mapM_paths, mapM_paths]
      have hl : ((List.range (k + n)).map (· + 1)).filter (fun x => decide (first ≤ x)) =
          (((List.range n).map (· + 1)).filter (fun x => decide (first - k ≤ x))).map (· + k) := by
        rw [List.range_add, List.map_append, List.filter_append]
        have h0 : ((List.range k).map (· + 1)).filter (fun x => decide (first ≤ x)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro i hi
          simp only [List.mem_map, List.mem_range] at hi
          obtain ⟨j, hj, rfl⟩ := hi
          simp; omega
        rw [h0, List.nil_append, List.map_map, List.filter_map, List.filter_map, List.map_map]
        have hp : ((fun x => decide (first ≤ x)) ∘ ((· + 1) ∘ (k + ·))) =
            ((fun x => decide (first - k ≤ x)) ∘ (· + 1)) := by
          funext j; simp only [Function.comp_apply, decide_eq_decide]; omega
        have hf : ((· + 1) ∘ (k + ·)) = ((· + k) ∘ (· + 1)) := by funext j; simp only [Function.comp_apply]; omega
        rw [hp, hf]
      rw [hl, List.map_map]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq] at hx
      obtain ⟨⟨j, hj, rfl⟩, hle⟩ := hx
      simp only [Function.comp]
      exact hs.before (j + 1 + k) (j + 1) (by simp only [dropRenaming, dropBefore]; rw [if_pos (by omega)]; congr 1; omega)
    · cases h
  | .append a b, a', h => by
    simp only [seqDrop, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨A, hA, h⟩ := bind_some h
    obtain ⟨B, hB, h⟩ := bind_some h
    cases h
    simp only [WitnessSeq.instantiate, List.mapM_append, seqDrop_values hs n hA, seqDrop_values hs n hB]

/-- **A transport at the bound call**: one whose default image is the next
exit slot and whose replacements name no saved position, its replacements
and certified-rigid slots reindexed. Its equations at the saved positions
are a call's (`TwoState.Shifted`). -/
def trDrop (k : Nat) (t : TransportSchema) : Option TransportSchema :=
  if t.shift = 1 ∧ t.overrides.all (fun p => decide (k < p.1)) = true then
    (t.overrides.mapM fun p => (renameWitness (dropAfter k) p.2).map ((p.1 - k), ·)).map fun ov =>
      ⟨1, ov, t.boxed, (t.stable.filter (k < ·)).map (· - k)⟩
  else none

private theorem lookup_drop {k : Nat} : ∀ {ov : List (Nat × Witness)} {ov' : List (Nat × Witness)},
    ov.all (fun p => decide (k < p.1)) = true →
    ov.mapM (fun p => (renameWitness (dropAfter k) p.2).map ((p.1 - k), ·)) = some ov' →
    ∀ j, ov'.lookup j = (ov.lookup (j + k)).bind (renameWitness (dropAfter k)) ∧
      ∀ w, ov.lookup (j + k) = some w → (renameWitness (dropAfter k) w).isSome
  | [], ov', _, hm, j => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm; subst hm
    exact ⟨rfl, fun w hw => by cases hw⟩
  | p :: ov, ov', hk, hm, j => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hk
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hm
    obtain ⟨q, hq, hm⟩ := bind_some hm
    obtain ⟨ov'', hrest, hm⟩ := bind_some hm
    cases hm
    simp only [Option.map_eq_some_iff] at hq
    obtain ⟨w', hw', rfl⟩ := hq
    have ih := lookup_drop hk.2 hrest j
    by_cases hj : j + k = p.1
    · have h1 : (j == p.1 - k) = true := by simp; omega
      have h2 : (j + k == p.1) = true := by simp [hj]
      simp only [List.lookup, h1, h2, Option.bind_some, hw']
      exact ⟨by simp, fun w hw => by cases hw; simp [hw']⟩
    · have h1 : (j == p.1 - k) = false := by simp; omega
      have h2 : (j + k == p.1) = false := by simp [hj]
      simp only [List.lookup, h1, h2]
      exact ih

private theorem lookup_none_of_le {k : Nat} : ∀ {ov : List (Nat × Witness)},
    ov.all (fun p => decide (k < p.1)) = true → ∀ i, i ≤ k → ov.lookup i = none
  | [], _, _, _ => rfl
  | p :: ov, hk, i, hi => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hk
    have h1 : (i == p.1) = false := by simp; omega
    simp only [List.lookup, h1]
    exact lookup_none_of_le hk.2 i hi

/-- A transport's image of a slot, before its domain under a box. -/
private def rawImage (t : TransportSchema) (i : Nat) : Witness :=
  match t.overrides.lookup i with
  | some w => w
  | none => .path ⟨i + t.shift, []⟩

private theorem image_eq (t : TransportSchema) (N : Nat) (b : Bool) (i : Nat) :
    ({ t.instantiate N with boxed := b } : Substitution).image i =
      if i < N then (if b && !(rawImage t i).heapFree && !t.stable.contains i then none else some (rawImage t i))
      else none := by
  unfold Substitution.image
  simp only
  rw [TransportSchema.images_getElem]
  by_cases hi : i < N
  · rw [if_pos hi, if_pos hi]; rfl
  · rw [if_neg hi, if_neg hi]

private theorem holds_trDrop {k : Nat} {t t' : TransportSchema} (ht : trDrop k t = some t') {s s' : TwoState}
    (hs : (dropRenaming k).Agrees s s') (hsh : s.Shifted) (hsh' : s'.Shifted) (N : Nat) (b : Bool) (h : Heap) :
    ({ t'.instantiate N with boxed := b } : Substitution).Holds s'.beforeEnv s'.afterEnv h ↔
      ({ t.instantiate (N + k) with boxed := b } : Substitution).Holds s.beforeEnv s.afterEnv h := by
  unfold trDrop at ht
  split at ht
  · rename_i hc
    simp only [Option.map_eq_some_iff] at ht
    obtain ⟨ov, hov, rfl⟩ := ht
    have hlk := lookup_drop hc.2 hov
    have hle := lookup_none_of_le hc.2
    have hstable : ∀ j, 1 ≤ j → ((t.stable.filter (k < ·)).map (· - k)).contains j = t.stable.contains (j + k) := by
      intro j _
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem, List.mem_map, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨hi, hk⟩, rfl⟩
        rw [show i - k + k = i by omega]; exact hi
      · intro h
        exact ⟨j + k, ⟨h, by omega⟩, by omega⟩
    let t' : TransportSchema := ⟨1, ov, t.boxed, (t.stable.filter (k < ·)).map (· - k)⟩
    have hval : ∀ (η : Env) m, Witness.value η h (.path ⟨m, []⟩) = some (η m) := fun η m => Path.read_nil rfl
    have hbef : ∀ j, 1 ≤ j → (dropRenaming k).before (j + k) = some j := by
      intro j hj; simp only [dropRenaming, dropBefore]; rw [if_pos (by omega)]; congr 1; omega
    have hlow : ∀ i, i ≤ k → rawImage t i = .path ⟨i + 1, []⟩ := by
      intro i hi; simp only [rawImage, hle i hi, hc.1]
    have hzero : rawImage t' 0 = .path ⟨0 + 1, []⟩ := by
      simp only [rawImage, t', (hlk 0).1, Nat.zero_add, hle k (Nat.le_refl _), Option.bind_none]
    have hren : ∀ j, 1 ≤ j → renameWitness (dropAfter k) (rawImage t (j + k)) = some (rawImage t' j) := by
      intro j hj
      cases hl : t.overrides.lookup (j + k) with
      | none =>
        simp only [rawImage, t', hl, (hlk j).1, Option.bind_none, hc.1]
        simp only [renameWitness, renamePath, dropAfter, dropBefore, Option.map_map]
        rw [if_neg (by omega), if_pos (by omega)]
        simp only [Option.map_some, Function.comp_apply]
        congr 3; omega
      | some w =>
        obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp ((hlk j).2 w hl)
        simp only [rawImage, t', hl, (hlk j).1, Option.bind_some, hw']
    have hcond : ∀ j, 1 ≤ j → (b && !(rawImage t' j).heapFree && !t'.stable.contains j) =
        (b && !(rawImage t (j + k)).heapFree && !t.stable.contains (j + k)) := by
      intro j hj
      rw [heapFree_renameWitness (hren j hj)]
      simp only [t', hstable j hj]
    show ({ t'.instantiate N with boxed := b } : Substitution).Holds _ _ h ↔ _
    constructor
    · intro hy i w hw
      rw [image_eq] at hw
      split at hw
      · rename_i hiN
        split at hw
        · cases hw
        · rename_i hb
          cases hw
          by_cases hik : i ≤ k
          · rw [hlow i hik, hval, hsh i]
          · obtain ⟨j, rfl⟩ : ∃ j, i = j + k := ⟨i - k, by omega⟩
            have hj : 1 ≤ j := by omega
            have himg : ({ t'.instantiate N with boxed := b } : Substitution).image j = some (rawImage t' j) := by
              rw [image_eq, if_pos (by omega), hcond j hj, if_neg hb]
            have := hy j _ himg
            rw [← value_renameWitness (hren j hj) hs.after h, this, hs.before _ _ (hbef j hj)]
      · cases hw
    · intro hx j w' hw
      rw [image_eq] at hw
      split at hw
      · rename_i hjN
        split at hw
        · cases hw
        · rename_i hb
          cases hw
          by_cases hj0 : j = 0
          · subst hj0; rw [hzero, hval, hsh' 0]
          · have hj : 1 ≤ j := by omega
            have himg : ({ t.instantiate (N + k) with boxed := b } : Substitution).image (j + k) =
                some (rawImage t (j + k)) := by
              rw [image_eq, if_pos (by omega), ← hcond j hj, if_neg hb]
            have := hx (j + k) _ himg
            rw [value_renameWitness (hren j hj) hs.after h, this, hs.before _ _ (hbef j hj)]
      · cases hw
  · cases ht

/-- **A transport at the bound call holds where the longer call's does**, at
a scope `k` slots narrower. -/
theorem holdsAt_trDrop {k : Nat} {t t' : TransportSchema} (ht : trDrop k t = some t') {s s' : TwoState}
    (hs : (dropRenaming k).Agrees s s') (hsh : s.Shifted) (hsh' : s'.Shifted) (N : Nat) :
    (t'.instantiate N).HoldsAt s'.beforeEnv s'.afterEnv s'.after ↔
      (t.instantiate (N + k)).HoldsAt s.beforeEnv s.afterEnv s.after := by
  unfold Substitution.HoldsAt Substitution.box
  rw [hs.post]
  have hb : (t'.instantiate N).boxed = (t.instantiate (N + k)).boxed := by
    unfold trDrop at ht
    split at ht
    · simp only [Option.map_eq_some_iff] at ht
      obtain ⟨ov, -, rfl⟩ := ht
      rfl
    · cases ht
  have h1 := holds_trDrop ht hs hsh hsh' N (t'.instantiate N).boxed s.after.h
  have e1 : ({ t'.instantiate N with boxed := (t'.instantiate N).boxed } : Substitution) = t'.instantiate N := rfl
  have e2 : ({ t.instantiate (N + k) with boxed := (t'.instantiate N).boxed } : Substitution) =
      t.instantiate (N + k) := by rw [hb]
  rw [e1, e2] at h1
  exact and_congr h1 (forall_congr' fun s₁ => imp_congr_right fun _ => holds_trDrop ht hs hsh hsh' N true s₁.h)

private theorem canonical_trDrop {k : Nat} {t t' : TransportSchema} (ht : trDrop k t = some t') :
    t.shift = 1 ∧ t'.shift = 1 := by
  unfold trDrop at ht
  split at ht
  · rename_i hc
    simp only [Option.map_eq_some_iff] at ht
    obtain ⟨ov, -, rfl⟩ := ht
    exact ⟨hc.1, rfl⟩
  · cases ht

private theorem canonical_renameFormula {k : Nat} :
    ∀ {F G : FormulaSchema}, renameFormula (dropRenaming k) (seqDrop k) (trDrop k) F = some G →
      F.canonical = true ∧ G.canonical = true
  | .at .., _, h => by cases h
  | .transport t, G, h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    have := canonical_trDrop ht
    simp [FormulaF.canonical, this.1, this.2]
  | .and F G, H, h => by
    simp only [renameFormula, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨A, hA, h⟩ := bind_some h
    obtain ⟨B, hB, h⟩ := bind_some h
    cases h
    have := canonical_renameFormula hA
    have := canonical_renameFormula hB
    simp_all [FormulaF.canonical]
  | .transition _, G, h | .operation _, G, h | .linear _, G, h | .defined _, G, h => by
    simp only [renameFormula, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .truth, G, h | .falsity, G, h => by cases h; exact ⟨rfl, rfl⟩

/-- **An exit schema at the bound call**: its frame and formulas with the
positions substituted, where none names a saved position. -/
def ExitSchema.drop (k : Nat) (q : ExitSchema) : Option ExitSchema := do
  pure ⟨← renameFootprint (dropBefore k) q.frame,
    ← q.ensures.mapM (renameFormula (dropRenaming k) (seqDrop k) (trDrop k))⟩

/-- **Binding `k` actuals** (the note, rule Call at a bound function): both
exits at the bound call, where neither names a saved position. -/
def Exits.drop (k : Nat) (x : Exits ExitSchema) : Option (Exits ExitSchema) := do
  pure ⟨← x.normal.drop k, ← x.exceptional.drop k⟩

private theorem mapM_pairs {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (∀ y ∈ ys, ∃ x ∈ xs, f x = some y) ∧ (∀ x ∈ xs, ∃ y ∈ ys, f x = some y)
  | [], ys, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨y, hy, h⟩ := bind_some h
    obtain ⟨ys', hys, h⟩ := bind_some h
    cases h
    obtain ⟨h1, h2⟩ := mapM_pairs hys
    refine ⟨fun y' hy' => ?_, fun x' hx' => ?_⟩
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · exact ⟨x, List.mem_cons_self .., hy⟩
      · obtain ⟨x'', hx'', hm⟩ := h1 y' hy'; exact ⟨x'', List.mem_cons_of_mem _ hx'', hm⟩
    · rcases List.mem_cons.mp hx' with rfl | hx'
      · exact ⟨y, List.mem_cons_self .., hy⟩
      · obtain ⟨y'', hy'', hm⟩ := h2 x' hx'; exact ⟨y'', List.mem_cons_of_mem _ hy'', hm⟩

private theorem ExitSchema.drop_canonical {k : Nat} {q q' : ExitSchema} (hd : q.drop k = some q') :
    q.canonicalTransports = true ∧ q'.canonicalTransports = true := by
  simp only [ExitSchema.drop, Option.bind_eq_bind, Option.pure_def] at hd
  obtain ⟨Φ, -, hd⟩ := bind_some hd
  obtain ⟨es, hes, hd⟩ := bind_some hd
  cases hd
  obtain ⟨h1, h2⟩ := mapM_pairs hes
  refine ⟨List.all_eq_true.mpr fun F hF => ?_, List.all_eq_true.mpr fun G hG => ?_⟩
  · obtain ⟨G, -, hm⟩ := h2 F hF; exact (canonical_renameFormula hm).1
  · obtain ⟨F, -, hm⟩ := h1 G hG; exact (canonical_renameFormula hm).2

/-- **An exit schema at the bound call holds where the original holds at
the longer call**, at entry scopes `k` slots apart. -/
theorem ExitSchema.holds_drop {k : Nat} {q q' : ExitSchema} (hd : q.drop k = some q') {s s' : TwoState}
    (hs : (dropRenaming k).Agrees s s') (hsh : s.Shifted) (hsh' : s'.Shifted) (n N : Nat) (hN : n + 1 ≤ N) :
    (q'.instantiate ⟨n, N, hN⟩).Holds AssertionArena.empty s' ↔
      (q.instantiate ⟨k + n, N + k, by omega⟩).Holds AssertionArena.empty s := by
  simp only [ExitSchema.drop, Option.bind_eq_bind, Option.pure_def] at hd
  obtain ⟨Φ, hΦ, hd⟩ := bind_some hd
  obtain ⟨es, hes, hd⟩ := bind_some hd
  cases hd
  obtain ⟨h1, h2⟩ := mapM_pairs hes
  have hF : ∀ {F G}, renameFormula (dropRenaming k) (seqDrop k) (trDrop k) F = some G →
      (Holds AssertionArena.empty s' (instantiateFormula ⟨n, N, hN⟩ G) ↔
        Holds AssertionArena.empty s (instantiateFormula ⟨k + n, N + k, by omega⟩ F)) :=
    fun hm => holds_renameFormula hs (fun _ _ ha => seqDrop_values hs n ha)
      (fun _ _ ht => holdsAt_trDrop ht hs hsh hsh' N) _ hm
  simp only [ExitSpec.Holds, ExitSchema.instantiate, List.forall_mem_map, hs.pre, hs.post]
  refine and_congr (action_renameFootprint hΦ hs.before) ⟨fun h F hFm => ?_, fun h G hG => ?_⟩
  · obtain ⟨G, hGm, hm⟩ := h2 F hFm
    exact (hF hm).mp (h G hGm)
  · obtain ⟨F, hFm, hm⟩ := h1 G hG
    exact (hF hm).mpr (h F hFm)

theorem Exits.drop_get {k : Nat} {x y : Exits ExitSchema} (hd : x.drop k = some y) (c : Completion) :
    (x.get c).drop k = some (y.get c) := by
  simp only [Exits.drop, Option.bind_eq_bind, Option.pure_def] at hd
  obtain ⟨a, ha, hd⟩ := bind_some hd
  obtain ⟨b, hb, hd⟩ := bind_some hd
  cases hd
  cases c
  · exact ha
  · exact hb

/-- **Binding is exact** (the note, rule Call at a bound function): where a
schema names no saved position, its exits at the bound call are its exits
at the longer call, the saved receiver and actuals in front. -/
theorem Exits.exitPost_drop {k : Nat} {x y : Exits ExitSchema} (hd : x.drop k = some y) {pre : List Tm}
    (hp : pre.length = k) {c : Completion} {r r₀ : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm} :
    y.exitPost c r args s s' v ↔ x.exitPost c r₀ (pre ++ args) s s' v := by
  have hq := Exits.drop_get hd c
  have hcx : x.canonicalTransports = true := by
    simp only [Exits.canonicalTransports, Bool.and_eq_true]
    exact ⟨(ExitSchema.drop_canonical (Exits.drop_get hd .normal)).1,
      (ExitSchema.drop_canonical (Exits.drop_get hd .exceptional)).1⟩
  have hcy : y.canonicalTransports = true := by
    simp only [Exits.canonicalTransports, Bool.and_eq_true]
    exact ⟨(ExitSchema.drop_canonical (Exits.drop_get hd .normal)).2,
      (ExitSchema.drop_canonical (Exits.drop_get hd .exceptional)).2⟩
  let N := max (args.length + 1) (max x.slots y.slots)
  have hlen : (pre ++ args).length = k + args.length := by simp [hp]
  unfold Exits.exitPost
  rw [← instantiate_completion hcy (N := N) (by omega),
    ← instantiate_completion hcx (N := N + k) (by rw [hlen]; omega)]
  have := ExitSchema.holds_drop hq (dropRenaming_agrees hp r r₀ args v s.h.length s s')
    (callState_shifted r₀ (pre ++ args) v _ s s') (callState_shifted r args v _ s s') args.length N (by omega)
  rw [this]
  simp only [hlen]

end Verification.CallEffects
