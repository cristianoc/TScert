import Verification.Programs.TolerantFramesNodePromise
import Verification.Programs.TolerantFramesNodeGoals
import Verification.Programs.TolerantFramesComposeEdges

/-! # Tolerant frames: a node's kept yields at its entry, its return and its exits

`run` reads a step's yields at the implications `slotImplOf entry.names I'`
for implications `I'` among the entry's `I` (all of them, or those testing a
read slot's name), restates each yield at every slot holding its target's
name (`passReturnYields`, `ysAll`), and refines an edge's context by them
(`refinedΓ`). Proved:

- `slotImplOf_ok`, `slotImplOf_entry`: the implications at slots hold
  where the slots hold their names' values and the implications over names
  hold; so wherever the entry state holds;
- `yieldsOk_passReturnYields`: the yields restated at the slots holding
  their targets' names hold where the yields do;
- `yieldsJudged_of_checked`: the yields `checkedYields` keeps are judged
  (`YieldsJudged`): outside a promise call by `yieldsJudged_of_follows`; at
  a promise call under `PromiseDerivChecked`, the check the pass's queued
  change puts the promise branch behind, by `promiseCall_yields_checked`;
- `exitDeliversY_head`: `exitDelivers_head` with the yields read at the
  step's value from the state after the step;
- `goalHolds_of_returnY`: a return's goal from the state after the step,
  the claim's type and the yields `returnCheck` read at the value.

The context as the yields refine it is `TolerantFramesNodeRefined`'s. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Slots
variable {ι : Type}

/-- **A slot `slotImplOf` lists for a name holds the name.** -/
theorem slotImplOf_mem {names : List Nat} {xs : List (PromiseCalls.Implication ι)}
    {y : PromiseCalls.Implication ι} (hy : y ∈ slotImplOf names xs) :
    ∃ x ∈ xs, names[y.test]? = some x.test ∧ names[y.target]? = some x.target ∧ y.type = x.type := by
  unfold slotImplOf at hy
  split at hy
  · simp at hy
  · simp only at hy
    generalize hW : (xs.foldl (fun acc (x : PromiseCalls.Implication ι) => (acc.insert x.test).insert x.target)
      ({} : Std.HashSet Nat)) = W at hy
    have hget : ∀ x i, i ∈ (names.zipIdx.foldl (fun (acc : Std.HashMap Nat (List Nat)) (p : Nat × Nat) =>
        if W.contains p.1 then acc.insert p.1 (p.2 :: acc.getD p.1 []) else acc) {}).getD x [] →
        names[i]? = some x := by
      refine foldl_inv (fun (acc : Std.HashMap Nat (List Nat)) => ∀ x i, i ∈ acc.getD x [] → names[i]? = some x)
        _ _ _ (fun x i h => by simp at h) ?_
      intro ⟨z, j⟩ hzj acc hacc x i hi
      simp only at hi
      split at hi
      · rw [Std.HashMap.getD_insert] at hi
        split at hi
        · rename_i he
          simp only [beq_iff_eq] at he
          subst he
          rcases List.mem_cons.mp hi with rfl | hi
          · obtain ⟨hj, hjz⟩ := List.mem_zipIdx' hzj
            rw [List.getElem?_eq_getElem hj, hjz]
          · exact hacc _ _ hi
        · exact hacc x i hi
      · exact hacc x i hi
    obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact ⟨x, hx, hget _ _ hi, hget _ _ hj, rfl⟩

/-- **The implications at slots hold** (`slotImplOf`): where the slots hold
their names' values (`η`) and the implications over names hold. -/
theorem slotImplOf_ok {G : NormalGraph ι} {names : List Nat} {xs : List (PromiseCalls.Implication ι)}
    {ρ η : Env} {n : Nat} {W : WorldT n} (hs : SlotsNamed names ρ η)
    (hx : PromiseCalls.ImpliesOk G xs η n W) : PromiseCalls.ImpliesOk G (slotImplOf names xs) ρ n W := by
  intro y hy ht
  obtain ⟨x, hxm, h1, h2, h3⟩ := slotImplOf_mem hy
  rw [h3, hs _ _ h2]
  exact hx x hxm (by rw [← hs _ _ h1]; exact ht)

/-- **The step's implications hold at the node's entry**: `slotImplOf` of
the entry's names over implications among the entry's (`I'` ⊆ `I`), wherever
the entry state holds. -/
theorem slotImplOf_entry {G : NormalGraph ι} {entry : SinglePass.State} {I I' : List (PromiseCalls.Implication ι)}
    {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap} (hsub : ∀ x ∈ I', x ∈ I)
    (hS : StateHolds G entry I start E ρ m s) : PromiseCalls.ImpliesOk G (slotImplOf entry.names I') ρ s.n s.W := by
  obtain ⟨η, hn, -, hI, -⟩ := hS
  exact slotImplOf_ok hn fun x hx => hI x (hsub x hx)

/-- **The yields restated at the slots holding their targets' names hold**
(`passReturnYields`, `ysAll` in `run`). -/
theorem yieldsOk_passReturnYields {G : NormalGraph ι} {entry : SinglePass.State} {ys : List (PromiseCalls.Yield ι)}
    {ρ η : Env} {n : Nat} {W : WorldT n} {u : Tm} (hs : SlotsNamed entry.names ρ η)
    (hy : PromiseCalls.YieldsOk G ys ρ n W u) : PromiseCalls.YieldsOk G (passReturnYields entry ys) ρ n W u := by
  intro y' hy' hc hf
  obtain ⟨y, hy0, hm⟩ := List.mem_flatMap.mp hy'
  split at hm
  · rename_i nm hnm
    obtain ⟨⟨nm', j⟩, hj, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hjz, hjeq⟩ := List.mem_filter.mp hj
    obtain ⟨hjl, hjn⟩ := List.mem_zipIdx' hjz
    have hnm' : nm' = nm := beq_iff_eq.mp hjeq
    have e1 : ρ j = η nm := hs j nm (by rw [List.getElem?_eq_getElem hjl, ← hjn, hnm'])
    have e2 : ρ y.target = η nm := hs _ _ hnm
    show PositiveRules.meaning G y.type n W (ρ j)
    rw [e1, ← e2]
    exact hy y hy0 hc hf
  · rcases List.mem_singleton.mp hm with rfl
    exact hy y' hy0 hc hf

end Slots

section Judged
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **A promise call's derivation checked**: where the step's derivation
states a promise, `derivChecked` accepts it at the step's facts and its
claim's type is the node's. -/
def PromiseDerivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : HeapKnowledge.Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Prop :=
  (PromiseCalls.promiseOf G deriv).isSome = true →
    derivChecked G images codes sums c node stepK deriv = true ∧ (ProgramCertificates.claim deriv).type = c.type

omit [Hashable ι] in
/-- **The pass's promise check gives `PromiseDerivChecked`**
(`SinglePass.promiseDerivChecked`: `derivChecked` and the claim's type the
node's). -/
theorem promiseDerivChecked_of {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {stepK : HeapKnowledge.Knowledge}
    {deriv : ProgramCertificates.Evidence ι}
    (h : SinglePass.promiseDerivChecked G images codes sums c node stepK deriv = true) :
    PromiseDerivChecked G images codes sums c node stepK deriv := fun _ => by
  simp only [SinglePass.promiseDerivChecked, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

omit [Hashable ι] in
/-- **A promise call's kept yields are judged** (`YieldsJudged`): at a
derivation stating a promise whose yields `promiseYields` accepts, under
`PromiseDerivChecked`, by `promiseCall_yields_checked` combined with the
step's judgment (`SafePostExc.conj_post`). -/
theorem yieldsJudged_of_promise {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {stepK : HeapKnowledge.Knowledge}
    {deriv : ProgramCertificates.Evidence ι} {entry : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {startNames : List Nat} {ρ0 : Env} {m : Nat} {ys : List (PromiseCalls.Yield ι)} {effect a T}
    (hp : PromiseCalls.promiseOf G deriv = some (effect, a, T))
    (hy : PromiseCalls.promiseYields G c.type effect a T ys = true)
    (hpd : PromiseDerivChecked G images codes sums c node stepK deriv)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) :
    YieldsJudged G c.type c.context node.expression entry I startNames ρ0 m stepK ys := by
  intro ρ s Q R _ he hk hj
  obtain ⟨hdc, hty⟩ := hpd (by rw [hp]; rfl)
  simp only [derivChecked, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hdc
  obtain ⟨⟨hterm, hctx⟩, htree⟩ := hdc
  exact SafePostExc.conj_post hj
    (PromiseCalls.promiseCall_yields_checked hp htree hctx hterm hty hcodes hsums hy he s.adm s.ok)

omit [DecidableEq ι] [Hashable ι] in
/-- No yields are judged. -/
theorem yieldsJudged_nil {G : NormalGraph ι} {A : Ty ι} {Γ : List (Ty ι)} {t : Tm} {entry : SinglePass.State}
    {I : List (PromiseCalls.Implication ι)} {startNames : List Nat} {ρ0 : Env} {m : Nat}
    {stepK : HeapKnowledge.Knowledge} : YieldsJudged G A Γ t entry I startNames ρ0 m stepK [] :=
  fun _ _ _ _ _ _ _ hj => SafePostExc.conj_post hj
    (consequence (fun _ _ _ hv => ⟨hv, fun _ hy => absurd hy List.not_mem_nil⟩) (fun _ _ h => h) hj.post)

omit [Hashable ι] in
/-- **The yields `checkedYields` keeps are judged**: outside a promise call
those `yieldFollows` accepts at the implications `xs`, which hold wherever
the entry state does (`checkedYields_follows`, `yieldsJudged_of_follows`);
at a promise call those `promiseYields` accepts where the pass's promise
check `promiseDerivChecked` accepts the derivation
(`yieldsJudged_of_promise`, `promiseDerivChecked_of`). -/
theorem yieldsJudged_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {c : PointClaim ι} {node : Node} {stepK out : HeapKnowledge.Knowledge}
    {deriv : ProgramCertificates.Evidence ι} {entry : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {startNames : List Nat} {ρ0 : Env} {m : Nat} {xs : List (PromiseCalls.Implication ι)}
    {ys : List (PromiseCalls.Yield ι)}
    (hx : ∀ ρ (s : IndexedHeap), StateHolds G entry I startNames ρ0 ρ m s → PromiseCalls.ImpliesOk G xs ρ s.n s.W)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) :
    YieldsJudged G c.type c.context node.expression entry I startNames ρ0 m stepK
      (checkedYields G images c.context c.type xs stepK out deriv node.expression
        (fun _ => SinglePass.promiseDerivChecked G images codes sums c node stepK deriv) ys) := by
  cases hp : PromiseCalls.promiseOf G deriv with
  | none => exact yieldsJudged_of_follows (checkedYields_follows hp) hx
  | some x =>
    obtain ⟨effect, a, T⟩ := x
    unfold checkedYields
    split
    · exact yieldsJudged_nil
    · rw [hp]
      simp only
      split
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact yieldsJudged_of_promise hp hc.1.1 (promiseDerivChecked_of hc.1.2) hcodes hsums
      · exact yieldsJudged_nil

end Judged

section Exits
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- **A normal exit into a loop head delivers, its yields at the step's
value** (`exitDelivers_head` with the step's yields read from the state
after the step at the returned value, and the head's types from the edge's
check where the yields hold). -/
theorem exitDeliversY_head {G : NormalGraph ι} {w : Walk ι} {ctx : Nat → List (Ty ι)} {A : Ty ι}
    {Γ : List (Ty ι)} {entry : SinglePass.State} {store : Store} {result width : Nat} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool} {t : Target}
    {I : List (PromiseCalls.Implication ι)} {ys : List (PromiseCalls.Yield ι)} {startNames : List Nat} {ρ0 : Env}
    {m : Nat} {req : HeapKnowledge.Knowledge} {gimp : List (PromiseCalls.Implication ι)} {argName : Option Nat}
    {argSlots : List Nat} {inputSlots : List (Nat × Nat)} {hwidth hfresh : Nat} {V : Bool}
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (hrecHead : (w.entry t.label, w.implies t.label) ∈ w.incoming t.label)
    (hentry : w.entry t.label =
        (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).1 ∧
      w.implies t.label =
        (SinglePass.headEntry req false hwidth hfresh startNames argName argSlots inputSlots gimp).2.1)
    (hnd : startNames.Nodup) (hlt : ∀ x ∈ startNames, x < hfresh)
    (hargs : ∀ a, argName = some a → ∃ q : Nat, startNames[q]? = some a)
    (hvac : V = true → ∀ (ρ : Env) (s' : IndexedHeap) v, EnvOk G (A :: Γ) (push v ρ) s'.n s'.W →
      ObservedOk observed promote v → False)
    (hq : V = false → KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (ctx t.label))
      (HeapKnowledge.withTypedLinks G (if pushed then A :: Γ else Γ)
        (ControlFlow.withTypedCells G (if pushed then A :: Γ else Γ) req t.mapping
          (materialize (⟨if pushed then result :: entry.names else entry.names,
              edgeStoreOf G (if pushed then A :: Γ else Γ) entry.store store
                (if pushed then result :: entry.names else entry.names) (result :: entry.names) width pushed false
                observed promote, []⟩ : SinglePass.State)
            (if pushed then width + 1 else width)
            (((atomsOf req).flatMap Atom.names).map (PointClaims.slot t.mapping)) true).1)) req t.mapping = true)
    (himp : V = false → ∀ x ∈ gimp, ∃ y ∈ I ++ freshImplOf pushed false ys entry.names result,
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping x.test]? = some y.test ∧
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping x.target]? = some y.target ∧
      ∀ n (W : WorldT n) v, meaning G y.type n W v → meaning G x.type n W v)
    (hin : V = false → ∀ p ∈ inputSlots,
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping p.1]? = startNames[p.2]?)
    (harg : V = false → ∀ j ∈ argSlots,
      (if pushed then result :: entry.names else entry.names)[PointClaims.slot t.mapping j]? = argName)
    (ρ : Env)
    (htc : ∀ (s' : IndexedHeap) v, EnvOk G (A :: Γ) (push v ρ) s'.n s'.W → ObservedOk observed promote v →
      PromiseCalls.YieldsOk G ys ρ s'.n s'.W v →
      EnvOk G (ctx t.label) (PointClaims.mapEnv t.mapping (if pushed then push v ρ else ρ)) s'.n s'.W) :
    ExitDelivers (edgePreT G w startNames ρ0 ctx) G A Γ
      (fun ρ' m' s' => StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I startNames ρ0 ρ' m' s' ∧
        PromiseCalls.YieldsOk G ys ρ s'.n s'.W (ρ' 0)) ρ m t pushed observed promote := by
  intro s' v _ hF he ho
  obtain ⟨hF, hy⟩ := hF
  cases hV : V with
  | true => exact (hvac hV ρ s' v he ho).elim
  | false =>
    have hS := edgeStore_normal (Γ := if pushed then A :: Γ else Γ) (width := width)
      (stateHolds_freshImpl (pushed := pushed) hF (fun _ => hy)) ho hpo hpp (fun hs => by rw [hpo hs]; simpa using he)
    have heΓ : EnvOk G (if pushed then A :: Γ else Γ) (if pushed then push v ρ else ρ) s'.n s'.W := by
      cases pushed with
      | true => simpa using he
      | false => simpa using envOk_tail he
    have htc' := htc s' v he ho hy
    have hest := headEstablishes_of_edge hS heΓ htc' (hq hV) (himp hV) (hin hV) (harg hV)
    refine ⟨⟨_, hrecHead, ?_⟩, htc'⟩
    rw [hentry.1, hentry.2]
    exact (headEntry_holds hnd hlt hargs hest).1

end Exits

section Return
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **A return meets its goal from its kept yields** (`NodeYielded.ret`):
where `returnCheck` accepts the return at the step's yields `ys`, the
subtype answers are sound (D5) and the promised argument's name is the
start name of the goal's slot, at the state after the step, the claim's
type and the yields at the value (`yieldsOk_passReturnYields`,
`goalHolds_of_return`, `returnCheck_plain`). -/
theorem goalHolds_of_returnY {G : NormalGraph ι} {images : InstanceImageCheck G}
    {ensures : List HeapKnowledge.IndexFact} {c : PointClaim ι} {l : Nat} {entry : SinglePass.State}
    {store : Store} {result start : Nat} {startNames : List Nat} {argName : Option Nat}
    {ys : List (PromiseCalls.Yield ι)} {debugNode : Nat} {answers : Answered G} {goal : Goal ι}
    {I : List (PromiseCalls.Implication ι)} {ρ0 : Env} {m : Nat}
    (hsub : SubtypeAnswersSound G images)
    (h : (returnCheck G images goal ensures c l entry store result start startNames argName ys
      debugNode answers).1 = none)
    (harg : argName = goal.slot.bind (startNames[·]?)) :
    ∀ ρ (s' : IndexedHeap) v, isVal v = true →
      StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I startNames ρ0 (push v ρ) m s' →
      EnvOk G (c.type :: c.context) (push v ρ) s'.n s'.W → PromiseCalls.YieldsOk G ys ρ s'.n s'.W v →
      GoalHolds G goal (goal.argument ρ0) s'.n s'.W v := by
  intro ρ s' v _ hS he hy
  obtain ⟨η, hn, -⟩ := id hS
  have hs : SlotsNamed entry.names ρ η := fun i x hx => by simpa [push] using hn (i + 1) x (by simpa using hx)
  refine goalHolds_of_return hsub h harg hS he (yieldsOk_passReturnYields hs hy) fun R hR n W v hv => ?_
  subst hR
  exact returnCheck_plain (a := .undef) h hv

end Return

end Verification.TolerantFrames
