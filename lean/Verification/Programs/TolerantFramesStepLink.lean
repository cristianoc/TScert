import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Elab.Tactic.ElabTerm
import Verification.Programs.TolerantFramesFootprint
import Verification.Programs.TolerantFramesStore

/-! # Tolerant frames: `checkedStep` read as its conditions

`SinglePass.checkedStep` is an `Id.run do` block with early returns. Its
accepting runs are characterized here by the conditions they pass
(`checkedStep_ok`): a copy of a slot at the claim's type, or a step whose
selected output, tree check, result name and store after the step are those
the development's definitions state (`StepAccepted`, over `passTreeCheck`,
`passWholeCheck`, `passPreserving`, `handedSet`, `passBack`).

The proof walks the block outermost first: three tactics generalize the
outermost `match` discriminant (`gen_discr`), the outermost `if` condition
(`gen_ite`) or the smallest `match` mentioning a local (`gen_match_on`) in
every hypothesis, so each case split reads one decision of the code and its
equation stays a hypothesis. -/

namespace Verification.TolerantFrames
open Verification SinglePass
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates

open Lean Elab Tactic Meta in
/-- Generalize, in every hypothesis, the first discriminant of the outermost
`match` of hypothesis `h`. -/
elab "gen_discr " h:ident " as " x:ident " with " hx:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let env ← getEnv
  let some e := ty.find? (fun e => match e.getAppFn with
      | .const n _ => Meta.isMatcherCore env n
      | _ => false) | throwError "gen_discr: no match"
  let some app ← Lean.Meta.matchMatcherApp? e | throwError "gen_discr: not a matcher application"
  let discr := app.discrs[0]!
  let hyps := (← getLCtx).getFVarIds
  let (_, _, g) ← (← getMainGoal).generalizeHyp #[{ expr := discr, xName? := x.getId, hName? := hx.getId }] hyps
  replaceMainGoal [g]

open Lean Elab Tactic Meta in
/-- Generalize, in every hypothesis, the Boolean tested by the outermost `if`
of hypothesis `h`. -/
elab "gen_ite " h:ident " as " x:ident " with " hx:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some e := ty.find? (fun e => e.isAppOfArity ``ite 5) | throwError "gen_ite: no if"
  let cond := e.getArg! 1
  let b := match cond.eq? with
    | some (_, b, _) => b
    | none => cond
  let hyps := (← getLCtx).getFVarIds
  let (_, _, g) ← (← getMainGoal).generalizeHyp #[{ expr := b, xName? := x.getId, hName? := hx.getId }] hyps
  replaceMainGoal [g]

open Lean in
/-- The matcher applications of `e` mentioning `fv`, with no loose bound
variable. -/
partial def matchersOn (env : Environment) (fv : FVarId) (e : Expr) (acc : Array Expr) : Array Expr :=
  let isM := match e.getAppFn with
    | .const n _ => Meta.isMatcherCore env n
    | _ => false
  let acc := if isM && e.containsFVar fv && !e.hasLooseBVars then acc.push e else acc
  match e with
  | .app f a => matchersOn env fv a (matchersOn env fv f acc)
  | .lam _ t b _ | .forallE _ t b _ => matchersOn env fv b (matchersOn env fv t acc)
  | .letE _ t v b _ => matchersOn env fv b (matchersOn env fv v (matchersOn env fv t acc))
  | .mdata _ b | .proj _ _ b => matchersOn env fv b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- Generalize, in every hypothesis, the smallest `match` of hypothesis `h`
mentioning the local `v`. -/
elab "gen_match_on " h:ident v:ident " as " x:ident " with " hx:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let fv ← Lean.Elab.Tactic.getFVarId v
  let cands ← (matchersOn (← getEnv) fv ty #[]).filterM fun c => do
    return !(← whnf (← inferType c)).isForall
  let some e := cands.foldl (fun (best : Option Expr) c => match best with
      | some b => if c.approxDepth < b.approxDepth then some c else some b
      | none => some c) none | throwError "gen_match_on: no match"
  let hyps := (← getLCtx).getFVarIds
  let (_, _, g) ← (← getMainGoal).generalizeHyp #[{ expr := e, xName? := x.getId, hName? := hx.getId }] hyps
  replaceMainGoal [g]

section StepLink
variable {ι : Type} [DecidableEq ι]

/-! ## `checkedStep` read as its conditions -/

/-- The node's sequent (`SinglePass.lean` 1228). -/
def jOf (c : PointClaim ι) (node : Node) : Sequent ι := ⟨c.context, node.expression, c.type⟩

/-- Whether the step reads every fact (`wholeStep`, line 1221). -/
def wholeOf : Tm → Bool
  | .construct .. => true
  | _ => false

/-- The step's knowledge (`kE`, line 1226) over the facts `materialize`
selects with `whole`. -/
def kOf (G : NormalGraph ι) (c : PointClaim ι) (entry : SinglePass.State) (ms : List Nat) (whole : Bool) :
    HeapKnowledge.Knowledge :=
  KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) (materialize entry c.context.length ms whole).1

/-- The copy test (lines 1202–1205). -/
def copiedOf (G : NormalGraph ι) (c : PointClaim ι) (entry : SinglePass.State) : Tm → Option Nat
  | .var i => if ((c.context[i]?).any (· == c.type) && (IndexWrites.litSlot G c.context i).isNone) = true then
      entry.names[i]? else none
  | _ => none

/-- The result's name and the next fresh name (lines 1311–1315): a slot's
read keeps the slot's name. -/
def resultOf (t : Tm) (names : List Nat) (fresh : Nat) : Nat × Nat :=
  match t with
  | .var i => match names[i]? with
    | some x => (x, fresh)
    | none => (fresh, fresh + 1)
  | _ => (fresh, fresh + 1)

/-- **A step `checkedStep` accepts, read as its conditions**, at the
evidence `effect` the search or the direct call returned, with the read
summaries `sums₀` the call layers read (line 1251) and `sums` the selection
and the tree check read: the selected output `out` at the step's facts `kE`,
the tree check (`passTreeCheck`) with the tree only `requiresTree` accepted
`pre`, the result's name, and the store after the step: a preserving step's
delta over the handed facts; a writing step's tree checked over every fact
(`passWholeCheck`), its output `out'` selected over every fact, and its delta
after the heap facts it is not handed are dropped. -/
def StepAccepted (G : NormalGraph ι) (images : InstanceImageCheck G) (pc : PassChecker G images)
    (codes : CodeEntry ι → Bool) (c : PointClaim ι) (node : Node) (entry : SinglePass.State) (ms : List Nat)
    (fresh : Nat) (effect : HeapExpressionRules.StepEvidence ι) (sums₀ sums : List (ReadSummary ι))
    (st : Stepped ι) : Prop :=
  ∃ out pre, (pc.checker.select (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes sums).value =
      some out ∧
    passTreeCheck pc (kOf G c entry ms (wholeOf node.expression)) codes sums effect = some pre ∧
    st.result = (resultOf node.expression entry.names fresh).1 ∧ st.fresh = (resultOf node.expression entry.names fresh).2 ∧
    st.copied = false ∧ st.stepEffect = some effect ∧
    (passPreserving G images (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes sums₀ = true →
      st.store = applyDelta entry.store (materialize entry c.context.length ms (wholeOf node.expression)).2.1 out true
        (passBack (materialize entry c.context.length ms (wholeOf node.expression)).2.2 entry.names st.result) ∧
      st.stepK = kOf G c entry ms (wholeOf node.expression) ∧ st.stepOut = out) ∧
    (passPreserving G images (jOf c node) (kOf G c entry ms (wholeOf node.expression)) effect codes sums₀ = false →
      ∃ out', passWholeCheck G images (kOf G c entry ms true) codes sums pre = true ∧
        (pc.checker.select (jOf c node) (kOf G c entry ms true) effect codes sums).value = some out' ∧
        st.store = applyDelta (entry.store.dropHeap (handedSet (materialize entry c.context.length ms true).2.1).contains)
          (materialize entry c.context.length ms true).2.1 out' true
          (passBack (materialize entry c.context.length ms true).2.2 entry.names st.result) ∧
        st.stepK = kOf G c entry ms true ∧ st.stepOut = out')

/-- The tree the pass checks, as `checkedStep` computes it (line 1273–1275). -/
def passTreeCode (effect : HeapExpressionRules.StepEvidence ι) : Option (ProgramCertificates.Evidence ι) :=
  match effect with
  | .slicedRead _ _ _ e _ => some e
  | _ => effect.proof?

omit [DecidableEq ι] in
theorem passTreeCode_eq (e : HeapExpressionRules.StepEvidence ι) : passTreeCode e = passTree e := by
  cases e <;> rfl

theorem passTreeCheck_none {G : NormalGraph ι} {images : InstanceImageCheck G} {pc : PassChecker G images}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {e : HeapExpressionRules.StepEvidence ι}
    (h : (if pc.selectChecks = true then none else passTreeCode e) = none) :
    passTreeCheck pc k codes sums e = some none := by
  unfold passTreeCheck; rw [← passTreeCode_eq, h]

theorem passTreeCheck_tree {G : NormalGraph ι} {images : InstanceImageCheck G} {pc : PassChecker G images}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {e : HeapExpressionRules.StepEvidence ι} {p : ProgramCertificates.Evidence ι}
    (h : (if pc.selectChecks = true then none else passTreeCode e) = some p)
    (ht : (!checkTreeUsing G images p codes sums) = false) :
    passTreeCheck pc k codes sums e = some none := by
  unfold passTreeCheck; rw [← passTreeCode_eq, h]; simp only [Bool.not_eq_false'] at ht; simp [ht]

theorem passTreeCheck_pre {G : NormalGraph ι} {images : InstanceImageCheck G} {pc : PassChecker G images}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {e : HeapExpressionRules.StepEvidence ι} {p : ProgramCertificates.Evidence ι}
    (h : (if pc.selectChecks = true then none else passTreeCode e) = some p)
    (ht : (!checkTreeUsing G images p codes sums) = true)
    (hr : PromiseCalls.requiresTree G images k codes sums p = true) :
    passTreeCheck pc k codes sums e = some (some p) := by
  unfold passTreeCheck; rw [← passTreeCode_eq, h]; simp only [Bool.not_eq_true'] at ht; simp [ht, hr]

theorem resultOf_var {t : Tm} {names : List Nat} {fresh i x : Nat} (h1 : t = .var i)
    (h2 : names[(match t with | .var i => i | _ => 0)]? = some x) : resultOf t names fresh = (x, fresh) := by
  subst h1; simp only at h2; simp [resultOf, h2]

theorem resultOf_other {t : Tm} {names : List Nat} {fresh : Nat}
    (h : ∀ (i x : Nat), t = .var i → names[(match t with | .var i => i | _ => 0)]? = some x → False) :
    resultOf t names fresh = (fresh, fresh + 1) := by
  unfold resultOf
  split
  · rename_i i
    split
    · rename_i x hx; exact (h i x rfl hx).elim
    · rfl
  · rfl

theorem wholeCheck_none {G : NormalGraph ι} {images : InstanceImageCheck G} {k : HeapKnowledge.Knowledge}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} : passWholeCheck G images k codes sums none = true := rfl

theorem wholeCheck_some {G : NormalGraph ι} {images : InstanceImageCheck G} {k : HeapKnowledge.Knowledge}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {p : ProgramCertificates.Evidence ι}
    (h : (!PromiseCalls.requiresTree G images k codes sums p) = false) :
    passWholeCheck G images k codes sums (some p) = true := by
  simpa [passWholeCheck] using h

set_option hygiene false in
/-- A leaf of `checkedStep`'s walk: an error leaf closes, a success leaf
names the step's record. -/
macro "close_errors" : tactic => `(tactic| all_goals (try (simp only [pure, Prod.mk.injEq, Except.ok.injEq,
  reduceCtorEq, false_and, and_false] at h)))

set_option hygiene false in
/-- The step's tail after its tree check (`SinglePass.lean` 1311–1347): the
result's name, the preserving delta or the writing step's checks. `TREE` the
proof of `passTreeCheck`, `WHOLE` that of `passWholeCheck`. -/
macro "step_tail " tree:term ", " whole:term : tactic => `(tactic| (
  split at h
  · rename_i i x hx1 hx2
    gen_ite h as P with hP
    rcases P with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] at h
    · first
        | (gen_ite h as Q with hQ
           rcases Q with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] at h)
        | skip
      close_errors
      gen_discr h as WV with hWV
      rcases WV with _ | out' <;> try dsimp only at h
      close_errors
      obtain ⟨rfl, -, rfl⟩ := h
      subst hM hW
      exact ⟨⟨out, _, hOV, $tree, (congrArg Prod.fst (resultOf_var hx1 hx2)).symm,
        (congrArg Prod.snd (resultOf_var hx1 hx2)).symm, rfl, rfl,
        fun ht => absurd (hP.symm.trans ht) (by decide),
        fun _ => ⟨out', $whole, hWV, rfl, rfl, rfl⟩⟩, rfl⟩
    · close_errors
      obtain ⟨rfl, -, rfl⟩ := h
      subst hM hW
      exact ⟨⟨out, _, hOV, $tree, (congrArg Prod.fst (resultOf_var hx1 hx2)).symm,
        (congrArg Prod.snd (resultOf_var hx1 hx2)).symm, rfl, rfl,
        fun _ => ⟨rfl, rfl, rfl⟩, fun hf => absurd (hP.symm.trans hf) (by decide)⟩, rfl⟩
  · rename_i hnv
    gen_ite h as P with hP
    rcases P with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] at h
    · first
        | (gen_ite h as Q with hQ
           rcases Q with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] at h)
        | skip
      close_errors
      gen_discr h as WV with hWV
      rcases WV with _ | out' <;> try dsimp only at h
      close_errors
      obtain ⟨rfl, -, rfl⟩ := h
      subst hM hW
      exact ⟨⟨out, _, hOV, $tree, (congrArg Prod.fst (resultOf_other hnv)).symm,
        (congrArg Prod.snd (resultOf_other hnv)).symm, rfl, rfl,
        fun ht => absurd (hP.symm.trans ht) (by decide),
        fun _ => ⟨out', $whole, hWV, rfl, rfl, rfl⟩⟩, rfl⟩
    · close_errors
      obtain ⟨rfl, -, rfl⟩ := h
      subst hM hW
      exact ⟨⟨out, _, hOV, $tree, (congrArg Prod.fst (resultOf_other hnv)).symm,
        (congrArg Prod.snd (resultOf_other hnv)).symm, rfl, rfl,
        fun _ => ⟨rfl, rfl, rfl⟩, fun hf => absurd (hP.symm.trans hf) (by decide)⟩, rfl⟩))

set_option hygiene false in
/-- The step from its selected output on (`SinglePass.lean` 1273–1347): the
tree check's three outcomes, each followed by the tail. -/
macro "step_rest" : tactic => `(tactic| (
  gen_discr h as TV with hTV
  rcases TV with _ | p <;> try dsimp only at h
  · step_tail (passTreeCheck_none hTV), wholeCheck_none
  · gen_ite h as B with hB
    rcases B with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] at h
    · step_tail (passTreeCheck_tree hTV hB), wholeCheck_none
    · gen_ite h as C with hC
      rcases C with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] at h
      · close_errors
      · step_tail (passTreeCheck_pre hTV hB hC), (wholeCheck_some hQ)))

variable [Hashable ι] in
/-- A table kept over itself is itself. -/
theorem keepSummaries_self {G : NormalGraph ι} (a : Answered G) : keepSummaries a a = a := by
  cases a
  simp [keepSummaries]

variable [Hashable ι] [Instantiates ι] in
/-- **`checkedStep` accepting, read as its conditions** (an unfolding of the
pass's code): a copy of a slot at the claim's type, the store unchanged; or a
step with the evidence `effect` the call layers read with the summaries of
`a0` (the answers after the direct call, if any) and the selection with
those of `a1` (after the search, if any), the final answers. -/
theorem checkedStep_ok {G : NormalGraph ι} {images : InstanceImageCheck G} {pool : List (Ty ι)} {fuel : Nat}
    {suggestions : List (Sequent ι)} {index : KnownIndex ι} {codes : CodeEntry ι → Bool}
    {aliases : List (ι × ι)} {passChecker : PassChecker G images} {undefTy : Option (Ty ι)}
    {l : Nat} {node : Node} {c : PointClaim ι} {entry : SinglePass.State} {ms : List Nat} {fresh : Nat}
    {answers : Answered G} {st : Stepped ι} {stats : StepStats} {ans : Answered G}
    (h : checkedStep G images pool fuel suggestions index codes aliases passChecker undefTy l node c entry ms fresh
      answers = (Except.ok st, stats, ans)) :
    (∃ x, copiedOf G c entry node.expression = some x ∧ st.result = x ∧ st.store = entry.store ∧
      st.fresh = fresh ∧ st.copied = true ∧ st.stepK = {} ∧ st.stepOut = {} ∧ ans = answers) ∨
    (copiedOf G c entry node.expression = none ∧
      ∃ (effect : HeapExpressionRules.StepEvidence ι) (a0 a1 : Answered G),
        (a0 = answers ∨
          ∃ adm, a0 = keepSummaries answers (directCall G images c.context node.expression c.type adm undefTy answers).2) ∧
        (a1 = a0 ∨ ∃ k own adm, a1 = keepSummaries a0 (expressionEffectUsing G images pool fuel
          (jOf c node) k suggestions index codes aliases passChecker.checker own adm a0).2) ∧
        StepAccepted G images passChecker codes c node entry ms fresh effect a0.summaries.toList a1.summaries.toList st ∧
        ans = a1) := by
  unfold checkedStep at h
  simp only [Id.run, timedKind] at h
  generalize hD : directCall G images c.context node.expression c.type _ undefTy answers = D at h
  generalize hS : expressionEffectUsing G images pool fuel _ _ suggestions index codes aliases _ _ _ = S at h
  generalize hM : materialize entry c.context.length ms _ = M at h
  generalize hW : materialize entry c.context.length ms true = MW at h
  gen_match_on h D as DO with hDO
  gen_discr h as CP with hCP
  rcases CP with _ | x <;> try dsimp only at h
  rotate_left
  · left
    simp only [pure, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨x, hCP, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  right
  refine ⟨hCP, ?_⟩
  obtain ⟨Df, a0⟩ := DO
  have ha0 : keepSummaries answers a0 = answers ∨
      ∃ adm, keepSummaries answers a0 =
        keepSummaries answers (directCall G images c.context node.expression c.type adm undefTy answers).2 := by
    split at hDO
    · exact .inr ⟨_, by rw [hD, hDO]⟩
    · cases hDO; exact .inl (keepSummaries_self _)
  rcases Df with _ | ⟨e, b⟩ <;> try dsimp only at h
  · generalize hR : S (keepSummaries answers a0) = R at h
    gen_discr h as RV with hRV
    rcases RV with _ | ⟨deriv, effect, searched⟩ <;> try dsimp only at h
    · close_errors
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at h
    gen_discr h as OV with hOV
    rcases OV with _ | out <;> try dsimp only at h
    · close_errors
    subst hR
    refine ⟨effect, keepSummaries answers a0, keepSummaries (keepSummaries answers a0) (S (keepSummaries answers a0)).2,
      ha0, .inr ⟨_, _, _, congrArg (fun f => keepSummaries (keepSummaries answers a0) (f (keepSummaries answers a0)).2)
        hS.symm⟩, ?_⟩
    step_rest
  · gen_discr h as RV with hRV
    rcases RV with _ | ⟨deriv, effect, searched⟩ <;> try dsimp only at h
    · close_errors
    simp only [CheckResult.map, Option.map_eq_some_iff, Prod.mk.injEq] at hRV
    obtain ⟨out, hOV, -, rfl, rfl⟩ := hRV
    simp only [Option.isSome_some, if_true] at h
    simp only [keepSummaries_self] at h
    refine ⟨.ordinary e, keepSummaries answers a0, keepSummaries answers a0, ha0, .inl rfl, ?_⟩
    step_rest

end StepLink
end Verification.TolerantFrames
