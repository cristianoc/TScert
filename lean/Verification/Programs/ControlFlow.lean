import Verification.Semantics.ObjectCoherence
import Verification.Programs.BranchRefinement
import Verification.Programs.HeapExpressionRules

/-! A finite control-flow graph over the existing expression language. Expression
steps use the existing heap machine. Dispatch and transfers are explicit steps,
so cycles consume execution budget without requiring invariant inference. -/
namespace Verification.ControlFlow
open ProgramTyping PositiveGraphs PositiveRules PointClaims ProgramCertificates BranchRefinement
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

/-! `Target` and `Continuation` are declared with the calculus
(`Semantics/Calculus.lean`): graph code carries them. -/

/-- A node's handler is where a throw out of its expression goes: the target
receives the thrown value bound in a fresh slot, as a `bind` continuation
receives a value. A node with none lets the throw leave the program. -/
structure Node where
  expression : Tm
  continuation : Continuation
  handler : Option Target := none
  deriving DecidableEq, Repr

abbrev Program := List Node

structure NodeEvidence (ι : Type) where
  expression : Evidence ι
  edges : List (EdgeEvidence ι)
  /-- Supplied precondition; incoming edges must establish it. -/
  knowledge : HeapKnowledge.Knowledge := ⟨[],[],[]⟩
  /-- None uses ordinary evidence; some selects a checked effect rule. -/
  effect : Option (HeapExpressionRules.StepEvidence ι) := none
  output : HeapKnowledge.Knowledge := ⟨[],[],[]⟩
  /-- For a node with a handler: the type the thrown value is bound at, which
  must admit every JavaScript value, and the evidence for the edge to the handler. -/
  handler : Option (Ty ι × EdgeEvidence ι) := none

abbrev Certificate (ι : Type) := List (NodeEvidence ι)
def entry (c : NodeEvidence ι) := (claim c.expression).context
def result (c : NodeEvidence ι) := (claim c.expression).type

/-- A run of a graph: at a node, evaluating a node's term (with its
continuation and handler), returned, or ended by a throw no handler caught. -/
inductive State where
  | at (label : Nat) (env : Env)
  | eval (term : Tm) (env : Env) (continuation : Continuation) (handler : Option Target)
  | done (value : Tm)
  | raised (value : Tm)

inductive Transition (P : Program) : Heap → State → Heap → State → Prop where
  | enter : P[l]? = some node →
      Transition P h (.at l ρ) h (.eval (instantiate 0 ρ node.expression) ρ node.continuation node.handler)
  | expr : Step h t h' t' → Transition P h (.eval t ρ k x) h' (.eval t' ρ k x)
  | ret : isVal v = true → Transition P h (.eval v ρ .ret x) h (.done v)
  | bind : isVal v = true → Transition P h (.eval v ρ (.bind l) x) h (.at l.label (mapEnv l.mapping (push v ρ)))
  | effect : isVal v = true → Transition P h (.eval v ρ (.effect l) x) h (.at l.label (mapEnv l.mapping ρ))
  | yes : Transition P h (.eval .tru ρ (.branch y n) x) h (.at y.label (mapEnv y.mapping ρ))
  | no : Transition P h (.eval .fls ρ (.branch y n) x) h (.at n.label (mapEnv n.mapping ρ))

  | yesBind : Transition P h (.eval .tru ρ (.branchBind y n) x) h (.at y.label (mapEnv y.mapping (push .tru ρ)))
  | noBind : Transition P h (.eval .fls ρ (.branchBind y n) x) h (.at n.label (mapEnv n.mapping (push .fls ρ)))

  | tagBind : isVal v = true →
      Transition P h (.eval v ρ (.tagBind tag y n) x) h
        (.at (if tagHoldsIn h tag v then y else n).label
          (mapEnv (if tagHoldsIn h tag v then y else n).mapping (push v ρ)))
  /-- A throw out of a node with a handler goes there, the thrown value bound. -/
  | handle : Raises t v →
      Transition P h (.eval t ρ k (some l)) h (.at l.label (mapEnv l.mapping (push v ρ)))
  /-- A throw out of a node without one ends the run. -/
  | raise : Raises t v → Transition P h (.eval t ρ k none) h (.raised v)

/-- The graph machine is safe: it returns a value of the result type, ends by
a throw of a closed value, or takes a transition. -/
def SafeGraph (Ξ : Fam) (P : Program) (T : Fam) : (n : Nat) → WorldT n → Heap → State → Prop
  | 0, _, _, _ => True
  | n+1, W, h, s =>
    ((∃ v, s = .done v ∧ isVal v = true ∧ T (n+1) W v) ∨ (∃ v, s = .raised v ∧ Scoped 0 v ∧ Ξ (n+1) W v)) ∨
    ∃ U : WorldT n, ∃ h' s', WExt (trunc n (Nat.le_succ n) W) U ∧
      WorldAdm U ∧ Transition P h s h' s' ∧ HeapOk n U h' ∧ SafeGraph Ξ P T n U h' s'

/-- Target existence is checked against both the actual graph and its claims. -/
@[nospecialize] def checkTargetResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := ⟨[],[],[]⟩) : CheckResult ι Unit :=
  match P[target.label]?, C[target.label]? with
  | some _, some c => (checkMappedResult G images Γ (entry c) target.mapping p).bind fun _ =>
      CheckResult.ofBool (HeapKnowledge.check facts c.knowledge target.mapping)
  | _, _ => failure

@[nospecialize] def checkTargetUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := ⟨[],[],[]⟩) : Bool :=
  (checkTargetResult G images P C Γ target p facts).accepted

theorem checkTargetUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) :
    checkTargetUsing G images P C Γ target p facts = (
  match P[target.label]?, C[target.label]? with
  | some _, some c => checkMappedUsing G images Γ (entry c) target.mapping p && HeapKnowledge.check facts c.knowledge target.mapping
  | _, _ => false
  ) := by
  cases hp : P[target.label]? <;> cases hc : C[target.label]? <;>
    simp only [checkTargetUsing, checkTargetResult, hp, hc, CheckResult.accepted_bind,
      CheckResult.accepted_ofBool, checkMappedUsing] <;> rfl

/-- The objects the value in `slot` was read from, with the field: the
current read links ending at it. -/
def readFields (facts : HeapKnowledge.Knowledge) (slot : Nat) : List (Nat × PropKey) :=
  facts.links.filterMap fun g =>
    if !g.alias && !g.distinct && !g.optional && g.value == slot then some (g.cell, g.field) else none

theorem readFields_holds {facts : HeapKnowledge.Knowledge} {slot ρ h}
    (hf : HeapKnowledge.Holds facts ρ h) :
    ∀ k f, (k, f) ∈ readFields facts slot → ∃ flds c oid l, ρ k = .objAt flds c oid ∧
      flds.lookup f = some l ∧ h[l]? = some (ρ slot) := by
  intro k f hk
  obtain ⟨g, hg, he⟩ := List.mem_filterMap.mp hk
  split at he
  · rename_i hc
    cases he
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    have := hf.2.2 g hg
    simp only [hc.1.1, hc.1.2, Bool.false_eq_true, ↓reduceIte] at this
    simpa [hc.2] using this
  · cases he

/-- The objects the value in `slot` was read from through a key they may
lack, with the key: the current optional read links ending at it. -/
def optionalFields (facts : HeapKnowledge.Knowledge) (slot : Nat) : List (Nat × PropKey) :=
  facts.links.filterMap fun g =>
    if !g.alias && !g.distinct && g.optional && g.value == slot then some (g.cell, g.field) else none

theorem optionalFields_holds {facts : HeapKnowledge.Knowledge} {slot ρ h}
    (hf : HeapKnowledge.Holds facts ρ h) :
    ∀ k f, (k, f) ∈ optionalFields facts slot → ∃ flds c oid, ρ k = .objAt flds c oid ∧
      (flds.lookup f = none → ρ slot = .undef) ∧
      (∀ l, flds.lookup f = some l → h[l]? = some (ρ slot)) := by
  intro k f hk
  obtain ⟨g, hg, he⟩ := List.mem_filterMap.mp hk
  split at he
  · rename_i hc
    cases he
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    have := hf.2.2 g hg
    simp only [hc.1.1.1, hc.1.1.2, hc.1.2, Bool.false_eq_true, ↓reduceIte] at this
    obtain ⟨flds, c, oid, hl, hr⟩ := this
    refine ⟨flds, c, oid, hl, fun hn => ?_, fun l hn => ?_⟩
    · unfold HeapLinks.ReadGave at hr
      rw [hn] at hr
      simpa [hc.2] using hr.2
    · unfold HeapLinks.ReadGave at hr
      rw [hn] at hr
      simpa [hc.2] using hr
  · cases he

@[nospecialize] def checkBranchTargetResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := ⟨[],[],[]⟩) : CheckResult ι Unit :=
  match P[target.label]?, C[target.label]? with
  | some _, some c =>
      (checkObservedResult G images Γ (entry c) 0 o target.mapping p
        (readFields facts 0) (optionalFields facts 0)).bind fun _ =>
      CheckResult.ofBool (HeapKnowledge.check (HeapKnowledge.observeTyped G Γ facts 0 o) c.knowledge target.mapping)
  | _, _ => failure

@[nospecialize] def checkBranchTargetUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := ⟨[],[],[]⟩) : Bool :=
  (checkBranchTargetResult G images P C Γ o target p facts).accepted

theorem checkBranchTargetUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) :
    checkBranchTargetUsing G images P C Γ o target p facts = (
  match P[target.label]?, C[target.label]? with
  | some _, some c => checkObservedUsing G images Γ (entry c) 0 o target.mapping p (readFields facts 0)
      (optionalFields facts 0) && HeapKnowledge.check (HeapKnowledge.observeTyped G Γ facts 0 o) c.knowledge target.mapping
  | _, _ => false
  ) := by
  cases hp : P[target.label]? <;> cases hc : C[target.label]? <;>
    simp only [checkBranchTargetUsing, checkBranchTargetResult, hp, hc, CheckResult.accepted_bind,
      CheckResult.accepted_ofBool, checkObservedUsing] <;> rfl


/-- A type admitting every closed JavaScript value. -/
def admitsAll (G : NormalGraph ι) (T : Ty ι) : Bool :=
  (expand G T).any fun c => match c with | .top | .source => true | _ => false

theorem admitsAll_sound {G : NormalGraph ι} {T : Ty ι} (h : admitsAll G T = true)
    {n W v} (hx : excOf G n W v) : meaning G T n W v := by
  obtain ⟨⟨hv, hs⟩, hinv⟩ := hx
  obtain ⟨c, hc, ht⟩ := List.any_eq_true.mp h
  apply (expand_sem G T (plain_of_mem_expand hc) n W v).mpr
  cases c <;> simp only [Bool.false_eq_true] at ht
  · exact ⟨.top, hc, ⟨sourceVal_isVal hv, hs⟩, builtinInvariant_of_withoutInvariant rfl n W v⟩
  · exact ⟨.source, hc, ⟨hv, hs⟩, hinv⟩

/-- The facts that hold wherever a node's expression throws: only what its
entry knowledge says without the heap (immutable values, alias and distinct
links), since the expression may have run any effect before throwing. The
thrown value takes the fresh slot, as a call's result does. -/
def handlerFacts (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  HeapExpressionRules.ordinaryOutput k

theorem handlerFacts_holds {k ρ h} (hk : HeapKnowledge.Holds k ρ h) (v : Tm) (h' : Heap) :
    HeapKnowledge.Holds (handlerFacts k) (push v ρ) h' :=
  ⟨HeapFacts.holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,
    HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2⟩

/-- A node's handler, when it has one, is a checked target for the thrown
value at a type admitting every value, under the facts that survive a throw. -/
@[nospecialize] def checkHandlerResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (node : Node) (c : NodeEvidence ι) : CheckResult ι Unit :=
  match node.handler, c.handler with
  | none, none => pure ()
  | some l, some (T, p) =>
      (CheckResult.ofBool (admitsAll G T)).bind fun _ =>
      checkTargetResult G images P C (T :: entry c) l p (handlerFacts c.knowledge)
  | _, _ => failure

@[nospecialize] def checkHandlerUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (node : Node) (c : NodeEvidence ι) : Bool :=
  (checkHandlerResult G images P C node c).accepted

theorem checkHandlerUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (node : Node) (c : NodeEvidence ι) :
    checkHandlerUsing G images P C node c = (
  match node.handler, c.handler with
  | none, none => true
  | some l, some (T, p) =>
      admitsAll G T && checkTargetUsing G images P C (T :: entry c) l p (handlerFacts c.knowledge)
  | _, _ => false
  ) := by
  cases hn : node.handler <;> cases hc : c.handler <;>
    simp only [checkHandlerUsing, checkHandlerResult, hn, hc, CheckResult.accepted_bind,
      CheckResult.accepted_ofBool, checkTargetUsing] <;> rfl

@[nospecialize] def checkNodeResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide ((claim c.expression).term = node.expression))).bind fun _ =>
  (checkHandlerResult G images P C node c).bind fun _ =>
  (CheckResult.ofBool (checkScope (entry c).length node.expression)).bind fun _ =>
  ((checker.run (claim c.expression) c.knowledge
    (c.effect.getD (.ordinary c.expression)) codes).expect c.output).bind fun _ =>
  match node.continuation, c.edges with
  | .ret, [] => CheckResult.ofBool (decide (result c = Rty))
  | .bind l, [p] => checkTargetResult G images P C (result c :: entry c) l p c.output
  | .effect l, [p] => checkTargetResult G images P C (entry c) l p (HeapKnowledge.dropResult c.output)
  | .branch y n, [py,pn] =>
      (CheckResult.ofBool (decide (expand G (result c) = [.bool]))).bind fun _ =>
      (checkTargetResult G images P C (entry c) y py (HeapKnowledge.dropResult c.output)).bind fun _ =>
      checkTargetResult G images P C (entry c) n pn (HeapKnowledge.dropResult c.output)
  | .branchBind y n, [py,pn] =>
      (CheckResult.ofBool (onlyBoolean G (result c))).bind fun _ =>
      (checkBranchTargetResult G images P C (result c :: entry c) (.boolean true) y py c.output).bind fun _ =>
      checkBranchTargetResult G images P C (result c :: entry c) (.boolean false) n pn c.output
  | .tagBind t y n, [py,pn] =>
      (checkBranchTargetResult G images P C (result c :: entry c) (.tag t true) y py c.output).bind fun _ =>
      checkBranchTargetResult G images P C (result c :: entry c) (.tag t false) n pn c.output
  | _, _ => failure

@[nospecialize] def checkNodeUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : Bool :=
  (checkNodeResult (checker := checker) G images Rty P C node c codes).accepted

theorem checkNodeUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι)
    (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    checkNodeUsing (checker := checker) G images Rty P C node c codes = (
  decide ((claim c.expression).term = node.expression) &&
  checkHandlerUsing G images P C node c &&
  checkScope (entry c).length node.expression &&
  decide ((checker.run (claim c.expression) c.knowledge
    (c.effect.getD (.ordinary c.expression)) codes).value = some c.output) &&
  match node.continuation, c.edges with
  | .ret, [] => decide (result c = Rty)
  | .bind l, [p] => checkTargetUsing G images P C (result c :: entry c) l p c.output
  | .effect l, [p] => checkTargetUsing G images P C (entry c) l p (HeapKnowledge.dropResult c.output)
  | .branch y n, [py,pn] => decide (expand G (result c) = [.bool]) &&
      checkTargetUsing G images P C (entry c) y py (HeapKnowledge.dropResult c.output) && checkTargetUsing G images P C (entry c) n pn (HeapKnowledge.dropResult c.output)
  | .branchBind y n, [py,pn] => onlyBoolean G (result c) &&
      checkBranchTargetUsing G images P C (result c :: entry c) (.boolean true) y py c.output &&
      checkBranchTargetUsing G images P C (result c :: entry c) (.boolean false) n pn c.output
  | .tagBind t y n, [py,pn] =>
      checkBranchTargetUsing G images P C (result c :: entry c) (.tag t true) y py c.output &&
      checkBranchTargetUsing G images P C (result c :: entry c) (.tag t false) n pn c.output
  | _, _ => false
  ) := by
  simp only [checkNodeUsing, checkNodeResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, CheckResult.accepted_expect, checkHandlerUsing,
    Bool.and_assoc]
  congr 1
  cases node.continuation <;> cases c.edges <;>
    (try (rename_i p ps; cases ps <;> (try (rename_i q qs; cases qs)))) <;>
    simp only [CheckResult.accepted_bind, CheckResult.accepted_ofBool,
      checkTargetUsing, checkBranchTargetUsing] <;> rfl

/-- Enumeration comes from the program, not a certificate-supplied edge list. -/
@[nospecialize] def checkGraphResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (P.length = C.length))).bind fun _ =>
  (CheckResult.all (List.range P.length) fun l =>
    match P[l]?, C[l]? with
    | some node, some c => (checkNodeResult (checker := checker) G images Rty P C node c codes).at (.node l)
    | _, _ => failure).bind fun _ =>
  CheckResult.ofBool (P.all (fun node => ObjectCoherence.sourceTerm node.expression))

@[nospecialize] def checkGraphUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : Bool :=
  (checkGraphResult (checker := checker) G images Rty P C codes).accepted

theorem checkGraphUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    checkGraphUsing (checker := checker) G images Rty P C codes = (
  decide (P.length = C.length) && (List.range P.length).all (fun l =>
    match P[l]?, C[l]? with
    | some node, some c => checkNodeUsing (checker := checker) G images Rty P C node c codes
    | _, _ => false) && P.all (fun node => ObjectCoherence.sourceTerm node.expression)
  ) := by
  simp only [checkGraphUsing, checkGraphResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, CheckResult.accepted_all, Bool.and_assoc]
  congr 2
  apply congrArg
  funext l
  cases P[l]? <;> cases C[l]? <;> rfl

def TargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι) (Γ : List (Ty ι)) (l : Target) (facts : HeapKnowledge.Knowledge) : Prop :=
  ∃ c, C[l.label]? = some c ∧ MappedCovers G Γ (entry c) l.mapping ∧ HeapKnowledge.check facts c.knowledge l.mapping = true

def BranchTargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (l : Target) (facts : HeapKnowledge.Knowledge) : Prop :=
  ∃ c, C[l.label]? = some c ∧ ObservedCovers G Γ (entry c) 0 o l.mapping (readFields facts 0)
    (optionalFields facts 0) ∧ HeapKnowledge.check (HeapKnowledge.observeTyped G Γ facts 0 o) c.knowledge l.mapping = true


/-- Where a throw out of a node in environment `ρ` may go: nowhere (it leaves
the program), or a target the thrown value and the surviving facts enter. -/
def HandlerOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (ρ : Env) : Option Target → Prop
  | none => True
  | some l => ∃ T facts, admitsAll G T = true ∧ TargetOk G C (T :: Γ) l facts ∧
      ∀ v h, HeapKnowledge.Holds facts (push v ρ) h

def ContinuationOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (A : Ty ι) (facts : HeapKnowledge.Knowledge) : Continuation → Prop
  | .ret => A = Rty
  | .bind l => TargetOk G C (A :: Γ) l facts
  | .effect l => TargetOk G C Γ l (HeapKnowledge.dropResult facts)
  | .branch y n => Represents G A .bool ∧ TargetOk G C Γ y (HeapKnowledge.dropResult facts) ∧ TargetOk G C Γ n (HeapKnowledge.dropResult facts)
  | .branchBind y n => onlyBoolean G A = true ∧
      BranchTargetOk G C (A::Γ) (.boolean true) y facts ∧ BranchTargetOk G C (A::Γ) (.boolean false) n facts
  | .tagBind t y n => BranchTargetOk G C (A::Γ) (.tag t true) y facts ∧
      BranchTargetOk G C (A::Γ) (.tag t false) n facts

theorem target_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {P C Γ l p facts}
    (hc : checkTargetUsing G images P C Γ l p facts = true) : TargetOk G C Γ l facts := by
  rw [checkTargetUsing_eq] at hc
  split at hc
  · rename_i node c hn he
    simp only [Bool.and_eq_true] at hc
    exact ⟨c, he, checkMapped_sound hc.1, hc.2⟩
  · contradiction

theorem branch_target_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {P C Γ q l p facts}
    (hc : checkBranchTargetUsing G images P C Γ q l p facts = true) : BranchTargetOk G C Γ q l facts := by
  rw [checkBranchTargetUsing_eq] at hc
  split at hc
  · simp only [Bool.and_eq_true] at hc
    exact ⟨_, by assumption, checkObserved_sound hc.1, hc.2⟩
  · contradiction


def ExpressionOk [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) : Prop :=
  ∀ n W h ρ, EnvOk G (entry c) ρ n W → HeapKnowledge.Holds c.knowledge ρ h →
    WorldAdm W → HeapOk n W h → HeapObservations.SafePost (excOf G) (meaning G (result c))
      (fun h' v => HeapKnowledge.Holds c.output (push v ρ) h') n W h (instantiate 0 ρ t)

theorem handler_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {P C node c}
    (hc : checkHandlerUsing G images P C node c = true) {ρ h} (hk : HeapKnowledge.Holds c.knowledge ρ h) :
    HandlerOk G C (entry c) ρ node.handler := by
  rw [checkHandlerUsing_eq] at hc
  split at hc
  · rename_i hn _; rw [hn]; trivial
  · rename_i l T p hn _
    rw [hn]
    simp only [Bool.and_eq_true] at hc
    exact ⟨T, _, hc.1, target_sound hc.2, fun v h' => handlerFacts_holds hk v h'⟩
  · contradiction

theorem node_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C node c}
    {codes : CodeEntry ι → Bool} (hc : checkNodeUsing (checker := checker) G images Rty P C node c codes = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    ExpressionOk G c node.expression ∧
    ContinuationOk G Rty C (entry c) (result c) c.output node.continuation ∧
    ∀ ρ h, HeapKnowledge.Holds c.knowledge ρ h → HandlerOk G C (entry c) ρ node.handler := by
  simp only [checkNodeUsing_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine ⟨?_, ?_, fun ρ h hk => handler_sound hc.1.1.1.2 hk⟩
  · intro n W h ρ he hf hw hh
    have ht := checker.sound hc.1.2 hcodes he hf hw hh
    simpa only [entry, result, hc.1.1.1.1] using ht
  · have hk := hc.2
    split at hk <;> (try (rename_i hcont hedges; rw [hcont]))
    · exact (of_decide_eq_true hk : result c = Rty)
    · exact target_sound hk
    · exact target_sound hk
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact ⟨hk.1.1, target_sound hk.1.2, target_sound hk.2⟩
    · simp only [Bool.and_eq_true] at hk
      exact ⟨hk.1.1, branch_target_sound hk.1.2, branch_target_sound hk.2⟩
    · simp only [Bool.and_eq_true] at hk
      exact ⟨branch_target_sound hk.1, branch_target_sound hk.2⟩
    · contradiction

theorem graph_node [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C c} {l : Nat}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (checker := checker) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) (hc : C[l]? = some c) :
    ∃ node : Node, P[l]? = some node ∧ ExpressionOk G c node.expression ∧
      ContinuationOk G Rty C (entry c) (result c) c.output node.continuation ∧
      ∀ ρ h, HeapKnowledge.Holds c.knowledge ρ h → HandlerOk G C (entry c) ρ node.handler := by
  simp only [checkGraphUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
  have hg := hg.1
  have hl : l < P.length := by
    rw [hg.1]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hn : P[l]? = some (P[l]'hl) := by simp [hl]
  have h := hg.2 l (List.mem_range.mpr hl)
  rw [hn, hc] at h
  exact ⟨_, hn, node_sound h hcodes⟩

/-- A state assertion used only in the global safety proof. -/
def StateOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Ty ι) (C : Certificate ι)
    (n : Nat) (W : WorldT n) (h : Heap) : State → Prop
  | .at l ρ => ∃ c, C[l]? = some c ∧ EnvOk G (entry c) ρ n W ∧ HeapKnowledge.Holds c.knowledge ρ h
  | .eval t ρ k x => ∃ Γ A out, EnvOk G Γ ρ n W ∧
      HeapObservations.SafePost (excOf G) (meaning G A) (fun h' v => HeapKnowledge.Holds out (push v ρ) h') n W h t ∧
      ContinuationOk G Rty C Γ A out k ∧ HandlerOk G C Γ ρ x
  | .done v => isVal v = true ∧ meaning G Rty n W v
  | .raised v => Scoped 0 v ∧ excOf G n W v

theorem target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ l ρ n W h facts}
    (ht : TargetOk G C Γ l facts) (he : EnvOk G Γ ρ n W) (hf : HeapKnowledge.Holds facts ρ h) : StateOk G Rty C n W h (.at l.label (mapEnv l.mapping ρ)) := by
  obtain ⟨c, hc, hcov, hfact⟩ := ht
  exact ⟨c, hc, hcov.env he, HeapKnowledge.check_sound hfact hf⟩

theorem branch_target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ q l ρ n W h facts}
    (ht : BranchTargetOk G C Γ q l facts) (he : EnvOk G Γ ρ (n+1) W) (hh : HeapOk (n+1) W h)
    (hq : q.holds (ρ 0)) (hf : HeapKnowledge.Holds facts ρ h) :
    StateOk G Rty C n (trunc n (Nat.le_succ n) W) h (.at l.label (mapEnv l.mapping ρ)) := by
  obtain ⟨c,hc,hcov,hfact⟩ := ht
  exact ⟨c,hc,(hcov.env he hq hh (readFields_holds hf) (optionalFields_holds hf)).transfer n
    (Nat.le_succ n) _ (WExt_refl _),
    HeapKnowledge.check_sound hfact (HeapKnowledge.observeTyped_holds he hf hq)⟩

/-- One checked graph transition preserves the point assertions. Keeping this
step lemma separate lets additional postconditions reuse exactly the same
control-flow and handler reasoning as ordinary safety. -/
theorem state_progress [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (checker := checker) G images Rty P C codes = true)
    (hcodes : CodesSound G codes)
    {n W h s} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C (n+1) W h s) :
    ((∃ v, s = .done v ∧ isVal v = true ∧ meaning G Rty (n+1) W v) ∨
      (∃ v, s = .raised v ∧ Scoped 0 v ∧ excOf G (n+1) W v)) ∨
    ∃ U : WorldT n, ∃ h' s', WExt (trunc n (Nat.le_succ n) W) U ∧
      WorldAdm U ∧ Transition P h s h' s' ∧ HeapOk n U h' ∧ StateOk G Rty C n U h' s' := by
  have hw' := WorldAdm_trunc (Nat.le_succ n) hw
  have hh' := HeapOk_trunc n W h hh
  let U := trunc n (Nat.le_succ n) W
  cases s with
  | «at» l ρ =>
    obtain ⟨c, hc, he, hf⟩ := hs
    obtain ⟨node, hn, ht, hk, hx⟩ := graph_node hg hcodes hc
    have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
    exact Or.inr ⟨U, h, _, WExt_refl _, hw', .enter hn, hh',
      ⟨entry c, result c, c.output, he', ht n U h ρ he' hf hw' hh', hk, hx ρ h hf⟩⟩
  | done v => exact Or.inl (Or.inl ⟨v, rfl, hs⟩)
  | raised v => exact Or.inl (Or.inr ⟨v, rfl, hs⟩)
  | eval t ρ k x =>
    obtain ⟨Γ, A, out, he, ht, hk, hx⟩ := hs
    rcases ht with (⟨hv, ha, hf⟩ | ⟨v, hr, hsc⟩) | ⟨V, h', t', hx', hu, step, hok, hsafe⟩
    · have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
      have ha' := (meaning_adm G A).down n W t ha
      cases k with
      | ret =>
        have heq : A = Rty := hk
        subst A
        exact Or.inr ⟨U, h, .done t, WExt_refl _, hw', .ret hv, hh',
          ⟨hv, ha'⟩⟩
      | bind l =>
        exact Or.inr ⟨U, h, .at l.label (mapEnv l.mapping (push t ρ)), WExt_refl _, hw', .bind hv, hh',
          (target_state hk (he'.push ha') hf)⟩
      | effect l =>
        exact Or.inr ⟨U, h, .at l.label (mapEnv l.mapping ρ), WExt_refl _, hw', .effect hv, hh',
          (target_state hk he' (HeapKnowledge.dropResult_holds hf))⟩
      | branch y no =>
        have hb := represents_raw hk.1 (n+1) W t ha
        rcases hb with rfl | rfl
        · exact Or.inr ⟨U, h, .at y.label (mapEnv y.mapping ρ), WExt_refl _, hw', .yes, hh',
            (target_state hk.2.1 he' (HeapKnowledge.dropResult_holds hf))⟩
        · exact Or.inr ⟨U, h, .at no.label (mapEnv no.mapping ρ), WExt_refl _, hw', .no, hh',
            (target_state hk.2.2 he' (HeapKnowledge.dropResult_holds hf))⟩
      | branchBind y no =>
        have hb := onlyBoolean_sound hk.1 ha
        rcases hb with rfl | rfl
        · exact Or.inr ⟨U, h, _, WExt_refl _, hw', .yesBind, hh',
            (branch_target_state hk.2.1 (he.push ha) hh rfl hf)⟩
        · exact Or.inr ⟨U, h, _, WExt_refl _, hw', .noBind, hh',
            (branch_target_state hk.2.2 (he.push ha) hh rfl hf)⟩
      | tagBind tag y no =>
        cases htag : tagHoldsIn h tag t with
        | true =>
          exact Or.inr ⟨U, h, _, WExt_refl _, hw', .tagBind hv, hh',
            (by
              simpa [htag] using (branch_target_state hk.1 (he.push ha) hh (tagHolds_of_heap htag) hf))⟩
        | false =>
          exact Or.inr ⟨U, h, _, WExt_refl _, hw', .tagBind hv, hh',
            (by
              simpa [htag] using (branch_target_state hk.2 (he.push ha) hh (tagHolds_of_heap htag) hf))⟩
    · have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
      cases x with
      | none =>
        exact Or.inr ⟨U, h, .raised v, WExt_refl _, hw', .raise hr, hh',
          ⟨hsc.1, (builtinExc_adm G _).down n W v hsc.2⟩⟩
      | some l =>
        obtain ⟨T, facts, hT, htarget, hfacts⟩ := hx
        exact Or.inr ⟨U, h, _, WExt_refl _, hw', .handle hr, hh',
          (target_state htarget
            (he'.push (admitsAll_sound hT ((builtinExc_adm G _).down n W v hsc.2))) (hfacts v h))⟩
    · exact Or.inr ⟨V, h', .eval t' ρ k x, hx', hu, .expr step, hok,
        ⟨Γ,A,out,he.transfer n (Nat.le_succ n) V hx',hsafe,hk,hx⟩⟩


/-- Global safety is by execution budget, not by acyclicity or graph unfolding. -/
theorem state_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (checker := checker) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) :
    ∀ n W h s, WorldAdm W → HeapOk n W h → StateOk G Rty C n W h s →
      SafeGraph (excOf G) P (meaning G Rty) n W h s := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h s hw hh hs
    rcases state_progress hg hcodes hw hh hs with terminal | ⟨U,h',s',hx,hu,st,hok,hs'⟩
    · exact .inl terminal
    · exact .inr ⟨U,h',s',hx,hu,st,hok,ih U h' s' hu hok hs'⟩

/-- Safety from any checked entry and concrete environment meeting its claim. -/
theorem accepted_entry_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C l c}
    {codes : CodeEntry ι → Bool} (hg : checkGraphUsing (checker := checker) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) (hc : C[l]? = some c)
    (n W h ρ) (he : EnvOk G (entry c) ρ n W) (hf : HeapKnowledge.Holds c.knowledge ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph (excOf G) P (meaning G Rty) n W h (.at l ρ) :=
  state_safe hg hcodes n W h _ hw hh ⟨c,hc,he,hf⟩

/-- The external input contract is independent of the supplied point claims. -/
@[nospecialize] def checkEntryResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : CheckResult ι Unit :=
  (checkGraphResult (checker := checker) G images Rty P C codes).bind fun _ =>
  match C[start]? with
  | some c => CheckResult.ofBool (decide (entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩))
  | none => failure

@[nospecialize] def checkEntryUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : Bool :=
  (checkEntryResult (checker := checker) G images Rty P C start inputs codes).accepted

theorem checkEntryUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Ty ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    checkEntryUsing (checker := checker) G images Rty P C start inputs codes = (
  checkGraphUsing (checker := checker) G images Rty P C codes && match C[start]? with
    | some c => decide (entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩)
    | none => false
  ) := by
  simp only [checkEntryUsing, checkEntryResult, CheckResult.accepted_bind, checkGraphUsing]
  congr 1
  cases C[start]? <;> simp only [CheckResult.accepted_ofBool] <;> rfl

theorem accepted_inputs_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C start inputs}
    {codes : CodeEntry ι → Bool} (hc : checkEntryUsing (checker := checker) G images Rty P C start inputs codes = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    SafeGraph (excOf G) P (meaning G Rty) n W h (.at start ρ) := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  have hg := hc.1
  have hx := hc.2
  split at hx
  · rename_i c hc
    have hem : entry c = inputs ∧ c.knowledge = ⟨[],[],[]⟩ := of_decide_eq_true hx
    apply accepted_entry_safe hg hcodes hc n W h ρ _ _ hw hh
    · simpa only [hem.1] using he
    · rw [hem.2]; exact HeapKnowledge.empty ρ h
  · contradiction

inductive Execution (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : Execution P 0 h s h s
  | next : Transition P h s h' s' → Execution P n h' s' h'' s'' → Execution P (n+1) h s h'' s''

#print axioms accepted_entry_safe
#print axioms accepted_inputs_safe
end Verification.ControlFlow
