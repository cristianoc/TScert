import Verification.Semantics.ObjectCoherence
import Verification.Programs.BranchRefinement
import Verification.Programs.HeapExpressionRules
import Verification.Programs.PromiseCalls
import Verification.Semantics.KnowledgeExpand

/-! A finite control-flow graph over the existing expression language. Expression
steps use the existing heap machine. Dispatch and transfers are explicit steps,
so cycles consume execution budget without requiring invariant inference. -/
namespace Verification.ControlFlow
variable {ε : Verification.HeapKnowledge.EntryState}
open ProgramTyping PositiveGraphs PositiveRules PointClaims ProgramCertificates BranchRefinement
open PromiseCalls (Implication Yield ImpliesOk YieldsOk refineBy yieldFacts edgeImplications impliesCheck
  argFollows ArgumentsOk)
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

/-- The typing derivation a step's evidence carries whose root is the node's
sequent: every constructor stating `claim e = j` of its proof (`checkStepResult`).
A sliced read's proof is at the location's contract, another sequent. -/
@[nospecialize] def _root_.Verification.HeapExpressionRules.StepEvidence.proof? :
    HeapExpressionRules.StepEvidence ι → Option (Evidence ι)
  | .ordinary e | .pure e | .reading e | .created e | .typedRead _ e | .allocated e | .written _ _ _ e => some e
  | .observedRead .. | .slicedRead .. | .knownValue .. | .linkedRead .. | .boundedWrite .. => none

/-- A node's ordinary typing derivation: its step's proof, or a separate tree. -/
inductive OrdinaryEvidence (ι : Type) where
  | effect
  | proof (tree : Evidence ι)

structure NodeEvidence (ι : Type) where
  /-- The node's ordinary typing derivation, whose root is the node's sequent;
  none where precise step evidence establishes the step alone. -/
  ordinary : Option (OrdinaryEvidence ι) := none
  /-- The node's sequent, where neither the ordinary derivation nor the
  step's proof states it. -/
  sequent : Option (Sequent ι) := none
  edges : List (EdgeEvidence ι)
  /-- Supplied precondition; incoming edges must establish it. -/
  knowledge : HeapKnowledge.Knowledge := {}
  /-- None uses ordinary evidence; some selects a checked effect rule. -/
  effect : Option (HeapExpressionRules.StepEvidence ι) := none
  output : HeapKnowledge.Knowledge := {}
  /-- For a node with a handler: the type the thrown value is bound at, which
  must admit every JavaScript value, and the evidence for the edge to the handler. -/
  handler : Option (Ty ι × EdgeEvidence ι) := none
  /-- Implications among the entry's slots; incoming edges must establish them. -/
  implies : List (Implication ι) := []
  /-- What the expression's result promises of the entry's slots. -/
  yields : List (Yield ι) := []
  /-- The entry slots holding the argument a promise goal is about. -/
  arguments : List Nat := []
  /-- At a return under a promise goal: one of those slots, and evidence that
  its type, as the yields leave it, is within the promise. -/
  promise : Option (Nat × PositiveCertificates.SubtypeChoices ι) := none

/-- What a graph's returns establish: a value of a type; or, for a promise
about the argument in an entry slot, a type guard's `true` or `false` with
`true` leaving the argument in the promise's type, or an assertion function's
`undefined`, leaving it there. -/
inductive Goal (ι : Type) where
  | plain (result : Ty ι)
  | guards (promise : Ty ι) (slot : Nat)
  | asserts (promise : Ty ι) (slot : Nat)
  deriving DecidableEq, Repr

instance : Coe (Ty ι) (Goal ι) := ⟨.plain⟩

/-- The entry slot a goal's promise is about. -/
def Goal.slot : Goal ι → Option Nat
  | .plain _ => none
  | .guards _ s | .asserts _ s => some s

/-- What a return meets, for the promised argument `a`. -/
def GoalHolds (G : NormalGraph ι) : Goal ι → Tm → Fam
  | .plain R, _ => meaning G R
  | .guards T _, a => fun n W v => (v = .tru ∧ meaning G T n W a) ∨ v = .fls
  | .asserts T _, a => fun n W v => v = .undef ∧ meaning G T n W a

abbrev Certificate (ι : Type) := List (NodeEvidence ι)

/-- The node's sequent: the root of its ordinary derivation, the stated
sequent, or the root of its step's proof. A well-formed node has one. -/
@[nospecialize] def NodeEvidence.header (c : NodeEvidence ι) : Sequent ι :=
  match c.ordinary, c.sequent, c.effect.bind HeapExpressionRules.StepEvidence.proof? with
  | some (.proof e), _, _ => claim e
  | _, some j, _ => j
  | _, none, some p => claim p
  | _, none, none => ⟨[], .nul, []⟩

/-- The derivation every consumer reads: the ordinary derivation, the step's
proof it selects, or, without one, the sequent alone as a `var` leaf, which
establishes no typing where the term is not that variable. -/
@[nospecialize] def NodeEvidence.expression (c : NodeEvidence ι) : Evidence ι :=
  match c.ordinary, c.effect.bind HeapExpressionRules.StepEvidence.proof? with
  | some (.proof e), _ => e
  | some .effect, some p => p
  | _, _ => .node c.header .var []

def entry (c : NodeEvidence ι) := (claim c.expression).context
def result (c : NodeEvidence ι) := (claim c.expression).type

/-- What a node's readers see of its stored knowledge: the knowledge
expanded at the entry's contexts (`KnowledgeExpand.expand`). -/
def entryFacts (G : NormalGraph ι) (c : NodeEvidence ι) : HeapKnowledge.Knowledge :=
  KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G (entry c)) c.knowledge

theorem entryFacts_holds {G : NormalGraph ι} {c : NodeEvidence ι} {ρ n W h} (he : EnvOk G (entry c) ρ n W)
    (hk : HeapKnowledge.Holds c.knowledge ε ρ h) : HeapKnowledge.Holds (entryFacts G c) ε ρ h :=
  KnowledgeExpand.expandLinks_holds (KnowledgeExpand.ctxOf_ok he) hk

/-- The contexts of a node's output slots: the entry's, one further; the
result's slot has none. -/
@[macro_inline] def outputCtx (G : NormalGraph ι) (c : NodeEvidence ι) : KnowledgeNormal.Ctx :=
  let sets := HeapKnowledge.typeSets G (entry c)
  HeapKnowledge.setsCtx sets 1

theorem outputCtx_ok {G : NormalGraph ι} {c : NodeEvidence ι} {ρ n W} (he : EnvOk G (entry c) ρ n W) (v : Tm) :
    KnowledgeNormal.CtxOk (outputCtx G c) (push v ρ) := by
  intro i C hC
  cases i with
  | zero => simp [outputCtx, HeapKnowledge.setsCtx] at hC
  | succ i =>
    simp only [outputCtx, HeapKnowledge.setsCtx, Nat.add_lt_iff_lt_sub_right, Nat.succ_sub_one,
      Nat.not_lt_zero, if_false] at hC
    exact HeapKnowledge.typeSets_mem he (by simpa using hC)

/-- A node's stated output follows from the output its step computes. -/
def outputFits (G : NormalGraph ι) (c : NodeEvidence ι) (out : HeapKnowledge.Knowledge) : Bool :=
  decide (out = c.output) || KnowledgeExpand.checkIn (outputCtx G c) out c.output none

theorem outputFits_sound {G : NormalGraph ι} {c : NodeEvidence ι} {out ρ n W h v}
    (hf : outputFits G c out = true) (he : EnvOk G (entry c) ρ n W)
    (ho : HeapKnowledge.Holds out ε (push v ρ) h) : HeapKnowledge.Holds c.output ε (push v ρ) h := by
  rcases Bool.or_eq_true_iff.mp hf with hf | hf
  · rw [← decide_eq_true_eq.mp hf]; exact ho
  · exact KnowledgeExpand.checkIn_sound (m := none) (ρ := push v ρ) hf (fun i C hC => outputCtx_ok he v i C hC) ho

/-- What a node's edges read of its stated output: its links restated on
every slot of their classes (`KnowledgeExpand.expandLinks`); its facts are
read by class at the edge (`KnowledgeExpand.checkIn`). -/
def outFacts (G : NormalGraph ι) (c : NodeEvidence ι) : HeapKnowledge.Knowledge :=
  KnowledgeExpand.expandLinks (outputCtx G c) c.output

theorem outFacts_holds {G : NormalGraph ι} {c : NodeEvidence ι} {ρ n W h v} (he : EnvOk G (entry c) ρ n W)
    (ho : HeapKnowledge.Holds c.output ε (push v ρ) h) : HeapKnowledge.Holds (outFacts G c) ε (push v ρ) h :=
  KnowledgeExpand.expandLinks_holds (outputCtx_ok he v) ho

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

/-- What an edge carries besides the slots' types: the implications the
source state establishes and the slots holding the promised argument, each
also at the slots its knowledge's alias links relate. A target's own
implications and argument slots must follow from them. -/
@[nospecialize] def carries [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (facts : HeapKnowledge.Knowledge)
    (xs : List (Implication ι)) (sources : List Nat) (target : Target) (c : NodeEvidence ι) : Bool :=
  impliesCheck G Γ (PromiseCalls.aliasImplications facts.links xs) target.mapping c.implies &&
    argFollows (PromiseCalls.aliasSources facts.links sources) target.mapping c.arguments

/-- `carries`, the source implications read by their slots. -/
@[nospecialize] def carriesIndexed [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (facts : HeapKnowledge.Knowledge) (xs : List (Implication ι)) (sources : List Nat) (target : Target)
    (c : NodeEvidence ι) : Bool :=
  PromiseCalls.impliesCheckIndexed G Γ facts.links xs target.mapping c.implies &&
    argFollows (PromiseCalls.aliasSources facts.links sources) target.mapping c.arguments

/-- The compiled checker runs `carriesIndexed` for `carries`. -/
@[csimp] theorem carries_eq_indexed : @carries = @carriesIndexed := by
  funext ι _ G Γ facts xs sources target c
  simp only [carries, carriesIndexed, PromiseCalls.impliesCheck_eq_indexed]

/-- The slots the target's guarded atoms test alone (`guarded s [] …`). -/
def guardedSlots (k : HeapKnowledge.Knowledge) : List Nat :=
  k.indices.filterMap fun a => match a.fact with
    | .guarded s [] _ _ => some s
    | _ => none

/-- An edge's facts with what the types of its context `Γ` state of the
cells the target's knowledge `k` requires, at the slots the target's mapping
`m` takes them from (`typed-cell`, PROGRAM-TYPING.md, "Facts a type states"),
and of the values of the slots its value facts and its guarded atoms test
alone (`typeValues`), which a guard's tag reads (`guardTags`). -/
@[nospecialize] def withTypedCells [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge)
    (m : Mapping) (facts : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  { facts with cells := HeapExpressionRules.typedCells G Γ (k.cells.map fun f => (slot m f.slot, f.field)) ++ facts.cells
               values := (guardedSlots k ++ k.values.map (·.slot)).eraseDups.filterMap (fun y =>
                 (HeapExpressionRules.typeValues G Γ (slot m y)).map
                 fun V => (⟨slot m y, V, valueField⟩ : HeapFacts.Fact)) ++ facts.values }

theorem withTypedCells_holds [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {k m facts ρ h}
    (hc : ∀ wanted, HeapFacts.Holds (HeapExpressionRules.typedCells G Γ wanted) ρ h)
    (hv : ∀ i R, HeapExpressionRules.typeValues G Γ i = some R → R.mem (ρ i) = true)
    (hf : HeapKnowledge.Holds facts ε ρ h) : HeapKnowledge.Holds (withTypedCells G Γ k m facts) ε ρ h := by
  refine ⟨fun f hm => ?_, fun f hm => ?_, hf.2.2.1, hf.2.2.2⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact hc _ f hm
    · exact hf.1 f hm
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨y, -, hy⟩ := List.mem_filterMap.mp hm
      obtain ⟨V, hV, rfl⟩ := Option.map_eq_some_iff.mp hy
      exact hv _ _ hV
    · exact hf.2.1 f hm

/-- A context no environment meets: one of its slots has a type of clause
rows none of which holds a clause, which no value meets. Each slot's labels
are read until one has a clause. -/
@[nospecialize] def unsatisfiable (G : NormalGraph ι) (Γ : List (Ty ι)) : Bool :=
  Γ.any fun A => A.all fun a => G.plain a && (G.rows a).isEmpty

theorem unsatisfiable_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W}
    (hu : unsatisfiable G Γ = true) (he : EnvOk G Γ ρ n W) : False := by
  obtain ⟨A, hA, hnil⟩ := List.any_eq_true.mp hu
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hnil
  have hplain : G.plainTy A = true := List.all_eq_true.mpr fun a ha => (hnil a ha).1
  have hexp : expand G A = [] := by
    rw [expand_of_plain hplain, clausesOf, List.flatMap_eq_nil_iff]
    intro a ha
    simp [NormalGraph.clauses, (hnil a ha).1, (hnil a ha).2]
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
  have hm := (expand_sem G A hplain n W _).mp (he.2 i A hi)
  rw [hexp] at hm
  obtain ⟨_, hmem, _⟩ := hm
  cases hmem

/-- Target existence is checked against both the actual graph and its claims.
An edge out of a context no environment meets is never taken: it establishes
the target's claims whatever they are (`vacuous-edge`). -/
@[nospecialize] def checkTargetResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := {})
    (xs : List (Implication ι) := []) (sources : List Nat := []) : CheckResult ι Unit :=
  match P[target.label]?, C[target.label]? with
  | some _, some c => (CheckResult.ofBool (unsatisfiable G Γ)).orElse fun _ =>
      (checkMappedResult G images Γ (entry c) target.mapping p).bind fun _ =>
      CheckResult.ofBool (KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry c)) (HeapKnowledge.withTypedLinks G Γ (withTypedCells G Γ c.knowledge target.mapping facts)) c.knowledge target.mapping && carries G Γ facts xs sources target c)
  | _, _ => failure

@[nospecialize] def checkTargetUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := {})
    (xs : List (Implication ι) := []) (sources : List Nat := []) : Bool :=
  (checkTargetResult G images P C Γ target p facts xs sources).accepted

theorem checkTargetUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge)
    (xs : List (Implication ι)) (sources : List Nat) :
    checkTargetUsing G images P C Γ target p facts xs sources = (
  match P[target.label]?, C[target.label]? with
  | some _, some c => unsatisfiable G Γ || (checkMappedUsing G images Γ (entry c) target.mapping p &&
      (KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry c)) (HeapKnowledge.withTypedLinks G Γ (withTypedCells G Γ c.knowledge target.mapping facts)) c.knowledge target.mapping && carries G Γ facts xs sources target c))
  | _, _ => false
  ) := by
  cases hp : P[target.label]? <;> cases hc : C[target.label]? <;>
    simp only [checkTargetUsing, checkTargetResult, hp, hc, CheckResult.accepted_bind,
      CheckResult.accepted_ofBool, CheckResult.accepted_orElse, checkMappedUsing] <;> rfl

/-- The objects the value in `slot` was read from, with the field: the
current read links ending at it. -/
def readFields (facts : HeapKnowledge.Knowledge) (slot : Nat) : List (Nat × PropKey) :=
  facts.links.filterMap fun g =>
    if !g.alias && !g.optional && g.value == slot then some (g.cell, g.field) else none

theorem readFields_holds {facts : HeapKnowledge.Knowledge} {slot ρ h}
    (hf : HeapKnowledge.Holds facts ε ρ h) :
    ∀ k f, (k, f) ∈ readFields facts slot → ∃ flds c oid l, ρ k = .objAt flds c oid ∧
      flds.lookup f = some l ∧ h[l]? = some (ρ slot) := by
  intro k f hk
  obtain ⟨g, hg, he⟩ := List.mem_filterMap.mp hk
  split at he
  · rename_i hc
    cases he
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    have := hf.2.2.1 g hg
    simp only [hc.1.1, hc.1.2, Bool.false_eq_true, ↓reduceIte] at this
    simpa [hc.2] using this
  · cases he

/-- The objects the value in `slot` was read from through a key they may
lack, with the key: the current optional read links ending at it. -/
def optionalFields (facts : HeapKnowledge.Knowledge) (slot : Nat) : List (Nat × PropKey) :=
  facts.links.filterMap fun g =>
    if !g.alias && g.optional && g.value == slot then some (g.cell, g.field) else none

theorem optionalFields_holds {facts : HeapKnowledge.Knowledge} {slot ρ h}
    (hf : HeapKnowledge.Holds facts ε ρ h) :
    ∀ k f, (k, f) ∈ optionalFields facts slot → ∃ flds c oid, ρ k = .objAt flds c oid ∧
      (flds.lookup f = none → ρ slot = .undef) ∧
      (∀ l, flds.lookup f = some l → h[l]? = some (ρ slot)) := by
  intro k f hk
  obtain ⟨g, hg, he⟩ := List.mem_filterMap.mp hk
  split at he
  · rename_i hc
    cases he
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    have := hf.2.2.1 g hg
    simp only [hc.1.1, hc.1.2, ↓reduceIte] at this
    obtain ⟨flds, c, oid, hl, hr⟩ := this
    refine ⟨flds, c, oid, hl, fun hn => ?_, fun l hn => ?_⟩
    · unfold HeapLinks.ReadGave at hr
      rw [hn] at hr
      simpa [hc.2] using hr.2
    · unfold HeapLinks.ReadGave at hr
      rw [hn] at hr
      simpa [hc.2] using hr
  · cases he

/-- A dispatch edge has no execution if its context is empty or its tested
value cannot give the selected answer. -/
@[nospecialize] def branchUnreachable [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (o : Observation) : Bool :=
  unsatisfiable G Γ || (Γ[0]?).any (impossible G · o)

@[nospecialize] def checkBranchTargetResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := {})
    (xs : List (Implication ι) := []) (sources : List Nat := []) : CheckResult ι Unit :=
  match P[target.label]?, C[target.label]? with
  | some _, some c => (CheckResult.ofBool (branchUnreachable G Γ o)).orElse fun _ =>
      (checkObservedResult G images Γ (entry c) 0 o target.mapping p
        (readFields facts 0) (optionalFields facts 0) (HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ facts 0 o))).bind fun _ =>
      CheckResult.ofBool (KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry c)) (HeapKnowledge.observeTyped G Γ (withTypedCells G Γ c.knowledge target.mapping facts) 0 o) c.knowledge target.mapping &&
        carries G Γ facts xs sources target c)
  | _, _ => failure

@[nospecialize] def checkBranchTargetUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge := {})
    (xs : List (Implication ι) := []) (sources : List Nat := []) : Bool :=
  (checkBranchTargetResult G images P C Γ o target p facts xs sources).accepted

theorem checkBranchTargetUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (target : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge)
    (xs : List (Implication ι)) (sources : List Nat) :
    checkBranchTargetUsing G images P C Γ o target p facts xs sources = (
  match P[target.label]?, C[target.label]? with
  | some _, some c => branchUnreachable G Γ o || (checkObservedUsing G images Γ (entry c) 0 o target.mapping p (readFields facts 0)
      (optionalFields facts 0) (HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ facts 0 o)) && (KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry c)) (HeapKnowledge.observeTyped G Γ (withTypedCells G Γ c.knowledge target.mapping facts) 0 o) c.knowledge target.mapping &&
        carries G Γ facts xs sources target c))
  | _, _ => false
  ) := by
  cases hp : P[target.label]? <;> cases hc : C[target.label]? <;>
    simp only [checkBranchTargetUsing, checkBranchTargetResult, hp, hc, CheckResult.accepted_bind,
      CheckResult.accepted_ofBool, CheckResult.accepted_orElse, checkObservedUsing] <;> rfl


/-- The slots holding the promised argument once a value is pushed: the
entry's, one further, and the pushed value itself where it is the argument
(`aliased`). -/
def pushedSources (arg : List Nat) (aliased : Bool) : List Nat :=
  arg.map (· + 1) ++ (if aliased then [0] else [])

/-- Whether a tag test's passing answer leaves a value of `A` `true`: a
truthiness test of a Boolean. -/
def truthyBoolean (G : NormalGraph ι) (tag : Tag) (A : Ty ι) : Bool :=
  tag == .truthy && onlyBoolean G A

theorem truthyBoolean_sound {G : NormalGraph ι} {tag : Tag} {A : Ty ι} {h n W v}
    (hb : truthyBoolean G tag A = true) (hv : meaning G A n W v) (ht : tagHoldsIn h tag v = true) : v = .tru := by
  simp only [truthyBoolean, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨rfl, hb⟩ := hb
  rcases onlyBoolean_sound hb hv with rfl | rfl
  · rfl
  · simp [tagHoldsIn, tagHolds] at ht

/-- Whether a node's expression reads the slot holding the promised argument. -/
def aliasedRead (arg : List Nat) (e : Tm) : Bool :=
  match e with
  | .var q => arg.contains q
  | _ => false

/-- How a node's expression establishes its yields: as a call at a promise
signature (`PromiseCalls.promiseCall_sound`), whose check stands for the
expression's; without one, by those of a slot read and of a tag test. -/
@[nospecialize] def checkYields [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (c : NodeEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι))
    (slices : PromiseCalls.FieldSlices G := PromiseCalls.FieldSlices.direct G) : Bool :=
  match PromiseCalls.promiseOf G c.expression with
  | some (effect, a, T) => checkTreeUsing G images c.expression codes sums &&
      PromiseCalls.promiseYields G (result c) effect a T c.yields &&
      ([HeapExpressionRules.ordinaryOutput (entryFacts G c), PromiseCalls.promiseOutput effect (entryFacts G c)].any fun out =>
        outputFits G c out ||
          outputFits G c (HeapExpressionRules.withStable G (entry c) (entryFacts G c) out))
  | none => c.yields.all (PromiseCalls.yieldFollows G images (entry c) c.implies (entryFacts G c).links
      (claim c.expression).term slices)

/-- The member-test field slices a certificate's yields read
(`PromiseCalls.memberYield`): for every node whose term is a membership
test, every yield with evidence and every read link its check reads. -/
abbrev SliceKey (ι : Type) := Ty ι × PropKey × List Tag × Bool × Ty ι

@[nospecialize] def sliceKeys (G : NormalGraph ι) (C : Certificate ι) : List (SliceKey ι) :=
  C.flatMap fun c => match PromiseCalls.memberParts (claim c.expression).term with
    | some (ts, i) => c.yields.flatMap fun y => if y.evidence.isNone then [] else
        (entryFacts G c).links.filterMap fun g =>
          if !g.alias && !g.optional && g.value == i && g.cell == y.target then
            ((entry c)[g.cell]?).map fun A => (A, g.field, ts, !y.onFalse, y.type)
          else none
    | none => []

@[nospecialize] def sliceKeyHash (G : NormalGraph ι) (k : SliceKey ι) : UInt64 :=
  mixHash (BranchRefinement.tyHash G k.1) (mixHash (hash k.2.1) (mixHash (hash k.2.2.1.length)
    (mixHash (hash k.2.2.2.1) (BranchRefinement.tyHash G k.2.2.2.2))))

/-- The slice of each key, computed once, by the key's hash. -/
@[nospecialize] def sliceTable [DecidableEq ι] (G : NormalGraph ι) (keys : List (SliceKey ι)) :
    Std.HashMap UInt64 (List (SliceKey ι × Ty ι)) :=
  keys.foldl (fun m k =>
    let h := sliceKeyHash G k
    let b := m.getD h []
    if b.any (·.1 == k) then m
    else m.insert h ((k, PromiseCalls.memberFieldSlice G k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) :: b)) {}

theorem sliceTable_mem [DecidableEq ι] (G : NormalGraph ι) :
    ∀ (keys : List (SliceKey ι)) (m : Std.HashMap UInt64 (List (SliceKey ι × Ty ι))),
      (∀ h k v, (k, v) ∈ m.getD h [] → v = PromiseCalls.memberFieldSlice G k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) →
      ∀ h k v, (k, v) ∈ (keys.foldl (fun m k =>
        let h := sliceKeyHash G k
        let b := m.getD h []
        if b.any (·.1 == k) then m
        else m.insert h ((k, PromiseCalls.memberFieldSlice G k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) :: b)) m).getD h [] →
        v = PromiseCalls.memberFieldSlice G k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2
  | [], _, hm => hm
  | k :: ks, m, hm => by
    simp only [List.foldl_cons]
    apply sliceTable_mem G ks
    intro h k' v hv
    split at hv
    · exact hm h k' v hv
    · rw [Std.HashMap.getD_insert] at hv
      by_cases hk : (sliceKeyHash G k == h) = true
      · rw [if_pos hk] at hv
        rcases List.mem_cons.mp hv with he | hv
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          rfl
        · exact hm _ k' v hv
      · rw [if_neg hk] at hv
        exact hm h k' v hv

/-- A key's slice in a bucket. -/
@[nospecialize] def bucketSlice [DecidableEq ι] (k : SliceKey ι) : List (SliceKey ι × Ty ι) → Option (Ty ι)
  | [] => none
  | (k', v) :: b => if k' = k then some v else bucketSlice k b

theorem bucketSlice_mem [DecidableEq ι] {k : SliceKey ι} :
    ∀ {b : List (SliceKey ι × Ty ι)} {v}, bucketSlice k b = some v → (k, v) ∈ b
  | [], _, h => by cases h
  | (k', v') :: b, v, h => by
    unfold bucketSlice at h
    split at h
    · rename_i hk
      cases h
      subst hk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (bucketSlice_mem h)

/-- The field slices of a certificate's yields, read from their table. -/
@[nospecialize] def FieldSlices.ofCertificate [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι) :
    PromiseCalls.FieldSlices G :=
  let tbl := sliceTable G (sliceKeys G C)
  { slice := fun A f ts q Y =>
      match bucketSlice (A, f, ts, q, Y) (tbl.getD (sliceKeyHash G (A, f, ts, q, Y)) []) with
      | some v => v
      | none => PromiseCalls.memberFieldSlice G A f ts q Y
    slice_eq := by
      funext A f ts q Y
      split
      · rename_i v hv
        exact sliceTable_mem G (sliceKeys G C) {} (fun h k v hv => by simp at hv) _ _ v (bucketSlice_mem hv)
      · rfl }

/-- A return under the graph's goal: at the result's type; a type guard's
Boolean, never `true` or with the argument, as the yields leave it where the
result is `true`, within the promise; an assertion function's `undefined`,
with the argument, as the yields leave it, within the promise. -/
@[nospecialize] def checkReturnResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (goal : Goal ι) (c : NodeEvidence ι) : CheckResult ι Unit :=
  match goal with
  | .plain R => CheckResult.ofBool (decide (result c = R ∨ result c = []))
  | .guards T _ => (CheckResult.ofBool (onlyBoolean G (result c))).bind fun _ =>
      (CheckResult.ofBool (impossible G (result c) (.boolean true))).orElse fun _ =>
        argumentWithin (yieldFacts c.yields true) T
  | .asserts T _ => (CheckResult.ofBool (PromiseCalls.onlyUndef G (result c))).bind fun _ =>
      (CheckResult.ofBool (result c).isEmpty).orElse fun _ =>
      argumentWithin (yieldFacts c.yields false) T
where
  argumentWithin (facts : List (Nat × Ty ι)) (T : Ty ι) : CheckResult ι Unit :=
    match c.promise with
    | some (p, proof) =>
      if c.arguments.contains p then match (refineBy G (entry c) facts 0)[p]? with
        | some B => ProgramCertificates.checkSubtypeUsing G images B T proof
        | none => failure
      else failure
    | none => failure

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
entry knowledge says without the heap (immutable values, alias links and
separation, and the index facts reading no heap), since the expression may have
run any effect before throwing. The
thrown value takes the fresh slot, as a call's result does. -/
def handlerFacts (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  HeapExpressionRules.ordinaryOutput k

theorem handlerFacts_holds {k ρ h} (hk : HeapKnowledge.Holds k ε ρ h) (v : Tm) (h' : Heap) :
    HeapKnowledge.Holds (handlerFacts k) ε (push v ρ) h' :=
  ⟨HeapFacts.holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,
    HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.1,
    (HeapKnowledge.shift_holds (v := v) hk).2.2.2.1, HeapKnowledge.elemsHolds_nil _ _,
    HeapKnowledge.envIndices_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.2.2.2 _⟩

/-- A node's handler, when it has one, is a checked target for the thrown
value at a type admitting every value, under the facts that survive a throw. -/
@[nospecialize] def checkHandlerResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (P : Program) (C : Certificate ι)
    (node : Node) (c : NodeEvidence ι) : CheckResult ι Unit :=
  match node.handler, c.handler with
  | none, none => pure ()
  | some l, some (T, p) =>
      (CheckResult.ofBool (admitsAll G T)).bind fun _ =>
      checkTargetResult G images P C (T :: entry c) l p (handlerFacts (entryFacts G c))
        (edgeImplications c.implies [] true) (pushedSources c.arguments false)
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
      admitsAll G T && checkTargetUsing G images P C (T :: entry c) l p (handlerFacts (entryFacts G c))
        (edgeImplications c.implies [] true) (pushedSources c.arguments false)
  | _, _ => false
  ) := by
  cases hn : node.handler <;> cases hc : c.handler <;>
    simp only [checkHandlerUsing, checkHandlerResult, hn, hc, CheckResult.accepted_bind,
      CheckResult.accepted_ofBool, checkTargetUsing] <;> rfl

@[nospecialize] def checkNodeResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι) := [])
    (slices : PromiseCalls.FieldSlices G := PromiseCalls.FieldSlices.direct G) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide ((claim c.expression).term = node.expression))).bind fun _ =>
  (checkHandlerResult G images P C node c).bind fun _ =>
  (CheckResult.ofBool (checkScope (entry c).length node.expression)).bind fun _ =>
  ((checker.run (claim c.expression) (entryFacts G c)
    (c.effect.getD (.ordinary c.expression)) codes sums).bind fun out => CheckResult.ofBool (outputFits G c out)).bind fun _ =>
  (CheckResult.ofBool (checkYields G images c codes sums slices)).bind fun _ =>
  let o := outFacts G c
  match node.continuation, c.edges with
  | .ret, [] => checkReturnResult G images Rty c
  | .bind l, [p] => checkTargetResult G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts o.links (yieldFacts c.yields false) 1) 0)
      l p o (edgeImplications c.implies c.yields true)
      (pushedSources c.arguments (aliasedRead c.arguments node.expression))
  | .effect l, [p] => checkTargetResult G images P C (refineBy G (entry c) (PromiseCalls.aliasFacts (HeapKnowledge.dropResult o).links (yieldFacts c.yields false) 0) 0)
      l p (HeapKnowledge.dropResult o) c.implies c.arguments
  | .branch y n, [py,pn] =>
      (CheckResult.ofBool (decide (expand G (result c) = [.bool]))).bind fun _ =>
      (checkTargetResult G images P C (refineBy G (entry c) (PromiseCalls.aliasFacts (HeapKnowledge.dropResult o).links (yieldFacts c.yields true) 0) 0) y py
        (HeapKnowledge.dropResult (HeapKnowledge.promoteTruthy o 0 true)) c.implies c.arguments).bind fun _ =>
      checkTargetResult G images P C (refineBy G (entry c) (PromiseCalls.aliasFacts (HeapKnowledge.dropResult o).links (yieldFacts c.yields false) 0) 0) n pn
        (HeapKnowledge.dropResult (HeapKnowledge.promoteTruthy o 0 false)) c.implies c.arguments
  | .branchBind y n, [py,pn] =>
      (CheckResult.ofBool (onlyBoolean G (result c))).bind fun _ =>
      (checkBranchTargetResult G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts o.links (yieldFacts c.yields true) 1) 0)
        (.boolean true) y py o (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression))).bind fun _ =>
      checkBranchTargetResult G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts o.links (yieldFacts c.yields false true) 1) 0)
        (.boolean false) n pn o (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression))
  | .tagBind t y n, [py,pn] =>
      (checkBranchTargetResult G images P C
        (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts o.links (yieldFacts c.yields (truthyBoolean G t (result c))) 1) 0)
        (.tag t true) y py o (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression))).bind fun _ =>
      checkBranchTargetResult G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts o.links (yieldFacts c.yields false) 1) 0)
        (.tag t false) n pn o (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression))
  | _, _ => failure

@[nospecialize] def checkNodeUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι) := []) : Bool :=
  (checkNodeResult (checker := checker) (sums := sums) G images Rty P C node c codes).accepted

theorem checkNodeUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (node : Node) (c : NodeEvidence ι)
    (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι)) :
    checkNodeUsing (checker := checker) (sums := sums) G images Rty P C node c codes = (
  decide ((claim c.expression).term = node.expression) &&
  checkHandlerUsing G images P C node c &&
  checkScope (entry c).length node.expression &&
  (checker.run (claim c.expression) (entryFacts G c)
    (c.effect.getD (.ordinary c.expression)) codes sums).value.any (outputFits G c) &&
  checkYields G images c codes sums &&
  match node.continuation, c.edges with
  | .ret, [] => (checkReturnResult G images Rty c).accepted
  | .bind l, [p] => checkTargetUsing G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts (outFacts G c).links (yieldFacts c.yields false) 1) 0)
      l p (outFacts G c) (edgeImplications c.implies c.yields true)
      (pushedSources c.arguments (aliasedRead c.arguments node.expression))
  | .effect l, [p] => checkTargetUsing G images P C (refineBy G (entry c) (PromiseCalls.aliasFacts (HeapKnowledge.dropResult (outFacts G c)).links (yieldFacts c.yields false) 0) 0)
      l p (HeapKnowledge.dropResult (outFacts G c)) c.implies c.arguments
  | .branch y n, [py,pn] => decide (expand G (result c) = [.bool]) &&
      checkTargetUsing G images P C (refineBy G (entry c) (PromiseCalls.aliasFacts (HeapKnowledge.dropResult (outFacts G c)).links (yieldFacts c.yields true) 0) 0) y py
        (HeapKnowledge.dropResult (HeapKnowledge.promoteTruthy (outFacts G c) 0 true)) c.implies c.arguments &&
      checkTargetUsing G images P C (refineBy G (entry c) (PromiseCalls.aliasFacts (HeapKnowledge.dropResult (outFacts G c)).links (yieldFacts c.yields false) 0) 0) n pn
        (HeapKnowledge.dropResult (HeapKnowledge.promoteTruthy (outFacts G c) 0 false)) c.implies c.arguments
  | .branchBind y n, [py,pn] => onlyBoolean G (result c) &&
      checkBranchTargetUsing G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts (outFacts G c).links (yieldFacts c.yields true) 1) 0)
        (.boolean true) y py (outFacts G c) (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression)) &&
      checkBranchTargetUsing G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts (outFacts G c).links (yieldFacts c.yields false true) 1) 0)
        (.boolean false) n pn (outFacts G c) (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression))
  | .tagBind t y n, [py,pn] =>
      checkBranchTargetUsing G images P C
        (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts (outFacts G c).links (yieldFacts c.yields (truthyBoolean G t (result c))) 1) 0)
        (.tag t true) y py (outFacts G c) (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression)) &&
      checkBranchTargetUsing G images P C (refineBy G (result c :: entry c) (PromiseCalls.aliasFacts (outFacts G c).links (yieldFacts c.yields false) 1) 0)
        (.tag t false) n pn (outFacts G c) (edgeImplications c.implies c.yields true)
        (pushedSources c.arguments (aliasedRead c.arguments node.expression))
  | _, _ => false
  ) := by
  simp only [checkNodeUsing, checkNodeResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, CheckResult.accepted_bind_ofBool, checkHandlerUsing,
    Bool.and_assoc]
  congr 1
  cases node.continuation <;> cases c.edges <;>
    (try (rename_i p ps; cases ps <;> (try (rename_i q qs; cases qs)))) <;>
    simp only [CheckResult.accepted_bind, CheckResult.accepted_ofBool,
      checkTargetUsing, checkBranchTargetUsing] <;> rfl

/-- Enumeration comes from the program, not a certificate-supplied edge list. -/
@[nospecialize] def checkGraphResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι) := []) : CheckResult ι Unit :=
  -- The member-test field slices the nodes' yields read, each computed once.
  let slices := FieldSlices.ofCertificate G C
  (CheckResult.ofBool (decide (P.length = C.length))).bind fun _ =>
  (CheckResult.all (List.range P.length) fun l =>
    match P[l]?, C[l]? with
    | some node, some c => (checkNodeResult (checker := checker) (sums := sums) (slices := slices)
        G images Rty P C node c codes).at (.node l)
    | _, _ => failure).bind fun _ =>
  CheckResult.ofBool (P.all (fun node => ObjectCoherence.sourceTerm node.expression))

@[nospecialize] def checkGraphUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι) := []) : Bool :=
  (checkGraphResult (checker := checker) (sums := sums) G images Rty P C codes).accepted

theorem FieldSlices.ofCertificate_eq [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι) :
    FieldSlices.ofCertificate G C = PromiseCalls.FieldSlices.direct G :=
  PromiseCalls.FieldSlices.eq_direct _

theorem checkGraphUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι)) :
    checkGraphUsing (checker := checker) (sums := sums) G images Rty P C codes = (
  decide (P.length = C.length) && (List.range P.length).all (fun l =>
    match P[l]?, C[l]? with
    | some node, some c => checkNodeUsing (checker := checker) (sums := sums) G images Rty P C node c codes
    | _, _ => false) && P.all (fun node => ObjectCoherence.sourceTerm node.expression)
  ) := by
  simp only [checkGraphUsing, checkGraphResult, FieldSlices.ofCertificate_eq, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, CheckResult.accepted_all, Bool.and_assoc]
  congr 2
  apply congrArg
  funext l
  cases P[l]? <;> cases C[l]? <;> rfl

/-! A certificate whose nodes reference their steps' proofs, or state only
their sequents, is checked as the certificate with every derivation written
out: the same graph check, node by node and at every edge. -/

def TargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι) (Γ : List (Ty ι)) (l : Target)
    (facts : HeapKnowledge.Knowledge) (xs : List (Implication ι)) (sources : List Nat) : Prop :=
  ∃ c, C[l.label]? = some c ∧ (unsatisfiable G Γ = true ∨ (MappedCovers G Γ (entry c) l.mapping ∧
    KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry c)) (HeapKnowledge.withTypedLinks G Γ (withTypedCells G Γ c.knowledge l.mapping facts)) c.knowledge l.mapping = true ∧
      carries G Γ facts xs sources l c = true))

def BranchTargetOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (o : Observation) (l : Target) (facts : HeapKnowledge.Knowledge)
    (xs : List (Implication ι)) (sources : List Nat) : Prop :=
  ∃ c, C[l.label]? = some c ∧ (branchUnreachable G Γ o = true ∨ (ObservedCovers G Γ (entry c) 0 o l.mapping (readFields facts 0)
    (optionalFields facts 0) (HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ facts 0 o)) ∧ KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G (entry c)) (HeapKnowledge.observeTyped G Γ (withTypedCells G Γ c.knowledge l.mapping facts) 0 o) c.knowledge l.mapping = true ∧
    carries G Γ facts xs sources l c = true))

/-- Where a throw out of a node in environment `ρ` may go: nowhere (it leaves
the program), or a target the thrown value and the surviving facts enter. -/
def HandlerOk [DecidableEq ι] (G : NormalGraph ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (xs : List (Implication ι)) (arg : List Nat) (ε : HeapKnowledge.EntryState) (ρ : Env) :
    Option Target → Prop
  | none => True
  | some l => ∃ T facts, admitsAll G T = true ∧
      TargetOk G C (T :: Γ) l facts (edgeImplications xs [] true) (pushedSources arg false) ∧
      ∀ v h, HeapKnowledge.Holds facts ε (push v ρ) h

/-- What a return establishes under the goal. -/
def ReturnOk [DecidableEq ι] (G : NormalGraph ι) (goal : Goal ι) (Γ : List (Ty ι)) (A : Ty ι)
    (ys : List (Yield ι)) (arg : List Nat) : Prop :=
  match goal with
  | .plain R => A = R ∨ A = []
  | .guards T _ => onlyBoolean G A = true ∧ ((∀ n W v, meaning G A n W v → v = .tru → False) ∨
      ∃ p B, p ∈ arg ∧ (refineBy G Γ (yieldFacts ys true) 0)[p]? = some B ∧ FamLe (meaning G B) (meaning G T))
  | .asserts T _ => (∀ n W v, meaning G A n W v → v = .undef) ∧ (A = [] ∨
      ∃ p B, p ∈ arg ∧ (refineBy G Γ (yieldFacts ys false) 0)[p]? = some B ∧ FamLe (meaning G B) (meaning G T))

def ContinuationOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Goal ι) (C : Certificate ι)
    (Γ : List (Ty ι)) (A : Ty ι) (facts : HeapKnowledge.Knowledge) (xs : List (Implication ι))
    (ys : List (Yield ι)) (arg : List Nat) (aliased : Bool) : Continuation → Prop
  | .ret => ReturnOk G Rty Γ A ys arg
  | .bind l => TargetOk G C (refineBy G (A :: Γ) (PromiseCalls.aliasFacts facts.links (yieldFacts ys false) 1) 0) l facts
      (edgeImplications xs ys true) (pushedSources arg aliased)
  | .effect l => TargetOk G C (refineBy G Γ (PromiseCalls.aliasFacts (HeapKnowledge.dropResult facts).links (yieldFacts ys false) 0) 0) l
      (HeapKnowledge.dropResult facts) xs arg
  | .branch y n => Represents G A .bool ∧
      TargetOk G C (refineBy G Γ (PromiseCalls.aliasFacts (HeapKnowledge.dropResult facts).links (yieldFacts ys true) 0) 0) y
        (HeapKnowledge.dropResult (HeapKnowledge.promoteTruthy facts 0 true)) xs arg ∧
      TargetOk G C (refineBy G Γ (PromiseCalls.aliasFacts (HeapKnowledge.dropResult facts).links (yieldFacts ys false) 0) 0) n
        (HeapKnowledge.dropResult (HeapKnowledge.promoteTruthy facts 0 false)) xs arg
  | .branchBind y n => onlyBoolean G A = true ∧
      BranchTargetOk G C (refineBy G (A::Γ) (PromiseCalls.aliasFacts facts.links (yieldFacts ys true) 1) 0) (.boolean true) y facts
        (edgeImplications xs ys true) (pushedSources arg aliased) ∧
      BranchTargetOk G C (refineBy G (A::Γ) (PromiseCalls.aliasFacts facts.links (yieldFacts ys false true) 1) 0) (.boolean false) n facts
        (edgeImplications xs ys true) (pushedSources arg aliased)
  | .tagBind t y n =>
      BranchTargetOk G C (refineBy G (A::Γ) (PromiseCalls.aliasFacts facts.links (yieldFacts ys (truthyBoolean G t A)) 1) 0) (.tag t true) y facts
        (edgeImplications xs ys true) (pushedSources arg aliased) ∧
      BranchTargetOk G C (refineBy G (A::Γ) (PromiseCalls.aliasFacts facts.links (yieldFacts ys false) 1) 0) (.tag t false) n facts
        (edgeImplications xs ys true) (pushedSources arg aliased)

theorem target_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {P C Γ l p facts xs sources}
    (hc : checkTargetUsing G images P C Γ l p facts xs sources = true) : TargetOk G C Γ l facts xs sources := by
  rw [checkTargetUsing_eq] at hc
  split at hc
  · rename_i node c hn he
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hu | hc
    · exact ⟨c, he, .inl hu⟩
    · exact ⟨c, he, .inr ⟨checkMapped_sound hc.1, hc.2.1, hc.2.2⟩⟩
  · contradiction

/-- A checked witness edge establishes both the saved value's type and the
receiver and field from which that value was read. -/
theorem witness_edge_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {P C Γ target p facts xs sources c ρ n W h receiver witness field optional A}
    (checked : checkTargetUsing G images P C Γ target p facts xs sources = true)
    (destination : C[target.label]? = some c)
    (typed : (entry c)[witness]? = some A)
    (linked : (⟨receiver,witness,false,field,optional⟩ : HeapLinks.Link) ∈ c.knowledge.links)
    (he : EnvOk G Γ ρ n W) (hk : HeapKnowledge.Holds facts ε ρ h)
    (hcells : ∀ wanted, HeapFacts.Holds (HeapExpressionRules.typedCells G Γ wanted) ρ h) :
    meaning G A n W (mapEnv target.mapping ρ witness) ∧
      ∃ flds cls oid, mapEnv target.mapping ρ receiver = .objAt flds cls oid ∧
        HeapFacts.ReadGave flds field h (mapEnv target.mapping ρ witness) := by
  obtain ⟨d, hd, hcases⟩ := target_sound checked
  rcases hcases with hu | ⟨covers, knowledge, _⟩
  · exact (unsatisfiable_sound hu he).elim
  have same : d = c := Option.some.inj (hd.symm.trans destination)
  subst d
  constructor
  · exact (covers.env he).2 witness A typed
  · have link := (KnowledgeExpand.checkIn_sound knowledge (KnowledgeExpand.ctxOf_ok (covers.env he))
      (HeapKnowledge.withTypedLinks_holds he (withTypedCells_holds hcells (fun _ _ hr => HeapExpressionRules.typeValues_sound hr he) hk))).2.2.1 _ linked
    cases optional <;> simp only [Bool.false_eq_true, ite_false, ite_true] at link
    · obtain ⟨flds, cls, oid, loc, obj, key, value⟩ := link
      exact ⟨flds, cls, oid, obj, HeapFacts.ReadGave.present key value⟩
    · exact link

theorem branch_target_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {P C Γ q l p facts xs sources}
    (hc : checkBranchTargetUsing G images P C Γ q l p facts xs sources = true) :
    BranchTargetOk G C Γ q l facts xs sources := by
  rw [checkBranchTargetUsing_eq] at hc
  split at hc
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hu | hc
    · exact ⟨_, by assumption, .inl hu⟩
    · exact ⟨_, by assumption, .inr ⟨checkObserved_sound hc.1, hc.2.1, hc.2.2⟩⟩
  · contradiction

theorem return_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {goal : Goal ι}
    {c : NodeEvidence ι} (hc : (checkReturnResult G images goal c).accepted = true) :
    ReturnOk G goal (entry c) (result c) c.yields c.arguments := by
  have within : ∀ {facts T}, (checkReturnResult.argumentWithin G images c facts T).accepted = true →
      ∃ p B, p ∈ c.arguments ∧ (refineBy G (entry c) facts 0)[p]? = some B ∧ FamLe (meaning G B) (meaning G T) := by
    intro facts T h
    unfold checkReturnResult.argumentWithin at h
    split at h
    · rename_i p proof _
      split at h
      · rename_i hmem
        split at h
        · rename_i B hB
          rw [ProgramCertificates.checkSubtypeUsing_accepted] at h
          exact ⟨p, B, List.contains_iff_mem.mp hmem, hB, PositiveCertificates.acceptedUsing h⟩
        · exact absurd h (by rw [CheckResult.accepted, CheckResult.value_failure]; simp)
      · exact absurd h (by rw [CheckResult.accepted, CheckResult.value_failure]; simp)
    · exact absurd h (by rw [CheckResult.accepted, CheckResult.value_failure]; simp)
  cases goal with
  | plain R =>
    simpa [checkReturnResult, CheckResult.accepted_ofBool, ReturnOk] using hc
  | guards T s =>
    simp only [checkReturnResult, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
      CheckResult.accepted_orElse, Bool.and_eq_true, Bool.or_eq_true] at hc
    refine ⟨hc.1, ?_⟩
    rcases hc.2 with himp | hw
    · exact .inl fun n W v hv ht => impossible_sound himp hv (show Observation.holds (.boolean true) v from ht)
    · exact .inr (within hw)
  | asserts T s =>
    simp only [checkReturnResult, CheckResult.accepted_bind, CheckResult.accepted_ofBool,
      CheckResult.accepted_orElse, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at hc
    exact ⟨fun n W v hv => PromiseCalls.onlyUndef_sound hc.1 hv, hc.2.imp id within⟩

def ExpressionOk [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) : Prop :=
  ∀ ε n W h ρ, EnvOk G (entry c) ρ n W → ImpliesOk G c.implies ρ n W → HeapKnowledge.Holds (entryFacts G c) ε ρ h →
    WorldAdm W → HeapOk n W h →
    HeapObservations.SafePost (excOf G) (fun k U u => meaning G (result c) k U u ∧ YieldsOk G c.yields ρ k U u)
      (fun h' v => HeapKnowledge.Holds (outFacts G c) ε (push v ρ) h') n W h (instantiate 0 ρ t)

theorem handler_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} {P C node c}
    (hc : checkHandlerUsing G images P C node c = true) {ρ h} (hk : HeapKnowledge.Holds (entryFacts G c) ε ρ h) :
    HandlerOk G C (entry c) c.implies c.arguments ε ρ node.handler := by
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
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (hc : checkNodeUsing (checker := checker) (sums := sums) G images Rty P C node c codes = true)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _)
    (hsums : SummariesSound G images sums := by exact Verification.ProgramCertificates.summariesSound_none _ _) :
    ExpressionOk G c node.expression ∧
    ContinuationOk G Rty C (entry c) (result c) (outFacts G c) c.implies c.yields c.arguments
      (aliasedRead c.arguments node.expression) node.continuation ∧
    ∀ ε ρ h, HeapKnowledge.Holds (entryFacts G c) ε ρ h → HandlerOk G C (entry c) c.implies c.arguments ε ρ node.handler := by
  simp only [checkNodeUsing_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine ⟨?_, ?_, fun ε ρ h hk => handler_sound hc.1.1.1.1.2 hk⟩
  · intro ε n W h ρ he hi hf hw hh
    have hterm := hc.1.1.1.1.1
    have hy := hc.1.2
    unfold checkYields at hy
    split at hy
    · rename_i effect a T hp
      simp only [Bool.and_eq_true] at hy
      have hs := PromiseCalls.promiseCall_sound hp hy.1.1 hcodes hsums hy.1.2 he hf hw hh
      have ho : ∀ out ∈ [HeapExpressionRules.ordinaryOutput (entryFacts G c), PromiseCalls.promiseOutput effect (entryFacts G c)],
          HeapObservations.SafePost (excOf G) (fun m U u => meaning G (claim c.expression).type m U u ∧ YieldsOk G c.yields ρ m U u)
            (fun h' v => HeapKnowledge.Holds out ε (push v ρ) h') n W h (instantiate 0 ρ (claim c.expression).term) := by
        intro out hout
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
        rcases hout with rfl | rfl
        · exact HeapObservations.consequence (fun _ _ _ hv => hv) (fun _ _ hq => PromiseCalls.promiseOutput_ordinary hq) hs
        · exact hs
      obtain ⟨out, hout, hor⟩ := List.any_eq_true.mp hy.2
      rcases Bool.or_eq_true_iff.mp hor with hsame | hstable
      · have hs' := HeapObservations.weaken (fun _ _ hq => outFacts_holds he (outputFits_sound hsame he hq))
          (ho out hout)
        simpa only [entry, result, hterm] using hs'
      · have hs' := HeapExpressionRules.withStable_sound (Γ := entry c) (out := out)
          he hf hh (by simpa only [entry] using ho out hout)
        have hs'' := HeapObservations.weaken (fun _ _ hq => outFacts_holds he (outputFits_sound hstable he hq)) hs'
        simpa only [entry, result, hterm] using hs''
    · have hany := hc.1.1.2
      obtain ⟨out, hrun, hfit⟩ : ∃ out, (checker.run (claim c.expression) (entryFacts G c)
          (c.effect.getD (.ordinary c.expression)) codes sums).value = some out ∧ outputFits G c out = true := by
        cases hv : (checker.run (claim c.expression) (entryFacts G c)
          (c.effect.getD (.ordinary c.expression)) codes sums).value <;> rw [hv] at hany
        · cases hany
        · exact ⟨_, rfl, hany⟩
      have ht := HeapObservations.weaken (fun _ _ ho => outFacts_holds he (outputFits_sound hfit he ho))
        (checker.sound hrun hcodes hsums he hf hw hh)
      have ht' := PromiseCalls.yieldFollows_sound hy he hi hh hf.2.2.1 ht
      simpa only [entry, result, hterm] using ht'
  · have hk := hc.2
    split at hk <;> (try (rename_i hcont hedges; rw [hcont]))
    · exact return_sound hk
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
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (hg : checkGraphUsing (checker := checker) (sums := sums) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) (hc : C[l]? = some c) :
    ∃ node : Node, P[l]? = some node ∧ ExpressionOk G c node.expression ∧
      ContinuationOk G Rty C (entry c) (result c) (outFacts G c) c.implies c.yields c.arguments
        (aliasedRead c.arguments node.expression) node.continuation ∧
      ∀ ε ρ h, HeapKnowledge.Holds (entryFacts G c) ε ρ h → HandlerOk G C (entry c) c.implies c.arguments ε ρ node.handler := by
  simp only [checkGraphUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
  have hg := hg.1
  have hl : l < P.length := by
    rw [hg.1]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hn : P[l]? = some (P[l]'hl) := by simp [hl]
  have h := hg.2 l (List.mem_range.mpr hl)
  rw [hn, hc] at h
  exact ⟨_, hn, node_sound h hcodes hsums⟩

/-- A state assertion used only in the global safety proof. `v0` is the
argument a promise goal is about. -/
def StateOk [DecidableEq ι] (G : NormalGraph ι) (Rty : Goal ι) (C : Certificate ι) (v0 : Tm)
    (ε : HeapKnowledge.EntryState) (n : Nat) (W : WorldT n) (h : Heap) : State → Prop
  | .at l ρ => ∃ c, C[l]? = some c ∧ EnvOk G (entry c) ρ n W ∧ ImpliesOk G c.implies ρ n W ∧
      ArgumentsOk c.arguments ρ v0 ∧ HeapKnowledge.Holds c.knowledge ε ρ h
  | .eval t ρ k x => ∃ Γ A out xs ys arg aliased, EnvOk G Γ ρ n W ∧ ImpliesOk G xs ρ n W ∧
      ArgumentsOk arg ρ v0 ∧ (aliased = true → t = v0) ∧
      HeapObservations.SafePost (excOf G) (fun k U u => meaning G A k U u ∧ YieldsOk G ys ρ k U u)
        (fun h' v => HeapKnowledge.Holds out ε (push v ρ) h') n W h t ∧
      ContinuationOk G Rty C Γ A out xs ys arg aliased k ∧ HandlerOk G C Γ xs arg ε ρ x
  | .done v => isVal v = true ∧ GoalHolds G Rty v0 n W v
  | .raised v => Scoped 0 v ∧ excOf G n W v

theorem target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ l ρ n W h facts xs sources v0}
    (ht : TargetOk G C Γ l facts xs sources) (he : EnvOk G Γ ρ n W) (hi : ImpliesOk G xs ρ n W)
    (ha : ArgumentsOk sources ρ v0) (hf : HeapKnowledge.Holds facts ε ρ h)
    (hcells : ∀ wanted, HeapFacts.Holds (HeapExpressionRules.typedCells G Γ wanted) ρ h) :
    StateOk G Rty C v0 ε n W h (.at l.label (mapEnv l.mapping ρ)) := by
  obtain ⟨c, hc, hcases⟩ := ht
  rcases hcases with hu | ⟨hcov, hfact, hcar⟩
  · exact (unsatisfiable_sound hu he).elim
  simp only [carries, Bool.and_eq_true] at hcar
  exact ⟨c, hc, hcov.env he,
    PromiseCalls.impliesCheck_sound hcar.1 he (PromiseCalls.aliasImplications_holds hf.2.2.1 hi),
    PromiseCalls.argFollows_sound hcar.2 (PromiseCalls.aliasSources_holds hf.2.2.1 ha),
    KnowledgeExpand.checkIn_sound hfact (KnowledgeExpand.ctxOf_ok (hcov.env he))
      (HeapKnowledge.withTypedLinks_holds he (withTypedCells_holds hcells (fun _ _ hr => HeapExpressionRules.typeValues_sound hr he) hf))⟩

theorem branch_target_state [DecidableEq ι] {G : NormalGraph ι} {Rty C Γ q l ρ n W h facts xs sources v0}
    (ht : BranchTargetOk G C Γ q l facts xs sources) (he : EnvOk G Γ ρ (n+1) W) (hh : HeapOk (n+1) W h)
    (hq : q.holds (ρ 0)) (hi : ImpliesOk G xs ρ (n+1) W) (ha : ArgumentsOk sources ρ v0)
    (hf : HeapKnowledge.Holds facts ε ρ h) :
    StateOk G Rty C v0 ε n (trunc n (Nat.le_succ n) W) h (.at l.label (mapEnv l.mapping ρ)) := by
  obtain ⟨c,hc,hcases⟩ := ht
  rcases hcases with hu | ⟨hcov,hfact,hcar⟩
  · simp only [branchUnreachable, Bool.or_eq_true] at hu
    rcases hu with hcontext | hanswer
    · exact (unsatisfiable_sound hcontext he).elim
    cases htype : Γ[0]? with
    | none => simp [htype] at hanswer
    | some A => exact (impossible_sound (by simpa [htype] using hanswer) (he.2 0 A htype) hq).elim
  simp only [carries, Bool.and_eq_true] at hcar
  exact ⟨c,hc,(hcov.env he hq hh (readFields_holds hf) (optionalFields_holds hf)
    (HeapKnowledge.aliasCells_holds (HeapKnowledge.observeTyped_holds he hf hq))).transfer n
    (Nat.le_succ n) _ (WExt_refl _),
    (PromiseCalls.impliesCheck_sound hcar.1 he (PromiseCalls.aliasImplications_holds hf.2.2.1 hi)).transfer n
      (Nat.le_succ n) _ (WExt_refl _),
    PromiseCalls.argFollows_sound hcar.2 (PromiseCalls.aliasSources_holds hf.2.2.1 ha),
    KnowledgeExpand.checkIn_sound hfact (KnowledgeExpand.ctxOf_ok (hcov.env he hq hh (readFields_holds hf) (optionalFields_holds hf)
      (HeapKnowledge.aliasCells_holds (HeapKnowledge.observeTyped_holds he hf hq))))
      (HeapKnowledge.observeTyped_holds he (withTypedCells_holds (fun _ => HeapExpressionRules.typedCells_holds he hh) (fun _ _ hr => HeapExpressionRules.typeValues_sound hr he) hf) hq)⟩

/-- A context refined by facts its values meet, with a heap meeting the
world (`PromiseCalls.envOk_refineBy`). -/
theorem refined_env [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W} {ys : List (Yield ι)}
    {u : Tm} {answered falsified : Bool} {h : Heap} (hh : HeapOk (n+1) W h) (he : EnvOk G Γ ρ (n+1) W)
    (hy : YieldsOk G ys ρ (n+1) W u)
    (ha : answered = true → u = .tru) (hfl : falsified = true → u = .fls) :
    EnvOk G (refineBy G Γ (yieldFacts ys answered falsified) 0) ρ (n+1) W :=
  PromiseCalls.envOk_refineBy hh he fun f hf => by
    simpa using PromiseCalls.yieldFacts_holds hy ha hfl f hf

/-- The same, at the slots alias links relate too. -/
theorem refined_env_aliased [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W} {ys : List (Yield ι)}
    {u : Tm} {answered falsified : Bool} {links : HeapLinks.Links} {h h' : Heap} (hh : HeapOk (n+1) W h')
    (he : EnvOk G Γ ρ (n+1) W)
    (hy : YieldsOk G ys ρ (n+1) W u) (ha : answered = true → u = .tru) (hfl : falsified = true → u = .fls)
    (hl : HeapLinks.Holds links ρ h) :
    EnvOk G (refineBy G Γ (PromiseCalls.aliasFacts links (yieldFacts ys answered falsified) 0) 0) ρ (n+1) W :=
  PromiseCalls.envOk_refineBy hh he (PromiseCalls.aliasFacts_holds hl fun f hf => by
    simpa using PromiseCalls.yieldFacts_holds hy ha hfl f hf)

theorem refined_push_aliased [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W} {ys : List (Yield ι)}
    {A : Ty ι} {u : Tm} {answered falsified : Bool} {links : HeapLinks.Links} {h h' : Heap}
    (hh : HeapOk (n+1) W h') (he : EnvOk G Γ ρ (n+1) W)
    (hu : meaning G A (n+1) W u) (hy : YieldsOk G ys ρ (n+1) W u) (ha : answered = true → u = .tru)
    (hfl : falsified = true → u = .fls) (hl : HeapLinks.Holds links (push u ρ) h) :
    EnvOk G (refineBy G (A :: Γ) (PromiseCalls.aliasFacts links (yieldFacts ys answered falsified) 1) 0) (push u ρ) (n+1) W :=
  PromiseCalls.envOk_refineBy hh (he.push hu) (PromiseCalls.aliasFacts_holds hl fun f hf => by
    simpa [push] using PromiseCalls.yieldFacts_holds hy ha hfl f hf)

theorem pushed_arguments {arg : List Nat} {aliased : Bool} {ρ v0 u}
    (ha : ArgumentsOk arg ρ v0) (hal : aliased = true → u = v0) :
    ArgumentsOk (pushedSources arg aliased) (push u ρ) v0 := by
  intro p hp
  simp only [pushedSources, List.mem_append] at hp
  rcases hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ha q hq
  · cases aliased with
    | false => cases hp
    | true =>
      cases List.mem_singleton.mp hp
      exact hal rfl

theorem goal_return [DecidableEq ι] {G : NormalGraph ι} {goal : Goal ι} {Γ A ys arg ρ n W v0 t}
    {h : Heap} (hh : HeapOk (n+1) W h)
    (hr : ReturnOk G goal Γ A ys arg) (he : EnvOk G Γ ρ (n+1) W) (ht : meaning G A (n+1) W t)
    (hy : YieldsOk G ys ρ (n+1) W t) (ha : ArgumentsOk arg ρ v0) :
    GoalHolds G goal v0 n (trunc n (Nat.le_succ n) W) t := by
  have promised : ∀ {answered p B T}, (answered = true → t = .tru) → p ∈ arg →
      (refineBy G Γ (yieldFacts ys answered) 0)[p]? = some B → FamLe (meaning G B) (meaning G T) →
      meaning G T n (trunc n (Nat.le_succ n) W) v0 := by
    intro answered p B T hans hp hB hle
    have henv := refined_env (falsified := false) hh he hy hans (fun h => by cases h)
    have hv0 : ρ p = v0 := ha p hp
    rw [← hv0]
    exact (meaning_adm G T).down n W _ (hle _ _ _ (henv.2 p B hB))
  cases goal with
  | plain R =>
    rcases (hr : A = R ∨ A = []) with rfl | rfl
    · exact (meaning_adm G A).down n W t ht
    · obtain ⟨a, ha, _⟩ := ht
      cases ha
  | guards T s =>
    obtain ⟨hb, hcase⟩ := hr
    rcases onlyBoolean_sound hb ht with rfl | rfl
    · refine .inl ⟨rfl, ?_⟩
      rcases hcase with himp | ⟨p, B, hp, hB, hle⟩
      · exact (himp _ _ _ ht rfl).elim
      · exact promised (fun _ => rfl) hp hB hle
    · exact .inr rfl
  | asserts T s =>
    obtain ⟨hu, hcase⟩ := hr
    rcases hcase with rfl | ⟨p, B, hp, hB, hle⟩
    · obtain ⟨a, ha, _⟩ := ht
      cases ha
    · exact ⟨hu _ _ _ ht, promised (answered := false) (fun h => by cases h) hp hB hle⟩

/-- One checked graph transition preserves the point assertions. Keeping this
step lemma separate lets additional postconditions reuse exactly the same
control-flow and handler reasoning as ordinary safety. -/
theorem state_progress [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (hg : checkGraphUsing (checker := checker) (sums := sums) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) {v0 : Tm} (hv0 : isVal v0 = true)
    {n W h s} (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : StateOk G Rty C v0 ε (n+1) W h s) :
    ((∃ v, s = .done v ∧ isVal v = true ∧ GoalHolds G Rty v0 (n+1) W v) ∨
      (∃ v, s = .raised v ∧ Scoped 0 v ∧ excOf G (n+1) W v)) ∨
    ∃ U : WorldT n, ∃ h' s', WExt (trunc n (Nat.le_succ n) W) U ∧
      WorldAdm U ∧ Transition P h s h' s' ∧ HeapOk n U h' ∧ StateOk G Rty C v0 ε n U h' s' := by
  have hw' := WorldAdm_trunc (Nat.le_succ n) hw
  have hh' := HeapOk_trunc n W h hh
  let U := trunc n (Nat.le_succ n) W
  cases s with
  | «at» l ρ =>
    obtain ⟨c, hc, he, hi, ha, hf⟩ := hs
    obtain ⟨node, hn, ht, hk, hx⟩ := graph_node hg hcodes hsums hc
    have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
    have hi' := hi.transfer n (Nat.le_succ n) U (WExt_refl _)
    have hal : aliasedRead c.arguments node.expression = true →
        instantiate 0 ρ node.expression = v0 := by
      intro hal
      unfold aliasedRead at hal
      split at hal
      · rename_i q hq
        rw [hq]
        simpa [instantiate] using ha q (List.contains_iff_mem.mp hal)
      · cases hal
    exact Or.inr ⟨U, h, _, WExt_refl _, hw', .enter hn, hh',
      ⟨entry c, result c, (outFacts G c), c.implies, c.yields, c.arguments, _, he', hi', ha, hal,
        ht ε n U h ρ he' hi' (entryFacts_holds he' hf) hw' hh', hk, hx ε ρ h (entryFacts_holds he' hf)⟩⟩
  | done v => exact Or.inl (Or.inl ⟨v, rfl, hs⟩)
  | raised v => exact Or.inl (Or.inr ⟨v, rfl, hs⟩)
  | eval t ρ k x =>
    obtain ⟨Γ, A, out, xs, ys, arg, aliased, he, hi, ha, hal, ht, hk, hx⟩ := hs
    rcases ht with (⟨hv, ⟨hA, hy⟩, hf⟩ | ⟨v, hr, hsc⟩) | ⟨V, h', t', hx', hu, step, hok, hsafe⟩
    · have hi' := hi.transfer n (Nat.le_succ n) U (WExt_refl _)
      have hy' := hy.transfer n (Nat.le_succ n) U (WExt_refl _)
      cases k with
      | ret =>
        exact Or.inr ⟨U, h, .done t, WExt_refl _, hw', .ret hv, hh',
          ⟨hv, goal_return hh hk he hA hy ha⟩⟩
      | bind l =>
        exact Or.inr ⟨U, h, .at l.label (mapEnv l.mapping (push t ρ)), WExt_refl _, hw', .bind hv, hh',
          (target_state hk ((refined_push_aliased hh he hA hy (answered := false) (fun h => by cases h) (fun h => by cases h) hf.2.2.1).transfer n (Nat.le_succ n) U (WExt_refl _))
            (PromiseCalls.edgeImplications_holds hi' hy') (pushed_arguments ha hal) hf
            (fun _ => HeapExpressionRules.typedCells_holds (refined_push_aliased hh he hA hy (answered := false) (fun h => by cases h) (fun h => by cases h) hf.2.2.1) hh))⟩
      | effect l =>
        exact Or.inr ⟨U, h, .at l.label (mapEnv l.mapping ρ), WExt_refl _, hw', .effect hv, hh',
          (target_state hk ((refined_env_aliased hh he hy (answered := false) (fun h => by cases h) (fun h => by cases h)
            (HeapKnowledge.dropResult_holds hf).2.2.1).transfer n (Nat.le_succ n) U (WExt_refl _)) hi' ha (HeapKnowledge.dropResult_holds hf)
            (fun _ => HeapExpressionRules.typedCells_holds (refined_env_aliased hh he hy (answered := false) (fun h => by cases h) (fun h => by cases h)
              (HeapKnowledge.dropResult_holds hf).2.2.1) hh))⟩
      | branch y no =>
        have hb := represents_raw hk.1 (n+1) W t hA
        rcases hb with rfl | rfl
        · exact Or.inr ⟨U, h, .at y.label (mapEnv y.mapping ρ), WExt_refl _, hw', .yes, hh',
            (target_state hk.2.1 ((refined_env_aliased hh he hy (answered := true) (fun _ => rfl) (fun h => by cases h)
              (HeapKnowledge.dropResult_holds hf).2.2.1).transfer n (Nat.le_succ n) U (WExt_refl _)) hi' ha
              (HeapKnowledge.dropResult_holds (HeapKnowledge.promoteTruthy_holds hf rfl))
              (fun _ => HeapExpressionRules.typedCells_holds (refined_env_aliased hh he hy (answered := true) (fun _ => rfl) (fun h => by cases h)
                (HeapKnowledge.dropResult_holds hf).2.2.1) hh))⟩
        · exact Or.inr ⟨U, h, .at no.label (mapEnv no.mapping ρ), WExt_refl _, hw', .no, hh',
            (target_state hk.2.2 ((refined_env_aliased hh he hy (answered := false) (fun h => by cases h) (fun h => by cases h)
              (HeapKnowledge.dropResult_holds hf).2.2.1).transfer n (Nat.le_succ n) U (WExt_refl _)) hi' ha
              (HeapKnowledge.dropResult_holds (HeapKnowledge.promoteTruthy_holds hf rfl))
              (fun _ => HeapExpressionRules.typedCells_holds (refined_env_aliased hh he hy (answered := false) (fun h => by cases h) (fun h => by cases h)
                (HeapKnowledge.dropResult_holds hf).2.2.1) hh))⟩
      | branchBind y no =>
        have hb := onlyBoolean_sound hk.1 hA
        rcases hb with rfl | rfl
        · exact Or.inr ⟨U, h, _, WExt_refl _, hw', .yesBind, hh',
            (branch_target_state hk.2.1 (refined_push_aliased hh he hA hy (answered := true) (fun _ => rfl) (fun h => by cases h) hf.2.2.1) hh rfl
              (PromiseCalls.edgeImplications_holds hi hy) (pushed_arguments ha hal) hf)⟩
        · exact Or.inr ⟨U, h, _, WExt_refl _, hw', .noBind, hh',
            (branch_target_state hk.2.2 (refined_push_aliased hh he hA hy (answered := false) (falsified := true) (fun h => by cases h) (fun _ => rfl) hf.2.2.1) hh rfl
              (PromiseCalls.edgeImplications_holds hi hy) (pushed_arguments ha hal) hf)⟩
      | tagBind tag y no =>
        cases htag : tagHoldsIn h tag t with
        | true =>
          exact Or.inr ⟨U, h, _, WExt_refl _, hw', .tagBind hv, hh',
            (by
              simpa [htag] using (branch_target_state hk.1
                (refined_push_aliased hh he hA hy (answered := truthyBoolean G tag A)
                  (fun hb => truthyBoolean_sound hb hA htag) (fun h => by cases h) hf.2.2.1) hh (tagHolds_of_heap htag)
                (PromiseCalls.edgeImplications_holds hi hy) (pushed_arguments ha hal) hf))⟩
        | false =>
          exact Or.inr ⟨U, h, _, WExt_refl _, hw', .tagBind hv, hh',
            (by
              simpa [htag] using (branch_target_state hk.2
                (refined_push_aliased hh he hA hy (answered := false) (fun h => by cases h) (fun h => by cases h) hf.2.2.1) hh (tagHolds_of_heap htag)
                (PromiseCalls.edgeImplications_holds hi hy) (pushed_arguments ha hal) hf))⟩
    · have he' := he.transfer n (Nat.le_succ n) U (WExt_refl _)
      have hi' := hi.transfer n (Nat.le_succ n) U (WExt_refl _)
      cases x with
      | none =>
        exact Or.inr ⟨U, h, .raised v, WExt_refl _, hw', .raise hr, hh',
          ⟨hsc.1, (builtinExc_adm G _).down n W v hsc.2⟩⟩
      | some l =>
        obtain ⟨T, facts, hT, htarget, hfacts⟩ := hx
        have hvT := admitsAll_sound hT ((builtinExc_adm G _).down n W v hsc.2)
        exact Or.inr ⟨U, h, _, WExt_refl _, hw', .handle hr, hh',
          (target_state htarget (he'.push hvT)
            (PromiseCalls.edgeImplications_holds (ys := []) hi' (fun y hy => by cases hy))
            (pushed_arguments ha (fun h => by cases h)) (hfacts v h)
            (fun _ => HeapExpressionRules.typedCells_holds (he.push (admitsAll_sound hT hsc.2)) hh))⟩
    · have hal' : aliased = true → t' = v0 := by
        intro hal'
        cases hal hal'
        exact absurd step (value_no_step hv0)
      exact Or.inr ⟨V, h', .eval t' ρ k x, hx', hu, .expr step, hok,
        ⟨Γ,A,out,xs,ys,arg,aliased,he.transfer n (Nat.le_succ n) V hx',hi.transfer n (Nat.le_succ n) V hx',
          ha,hal',hsafe,hk,hx⟩⟩

/-- Global safety is by execution budget, not by acyclicity or graph unfolding. -/
theorem state_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (hg : checkGraphUsing (checker := checker) (sums := sums) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) {v0 : Tm} (hv0 : isVal v0 = true) :
    ∀ n W h s, WorldAdm W → HeapOk n W h → StateOk G Rty C v0 ε n W h s →
      SafeGraph (excOf G) P (GoalHolds G Rty v0) n W h s := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h s hw hh hs
    rcases state_progress hg hcodes hsums hv0 hw hh hs with terminal | ⟨U,h',s',hx,hu,st,hok,hs'⟩
    · exact .inl terminal
    · exact .inr ⟨U,h',s',hx,hu,st,hok,ih U h' s' hu hok hs'⟩

/-- Safety from any checked entry and concrete environment meeting its claim. -/
theorem accepted_entry_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C l c}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} (hg : checkGraphUsing (checker := checker) (sums := sums) G images Rty P C codes = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) (hc : C[l]? = some c) {v0 : Tm} (hv0 : isVal v0 = true)
    (n W h ρ) (he : EnvOk G (entry c) ρ n W) (hi : ImpliesOk G c.implies ρ n W)
    (ha : ArgumentsOk c.arguments ρ v0) (hf : HeapKnowledge.Holds c.knowledge ε ρ h) (hw : WorldAdm W)
    (hh : HeapOk n W h) :
    SafeGraph (excOf G) P (GoalHolds G Rty v0) n W h (.at l ρ) :=
  state_safe hg hcodes hsums hv0 n W h _ hw hh ⟨c,hc,he,hi,ha,hf⟩

/-- What the entry's knowledge may state: nothing, or what follows from the
separation the request assumes of its inputs (`entrySeparation`): a unit's
module cells, two cells apart (SOURCE-ELABORATION.md, "Module cells"); and
from the index facts code assumes of its frame (`entryIndices`): its
signature's precondition on the call's values (PROGRAM-TYPING.md, "Reads
below the length"). -/
@[nospecialize] def entryKnows [DecidableEq ι] (G : NormalGraph ι) (inputs : List (Ty ι))
    (entrySeparation : HeapSeparation.Separation) (entryIndices : List HeapKnowledge.IndexAtom)
    (k : HeapKnowledge.Knowledge) : Bool :=
  k == {} || KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G inputs)
    { separation := entrySeparation, indices := entryIndices } k.toNow none

/-- **The entry facts entail the start's knowledge**, read at the entry
state itself, where `old(t)` is `t` (`HeapKnowledge.holds_toNow`). -/
theorem entryKnows_sound [DecidableEq ι] {G : NormalGraph ι} {inputs : List (Ty ι)}
    {S : HeapSeparation.Separation} {I : List HeapKnowledge.IndexAtom} {k : HeapKnowledge.Knowledge} {ρ n W h}
    (hk : entryKnows G inputs S I k = true) (he : EnvOk G inputs ρ n W) (hs : HeapSeparation.Holds S ρ)
    (hi : HeapKnowledge.IndexHolds ⟨ρ, h⟩ I ρ h) :
    HeapKnowledge.Holds k ⟨ρ, h⟩ ρ h := by
  rcases Bool.or_eq_true_iff.mp hk with hk | hk
  · rw [eq_of_beq hk]; exact HeapKnowledge.empty ρ h
  · have hid : PointClaims.mapEnv none ρ = ρ := rfl
    have hctx : KnowledgeNormal.CtxOk (KnowledgeExpand.ctxOf G inputs) (PointClaims.mapEnv none ρ) := by
      rw [hid]; exact KnowledgeExpand.ctxOf_ok he
    have hsrc : HeapKnowledge.Holds { separation := S, indices := I } ⟨ρ, h⟩ ρ h :=
      ⟨HeapFacts.holds_nil ρ h, by simp [HeapKnowledge.ValueHolds], by simp [HeapLinks.Holds], hs,
        HeapKnowledge.elemsHolds_nil ρ h, hi⟩
    have := KnowledgeExpand.checkIn_sound hk hctx hsrc
    rw [hid] at this
    exact (HeapKnowledge.holds_toNow rfl rfl).mp this

/-- The external input contract is independent of the supplied point claims.
The entry states no implication, knows only what the inputs' separation
states (`entryKnows`), and holds the promised argument where the goal says
it is, a slot the inputs type. -/
@[nospecialize] def checkEntryResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι) := []) (entrySeparation : HeapSeparation.Separation := {})
    (entryIndices : List HeapKnowledge.IndexAtom := []) : CheckResult ι Unit :=
  (checkGraphResult (checker := checker) (sums := sums) G images Rty P C codes).bind fun _ =>
  match C[start]? with
  | some c => CheckResult.ofBool (decide (entry c = inputs ∧ c.implies = [] ∧
      c.arguments = Rty.slot.toList) && entryKnows G inputs entrySeparation entryIndices c.knowledge &&
      Rty.slot.all (· < inputs.length))
  | none => failure

@[nospecialize] def checkEntryUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι) := []) (entrySeparation : HeapSeparation.Separation := {})
    (entryIndices : List HeapKnowledge.IndexAtom := []) : Bool :=
  (checkEntryResult (checker := checker) (sums := sums) (entrySeparation := entrySeparation)
    (entryIndices := entryIndices) G images Rty P C start inputs codes).accepted

theorem checkEntryUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (sums : List (ReadSummary ι)) (entrySeparation : HeapSeparation.Separation := {})
    (entryIndices : List HeapKnowledge.IndexAtom := []) :
    checkEntryUsing (checker := checker) (sums := sums) (entrySeparation := entrySeparation)
      (entryIndices := entryIndices) G images Rty P C start inputs codes = (
  checkGraphUsing (checker := checker) (sums := sums) G images Rty P C codes && match C[start]? with
    | some c => decide (entry c = inputs ∧ c.implies = [] ∧
        c.arguments = Rty.slot.toList) && entryKnows G inputs entrySeparation entryIndices c.knowledge &&
        Rty.slot.all (· < inputs.length)
    | none => false
  ) := by
  simp only [checkEntryUsing, checkEntryResult, CheckResult.accepted_bind, checkGraphUsing]
  congr 1
  cases C[start]? <;> simp only [CheckResult.accepted_ofBool] <;> rfl

/-- The value a goal's promise is about, in an entry environment. -/
def Goal.argument (goal : Goal ι) (ρ : Env) : Tm :=
  match goal.slot with
  | some s => ρ s
  | none => .undef

theorem accepted_inputs_safe [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {Rty P C start inputs}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {entrySeparation : HeapSeparation.Separation}
    {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntryUsing (checker := checker) (sums := sums) (entrySeparation := entrySeparation)
      (entryIndices := entryIndices) G images Rty P C start inputs codes = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _)
    (hsums : SummariesSound G images sums := by exact Verification.ProgramCertificates.summariesSound_none _ _)
    (hsep : HeapSeparation.Holds entrySeparation ρ := by exact HeapSeparation.empty_holds _)
    (hidx : HeapKnowledge.IndexHolds ⟨ρ, h⟩ entryIndices ρ h := by exact HeapKnowledge.indexHolds_nil _ _) :
    SafeGraph (excOf G) P (GoalHolds G Rty (Rty.argument ρ)) n W h (.at start ρ) := by
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hc
  have hg := hc.1
  have hx := hc.2
  split at hx
  · rename_i c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨hin, himp, harg⟩, hk⟩, hslot⟩ := hx
    have hv0 : isVal (Rty.argument ρ) = true := by
      unfold Goal.argument
      cases hs : Rty.slot with
      | none => rfl
      | some s =>
        rw [hs] at hslot
        have hlt : s < inputs.length := by simpa using hslot
        exact (meaning_value (he.2 s inputs[s] (List.getElem?_eq_getElem hlt))).1
    apply accepted_entry_safe (ε := ⟨ρ, h⟩) hg hcodes hsums hc hv0 n W h ρ _ _ _ _ hw hh
    · simpa only [hin] using he
    · rw [himp]; exact PromiseCalls.ImpliesOk.nil G ρ n W
    · intro p hp
      rw [harg] at hp
      unfold Goal.argument
      cases hs : Rty.slot with
      | none => rw [hs] at hp; cases hp
      | some s =>
        rw [hs] at hp
        cases List.mem_singleton.mp hp
        rfl
    · exact entryKnows_sound hk (by simpa only [hin] using he) hsep hidx
  · contradiction

inductive Execution (P : Program) : Nat → Heap → State → Heap → State → Prop where
  | refl : Execution P 0 h s h s
  | next : Transition P h s h' s' → Execution P n h' s' h'' s'' → Execution P (n+1) h s h'' s''

end Verification.ControlFlow
