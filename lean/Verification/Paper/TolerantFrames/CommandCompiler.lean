import Verification.Paper.TolerantFrames.CompilerScope
import Verification.Paper.TolerantFrames.CommandMachine
/-! # Fixed finite command graphs

The existing graph nodes and finite-frame maps are assembled in CPS order.
This file generates concrete terms, labels and source-control metadata; its
size/lookup proofs alone do not assert compiler correctness or Fun.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow

/-- Ordinary labels record source control; sink labels retain their exit
kind until the run proof has recovered the named environment. -/
inductive Site where
  | command (body : Command) (stack : CommandMachine.Stack)
  | normal | broken | returned | thrown

structure AnnotatedNode where
  node : Node
  site : Site

/-- Strip finite wrappers only. A loop remains an actual reserved header. -/
def front : Command → CommandMachine.Stack → CommandMachine.Control
  | .seq a b, stack => front a (.sequence b :: stack)
  | .handle b x d, stack => front b (.catcher x d :: stack)
  | c, stack => .run c stack

theorem front_trace (c : Command) (stack : CommandMachine.Stack) (host : NativeCode) (ρ : Env) (h : Heap) :
    CommandMachine.Runs host (.run c stack) ρ h 0 (front c stack) ρ h := by
  induction c generalizing stack with
  | seq a b ih _ => exact .next .sequence (ih _)
  | handle b x d ih _ => exact .next .handler (ih _)
  | _ => exact .refl

def codeSize : Command → Nat
  | .step _ | .return_ _ | .throw_ _ | .break_ => 1
  | .seq a b | .handle a _ b => codeSize a + codeSize b
  | .choice _ a b => 1 + codeSize a + codeSize b
  | .loop b => 1 + codeSize b

theorem codeSize_pos (c : Command) : 0 < codeSize c := by
  induction c <;> simp_all [codeSize] <;> omega

def target (label : Nat) : Target := ⟨label, none⟩
def resultTarget (bound label name : Nat) : Target := ⟨label, replaceMap (width bound) name⟩
def payloadTarget (bound label : Nat) : Target := resultTarget bound label (bound + 3)

def annotated (expression : Tm) (continuation : Continuation) (handler : Option Target)
    (c : Command) (stack : CommandMachine.Stack) : AnnotatedNode :=
  ⟨⟨expression, continuation, handler⟩, .command c stack⟩

/-- Pure offset-based CPS flattening. Generated terms depend on source syntax
and finite labels, never on the eventual input values, heap or world. -/
def block (bound : Nat) : Command → CommandMachine.Stack → Nat → Nat → Nat → Target → Nat → List AnnotatedNode
  | .step p, stack, next, _, _, thrown, _ =>
    let k := match p with
      | .bind x _ => Continuation.bind (resultTarget bound next x)
      | .perform _ => Continuation.effect (target next)
    [annotated (p.operation.symbolic (hostTemplate bound)) k (some thrown) (.step p) stack]
  | .seq a b, stack, next, broken, returned, thrown, offset =>
    block bound a (.sequence b :: stack) (offset + codeSize a) broken returned thrown offset ++
      block bound b stack next broken returned thrown (offset + codeSize a)
  | .choice test yes no, stack, next, broken, returned, thrown, offset =>
    let yesTarget : Target := ⟨offset + 1, dropMap (width bound)⟩
    let noTarget : Target := ⟨offset + 1 + codeSize yes, dropMap (width bound)⟩
    annotated (test.code 0) (.tagBind .truthy yesTarget noTarget) none (.choice test yes no) stack ::
      (block bound yes stack next broken returned thrown (offset + 1) ++
        block bound no stack next broken returned thrown (offset + 1 + codeSize yes))
  | .loop body, stack, next, _, returned, thrown, offset =>
    annotated .undef (.effect (target (offset + 1))) none (.loop body) stack ::
      block bound body (.loop body :: stack) offset next returned thrown (offset + 1)
  | .handle body name handler, stack, next, broken, returned, thrown, offset =>
    block bound body (.catcher name handler :: stack) next broken returned
      (resultTarget bound (offset + codeSize body) name) offset ++
      block bound handler stack next broken returned thrown (offset + codeSize body)
  | .return_ value, stack, _, _, returned, _, _ =>
    [annotated (value.code 0) (.bind (payloadTarget bound returned)) none (.return_ value) stack]
  | .throw_ value, stack, next, _, _, thrown, _ =>
    [annotated (.throw (value.code 0)) (.effect (target next)) (some thrown) (.throw_ value) stack]
  | .break_, stack, _, broken, _, _, _ =>
    [annotated .undef (.effect (target broken)) none .break_ stack]

theorem block_length (bound : Nat) (c : Command) : ∀ stack next broken returned thrown offset,
    (block bound c stack next broken returned thrown offset).length = codeSize c := by
  induction c with
  | step p => intros; simp [block, codeSize]
  | return_ _ | throw_ _ | break_ => intros; simp [block, codeSize]
  | seq _ _ ih₁ ih₂ | choice _ _ _ ih₁ ih₂ | handle _ _ _ ih₁ ih₂ =>
    intros; simp [block, codeSize, ih₁, ih₂] <;> omega
  | loop _ ih => intros; simp [block, codeSize, ih] <;> omega

def sinks (bound : Nat) : List AnnotatedNode :=
  [⟨⟨.undef, .ret, none⟩, .normal⟩,
   ⟨⟨.undef, .ret, none⟩, .broken⟩,
   ⟨⟨.var (bound + 3), .ret, none⟩, .returned⟩,
   ⟨⟨.throw (.var (bound + 3)), .ret, none⟩, .thrown⟩]

def compile (bound : Nat) (c : Command) : List AnnotatedNode :=
  sinks bound ++ block bound c [] 0 1 2 (payloadTarget bound 3) 4

def expressions (nodes : List AnnotatedNode) : List Tm := nodes.map (·.node.expression)
def continuations (nodes : List AnnotatedNode) : List (Continuation × Option Target) :=
  nodes.map fun n => (n.node.continuation, n.node.handler)

theorem compile_length (bound : Nat) (c : Command) : (compile bound c).length = 4 + codeSize c := by
  simp [compile, sinks, block_length]; omega

def frontSite : Command → CommandMachine.Stack → Site
  | .seq a b, stack => frontSite a (.sequence b :: stack)
  | .handle b x d, stack => frontSite b (.catcher x d :: stack)
  | c, stack => .command c stack

def Site.control (bound : Nat) (graph : Env) : Site → CommandMachine.Control
  | .command c stack => .run c stack
  | .normal => .exit .normal []
  | .broken => .exit .break []
  | .returned => .exit (.returned (graph (bound + 3))) []
  | .thrown => .exit (.thrown (graph (bound + 3))) []

theorem frontSite_control (bound : Nat) (graph : Env) (c : Command) (stack : CommandMachine.Stack) :
    (frontSite c stack).control bound graph = front c stack := by
  induction c generalizing stack with
  | seq _ _ ih _ | handle _ _ _ ih _ => exact ih _
  | _ => rfl

theorem block_entry (bound : Nat) (c : Command) : ∀ stack next broken returned thrown offset,
    ((block bound c stack next broken returned thrown offset)[0]?).map AnnotatedNode.site =
      some (frontSite c stack) := by
  induction c with
  | seq a b ih _ | handle a _ b ih _ =>
    intros
    simp only [block]
    rw [List.getElem?_append_left (by rw [block_length]; exact codeSize_pos a)]
    exact ih _ _ _ _ _ _
  | step p => intros; rfl
  | _ => intros; rfl

theorem compile_entry (bound : Nat) (c : Command) :
    ((compile bound c)[4]?).map AnnotatedNode.site = some (frontSite c []) := by
  change ((sinks bound ++ block bound c [] 0 1 2 (payloadTarget bound 3) 4)[4]?).map _ = _
  rw [List.getElem?_append_right (by simp [sinks])]
  exact block_entry bound c _ _ _ _ _ _

/-- The actual callable graph lists recover exactly the generated nodes. -/
theorem program_nodes (nodes : List AnnotatedNode) :
    GraphCode.program (expressions nodes) (continuations nodes) = nodes.map AnnotatedNode.node := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => exact congrArg (List.cons node.node) ih

theorem program_lookup_annotated {nodes : List AnnotatedNode} {i : Nat} {node : AnnotatedNode}
    (hn : nodes[i]? = some node) :
    (GraphCode.program (expressions nodes) (continuations nodes))[i]? = some node.node := by
  rw [program_nodes, List.getElem?_map, hn]
  rfl

end Verification.Paper.TolerantFrames.Compiler
