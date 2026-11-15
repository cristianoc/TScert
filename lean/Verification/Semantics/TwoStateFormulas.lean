import Verification.Semantics.ExceptionalPosts
import Verification.Semantics.Purity
import Verification.Semantics.ClosedFootprints
import Verification.Semantics.IndexFacts
import Verification.Semantics.StoreRegions
import Verification.Semantics.ElementWrites
import Verification.Semantics.StepRelations

/-! # Two-state formulas

The syntax and meaning of the note *Tolerant frames*' assertions and
two-state formulas, below the callable guarantees (`CallEffects`), so that a
signature's per-exit specification can be stated in them: the states and
admissible transitions with the action of an effect (the note, §3 and §6);
the assertion arena and its satisfaction (§4, "Syntax", "Atoms",
"Satisfaction"); substitutions of slots by witnesses (I5); and the two-state
formulas with the operational posts they read (I4, `Formula`, `Holds`). The
lemmas about these definitions are stated in the modules that use them:
`TolerantFrames`, `ParityAssertions`, `ParityEvidence`, `ParityDerivations`
and `CallEffects`. -/

namespace Verification.CallEffects
open HeapObservations
/-- A predicate of values by their kind: what an element fact states of
every present element of an array (`ElemsAt`). It reads no heap and no
world: `string`, `number`, `boolean`, `null`, `undefined`, and their unions,
the nullish exclusions among them. -/
structure ElemPred where
  nul : Bool := false
  undef : Bool := false
  bool : Bool := false
  num : Bool := false
  str : Bool := false
  big : Bool := false
  sym : Bool := false
  obj : Bool := false
  deriving Repr, DecidableEq, Hashable

def ElemPred.mem (R : ElemPred) : Tm → Bool
  | .nul => R.nul
  | .undef => R.undef
  | .tru | .fls => R.bool
  | .num _ => R.num
  | .str _ => R.str
  | .bigint _ => R.big
  | .sym _ => R.sym
  | .objAt .. => R.obj
  | _ => false

/-- Inclusion of predicates. -/
def ElemPred.le (a b : ElemPred) : Bool :=
  (!a.nul || b.nul) && (!a.undef || b.undef) && (!a.bool || b.bool) && (!a.num || b.num) &&
    (!a.str || b.str) && (!a.big || b.big) && (!a.sym || b.sym) && (!a.obj || b.obj)

/-- **The elements fact** of a value `r` at a heap: `r`'s array store exists
and every element location it lists holds a value meeting `R`. A hole lists
no location, so the fact is about present elements. -/
def ElemsAt (R : ElemPred) (r : Tm) (h : Heap) : Prop :=
  ∃ s ls, Footprints.storeOf r = some s ∧ h[s]? = some (.arr ls) ∧
    ∀ l, some l ∈ ls → ∃ v, h[l]? = some v ∧ R.mem v = true

/-- A change from `before` to `after` appending the actuals `args`, where each
is a value, to the receiver `r`'s store: the store it held holds one longer
by the actuals' number, whose element at the old length plus `j` is present
and holds the `j`-th actual at a location beyond the input heap: `Array.prototype.push` on an ordinary array
(SOURCE-CONTRACTS.md, "Native footprints"). -/
def ReceiverAppends (r : Tm) (args : List Tm) (before after : Heap) : Prop :=
  (∀ a ∈ args, isVal a = true) → ∀ s ls, Footprints.storeOf r = some s → before[s]? = some (.arr ls) →
    ∃ ls', after[s]? = some (.arr ls') ∧ ls'.length = ls.length + args.length ∧
      ∀ j a, args[j]? = some a → ∃ l, ls'[ls.length + j]? = some (some l) ∧ after[l]? = some a ∧ before.length ≤ l

end Verification.CallEffects

namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
/-- A state: budget `n`, positive, a world at `n` whose contracts survive
allocation, and a heap meeting the world. -/
structure IndexedHeap where
  n : Nat
  W : WorldT n
  h : Heap
  pos : 0 < n
  adm : WorldAdm W
  ok : HeapOk n W h

/-- `s'` is reachable from `s` by what safe code may do: its budget is at
most `s`'s, and its world extends `s`'s world truncated to its budget. -/
def Admissible (s s' : IndexedHeap) : Prop :=
  ∃ hle : s'.n ≤ s.n, WExt (trunc s'.n hle s.W) s'.W

/-- An action of the footprint `Φ` at the name valuation `ρ`: an admissible
transition whose heaps meet `Φ`'s postcondition, its regions read at the
heap it starts from. -/
def Action (Φ : Footprint) (ρ : Env) (s s' : IndexedHeap) : Prop :=
  Admissible s s' ∧ Post Φ ρ s.h s'.h

end Verification.TolerantFrames

namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames
/-- **The action of an effect** at a name valuation (the note, §3, "the
effect action" `h →Φ_ρ h'`): an admissible transition whose heaps meet the
effect's postcondition, its regions read at the state it starts from
(`TolerantFrames.Action`). -/
def EffectAction (Φ : Footprint) (η : Env) (s s' : IndexedHeap) : Prop :=
  TolerantFrames.Action Φ η s s'

/-- **The cells a typed array lists** (the note, §4, "Atoms", the element
of a typed array): the entries of the view store its descriptor names
(`HeapKnowledge.descriptorStore`, `storeEntries`), of a value owning no
array store, which every well-formed typed array is
(`HeapKnowledge.RefsOk.view_selects`). An ordinary array lists none here. -/
def viewCells (h : Heap) (v : Val) : Option (List (Option Nat)) :=
  match storeOf v, HeapKnowledge.descriptorStore v with
  | none, some s => h[s]?.bind storeEntries
  | _, _ => none

/-- A reference to an arena node. -/
structure AssertionRef where
  index : Nat
  deriving DecidableEq, Repr

/-- An ordinary path (the note, §2, "paths" `π`): a root slot and the named
data fields read in turn from its value. -/
structure Path where
  root : Nat
  fields : List String
  deriving DecidableEq, Repr

namespace Path

/-- The value a path reads, where every field it passes is owned. -/
def read (η : Env) (h : Heap) (p : Path) : Option Val := readPath h (η p.root) p.fields

end Path

/-- A witness expression (I4): a path, or a literal source value. -/
inductive Witness where
  | path (p : Path)
  | literal (v : Val)
  deriving DecidableEq

/-- The value a witness denotes, where it denotes one. -/
def Witness.value (η : Env) (h : Heap) : Witness → Option Val
  | .path p => p.read η h
  | .literal v => some v

/-- What a scalar variable denotes at index `i` of the store listing `ls`:
the index, the present element's safe integer, the present element's string
length, or the parameter's value. -/
def scalarValue (η : Env) (h : Heap) (ls : List (Option Nat)) (i : Nat) : Bound → Option Int
  | .index => some (i : Int)
  | .elem => elementInt h ls i
  | .project .strLength [] => match ls[i]? with
    | some (some l) => h[l]?.bind strLengthOf
    | _ => none
  | .free t => termAt η h t
  | _ => none

/-- The selected first-order atoms (the note, §4, "Atoms"; I4, `Atom`):
a linear fact over current terms, a path's value, a dense prefix, a kind of
contents, a bounded quantification, a typed-array element, a defined term, a
safe integer, and the double `2^53` past the safe integers. -/
inductive Atom where
  | linear (fact : Linear.Fact Term)
  | equal (path : Path) (value : Witness)
  | dense (path : Path) (bound : Term)
  | contents (path : Path) (kind : CallEffects.ElemPred)
  | every (path : Path) (bound : Term) (body : List (LinearClause Bound))
  | element (path : Path) (index : Term) (value : Witness)
  | defined (term : Term)
  | safeInt (path : Path)
  | pastSafe (path : Path)
  deriving DecidableEq

/-- **The meaning of an atom** (the note, §4, "Atoms": an atom is true only
where every path it reads is defined). -/
def Atom.Holds (η : Env) (h : Heap) : Atom → Prop
  | .linear F => FactAt (termAt η h) F
  | .equal p w => ∃ v, p.read η h = some v ∧ w.value η h = some v
  | .dense p n => ∃ w s ls k, p.read η h = some w ∧ storeOf w = some s ∧ h[s]? = some (.arr ls) ∧
      termAt η h n = some k ∧ 0 ≤ k ∧ DensePrefix k.toNat ls
  | .contents p R => ∃ v, p.read η h = some v ∧ R.mem v = true
  | .every p n body => ∃ w s ls k, p.read η h = some w ∧ storeOf w = some s ∧ h[s]? = some (.arr ls) ∧
      termAt η h n = some k ∧ ∀ i : Nat, (i : Int) < k →
        (∃ l, ls[i]? = some (some l)) ∧ ∀ F ∈ body, F.HoldsAt (scalarValue η h ls i)
  | .element p t w => ∃ u ls k l v, p.read η h = some u ∧ viewCells h u = some ls ∧
      termAt η h t = some k ∧ 0 ≤ k ∧ ls[k.toNat]? = some (some l) ∧ h[l]? = some v ∧ w.value η h = some v
  | .defined t => (termAt η h t).isSome
  | .safeInt p => ∃ v, p.read η h = some v ∧ (intValue v).isSome
  | .pastSafe p => p.read η h = some (.num SafeIntegers.pastSafeBits)

/-- **An ordinary array's store** (the note, §2, "Arrays"): the value's `[]`
slot names a location holding an array store listing `xs`, and the value
names no typed array's store, so the store it owns is that one alone. -/
def ArrayStore (h : Heap) (u : Val) (s : Nat) (xs : List (Option Nat)) : Prop :=
  storeOf u = some s ∧ descriptorStore u = none ∧ h[s]? = some (.arr xs)

/-- `π # π'` (the note, §4, "Satisfaction"): the two paths read ordinary
arrays, with different store locations. -/
def Separated (η : Env) (h : Heap) (p q : Path) : Prop :=
  ∃ u w s t xs ys, p.read η h = some u ∧ q.read η h = some w ∧ ArrayStore h u s xs ∧ ArrayStore h w t ys ∧ s ≠ t

/-- `apart(π, π')` (the note, §4, "Satisfaction"): `π # π'`, and the stores
of the two arrays list no common element cell. -/
def Apart (η : Env) (h : Heap) (p q : Path) : Prop :=
  ∃ u w s t xs ys, p.read η h = some u ∧ q.read η h = some w ∧ ArrayStore h u s xs ∧ ArrayStore h w t ys ∧
    s ≠ t ∧ ∀ l, some l ∈ xs → some l ∉ ys

/-- `fresh(π)` (the note, §4, "Satisfaction"): the store of the array the
path reads is at or above the entry mark. -/
def FreshPath (η : Env) (m : Nat) (h : Heap) (p : Path) : Prop :=
  ∃ v, p.read η h = some v ∧ FreshAt m v

/-- An arena node (the note, §4, "Syntax"; I4, `AssertionNode`): sharing is
the representation of the note's ordinary syntax. `guarded g A` is the
note's `g ∨ A` with `g` invariant; `existsValue A` binds logical slot `0`;
`box Φ A` is `□_Φ A`. -/
inductive AssertionNode where
  | truth
  | falsity
  | atom (a : Atom)
  | and (left right : AssertionRef)
  | guarded (guard body : AssertionRef)
  | existsValue (body : AssertionRef)
  | separated (left right : Path)
  | apart (left right : Path)
  | fresh (path : Path)
  | box (effect : Footprint) (body : AssertionRef)
  deriving DecidableEq

/-- Finite immutable nodes. -/
structure AssertionArena where
  nodes : Array AssertionNode

/-- **Satisfaction of node `i`** (the note, §4, "Satisfaction"). A reference
not below its user denotes `False`; a valid arena has none. -/
def satNode (nodes : Array AssertionNode) (i : Nat) (η : Env) (m : Nat) (s : IndexedHeap) : Prop :=
  match nodes[i]? with
  | none => False
  | some .truth => True
  | some .falsity => False
  | some (.atom a) => a.Holds η s.h
  | some (.and l r) =>
    (if _ : l.index < i then satNode nodes l.index η m s else False) ∧
      (if _ : r.index < i then satNode nodes r.index η m s else False)
  | some (.guarded g b) =>
    (if _ : g.index < i then satNode nodes g.index η m s else False) ∨
      (if _ : b.index < i then satNode nodes b.index η m s else False)
  | some (.existsValue b) =>
    ∃ v : Val, if _ : b.index < i then satNode nodes b.index (push v η) m s else False
  | some (.separated p q) => Separated η s.h p q
  | some (.apart p q) => Apart η s.h p q
  | some (.fresh p) => FreshPath η m s.h p
  | some (.box Φ b) =>
    ∀ s', EffectAction Φ η s s' → if _ : b.index < i then satNode nodes b.index η m s' else False
termination_by i

/-- `η, m, s ⊨ a`. -/
def Sat (arena : AssertionArena) (η : Env) (m : Nat) (s : IndexedHeap) (a : AssertionRef) : Prop :=
  satNode arena.nodes a.index η m s

end Verification.Parity

namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames
/-- A witness reading no heap: a variable or a literal. -/
def Witness.heapFree : Witness → Bool
  | .path p => p.fields.isEmpty
  | .literal _ => true

/-- **A substitution of slots by witnesses** (I5, `Substitution`): slot `i`
of the substituted assertion is replaced by the path or the literal
`images[i]`. Slots past the images are outside its domain. Under a box
(`boxed`) only the images reading no heap are in its domain: the box's body
is read at every state an action reaches, where a path image may read
otherwise. -/
structure Substitution where
  images : Array Witness
  boxed : Bool := false
  /-- The slots whose path images are certified rigid: read alike at every
  state an admissible transition reaches (`HoldsAt`). Under a box they stay
  in the domain. -/
  stable : List Nat := []
  deriving DecidableEq

namespace Substitution

/-- The image of slot `i`, where it is in the substitution's domain. -/
def image (θ : Substitution) (i : Nat) : Option Witness :=
  match θ.images[i]? with
  | some w => if θ.boxed && !w.heapFree && !θ.stable.contains i then none else some w
  | none => none

end Substitution

namespace Substitution

/-- **The interpretation of names** (I5, `Substitution.Holds`): each image
in the domain, read at `source`, gives the value slot `i` has at `target`. -/
def Holds (θ : Substitution) (target source : Env) (h : Heap) : Prop :=
  ∀ (i : Nat) (w : Witness), θ.image i = some w → w.value source h = some (target i)

end Substitution

namespace Substitution

/-- The substitution read under a box: its heap-free and certified-rigid
images alone. -/
def box (θ : Substitution) : Substitution := { θ with boxed := true }

end Substitution

namespace Substitution

/-- **The substitution at a state** (I5, the agreement a box needs): it
holds at the state, and, read under a box, at every state an admissible
transition reaches. -/
def HoldsAt (θ : Substitution) (target source : Env) (s : TolerantFrames.IndexedHeap) : Prop :=
  θ.Holds target source s.h ∧ ∀ s', TolerantFrames.Admissible s s' → θ.box.Holds target source s'.h

end Substitution

end Verification.Parity

namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames
/-- The state a formula reads (I4, `Phase`): the command's entry or exit. -/
inductive Phase where
  | before
  | after
  deriving DecidableEq, Repr

def Phase.swap : Phase → Phase
  | .before => .after
  | .after => .before

/-- One node entry and one exit, with a common invocation mark (I4,
`TwoState`). -/
structure TwoState where
  beforeEnv : Env
  afterEnv : Env
  mark : Nat
  before : IndexedHeap
  after : IndexedHeap

namespace TwoState

def env (s : TwoState) : Phase → Env
  | .before => s.beforeEnv
  | .after => s.afterEnv

end TwoState

namespace TwoState

def state (s : TwoState) : Phase → IndexedHeap
  | .before => s.before
  | .after => s.after

end TwoState

/-- A term read in the state of phase `p`. -/
def tagVar : Phase → Term → StepVar
  | .before, t => .before t
  | .after, t => .after t

/-- A two-state variable with entry and exit exchanged. -/
def stepSwap : StepVar → StepVar
  | .before t => .after t
  | .after t => .before t

/-- **What a two-state variable denotes**: a before-term at the entry, an
after-term at the exit. -/
def stepValue (s : TwoState) : StepVar → Option Int
  | .before t => termAt s.beforeEnv s.before.h t
  | .after t => termAt s.afterEnv s.after.h t

/-- **Internal exact operational posts** (I4, `OperationPost`) of the
arithmetic in scope, read at the exit: the result path reads the value of the
operator on what its operands read (`binop`); a string's length read
(`Step.lenStr`); a string's element read (`codeUnitAt`). -/
inductive OperationPost where
  | arith (op : Arith) (left right : Witness) (result : Path)
  | stringLength (string result : Path)
  | stringRead (string : Path) (index : Witness) (result : Path)
  /-- A write keeping every array store's length, the array at entry slot
  `x` and exit slot `x'` (`ExpressionEffects.elem_var_write_length`). -/
  | lengthsKept (x x' : Nat)
  /-- A write at the index in entry slot `i` of the array at entry slot `x`
  (exit slot `x'`): the index is below the store's new length, the length
  grows to at most `index + 1`, by one where the index was at or past it
  (`IndexWrites.boundedWrite_store`). -/
  | boundedWrite (x i x' : Nat)
  /-- An append of the argument values to the array at entry slot `x`
  (exit slot `x'`): the assumed contract `CallEffects.ReceiverAppends`. -/
  | push (x x' : Nat) (args : List Witness)
  /-- An index fact (`HeapKnowledge.IndexFact`) read in the state of phase
  `phase`, its slot `i` that phase's slot `i + lift`, its entry terms at the
  entry. -/
  | fact (phase : Phase) (lift : Nat) (F : IndexFact)
  /-- The array store of the value at exit slot `x` was allocated after the
  entry: its location is at or beyond the entry heap's length
  (`Footprints.FreshAt`). -/
  | freshStore (x : Nat)
  /-- The value at exit slot `x` is an object every own location of which
  was allocated after the entry (`Footprints.FreshObjectAt`). -/
  | freshObject (x : Nat)
  /-- Where exit slot `x` holds `v`, every present element of the array at
  exit slot `y` meets `R` (`CallEffects.ElemsAt`). -/
  | elementsWhen (x : Nat) (v : Val) (y : Nat) (R : CallEffects.ElemPred)
  /-- The store of the array at entry slot `x` keeps its contents, or holds
  an array store its entry list is a prefix of, at most `2^32 − 1` long. -/
  | storeExtends (x : Nat)
  /-- View-Write (the note *Tolerant frames*): the write of the number at
  entry slot `v` at the index at entry slot `i` of the typed array at entry
  slot `x` (`CallEffects.WriteAt`), at the format `f`, or at the typed
  array's own format where `f` is none. -/
  | viewWrite (x i v : Nat) (format : Option ViewFormat)
  deriving DecidableEq

/-- The formats a view write is stated at: the given one, or the typed
array's own. -/
def writeFormats (x : Val) : Option ViewFormat → ViewFormat → Prop
  | some f, g => g = f
  | none, g => CallEffects.viewFormatOf x = some g

def OperationPost.Holds (s : TwoState) : OperationPost → Prop
  | .arith op l r y => ∃ a b c, l.value s.afterEnv s.after.h = some a ∧ r.value s.afterEnv s.after.h = some b ∧
      y.read s.afterEnv s.after.h = some c ∧ binop op a b = some c
  | .stringLength x y => ∃ str, x.read s.afterEnv s.after.h = some (.str str) ∧
      (utf16Units str).length ≤ maxStringLength ∧
      y.read s.afterEnv s.after.h = some (.num (bitsOfNat (utf16Units str).length))
  | .stringRead x i y => ∃ str b, x.read s.afterEnv s.after.h = some (.str str) ∧
      i.value s.afterEnv s.after.h = some (.num b) ∧ y.read s.afterEnv s.after.h = some (codeUnitAt str b)
  | .lengthsKept x x' => (⟨true, true, .length⟩ : Changes).Holds s.before.h s.after.h ∧ s.afterEnv x' = s.beforeEnv x
  | .boundedWrite x i x' => (∃ st ls ls' b idx, storeOf (s.beforeEnv x) = some st ∧ s.before.h[st]? = some (.arr ls) ∧
      s.after.h[st]? = some (.arr ls') ∧ s.beforeEnv i = .num b ∧ indexOfBits b = some idx ∧ idx < ls'.length ∧
      ls'.length ≤ max ls.length (idx + 1) ∧ (ls.length ≤ idx → ls'.length = ls.length + 1)) ∧
      s.afterEnv x' = s.beforeEnv x
  | .push x x' args => ∃ vs, args.mapM (·.value s.beforeEnv s.before.h) = some vs ∧ (∀ a ∈ vs, isVal a = true) ∧
      CallEffects.ReceiverAppends (s.beforeEnv x) vs s.before.h s.after.h ∧ s.afterEnv x' = s.beforeEnv x
  | .fact p l F => F.HoldsAt ⟨s.beforeEnv, s.before.h⟩ (fun i => s.env p (i + l)) (s.state p).h
  | .freshStore x => FreshAt s.before.h.length (s.afterEnv x)
  | .freshObject x => FreshObjectAt s.before.h.length (s.afterEnv x)
  | .elementsWhen x v y R => s.afterEnv x = v → CallEffects.ElemsAt R (s.afterEnv y) s.after.h
  | .storeExtends x => ∀ st v, storeOf (s.beforeEnv x) = some st → s.before.h[st]? = some v →
      s.after.h[st]? = some v ∨ ∃ ls ls', v = .arr ls ∧ s.after.h[st]? = some (.arr ls') ∧ ls <+: ls' ∧
        ls'.length ≤ maxArrayLength
  | .viewWrite x i v f => ∀ g, writeFormats (s.beforeEnv x) f g →
      CallEffects.WriteAt g [s.beforeEnv x, s.beforeEnv i, s.beforeEnv v] s.before.h s.after.h

/-- **Two-state formulas** (I4, `Formula`): an assertion at one phase, the
action of an effect from the entry to the exit (the note's `tr_Φ`, §6,
Entry), an operational post, a linear fact over before- and after-terms, the
transport of names (the exit environment reads each entry slot `i` at the
path `θ(i)`), and the connectives. -/
inductive Formula where
  | at (phase : Phase) (assertion : AssertionRef)
  | transition (effect : Footprint)
  | operation (post : OperationPost)
  | linear (fact : Linear.Fact StepVar)
  | defined (v : StepVar)
  | transport (θ : Substitution)
  | and (left right : Formula)
  | truth
  | falsity
  deriving DecidableEq

/-- **The meaning of a formula** (I4, `Holds`): `before` interprets `old`;
the transition reads the entry's environment. -/
def Holds (arena : AssertionArena) (s : TwoState) : Formula → Prop
  | .at p a => Sat arena (s.env p) s.mark (s.state p) a
  | .transition Φ => EffectAction Φ s.beforeEnv s.before s.after
  | .operation q => q.Holds s
  | .linear F => FactAt (stepValue s) F
  | .defined v => (stepValue s v).isSome
  | .transport θ => θ.HoldsAt s.beforeEnv s.afterEnv s.after
  | .and F G => Holds arena s F ∧ Holds arena s G
  | .truth => True
  | .falsity => False

end Verification.Parity
