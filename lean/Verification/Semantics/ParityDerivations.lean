import Verification.Semantics.ParityEvidence
import Verification.Semantics.StepRelations
import Verification.Semantics.HeapKnowledge

/-! # Parity derivations: two-state formulas and the checked consequence

The two-state formulas and the checked derivation of the design
`docs/drafts/parity-interfaces.md`, I4 ("Two-state formulas", "Checked
derivations", "Arithmetic indices and range conditions"), over the assertion
arena (`ParityAssertions`). A formula is read at a `TwoState`: the
environments and states at a command's entry (`before`, the note's `old`)
and at one of its exits (`after`), with one invocation mark.

`Derivation arena Γ F` is a checked derivation of `F` from the premises `Γ`;
its constructors are the rule schemas of the note "Tolerant frames"
(`docs/drafts/tolerant-frames-note/note.tex`) that read no region
membership: the connectives, guards, witnesses, substitution, the laws of the
modality (§4, Proposition "Laws"), the axioms (Grow) and (Dense) (§5,
Proposition "Axioms of the atoms"), Frame and Frame⁺ (§6, "Programs"),
linear arithmetic by `Linear.check` certificates, and the arithmetic of
bound facts: exact integer operations, a signed right shift and a mask by a
constant, the UTF-16 length of a string, a string's element read, the length
of a concatenation, and the sum at the `2^53` boundary.
`RawDerivation` is the untrusted finite proof data `checkDerivation` checks
into a derivation, and `Derivation.sound` is the common consequence theorem. -/
namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

/-! ## Two-state formulas -/

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

def state (s : TwoState) : Phase → IndexedHeap
  | .before => s.before
  | .after => s.after

/-- The two-state with the environment of phase `p` replaced. -/
def withEnv (s : TwoState) : Phase → Env → TwoState
  | .before, η => { s with beforeEnv := η }
  | .after, η => { s with afterEnv := η }

/-- The two-state with entry and exit exchanged. -/
def swap (s : TwoState) : TwoState := ⟨s.afterEnv, s.beforeEnv, s.mark, s.after, s.before⟩

@[simp] theorem env_withEnv (s : TwoState) (p : Phase) (η : Env) : (s.withEnv p η).env p = η := by
  cases p <;> rfl

@[simp] theorem state_withEnv (s : TwoState) (p q : Phase) (η : Env) : (s.withEnv p η).state q = s.state q := by
  cases p <;> cases q <;> rfl

@[simp] theorem mark_withEnv (s : TwoState) (p : Phase) (η : Env) : (s.withEnv p η).mark = s.mark := by
  cases p <;> rfl

@[simp] theorem env_swap (s : TwoState) (p : Phase) : s.swap.env p = s.env p.swap := by cases p <;> rfl
@[simp] theorem state_swap (s : TwoState) (p : Phase) : s.swap.state p = s.state p.swap := by cases p <;> rfl

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

@[simp] theorem stepValue_tag (s : TwoState) (p : Phase) (t : Term) :
    stepValue s (tagVar p t) = termAt (s.env p) (s.state p).h t := by
  cases p <;> rfl

theorem stepValue_swap (s : TwoState) (v : StepVar) : stepValue s.swap v = stepValue s (stepSwap v) := by
  cases v <;> rfl

/-- A fact with its variables renamed. -/
def renameFact {V W : Type} (g : V → W) : Linear.Fact V → Linear.Fact W
  | .le f d => .le (f.map fun (x, c) => (g x, c)) d
  | .ne f d => .ne (f.map fun (x, c) => (g x, c)) d

private theorem eval_rename {V W : Type} (g : V → W) (v : W → Int) (f : Linear.Form V) :
    Linear.Form.eval v (f.map fun (x, c) => (g x, c)) = Linear.Form.eval (v ∘ g) f := by
  induction f with
  | nil => rfl
  | cons p t ih => obtain ⟨x, c⟩ := p; simp only [List.map_cons, Linear.Form.eval, ih, Function.comp]

/-- **A renamed fact holds where the fact holds of the renamed valuation.** -/
theorem factAt_rename {V W : Type} (g : V → W) (val : W → Option Int) (F : Linear.Fact V) :
    FactAt val (renameFact g F) ↔ FactAt (val ∘ g) F := by
  have hv : (renameFact g F).vars = F.vars.map g := by
    cases F <;> simp [renameFact, Linear.Fact.vars, Function.comp_def]
  unfold FactAt
  rw [hv]
  have hh : (renameFact g F).Holds (fun x => (val x).getD 0) ↔ F.Holds (fun x => ((val ∘ g) x).getD 0) := by
    cases F <;> simp only [renameFact, Linear.Fact.Holds, eval_rename] <;> rfl
  rw [hh]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Function.comp]

/-- A linear fact over current terms read in phase `p`. -/
def tagFact (p : Phase) (F : Linear.Fact Term) : Linear.Fact StepVar := renameFact (tagVar p) F

theorem factAt_tag (s : TwoState) (p : Phase) (F : Linear.Fact Term) :
    FactAt (stepValue s) (tagFact p F) ↔ FactAt (termAt (s.env p) (s.state p).h) F := by
  rw [tagFact, factAt_rename]
  exact Iff.of_eq (congrArg (FactAt · F) (funext fun t => stepValue_tag s p t))

/-- **Internal exact operational posts** (I4, `OperationPost`) of the
arithmetic in scope, read at the exit: the result path reads the value of the
operator on what its operands read (`binop`); a string's length read
(`Step.lenStr`); a string's element read (`codeUnitAt`). -/
inductive OperationPost where
  | arith (op : Arith) (left right : Witness) (result : Path)
  | stringLength (string result : Path)
  | stringRead (string : Path) (index : Witness) (result : Path)
  deriving DecidableEq

def OperationPost.Holds (s : TwoState) : OperationPost → Prop
  | .arith op l r y => ∃ a b c, l.value s.afterEnv s.after.h = some a ∧ r.value s.afterEnv s.after.h = some b ∧
      y.read s.afterEnv s.after.h = some c ∧ binop op a b = some c
  | .stringLength x y => ∃ str, x.read s.afterEnv s.after.h = some (.str str) ∧
      (utf16Units str).length ≤ maxStringLength ∧
      y.read s.afterEnv s.after.h = some (.num (bitsOfNat (utf16Units str).length))
  | .stringRead x i y => ∃ str b, x.read s.afterEnv s.after.h = some (.str str) ∧
      i.value s.afterEnv s.after.h = some (.num b) ∧ y.read s.afterEnv s.after.h = some (codeUnitAt str b)

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
  | .transport θ => θ.Holds s.beforeEnv s.afterEnv s.after.h
  | .and F G => Holds arena s F ∧ Holds arena s G
  | .truth => True
  | .falsity => False

/-- The conjunction of a list of formulas. -/
def conj : List Formula → Formula
  | [] => .truth
  | F :: t => .and F (conj t)

theorem holds_conj {arena : AssertionArena} {s : TwoState} :
    ∀ {l : List Formula}, Holds arena s (conj l) ↔ ∀ F ∈ l, Holds arena s F
  | [] => by simp [conj, Holds]
  | F :: t => by simp only [conj, Holds, holds_conj, List.mem_cons, forall_eq_or_imp]

/-- Entry and exit exchanged in a formula reading states alone. -/
def Formula.swap : Formula → Formula
  | .at p a => .at p.swap a
  | .linear F => .linear (renameFact stepSwap F)
  | .defined v => .defined (stepSwap v)
  | .and F G => .and F.swap G.swap
  | F => F

/-- A formula reading the two states symmetrically: assertions, linear
facts and their connectives. -/
def Formula.swappable : Formula → Bool
  | .at _ _ | .linear _ | .defined _ | .truth | .falsity => true
  | .and F G => F.swappable && G.swappable
  | _ => false

theorem holds_swap {arena : AssertionArena} {s : TwoState} :
    ∀ {F : Formula}, F.swappable = true → (Holds arena s.swap F.swap ↔ Holds arena s F)
  | .at p a, _ => by cases p <;> rfl
  | .linear F, _ => by
    simp only [Formula.swap, Holds, factAt_rename]
    exact Iff.of_eq (congrArg (FactAt · F) (funext fun v => by cases v <;> rfl))
  | .defined v, _ => by cases v <;> rfl
  | .and F G, h => by
    simp only [Formula.swappable, Bool.and_eq_true] at h
    simp only [Formula.swap, Holds, holds_swap h.1, holds_swap h.2]
  | .truth, _ => Iff.rfl
  | .falsity, _ => Iff.rfl

/-! ## The arithmetic conclusions -/

/-- The safe integer a path reads at the exit. -/
def av (p : Path) : StepVar := .after (p.term .value)

/-- The UTF-16 length of the string a path reads at the exit. -/
def alen (p : Path) : StepVar := .after (p.term .strLength)

/-- The note's (Grow) atom `y ≤ |x|` (`TolerantFrames.lowerBoundFact`). -/
def lowerFact (y x : Nat) : Linear.Fact Term := .le [(Term.value y, 1), (Term.length x, -1)] 0

/-- A linear fact over current terms read at the exit. -/
def lin (G : Linear.Fact Term) : Formula := .linear (tagFact .after G)

/-- The safe integer a path reads, as a current term. -/
abbrev vt (p : Path) : Term := p.term .value

/-- **An operand with its value evidence** (I4, "Arithmetic indices and
range conditions"): a path read as its own safe integer, a path proved equal
to a constant, or a literal number. These are the operands of the pass's
producers (`IndexWrites.operandForm`: a slot the knowledge states a safe
integer, that slot's checked constant `knownConstant`, or a literal). -/
inductive Operand where
  | var (p : Path)
  | const (p : Path) (c : Int)
  | literal (b : UInt64)
  deriving DecidableEq

/-- The witness an operation reads the operand at. -/
def Operand.witness : Operand → Witness
  | .var p | .const p _ => .path p
  | .literal b => .literal (.num b)

/-- The operand's value as a linear form over current terms plus a constant. -/
def Operand.form : Operand → Option (Linear.Form Term × Int)
  | .var p => some ([(vt p, 1)], 0)
  | .const _ c => some ([], c)
  | .literal b => (SafeIntegers.safeIntOfBits b).map fun i => ([], i)

/-- The evidence an operand's form needs: a path's safe integer defined, a
path's value equal to the constant, nothing for a literal. -/
def Operand.premise : Operand → Formula
  | .var p => .defined (.after (vt p))
  | .const p c => conj [lin (.le [(vt p, 1)] c), lin (.le [(vt p, -1)] (-c))]
  | .literal _ => .truth

/-- The result a path reads is a safe integer (`IndexFact.int`). -/
def safeFact (y : Path) : Formula := .defined (.after (vt y))

/-- `0 ≤ F + c ≤ 2^31 − 1` (`IndexWrites.smallOperand`). -/
def smallFacts (F : Linear.Form Term) (c : Int) : Formula :=
  conj [lin (.le (F.scale (-1)) c), lin (.le F (2 ^ 31 - 1 - c))]

/-- **Shift right by a constant** (I4, "Arithmetic indices and range
conditions"; the note has no rule for it yet): of `y = x >> d` with
`x = F + c`, `y` a safe integer, `0 ≤ y` and
`2^d·y ≤ x ≤ 2^d·y + (2^d − 1)` (`IndexWrites.bitAtoms .shr`). -/
def shrFacts (y : Path) (F : Linear.Form Term) (c d : Int) : Formula :=
  conj [safeFact y, lin (.le [(vt y, -1)] 0), lin (.le ((vt y, 2 ^ d.toNat) :: F.scale (-1)) c),
    lin (.le ((vt y, -(2 ^ d.toNat)) :: F) (2 ^ d.toNat - 1 - c))]

/-- **Mask by a constant** (I4, "Arithmetic indices and range conditions";
the note has no rule for it yet): of `y = x & m` with `x = F + c`, `y` a
safe integer, `0 ≤ y ≤ m` and `y ≤ x` (`IndexWrites.bitAtoms .bitAnd`). -/
def maskFacts (y : Path) (F : Linear.Form Term) (c m : Int) : Formula :=
  conj [safeFact y, lin (.le [(vt y, -1)] 0), lin (.le [(vt y, 1)] m), lin (.le ((vt y, 1) :: F.scale (-1)) c)]

/-- The exact result of an integer operation on two operand forms: a sum, a
difference, or a product with a constant factor, a zero factor giving the
constant `0` (the pass's `linearAtoms` on `arith`). -/
def resultForm (op : Arith) (fl : Linear.Form Term) (cl : Int) (fr : Linear.Form Term) (cr : Int) :
    Option (Linear.Form Term × Int) :=
  match op with
  | .add => some (fl ++ fr, cl + cr)
  | .sub => some (fl ++ fr.scale (-1), cl - cr)
  | .mul => if fl = [] then some (if cl = 0 then [] else fr.scale cl, cl * cr)
      else if fr = [] then some (if cr = 0 then [] else fl.scale cr, cl * cr) else none
  | _ => none

/-- `y = F + c` as two current linear facts. -/
def exactTermFacts (y : Path) (F : Linear.Form Term) (c : Int) : Linear.Fact Term × Linear.Fact Term :=
  (.le ((vt y, 1) :: F.scale (-1)) c, .le ((vt y, -1) :: F) (-c))

/-- `y` a safe integer and `y = F + c` (`IndexWrites.valueAtoms`). -/
def valueFacts (y : Path) (F : Linear.Form Term) (c : Int) : Formula :=
  conj [safeFact y, lin (exactTermFacts y F c).1, lin (exactTermFacts y F c).2]

/-- `|F + c| ≤ 2^53 − 1`: the exact result is a safe integer. -/
def rangeFacts (F : Linear.Form Term) (c : Int) : Formula :=
  conj [lin (.le F (2 ^ 53 - 1 - c)), lin (.le (F.scale (-1)) (2 ^ 53 - 1 + c))]

/-- `x = |s|`: the operand is a string's length. -/
def lengthEq (x s : Path) : Formula :=
  conj [lin (.le [(vt x, 1), (s.term .strLength, -1)] 0), lin (.le [(vt x, -1), (s.term .strLength, 1)] 0)]

/-- The operand is one: the literal `1`, or a path whose safe integer is `1`
(`IndexWrites.stringLengthPlusOne`'s `isOne`). -/
def oneFacts : Operand → Option Formula
  | .literal b => if SafeIntegers.safeIntOfBits b = some 1 then some .truth else none
  | .var p => some (conj [lin (.le [(vt p, 1)] 1), lin (.le [(vt p, -1)] (-1))])
  | .const _ _ => none

/-- A term's lower and upper string-length range. -/
def strRange (t : StepVar) : Formula :=
  conj [.linear (.le [(t, -1)] 0), .linear (.le [(t, 1)] (2 ^ 53 - 1))]

/-- `|y| = |x| + |z|`. -/
def concatFacts (x z y : Path) : Formula :=
  conj [.linear (.le [(alen y, 1), (alen x, -1), (alen z, -1)] 0),
    .linear (.le [(alen y, -1), (alen x, 1), (alen z, 1)] 0)]

/-- `y = |x|`. -/
def lengthReadFacts (x y : Path) : Formula :=
  conj [safeFact y, .linear (.le [(av y, 1), (alen x, -1)] 0), .linear (.le [(av y, -1), (alen x, 1)] 0)]

/-- `|y| = 1`. -/
def unitFacts (y : Path) : Formula :=
  conj [.linear (.le [(alen y, 1)] 1), .linear (.le [(alen y, -1)] (-1))]

/-- A valid string index: `0 ≤ i`, `i + 1 ≤ |x|`, and `i ≤ 2^32 − 2`. The
last bound is the code-unit model's: a string's element read (`codeUnitAt`)
reads its index through `indexOfBits`, which denotes indices below
`2^32 − 1` alone. -/
def stringIndexFacts (x i : Path) : Formula :=
  conj [.linear (.le [(av i, -1)] 0), .linear (.le [(av i, 1), (alen x, -1)] (-1)),
    .linear (.le [(av i, 1)] (2 ^ 32 - 2))]

/-- Linear certificate check: the certificate concludes the goal from the
facts, and the goal names only terms the facts name. -/
def linearCheck (Fs : List (Linear.Fact StepVar)) (defs : List StepVar) (steps : List (Linear.Step StepVar))
    (G : Linear.Fact StepVar) : Bool :=
  (match Linear.check Fs steps with
    | some out => out.contains G
    | none => false) && G.vars.all fun x => defs.contains x || Fs.any fun F => F.vars.contains x

/-! ## Reading a formula one slot further -/

/-- A two-state variable of phase `p` read one slot further. -/
def shiftVar (p : Phase) : StepVar → StepVar
  | .before t => if p = .before then .before (Term.now t.kind (t.slot + 1) t.path) else .before t
  | .after t => if p = .after then .after (Term.now t.kind (t.slot + 1) t.path) else .after t

def OperationPost.shift : OperationPost → OperationPost
  | .arith op l r y => .arith op l.shift r.shift ⟨y.root + 1, y.fields⟩
  | .stringLength x y => .stringLength ⟨x.root + 1, x.fields⟩ ⟨y.root + 1, y.fields⟩
  | .stringRead x i y => .stringRead ⟨x.root + 1, x.fields⟩ i.shift ⟨y.root + 1, y.fields⟩

/-- **`F'` is `F` with the valuation of phase `p` read one slot further**:
assertions by the shift substitution of the slots below `n`, terms of phase
`p` at their next slot, an entry transition with its roots renamed, an exit
operation and an exit transport with their roots shifted. -/
def shiftFormula (nodes : Array AssertionNode) (p : Phase) (n : Nat) : Formula → Formula → Bool
  | .at q a, .at q' a' => q == q' && (if q = p then substCheck nodes (Substitution.shift n) a.index a'.index else a == a')
  | .linear F, .linear F' => F' == renameFact (shiftVar p) F
  | .defined v, .defined v' => v' == shiftVar p v
  | .transition Φ, .transition Φ' => if p = .before then Φ' == Footprint.rename (· + 1) Φ else Φ' == Φ
  | .operation q, .operation q' => if p = .after then q' == q.shift else q' == q
  | .transport θ, .transport θ' => p == .after && θ' == ⟨θ.images.map Witness.shift⟩
  | .and F G, .and F' G' => shiftFormula nodes p n F F' && shiftFormula nodes p n G G'
  | .truth, .truth => true
  | .falsity, .falsity => true
  | _, _ => false

/-- A scalar variable at the index term `k`: the index is `k`, a parameter
is itself. -/
def boundAt (k : Term) : Bound → Option Term
  | .index => some k
  | .free t => some t
  | _ => none

/-- The atomic clauses of a scalar body reading the index and the
parameters alone, at the index `k`. -/
def everyInstances (body : List (LinearClause Bound)) (k : Term) : List (Linear.Fact Term) :=
  body.filterMap fun
    | .atom F => F.mapVars (boundAt k)
    | _ => none

/-! ## Derivations -/

/-- **A checked derivation of one two-state formula** (I4, `Derivation`).
`Γ` holds the premises. Each constructor is a rule schema of the note, its
side conditions decided on the arena. -/
inductive Derivation (arena : AssertionArena) : List Formula → Formula → Type where
  /-- A premise. -/
  | assumption {Γ F} (h : F ∈ Γ) : Derivation arena Γ F
  | truth {Γ} : Derivation arena Γ .truth
  | falseElim {Γ F} (d : Derivation arena Γ .falsity) : Derivation arena Γ F
  | andIntro {Γ F G} (d : Derivation arena Γ F) (e : Derivation arena Γ G) : Derivation arena Γ (.and F G)
  | andLeft {Γ F G} (d : Derivation arena Γ (.and F G)) : Derivation arena Γ F
  | andRight {Γ F G} (d : Derivation arena Γ (.and F G)) : Derivation arena Γ G
  | cut {Γ F G} (d : Derivation arena Γ F) (e : Derivation arena (F :: Γ) G) : Derivation arena Γ G
  /-- The assertion `true`, at either phase. -/
  | atTruth {Γ p a} (hn : arena.nodes[a.index]? = some .truth) : Derivation arena Γ (.at p a)
  /-- The assertion `false` proves anything. -/
  | atFalse {Γ p a F} (hn : arena.nodes[a.index]? = some .falsity) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ F
  | atAndIntro {Γ p a l r} (hn : arena.nodes[a.index]? = some (.and l r))
      (dl : Derivation arena Γ (.at p l)) (dr : Derivation arena Γ (.at p r)) : Derivation arena Γ (.at p a)
  | atAndLeft {Γ p a l r} (hn : arena.nodes[a.index]? = some (.and l r)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p l)
  | atAndRight {Γ p a l r} (hn : arena.nodes[a.index]? = some (.and l r)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p r)
  /-- `g ⊢ g ∨ A`. -/
  | guardLeft {Γ p a g b} (hn : arena.nodes[a.index]? = some (.guarded g b)) (d : Derivation arena Γ (.at p g)) :
      Derivation arena Γ (.at p a)
  /-- `A ⊢ g ∨ A`. -/
  | guardRight {Γ p a g b} (hn : arena.nodes[a.index]? = some (.guarded g b)) (d : Derivation arena Γ (.at p b)) :
      Derivation arena Γ (.at p a)
  /-- Cases on `g ∨ A`. -/
  | guardCases {Γ p a g b F} (hn : arena.nodes[a.index]? = some (.guarded g b)) (d : Derivation arena Γ (.at p a))
      (dg : Derivation arena (.at p g :: Γ) F) (db : Derivation arena (.at p b :: Γ) F) : Derivation arena Γ F
  /-- `π` defined and `A[π/v]` give `∃v. A`. -/
  | existsIntro {Γ p a b c e} (w : Path) (n : Nat) (hn : arena.nodes[a.index]? = some (.existsValue b))
      (hc : substCheck arena.nodes (Substitution.instantiate (.path w) n) b.index c.index = true)
      (he : arena.nodes[e.index]? = some (.atom (.equal w (.path w))))
      (de : Derivation arena Γ (.at p e)) (dc : Derivation arena Γ (.at p c)) : Derivation arena Γ (.at p a)
  /-- `A[ℓ/v]` gives `∃v. A` for a literal `ℓ`. -/
  | existsIntroLiteral {Γ p a b c} (ℓ : Val) (n : Nat) (hn : arena.nodes[a.index]? = some (.existsValue b))
      (hc : substCheck arena.nodes (Substitution.instantiate (.literal ℓ) n) b.index c.index = true)
      (dc : Derivation arena Γ (.at p c)) : Derivation arena Γ (.at p a)
  /-- Open `∃v. B` at phase `p`: the eigenvariable is slot `0` of that
  phase's valuation; the ambient premises `Γ'` and the conclusion `G'` are
  formulas of `Γ` and `G` read one slot further, so the eigenvariable occurs
  in none of them. -/
  | existsElim {Γ Γ' p a b G G'} (n : Nat) (hn : arena.nodes[a.index]? = some (.existsValue b))
      (hΓ : Γ'.all (fun F' => Γ.any fun F => shiftFormula arena.nodes p n F F') = true)
      (hG : shiftFormula arena.nodes p n G G' = true)
      (d : Derivation arena Γ (.at p a)) (e : Derivation arena (.at p b :: Γ') G') : Derivation arena Γ G
  /-- `π ≐ π'` and `A[π/v]` give `A[π'/v]`. -/
  | equalitySubst {Γ p} {b c₁ c₂ e : AssertionRef} (w w' : Path) (n : Nat)
      (h₁ : substCheck arena.nodes (Substitution.instantiate (.path w) n) b.index c₁.index = true)
      (h₂ : substCheck arena.nodes (Substitution.instantiate (.path w') n) b.index c₂.index = true)
      (he : arena.nodes[e.index]? = some (.atom (.equal w (.path w'))))
      (de : Derivation arena Γ (.at p e)) (d : Derivation arena Γ (.at p c₁)) : Derivation arena Γ (.at p c₂)
  /-- A derivation reading the states symmetrically holds with entry and
  exit exchanged: a one-state derivation read before the command. -/
  | oldLift {Γ F} (hΓ : Γ.all Formula.swappable = true) (hF : F.swappable = true)
      (d : Derivation arena (Γ.map Formula.swap) F.swap) : Derivation arena Γ F
  /-- Law (a): `□_Φ A ⊢ A`. -/
  | boxElim {Γ p a b Φ} (hn : arena.nodes[a.index]? = some (.box Φ b)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p b)
  /-- Law (b): `□_Φ A ∧ □_Φ B ⊢ □_Φ (A ∧ B)`. -/
  | boxAndIntro {Γ p a c l r bl br Φ} (hn : arena.nodes[a.index]? = some (.box Φ c))
      (hc : arena.nodes[c.index]? = some (.and l r)) (hl : arena.nodes[bl.index]? = some (.box Φ l))
      (hr : arena.nodes[br.index]? = some (.box Φ r))
      (dl : Derivation arena Γ (.at p bl)) (dr : Derivation arena Γ (.at p br)) : Derivation arena Γ (.at p a)
  /-- Law (b): `□_Φ (A ∧ B) ⊢ □_Φ A`. -/
  | boxAndLeft {Γ p a c l r bl Φ} (hn : arena.nodes[a.index]? = some (.box Φ c))
      (hc : arena.nodes[c.index]? = some (.and l r)) (hl : arena.nodes[bl.index]? = some (.box Φ l))
      (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.at p bl)
  /-- Law (b): `□_Φ (A ∧ B) ⊢ □_Φ B`. -/
  | boxAndRight {Γ p a c l r br Φ} (hn : arena.nodes[a.index]? = some (.box Φ c))
      (hc : arena.nodes[c.index]? = some (.and l r)) (hr : arena.nodes[br.index]? = some (.box Φ r))
      (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.at p br)
  /-- Law (b): a context-free `A ⊢ B` gives `□_Φ A ⊢ □_Φ B`. -/
  | boxMono {Γ p a b x y Φ} (ha : arena.nodes[a.index]? = some (.box Φ x)) (hb : arena.nodes[b.index]? = some (.box Φ y))
      (e : Derivation arena [.at .after x] (.at .after y)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p b)
  /-- Law (c): `Φ ⊑ Ψ` under `K`, by an inclusion certificate, gives
  `K ∧ □_Ψ A ⊢ □_Φ A`. -/
  | boxAnti {Γ p a b x K Φ Ψ} (ev : InclusionEvidence) (hev : ev.check Φ Ψ = true)
      (ha : arena.nodes[a.index]? = some (.box Ψ x)) (hb : arena.nodes[b.index]? = some (.box Φ x))
      (dK : Derivation arena Γ (.at p K)) (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.at p b)
  /-- Law (d): `g ∨ □_Φ A ⊢ □_Φ (g ∨ A)` for the invariant guard `g`. -/
  | boxGuard {Γ p a g bx x b c Φ} (ha : arena.nodes[a.index]? = some (.guarded g bx))
      (hbx : arena.nodes[bx.index]? = some (.box Φ x)) (hb : arena.nodes[b.index]? = some (.box Φ c))
      (hc : arena.nodes[c.index]? = some (.guarded g x)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p b)
  /-- Law (e): `D ∧ □_Φ A ⊢ □_Φ □_Φ A` for `Φ` rigid on the domain `D`, by
  a rigidity certificate. -/
  | boxIdem {Γ p a b x D Φ} (ev : RigidityEvidence) (hev : ev.check arena D Φ = true)
      (ha : arena.nodes[a.index]? = some (.box Φ x)) (hb : arena.nodes[b.index]? = some (.box Φ a))
      (dD : Derivation arena Γ (.at p D)) (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.at p b)
  /-- **The tolerant frame theorem** (the note, §5, Theorem "Tolerant
  frame"): `S` supports `A` in a context, `Φ` respects `S` under `K` (the
  note's pairwise definition), and the context holds throughout the modal
  domain of an assertion `g` derived from `K`: `K ∧ A ⊢ □_Φ A`. -/
  | tolerantFrame {Γ p K A b g Φ} (S : Footprint) (sev : SupportEvidence) (rev : RespectEvidence)
      (cev : ContextEvidence) (hs : sev.check arena A = true) (hr : rev.check S Φ = true)
      (hc : cev.check arena g = true) (hb : arena.nodes[b.index]? = some (.box Φ A))
      (e : Derivation arena [.at .after K] (.at .after g)) (dK : Derivation arena Γ (.at p K))
      (dA : Derivation arena Γ (.at p A)) : Derivation arena Γ (.at p b)
  /-- Bounded quantification over an empty range: `n ≤ 0` and `π` an
  ordinary array give `every(π, n, φ)`. -/
  | everyEmpty {Γ p a d} (π : Path) (n z : Term) (body : List (LinearClause Bound))
      (ha : arena.nodes[a.index]? = some (.atom (.every π n body)))
      (hd : arena.nodes[d.index]? = some (.atom (.dense π z))) (dd : Derivation arena Γ (.at p d))
      (dn : Derivation arena Γ (.linear (tagFact p (.le [(n, 1)] 0)))) : Derivation arena Γ (.at p a)
  /-- Bounded quantification at an index: `every(π, n, φ)` and `0 ≤ k < n`
  give each atomic clause of `φ` reading the index and the parameters, at
  `k`. -/
  | everyElim {Γ p a} (π : Path) (n k : Term) (body : List (LinearClause Bound)) (G : Linear.Fact Term)
      (ha : arena.nodes[a.index]? = some (.atom (.every π n body))) (hG : G ∈ everyInstances body k)
      (d : Derivation arena Γ (.at p a)) (dk : Derivation arena Γ (.linear (tagFact p (.le [(k, -1)] 0))))
      (dlt : Derivation arena Γ (.linear (tagFact p (.le [(k, 1), (n, -1)] (-1))))) :
      Derivation arena Γ (.linear (tagFact p G))
  /-- (Grow): `y ≤ |x| ⊢ □_{values: any, stores: grow} (y ≤ |x|)`. -/
  | grow {Γ p a b} (y x : Nat) (ha : arena.nodes[a.index]? = some (.atom (.linear (lowerFact y x))))
      (hb : arena.nodes[b.index]? = some (.box growEffect.fp a)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p b)
  /-- (Dense): `dense(x, k) ⊢ □_{values: any, stores: grow} dense(x, k)`. -/
  | dense {Γ p a b} (x k : Nat) (ha : arena.nodes[a.index]? = some (.atom (.dense (Path.var x) (Term.value k))))
      (hb : arena.nodes[b.index]? = some (.box growEffect.fp a)) (d : Derivation arena Γ (.at p a)) :
      Derivation arena Γ (.at p b)
  /-- Frame (the note, §6): `old(□_Φ A) ∧ tr_Φ` gives `A` at the exit, its
  names transported by `θ`. -/
  | frame {Γ a b c Φ} (θ : Substitution) (ha : arena.nodes[a.index]? = some (.box Φ b))
      (hc : substCheck arena.nodes θ b.index c.index = true)
      (d : Derivation arena Γ (.at .before a)) (dt : Derivation arena Γ (.transition Φ))
      (dθ : Derivation arena Γ (.transport θ)) : Derivation arena Γ (.at .after c)
  /-- Frame⁺ (the note, §6): for an effect rigid on the domain `D` the box
  itself holds at the exit. -/
  | framePlus {Γ a b c D Φ} (ev : RigidityEvidence) (hev : ev.check arena D Φ = true) (θ : Substitution)
      (ha : arena.nodes[a.index]? = some (.box Φ b)) (hc : substCheck arena.nodes θ a.index c.index = true)
      (dD : Derivation arena Γ (.at .before D)) (d : Derivation arena Γ (.at .before a))
      (dt : Derivation arena Γ (.transition Φ)) (dθ : Derivation arena Γ (.transport θ)) :
      Derivation arena Γ (.at .after c)
  /-- Linear arithmetic over defined terms, by a `Linear.check` certificate. -/
  | linear {Γ G} (Fs : List (Linear.Fact StepVar)) (defs : List StepVar) (steps : List (Linear.Step StepVar))
      (hc : linearCheck Fs defs steps G = true) (d : Derivation arena Γ (conj (Fs.map .linear)))
      (dd : Derivation arena Γ (conj (defs.map .defined))) : Derivation arena Γ (.linear G)
  /-- A linear fact defines each of its terms. -/
  | definedOfLinear {Γ F v} (hv : v ∈ F.vars) (d : Derivation arena Γ (.linear F)) : Derivation arena Γ (.defined v)
  /-- The atom `defined(t)` is the definedness of `t` at its phase. -/
  | definedToAtom {Γ p a t} (ha : arena.nodes[a.index]? = some (.atom (.defined t)))
      (d : Derivation arena Γ (.defined (tagVar p t))) : Derivation arena Γ (.at p a)
  | atomToDefined {Γ p a t} (ha : arena.nodes[a.index]? = some (.atom (.defined t)))
      (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.defined (tagVar p t))
  /-- `safeInt(π)` is the definedness of `π`'s safe integer. -/
  | safeIntToDefined {Γ p a π} (ha : arena.nodes[a.index]? = some (.atom (.safeInt π)))
      (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.defined (tagVar p (π.term .value)))
  | definedToSafeInt {Γ p a π} (ha : arena.nodes[a.index]? = some (.atom (.safeInt π)))
      (d : Derivation arena Γ (.defined (tagVar p (π.term .value)))) : Derivation arena Γ (.at p a)
  /-- A linear atom read as a linear formula of its phase. -/
  | atomToLinear {Γ p a} (F : Linear.Fact Term) (ha : arena.nodes[a.index]? = some (.atom (.linear F)))
      (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (.linear (tagFact p F))
  /-- A linear formula of one phase read as a linear atom. -/
  | linearToAtom {Γ p a} (F : Linear.Fact Term) (ha : arena.nodes[a.index]? = some (.atom (.linear F)))
      (d : Derivation arena Γ (.linear (tagFact p F))) : Derivation arena Γ (.at p a)
  /-- Atoms are a first-order language: `π ≐ v` and the contents of `π`
  of a kind `v` is not of are contradictory. -/
  | atomClash {Γ p e c F} (π : Path) (v : Val) (R : CallEffects.ElemPred) (hv : R.mem v = false)
      (he : arena.nodes[e.index]? = some (.atom (.equal π (.literal v))))
      (hc : arena.nodes[c.index]? = some (.atom (.contents π R)))
      (de : Derivation arena Γ (.at p e)) (dc : Derivation arena Γ (.at p c)) : Derivation arena Γ F
  /-- **Shift right by a constant** (I4, "Arithmetic indices and range
  conditions"): a constant `d ∈ [0, 31]` (a literal or a path proved
  constant) of an operand in `[0, 2^31 − 1]`. -/
  | shiftRight {Γ} (x k : Operand) (y : Path) (F : Linear.Form Term) (c d : Int) (hx : x.form = some (F, c))
      (hk : k.form = some ([], d)) (hd : 0 ≤ d ∧ d < 32)
      (dop : Derivation arena Γ (.operation (.arith .shr x.witness k.witness y)))
      (dx : Derivation arena Γ x.premise) (dk : Derivation arena Γ k.premise)
      (ds : Derivation arena Γ (smallFacts F c)) : Derivation arena Γ (shrFacts y F c d)
  /-- **Mask by a constant** (I4, "Arithmetic indices and range
  conditions"): a constant `m ∈ [0, 2^31 − 1]` of an operand in
  `[0, 2^31 − 1]`. -/
  | mask {Γ} (x k : Operand) (y : Path) (F : Linear.Form Term) (c m : Int) (hx : x.form = some (F, c))
      (hk : k.form = some ([], m)) (hm : 0 ≤ m ∧ m < 2 ^ 31)
      (dop : Derivation arena Γ (.operation (.arith .bitAnd x.witness k.witness y)))
      (dx : Derivation arena Γ x.premise) (dk : Derivation arena Γ k.premise)
      (ds : Derivation arena Γ (smallFacts F c)) : Derivation arena Γ (maskFacts y F c m)
  /-- **Exact integer operations** (I4, "Arithmetic indices and range
  conditions"): a sum, a difference or a product with a constant factor of
  safe integers, its exact result a safe integer. -/
  | integerOperation {Γ} (op : Arith) (l r : Operand) (y : Path) (fl : Linear.Form Term) (cl : Int)
      (fr : Linear.Form Term) (cr : Int) (F : Linear.Form Term) (c : Int)
      (hl : l.form = some (fl, cl)) (hr : r.form = some (fr, cr)) (hF : resultForm op fl cl fr cr = some (F, c))
      (dop : Derivation arena Γ (.operation (.arith op l.witness r.witness y)))
      (dl : Derivation arena Γ l.premise) (dr : Derivation arena Γ r.premise)
      (drange : Derivation arena Γ (rangeFacts F c)) : Derivation arena Γ (valueFacts y F c)
  /-- **A string's length plus one** (I4, "Arithmetic indices and range
  conditions", `lengthSuccessor`; the pass's `stringLengthPlusOne`): of
  `y = x + 1` (either order) with `x = |s|`, `pastSafe(y)` or `y` the exact
  sum, a safe integer. -/
  | lengthSuccessor {Γ g pg e e₀ e' e₁ e₂} (l r : Operand) (y s : Path) (lengthLeft : Bool) (x : Path)
      (fl : Linear.Form Term) (cl : Int) (fr : Linear.Form Term) (cr : Int) (one : Formula)
      (hl : l.form = some (fl, cl)) (hr : r.form = some (fr, cr))
      (hx : (if lengthLeft then l else r) = .var x) (hone : oneFacts (if lengthLeft then r else l) = some one)
      (hg : arena.nodes[g.index]? = some (.guarded pg e)) (hpg : arena.nodes[pg.index]? = some (.atom (.pastSafe y)))
      (he : arena.nodes[e.index]? = some (.and e₀ e')) (he₀ : arena.nodes[e₀.index]? = some (.atom (.safeInt y)))
      (he' : arena.nodes[e'.index]? = some (.and e₁ e₂))
      (he₁ : arena.nodes[e₁.index]? = some (.atom (.linear (exactTermFacts y (fl ++ fr) (cl + cr)).1)))
      (he₂ : arena.nodes[e₂.index]? = some (.atom (.linear (exactTermFacts y (fl ++ fr) (cl + cr)).2)))
      (dop : Derivation arena Γ (.operation (.arith .add l.witness r.witness y)))
      (dl : Derivation arena Γ l.premise) (dr : Derivation arena Γ r.premise)
      (dlen : Derivation arena Γ (lengthEq x s)) (done : Derivation arena Γ one) :
      Derivation arena Γ (.at .after g)
  /-- **A defined string has its UTF-16 length**, in `[0, 2^53 − 1]` (I4,
  "Arithmetic indices and range conditions"; the note has no rule for it yet). -/
  | stringLength {Γ p a} (t : Term) (ht : t.kind = .strLength) (ha : arena.nodes[a.index]? = some (.atom (.defined t)))
      (d : Derivation arena Γ (.at p a)) : Derivation arena Γ (strRange (tagVar p t))
  /-- **A string's length read** is its UTF-16 length, a safe integer (I4;
  the pass's atoms on `lenOf` of a string; the note has no rule for it yet). -/
  | stringLengthRead {Γ} (x y : Path) (dop : Derivation arena Γ (.operation (.stringLength x y))) :
      Derivation arena Γ (lengthReadFacts x y)
  /-- **A string's element read at a valid index** is one code unit (I4,
  `stringRead`; the note has no rule for it yet). The index bound
  `i ≤ 2^32 − 2` is the code-unit model's (`stringIndexFacts`). No producer
  of the pass emits this consequence: it is no replacement of one. -/
  | stringRead {Γ} (x i y : Path) (dop : Derivation arena Γ (.operation (.stringRead x (.path i) y)))
      (di : Derivation arena Γ (stringIndexFacts x i)) : Derivation arena Γ (unitFacts y)
  /-- **A normal concatenation** has the sum of the operands' lengths (I4;
  the pass's `concatAtoms`; the note has no rule for it yet). -/
  | stringConcat {Γ} (x z y : Path) (dop : Derivation arena Γ (.operation (.arith .add (.path x) (.path z) y)))
      (dx : Derivation arena Γ (.linear (.le [(alen x, -1)] 0)))
      (dz : Derivation arena Γ (.linear (.le [(alen z, -1)] 0))) : Derivation arena Γ (concatFacts x z y)

/-! ## Raw derivations and their check -/

/-- **Untrusted finite proof data** (I4, `RawDerivation`): a rule tag per
step, the references and data the rule names, and `Linear.Step`
certificates. `checkDerivation` checks it into a `Derivation`. -/
inductive RawDerivation where
  | assumption
  | truth
  | falseElim (d : RawDerivation)
  | andIntro (d e : RawDerivation)
  | andLeft (other : Formula) (d : RawDerivation)
  | andRight (other : Formula) (d : RawDerivation)
  | cut (lemma : Formula) (d e : RawDerivation)
  | atTruth
  | atFalse (p : Phase) (a : AssertionRef) (d : RawDerivation)
  | atAndIntro (l r : AssertionRef) (dl dr : RawDerivation)
  | atAndLeft (a r : AssertionRef) (d : RawDerivation)
  | atAndRight (a l : AssertionRef) (d : RawDerivation)
  | guardLeft (g b : AssertionRef) (d : RawDerivation)
  | guardRight (g b : AssertionRef) (d : RawDerivation)
  | guardCases (p : Phase) (a g b : AssertionRef) (d dg db : RawDerivation)
  | existsIntro (b : AssertionRef) (w : Path) (n : Nat) (c e : AssertionRef) (de dc : RawDerivation)
  | existsIntroLiteral (b : AssertionRef) (ℓ : Val) (n : Nat) (c : AssertionRef) (dc : RawDerivation)
  | existsElim (p : Phase) (a b : AssertionRef) (n : Nat) (shifted : List Formula) (goal : Formula)
      (d e : RawDerivation)
  | equalitySubst (b : AssertionRef) (w w' : Path) (n : Nat) (c₁ e : AssertionRef) (de d : RawDerivation)
  | oldLift (d : RawDerivation)
  | boxElim (Φ : Footprint) (a : AssertionRef) (d : RawDerivation)
  | boxAndIntro (Φ : Footprint) (c l r bl br : AssertionRef) (dl dr : RawDerivation)
  | boxAndLeft (Φ : Footprint) (a c r : AssertionRef) (d : RawDerivation)
  | boxAndRight (Φ : Footprint) (a c l : AssertionRef) (d : RawDerivation)
  | boxMono (Φ : Footprint) (a x y : AssertionRef) (e d : RawDerivation)
  | boxAnti (ev : InclusionEvidence) (Ψ : Footprint) (a x K : AssertionRef) (dK d : RawDerivation)
  | boxGuard (Φ : Footprint) (a g bx x c : AssertionRef) (d : RawDerivation)
  | boxIdem (ev : RigidityEvidence) (a x D : AssertionRef) (dD d : RawDerivation)
  | tolerantFrame (S : Footprint) (sev : SupportEvidence) (rev : RespectEvidence) (cev : ContextEvidence)
      (K g : AssertionRef) (e dK dA : RawDerivation)
  | everyEmpty (π : Path) (n z : Term) (body : List (LinearClause Bound)) (d : AssertionRef) (dd dn : RawDerivation)
  | everyElim (p : Phase) (a : AssertionRef) (π : Path) (n k : Term) (body : List (LinearClause Bound))
      (d dk dlt : RawDerivation)
  | grow (y x : Nat) (a : AssertionRef) (d : RawDerivation)
  | dense (x k : Nat) (a : AssertionRef) (d : RawDerivation)
  | frame (Φ : Footprint) (a b : AssertionRef) (θ : Substitution) (d dt dθ : RawDerivation)
  | framePlus (ev : RigidityEvidence) (Φ : Footprint) (a b D : AssertionRef) (θ : Substitution)
      (dD d dt dθ : RawDerivation)
  | linear (Fs : List (Linear.Fact StepVar)) (defs : List StepVar) (steps : List (Linear.Step StepVar))
      (d dd : RawDerivation)
  | definedOfLinear (F : Linear.Fact StepVar) (d : RawDerivation)
  | definedToAtom (t : Term) (d : RawDerivation)
  | atomToDefined (a : AssertionRef) (d : RawDerivation)
  | safeIntToDefined (a : AssertionRef) (π : Path) (d : RawDerivation)
  | definedToSafeInt (π : Path) (d : RawDerivation)
  | atomToLinear (p : Phase) (a : AssertionRef) (F : Linear.Fact Term) (d : RawDerivation)
  | linearToAtom (F : Linear.Fact Term) (d : RawDerivation)
  | atomClash (p : Phase) (π : Path) (v : Val) (R : CallEffects.ElemPred) (e c : AssertionRef)
      (de dc : RawDerivation)
  | shiftRight (x k : Operand) (y : Path) (dop dx dk ds : RawDerivation)
  | mask (x k : Operand) (y : Path) (dop dx dk ds : RawDerivation)
  | integerOperation (op : Arith) (l r : Operand) (y : Path) (dop dl dr drange : RawDerivation)
  | lengthSuccessor (l r : Operand) (y s : Path) (lengthLeft : Bool) (pg e e₀ e' e₁ e₂ : AssertionRef)
      (dop dl dr dlen done : RawDerivation)
  | stringLength (t : Term) (a : AssertionRef) (d : RawDerivation)
  | stringLengthRead (x y : Path) (dop : RawDerivation)
  | stringRead (x i y : Path) (dop di : RawDerivation)
  | stringConcat (x z y : Path) (dop dx dz : RawDerivation)

/-- The node at a reference, where it is the stated one. -/
private def node? (arena : AssertionArena) (a : AssertionRef) (n : AssertionNode) :
    Except String (PLift (arena.nodes[a.index]? = some n)) :=
  if h : arena.nodes[a.index]? = some n then .ok ⟨h⟩ else .error s!"node {a.index} is not the stated node"

private def req (c : Prop) [Decidable c] (msg : String) : Except String (PLift c) :=
  if h : c then .ok ⟨h⟩ else .error msg

/-- **The derivation check** (I4, `checkDerivation`): checks scopes, every
premise, every node shape and every arithmetic certificate, building the
checked derivation of `goal` from `premises`. -/
def checkDerivation (arena : AssertionArena) (premises : List Formula) (goal : Formula) :
    RawDerivation → Except String (Derivation arena premises goal)
  | .assumption => do
    let ⟨h⟩ ← req (goal ∈ premises) "assumption: not a premise"
    pure (.assumption h)
  | .truth => match goal with
    | .truth => pure .truth
    | _ => .error "truth: goal is not true"
  | .falseElim d => do pure (.falseElim (← checkDerivation arena premises .falsity d))
  | .andIntro d e => match goal with
    | .and F G => do
      pure (.andIntro (← checkDerivation arena premises F d) (← checkDerivation arena premises G e))
    | _ => .error "andIntro: goal is no conjunction"
  | .andLeft G d => do pure (.andLeft (← checkDerivation arena premises (.and goal G) d))
  | .andRight F d => do pure (.andRight (← checkDerivation arena premises (.and F goal) d))
  | .cut F d e => do
    pure (.cut (← checkDerivation arena premises F d) (← checkDerivation arena (F :: premises) goal e))
  | .atTruth => match goal with
    | .at _ a => do let ⟨h⟩ ← node? arena a .truth; pure (.atTruth h)
    | _ => .error "atTruth: goal is no assertion"
  | .atFalse p a d => do
    let ⟨h⟩ ← node? arena a .falsity
    pure (.atFalse h (← checkDerivation arena premises (.at p a) d))
  | .atAndIntro l r dl dr => match goal with
    | .at p a => do
      let ⟨h⟩ ← node? arena a (.and l r)
      pure (.atAndIntro h (← checkDerivation arena premises (.at p l) dl) (← checkDerivation arena premises (.at p r) dr))
    | _ => .error "atAndIntro: goal is no assertion"
  | .atAndLeft a r d => match goal with
    | .at p l => do
      let ⟨h⟩ ← node? arena a (.and l r)
      pure (.atAndLeft h (← checkDerivation arena premises (.at p a) d))
    | _ => .error "atAndLeft: goal is no assertion"
  | .atAndRight a l d => match goal with
    | .at p r => do
      let ⟨h⟩ ← node? arena a (.and l r)
      pure (.atAndRight h (← checkDerivation arena premises (.at p a) d))
    | _ => .error "atAndRight: goal is no assertion"
  | .guardLeft g b d => match goal with
    | .at p a => do
      let ⟨h⟩ ← node? arena a (.guarded g b)
      pure (.guardLeft h (← checkDerivation arena premises (.at p g) d))
    | _ => .error "guardLeft: goal is no assertion"
  | .guardRight g b d => match goal with
    | .at p a => do
      let ⟨h⟩ ← node? arena a (.guarded g b)
      pure (.guardRight h (← checkDerivation arena premises (.at p b) d))
    | _ => .error "guardRight: goal is no assertion"
  | .guardCases p a g b d dg db => do
    let ⟨h⟩ ← node? arena a (.guarded g b)
    pure (.guardCases h (← checkDerivation arena premises (.at p a) d)
      (← checkDerivation arena (.at p g :: premises) goal dg) (← checkDerivation arena (.at p b :: premises) goal db))
  | .existsIntro b w n c e de dc => match goal with
    | .at p a => do
      let ⟨hn⟩ ← node? arena a (.existsValue b)
      let ⟨hc⟩ ← req (substCheck arena.nodes (Substitution.instantiate (.path w) n) b.index c.index = true)
        "existsIntro: not the instance"
      let ⟨he⟩ ← node? arena e (.atom (.equal w (.path w)))
      pure (.existsIntro w n hn hc he (← checkDerivation arena premises (.at p e) de)
        (← checkDerivation arena premises (.at p c) dc))
    | _ => .error "existsIntro: goal is no assertion"
  | .existsIntroLiteral b ℓ n c dc => match goal with
    | .at p a => do
      let ⟨hn⟩ ← node? arena a (.existsValue b)
      let ⟨hc⟩ ← req (substCheck arena.nodes (Substitution.instantiate (.literal ℓ) n) b.index c.index = true)
        "existsIntroLiteral: not the instance"
      pure (.existsIntroLiteral ℓ n hn hc (← checkDerivation arena premises (.at p c) dc))
    | _ => .error "existsIntroLiteral: goal is no assertion"
  | .existsElim p a b n Γ' G' d e => do
    let ⟨hn⟩ ← node? arena a (.existsValue b)
    let ⟨hΓ⟩ ← req (Γ'.all (fun F' => premises.any fun F => shiftFormula arena.nodes p n F F') = true)
      "existsElim: a premise is not read one slot further"
    let ⟨hG⟩ ← req (shiftFormula arena.nodes p n goal G' = true) "existsElim: the conclusion is not read one slot further"
    pure (.existsElim n hn hΓ hG (← checkDerivation arena premises (.at p a) d)
      (← checkDerivation arena (.at p b :: Γ') G' e))
  | .equalitySubst b w w' n c₁ e de d => match goal with
    | .at p c₂ => do
      let ⟨h₁⟩ ← req (substCheck arena.nodes (Substitution.instantiate (.path w) n) b.index c₁.index = true)
        "equalitySubst: not the first instance"
      let ⟨h₂⟩ ← req (substCheck arena.nodes (Substitution.instantiate (.path w') n) b.index c₂.index = true)
        "equalitySubst: not the second instance"
      let ⟨he⟩ ← node? arena e (.atom (.equal w (.path w')))
      pure (.equalitySubst w w' n h₁ h₂ he (← checkDerivation arena premises (.at p e) de)
        (← checkDerivation arena premises (.at p c₁) d))
    | _ => .error "equalitySubst: goal is no assertion"
  | .oldLift d => do
    let ⟨hΓ⟩ ← req (premises.all Formula.swappable = true) "oldLift: a premise reads a transition"
    let ⟨hF⟩ ← req (goal.swappable = true) "oldLift: the goal reads a transition"
    pure (.oldLift hΓ hF (← checkDerivation arena (premises.map Formula.swap) goal.swap d))
  | .boxElim Φ a d => match goal with
    | .at p b => do
      let ⟨h⟩ ← node? arena a (.box Φ b)
      pure (.boxElim h (← checkDerivation arena premises (.at p a) d))
    | _ => .error "boxElim: goal is no assertion"
  | .boxAndIntro Φ c l r bl br dl dr => match goal with
    | .at p a => do
      let ⟨hn⟩ ← node? arena a (.box Φ c)
      let ⟨hc⟩ ← node? arena c (.and l r)
      let ⟨hl⟩ ← node? arena bl (.box Φ l)
      let ⟨hr⟩ ← node? arena br (.box Φ r)
      pure (.boxAndIntro hn hc hl hr (← checkDerivation arena premises (.at p bl) dl)
        (← checkDerivation arena premises (.at p br) dr))
    | _ => .error "boxAndIntro: goal is no assertion"
  | .boxAndLeft Φ a c r d => match goal with
    | .at p bl => do
      let ⟨hn⟩ ← node? arena a (.box Φ c)
      match arena.nodes[bl.index]? with
      | some (.box _ l) => do
        let ⟨hc⟩ ← node? arena c (.and l r)
        let ⟨hl⟩ ← node? arena bl (.box Φ l)
        pure (.boxAndLeft hn hc hl (← checkDerivation arena premises (.at p a) d))
      | _ => .error "boxAndLeft: goal is no box"
    | _ => .error "boxAndLeft: goal is no assertion"
  | .boxAndRight Φ a c l d => match goal with
    | .at p br => do
      let ⟨hn⟩ ← node? arena a (.box Φ c)
      match arena.nodes[br.index]? with
      | some (.box _ r) => do
        let ⟨hc⟩ ← node? arena c (.and l r)
        let ⟨hr⟩ ← node? arena br (.box Φ r)
        pure (.boxAndRight hn hc hr (← checkDerivation arena premises (.at p a) d))
      | _ => .error "boxAndRight: goal is no box"
    | _ => .error "boxAndRight: goal is no assertion"
  | .boxMono Φ a x y e d => match goal with
    | .at p b => do
      let ⟨ha⟩ ← node? arena a (.box Φ x)
      let ⟨hb⟩ ← node? arena b (.box Φ y)
      pure (.boxMono ha hb (← checkDerivation arena [.at .after x] (.at .after y) e)
        (← checkDerivation arena premises (.at p a) d))
    | _ => .error "boxMono: goal is no assertion"
  | .boxAnti ev Ψ a x K dK d => match goal with
    | .at p b => do
      match arena.nodes[b.index]? with
      | some (.box Φ _) => do
        let ⟨hev⟩ ← req (ev.check Φ Ψ = true) "boxAnti: the effects are not included"
        let ⟨ha⟩ ← node? arena a (.box Ψ x)
        let ⟨hb⟩ ← node? arena b (.box Φ x)
        pure (.boxAnti (K := K) ev hev ha hb (← checkDerivation arena premises (.at p K) dK)
          (← checkDerivation arena premises (.at p a) d))
      | _ => .error "boxAnti: goal is no box"
    | _ => .error "boxAnti: goal is no assertion"
  | .boxGuard Φ a g bx x c d => match goal with
    | .at p b => do
      let ⟨ha⟩ ← node? arena a (.guarded g bx)
      let ⟨hbx⟩ ← node? arena bx (.box Φ x)
      let ⟨hb⟩ ← node? arena b (.box Φ c)
      let ⟨hc⟩ ← node? arena c (.guarded g x)
      pure (.boxGuard ha hbx hb hc (← checkDerivation arena premises (.at p a) d))
    | _ => .error "boxGuard: goal is no assertion"
  | .boxIdem ev a x D dD d => match goal with
    | .at p b => do
      match arena.nodes[b.index]? with
      | some (.box Φ _) => do
        let ⟨hev⟩ ← req (ev.check arena D Φ = true) "boxIdem: the effect is not rigid on the domain"
        let ⟨ha⟩ ← node? arena a (.box Φ x)
        let ⟨hb⟩ ← node? arena b (.box Φ a)
        pure (.boxIdem ev hev ha hb (← checkDerivation arena premises (.at p D) dD)
          (← checkDerivation arena premises (.at p a) d))
      | _ => .error "boxIdem: goal is no box"
    | _ => .error "boxIdem: goal is no assertion"
  | .tolerantFrame S sev rev cev K g e dK dA => match goal with
    | .at p b => do
      match arena.nodes[b.index]? with
      | some (.box Φ A) => do
        let ⟨hs⟩ ← req (sev.check arena A = true) "tolerantFrame: no support"
        let ⟨hr⟩ ← req (rev.check S Φ = true) "tolerantFrame: the effect does not respect the support"
        let ⟨hc⟩ ← req (cev.check arena g = true) "tolerantFrame: the context evidence does not check"
        let ⟨hb⟩ ← node? arena b (.box Φ A)
        pure (.tolerantFrame S sev rev cev hs hr hc hb (← checkDerivation arena [.at .after K] (.at .after g) e)
          (← checkDerivation arena premises (.at p K) dK) (← checkDerivation arena premises (.at p A) dA))
      | _ => .error "tolerantFrame: goal is no box"
    | _ => .error "tolerantFrame: goal is no assertion"
  | .everyEmpty π n z body d dd dn => match goal with
    | .at p a => do
      let ⟨ha⟩ ← node? arena a (.atom (.every π n body))
      let ⟨hd⟩ ← node? arena d (.atom (.dense π z))
      pure (.everyEmpty π n z body ha hd (← checkDerivation arena premises (.at p d) dd)
        (← checkDerivation arena premises (.linear (tagFact p (.le [(n, 1)] 0))) dn))
    | _ => .error "everyEmpty: goal is no assertion"
  | .everyElim p a π n k body d dk dlt => do
    let ⟨ha⟩ ← node? arena a (.atom (.every π n body))
    match (everyInstances body k).find? (fun G => goal == .linear (tagFact p G)) with
    | some G => do
      let ⟨hG⟩ ← req (G ∈ everyInstances body k) "everyElim: not an instance"
      let ⟨hg⟩ ← req (goal = .linear (tagFact p G)) "everyElim: goal is not the instance"
      pure (hg.symm ▸ .everyElim π n k body G ha hG (← checkDerivation arena premises (.at p a) d)
        (← checkDerivation arena premises (.linear (tagFact p (.le [(k, -1)] 0))) dk)
        (← checkDerivation arena premises (.linear (tagFact p (.le [(k, 1), (n, -1)] (-1)))) dlt))
    | none => .error "everyElim: goal is no instance of the body"
  | .grow y x a d => match goal with
    | .at p b => do
      let ⟨ha⟩ ← node? arena a (.atom (.linear (lowerFact y x)))
      let ⟨hb⟩ ← node? arena b (.box growEffect.fp a)
      pure (.grow y x ha hb (← checkDerivation arena premises (.at p a) d))
    | _ => .error "grow: goal is no assertion"
  | .dense x k a d => match goal with
    | .at p b => do
      let ⟨ha⟩ ← node? arena a (.atom (.dense (Path.var x) (Term.value k)))
      let ⟨hb⟩ ← node? arena b (.box growEffect.fp a)
      pure (.dense x k ha hb (← checkDerivation arena premises (.at p a) d))
    | _ => .error "dense: goal is no assertion"
  | .frame Φ a b θ d dt dθ => match goal with
    | .at .after c => do
      let ⟨ha⟩ ← node? arena a (.box Φ b)
      let ⟨hc⟩ ← req (substCheck arena.nodes θ b.index c.index = true) "frame: not the transported body"
      pure (.frame θ ha hc (← checkDerivation arena premises (.at .before a) d)
        (← checkDerivation arena premises (.transition Φ) dt) (← checkDerivation arena premises (.transport θ) dθ))
    | _ => .error "frame: goal is no exit assertion"
  | .framePlus ev Φ a b D θ dD d dt dθ => match goal with
    | .at .after c => do
      let ⟨hev⟩ ← req (ev.check arena D Φ = true) "framePlus: the effect is not rigid on the domain"
      let ⟨ha⟩ ← node? arena a (.box Φ b)
      let ⟨hc⟩ ← req (substCheck arena.nodes θ a.index c.index = true) "framePlus: not the transported box"
      pure (.framePlus ev hev θ ha hc (← checkDerivation arena premises (.at .before D) dD)
        (← checkDerivation arena premises (.at .before a) d)
        (← checkDerivation arena premises (.transition Φ) dt) (← checkDerivation arena premises (.transport θ) dθ))
    | _ => .error "framePlus: goal is no exit assertion"
  | .linear Fs defs steps d dd => match goal with
    | .linear G => do
      let ⟨hc⟩ ← req (linearCheck Fs defs steps G = true) "linear: the certificate does not conclude the goal"
      pure (.linear Fs defs steps hc (← checkDerivation arena premises (conj (Fs.map .linear)) d)
        (← checkDerivation arena premises (conj (defs.map .defined)) dd))
    | _ => .error "linear: goal is no linear fact"
  | .definedOfLinear F d => match goal with
    | .defined v => do
      let ⟨hv⟩ ← req (v ∈ F.vars) "definedOfLinear: the fact does not name the term"
      pure (.definedOfLinear hv (← checkDerivation arena premises (.linear F) d))
    | _ => .error "definedOfLinear: goal is no definedness"
  | .definedToAtom t d => match goal with
    | .at p a => do
      let ⟨ha⟩ ← node? arena a (.atom (.defined t))
      pure (.definedToAtom ha (← checkDerivation arena premises (.defined (tagVar p t)) d))
    | _ => .error "definedToAtom: goal is no assertion"
  | .atomToDefined a d => match goal with
    | .defined v => match v with
      | .before t => do
        let ⟨ha⟩ ← node? arena a (.atom (.defined t))
        pure (.atomToDefined (p := .before) ha (← checkDerivation arena premises (.at .before a) d))
      | .after t => do
        let ⟨ha⟩ ← node? arena a (.atom (.defined t))
        pure (.atomToDefined (p := .after) ha (← checkDerivation arena premises (.at .after a) d))
    | _ => .error "atomToDefined: goal is no definedness"
  | .safeIntToDefined a π d => do
    let ⟨ha⟩ ← node? arena a (.atom (.safeInt π))
    if hg : goal = .defined (tagVar .before (π.term .value)) then
      pure (hg.symm ▸ .safeIntToDefined (p := .before) ha (← checkDerivation arena premises (.at .before a) d))
    else if hg : goal = .defined (tagVar .after (π.term .value)) then
      pure (hg.symm ▸ .safeIntToDefined (p := .after) ha (← checkDerivation arena premises (.at .after a) d))
    else .error "safeIntToDefined: goal is not the path's safe integer"
  | .definedToSafeInt π d => match goal with
    | .at p a => do
      let ⟨ha⟩ ← node? arena a (.atom (.safeInt π))
      pure (.definedToSafeInt ha (← checkDerivation arena premises (.defined (tagVar p (π.term .value))) d))
    | _ => .error "definedToSafeInt: goal is no assertion"
  | .atomToLinear p a F d => do
    let ⟨ha⟩ ← node? arena a (.atom (.linear F))
    let ⟨hg⟩ ← req (goal = .linear (tagFact p F)) "atomToLinear: goal is not the atom's fact"
    pure (hg.symm ▸ .atomToLinear F ha (← checkDerivation arena premises (.at p a) d))
  | .linearToAtom F d => match goal with
    | .at p a => do
      let ⟨ha⟩ ← node? arena a (.atom (.linear F))
      pure (.linearToAtom F ha (← checkDerivation arena premises (.linear (tagFact p F)) d))
    | _ => .error "linearToAtom: goal is no assertion"
  | .atomClash p π v R e c de dc => do
    let ⟨hv⟩ ← req (R.mem v = false) "atomClash: the value is of the kind"
    let ⟨he⟩ ← node? arena e (.atom (.equal π (.literal v)))
    let ⟨hc⟩ ← node? arena c (.atom (.contents π R))
    pure (.atomClash π v R hv he hc (← checkDerivation arena premises (.at p e) de)
      (← checkDerivation arena premises (.at p c) dc))
  | .shiftRight x k y dop dx dk ds => do
    match hx : x.form, hk : k.form with
    | some (F, c), some ([], d) =>
      let ⟨hd⟩ ← req (0 ≤ d ∧ d < 32) "shiftRight: the shift is not in [0, 31]"
      let ⟨hg⟩ ← req (goal = shrFacts y F c d) "shiftRight: goal is not the shift's facts"
      pure (hg.symm ▸ .shiftRight x k y F c d hx hk hd
        (← checkDerivation arena premises (.operation (.arith .shr x.witness k.witness y)) dop)
        (← checkDerivation arena premises x.premise dx) (← checkDerivation arena premises k.premise dk)
        (← checkDerivation arena premises (smallFacts F c) ds))
    | _, _ => .error "shiftRight: the shift is no constant safe integer"
  | .mask x k y dop dx dk ds => do
    match hx : x.form, hk : k.form with
    | some (F, c), some ([], m) =>
      let ⟨hm⟩ ← req (0 ≤ m ∧ m < 2 ^ 31) "mask: the mask is not in [0, 2^31 - 1]"
      let ⟨hg⟩ ← req (goal = maskFacts y F c m) "mask: goal is not the mask's facts"
      pure (hg.symm ▸ .mask x k y F c m hx hk hm
        (← checkDerivation arena premises (.operation (.arith .bitAnd x.witness k.witness y)) dop)
        (← checkDerivation arena premises x.premise dx) (← checkDerivation arena premises k.premise dk)
        (← checkDerivation arena premises (smallFacts F c) ds))
    | _, _ => .error "mask: the mask is no constant safe integer"
  | .integerOperation op l r y dop dl dr drange => do
    match hl : l.form, hr : r.form with
    | some (fl, cl), some (fr, cr) =>
      match hF : resultForm op fl cl fr cr with
      | some (F, c) => do
        let ⟨hg⟩ ← req (goal = valueFacts y F c) "integerOperation: goal is not the exact result"
        pure (hg.symm ▸ .integerOperation op l r y fl cl fr cr F c hl hr hF
          (← checkDerivation arena premises (.operation (.arith op l.witness r.witness y)) dop)
          (← checkDerivation arena premises l.premise dl) (← checkDerivation arena premises r.premise dr)
          (← checkDerivation arena premises (rangeFacts F c) drange))
      | none => .error "integerOperation: no exact form"
    | _, _ => .error "integerOperation: an operand is no safe integer"
  | .lengthSuccessor l r y s lengthLeft pg e e₀ e' e₁ e₂ dop dl dr dlen done => match goal with
    | .at .after g => do
      match hl : l.form, hr : r.form, hx : (if lengthLeft then l else r), hone : oneFacts (if lengthLeft then r else l) with
      | some (fl, cl), some (fr, cr), .var x, some one => do
        let ⟨hg⟩ ← node? arena g (.guarded pg e)
        let ⟨hpg⟩ ← node? arena pg (.atom (.pastSafe y))
        let ⟨he⟩ ← node? arena e (.and e₀ e')
        let ⟨he₀⟩ ← node? arena e₀ (.atom (.safeInt y))
        let ⟨he'⟩ ← node? arena e' (.and e₁ e₂)
        let ⟨he₁⟩ ← node? arena e₁ (.atom (.linear (exactTermFacts y (fl ++ fr) (cl + cr)).1))
        let ⟨he₂⟩ ← node? arena e₂ (.atom (.linear (exactTermFacts y (fl ++ fr) (cl + cr)).2))
        pure (.lengthSuccessor l r y s lengthLeft x fl cl fr cr one hl hr hx hone hg hpg he he₀ he' he₁ he₂
          (← checkDerivation arena premises (.operation (.arith .add l.witness r.witness y)) dop)
          (← checkDerivation arena premises l.premise dl) (← checkDerivation arena premises r.premise dr)
          (← checkDerivation arena premises (lengthEq x s) dlen) (← checkDerivation arena premises one done))
      | _, _, _, _ => .error "lengthSuccessor: no string length plus one"
    | _ => .error "lengthSuccessor: goal is no exit assertion"
  | .stringLength t a d => do
    let ⟨ht⟩ ← req (t.kind = .strLength) "stringLength: the term is no string length"
    let ⟨ha⟩ ← node? arena a (.atom (.defined t))
    match goal with
    | .and (.linear (.le [(v, _)] _)) _ =>
      let p : Phase := match v with
        | .before _ => .before
        | .after _ => .after
      let ⟨hg⟩ ← req (goal = strRange (tagVar p t)) "stringLength: goal is not the length's range"
      pure (hg.symm ▸ .stringLength t ht ha (← checkDerivation arena premises (.at p a) d))
    | _ => .error "stringLength: goal is not the length's range"
  | .stringLengthRead x y dop => do
    let ⟨hg⟩ ← req (goal = lengthReadFacts x y) "stringLengthRead: goal is not the read's facts"
    pure (hg.symm ▸ .stringLengthRead x y (← checkDerivation arena premises (.operation (.stringLength x y)) dop))
  | .stringRead x i y dop di => do
    let ⟨hg⟩ ← req (goal = unitFacts y) "stringRead: goal is not the unit's length"
    pure (hg.symm ▸ .stringRead x i y (← checkDerivation arena premises (.operation (.stringRead x (.path i) y)) dop)
      (← checkDerivation arena premises (stringIndexFacts x i) di))
  | .stringConcat x z y dop dx dz => do
    let ⟨hg⟩ ← req (goal = concatFacts x z y) "stringConcat: goal is not the concatenation's length"
    pure (hg.symm ▸ .stringConcat x z y
      (← checkDerivation arena premises (.operation (.arith .add (.path x) (.path z) y)) dop)
      (← checkDerivation arena premises (.linear (.le [(alen x, -1)] 0)) dx)
      (← checkDerivation arena premises (.linear (.le [(alen z, -1)] 0)) dz))


/-! ## Soundness of the arithmetic rules -/

section Arithmetic

/-- Every code unit of a string is below `2^16`. -/
theorem utf16Units_lt (str : String) : ∀ u ∈ utf16Units str, u < 0x10000 := by
  intro u hu
  simp only [utf16Units, List.mem_flatMap] at hu
  obtain ⟨c, -, hc⟩ := hu
  have hv := c.valid
  have e : c.toNat = c.val.toNat := rfl
  have hlt : c.val.toNat < 0x110000 := by
    rcases hv with h | h
    · have := h; simp at this; omega
    · have := h.2; simp at this; omega
  split at hc
  · simp at hc; omega
  · simp at hc; omega

/-- **The string of one code unit has UTF-16 length one.** -/
theorem unitString_length (u : Nat) (hu : u < 0x10000) : (utf16Units (unitString u)).length = 1 := by
  unfold unitString
  split
  · decide
  · simp only [utf16Units, String.toList_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have : (Char.ofNat u).val.toNat < 0x10000 := by
      unfold Char.ofNat
      split
      · simp [Char.ofNatAux]; omega
      · decide
    have h2 : (Char.ofNat u).toNat < 0x10000 := this
    simp [h2]

theorem av_eq (s : TwoState) (p : Path) : stepValue s (av p) = (p.read s.afterEnv s.after.h).bind intValue := rfl

theorem alen_eq (s : TwoState) (p : Path) :
    stepValue s (alen p) = (p.read s.afterEnv s.after.h).bind strLengthOf := rfl

theorem av_some {s : TwoState} {p : Path} {i : Int} (h : stepValue s (av p) = some i) :
    ∃ b, p.read s.afterEnv s.after.h = some (.num b) ∧ SafeIntegers.SafeInt b i := by
  rw [av_eq] at h
  obtain ⟨v, hv, hi⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, rfl, hb⟩ := intValue_safe hi
  exact ⟨b, hv, hb⟩

theorem alen_some {s : TwoState} {p : Path} {n : Int} (h : stepValue s (alen p) = some n) :
    ∃ str, p.read s.afterEnv s.after.h = some (.str str) ∧ (utf16Units str).length ≤ maxStringLength ∧
      n = (utf16Units str).length := by
  rw [alen_eq] at h
  obtain ⟨v, hv, hn⟩ := Option.bind_eq_some_iff.mp h
  cases v <;> simp only [strLengthOf, reduceCtorEq] at hn
  rename_i str
  split at hn
  · cases hn; exact ⟨str, hv, by assumption, rfl⟩
  · cases hn

theorem factAt_defined {V : Type} {val : V → Option Int} {F : Linear.Fact V} (h : FactAt val F) {x : V}
    (hx : x ∈ F.vars) : ∃ i, val x = some i :=
  Option.isSome_iff_exists.mp (h.1 x hx)

theorem safeInt_nat {L : Nat} (hL : L ≤ maxStringLength) : SafeIntegers.SafeInt (bitsOfNat L) (L : Int) :=
  ⟨by simp [maxStringLength] at hL ⊢; omega, .inl ⟨by omega, by simp⟩⟩

theorem binop_num_of {op : Arith} (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .shr ∨ op = .bitAnd)
    {x y : UInt64} {c : Val} (h : binop op (.num x) (.num y) = some c) : c = .num (arithBits op x y) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp [binop, Arith.relational] at h <;> exact h.symm

theorem scale_vars {V : Type} (k : Int) (f : Linear.Form V) : (f.scale k).map (·.1) = f.map (·.1) := by
  simp [Linear.Form.scale, Function.comp_def]

theorem holds_lin {arena : AssertionArena} {s : TwoState} {G : Linear.Fact Term} :
    Holds arena s (lin G) ↔ FactAt (termAt s.afterEnv s.after.h) G :=
  factAt_tag s .after G

/-- A fact `a·y + G ≤ d` holds where `y` denotes `r`, `G`'s terms are
defined and the inequality holds of those values. -/
theorem factAt_cons {V : Type} {val : V → Option Int} {y : V} {r a d : Int} {G : Linear.Form V}
    (hy : val y = some r) (hG : ∀ t ∈ G.map (·.1), (val t).isSome)
    (h : a * r + Linear.Form.eval (fun t => (val t).getD 0) G ≤ d) : FactAt val (.le ((y, a) :: G) d) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · simp only [Linear.Fact.vars, List.map_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp [hy]
    · exact hG t ht
  · simp only [Linear.Fact.Holds, Linear.Form.eval, hy, Option.getD_some]; exact h

/-- **An operand denotes its form**: under its evidence, the operand's
witness reads a safe integer, the value of its form, whose terms are
defined. -/
theorem Operand.sound {arena : AssertionArena} {s : TwoState} {o : Operand} {F : Linear.Form Term} {c : Int}
    (hf : o.form = some (F, c)) (hp : Holds arena s o.premise) :
    (∀ t ∈ F.map (·.1), (termAt s.afterEnv s.after.h t).isSome) ∧
    ∃ b, o.witness.value s.afterEnv s.after.h = some (.num b) ∧
      SafeIntegers.SafeInt b (Linear.Form.eval (fun t => (termAt s.afterEnv s.after.h t).getD 0) F + c) := by
  cases o with
  | var p =>
    simp only [Operand.form, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have hd : (termAt s.afterEnv s.after.h (vt p)).isSome := hp
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hd
    rw [Path.termAt_term] at hi
    obtain ⟨v, hv, hiv⟩ := Option.bind_eq_some_iff.mp hi
    obtain ⟨b, rfl, hs⟩ := intValue_safe hiv
    have hi' : termAt s.afterEnv s.after.h (vt p) = some i := by rw [Path.termAt_term, hv]; exact hiv
    refine ⟨by simp [hi'], b, hv, ?_⟩
    simpa [Linear.Form.eval, hi'] using hs
  | const p k =>
    simp only [Operand.form, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp only [Operand.premise, conj, Holds] at hp
    have h1 := holds_lin.mp hp.1
    have h2 := holds_lin.mp hp.2.1
    obtain ⟨i, hi⟩ := factAt_defined h1 (x := vt p) (by simp [Linear.Fact.vars])
    have e1 := h1.2
    have e2 := h2.2
    simp only [Linear.Fact.Holds, Linear.Form.eval, hi, Option.getD_some] at e1 e2
    rw [Path.termAt_term] at hi
    obtain ⟨v, hv, hiv⟩ := Option.bind_eq_some_iff.mp hi
    obtain ⟨b, rfl, hs⟩ := intValue_safe hiv
    refine ⟨by simp, b, hv, ?_⟩
    simpa [Linear.Form.eval, show i = k by omega] using hs
  | literal b =>
    simp only [Operand.form, Option.map_eq_some_iff, Prod.mk.injEq] at hf
    obtain ⟨i, hi, rfl, rfl⟩ := hf
    exact ⟨by simp, b, rfl, by simpa [Linear.Form.eval] using SafeIntegers.safeIntOfBits_sound hi⟩

theorem binop_operands {op : Arith} (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .shr ∨ op = .bitAnd)
    {s : TwoState} {l r : Witness} {y : Path} {a b : UInt64} (hl : l.value s.afterEnv s.after.h = some (.num a))
    (hr : r.value s.afterEnv s.after.h = some (.num b)) (h : (OperationPost.arith op l r y).Holds s) :
    y.read s.afterEnv s.after.h = some (.num (arithBits op a b)) := by
  obtain ⟨a', b', c', ha, hb, hy, hbin⟩ := h
  rw [hl] at ha; cases ha
  rw [hr] at hb; cases hb
  rw [binop_num_of hop hbin] at hy
  exact hy

theorem result_term {s : TwoState} {y : Path} {bits : UInt64} {r : Int}
    (hy : y.read s.afterEnv s.after.h = some (.num bits)) (hs : SafeIntegers.SafeInt bits r) :
    termAt s.afterEnv s.after.h (vt y) = some r := by
  rw [Path.termAt_term, hy]; exact intValue_num hs

/-- The facts `0 ≤ F + c ≤ 2^31 − 1`. -/
theorem small_sound {arena : AssertionArena} {s : TwoState} {F : Linear.Form Term} {c : Int}
    (h : Holds arena s (smallFacts F c)) :
    0 ≤ Linear.Form.eval (fun t => (termAt s.afterEnv s.after.h t).getD 0) F + c ∧
      Linear.Form.eval (fun t => (termAt s.afterEnv s.after.h t).getD 0) F + c < 2 ^ 31 := by
  simp only [smallFacts, conj, Holds] at h
  have h1 := (holds_lin.mp h.1).2
  have h2 := (holds_lin.mp h.2.1).2
  simp only [Linear.Fact.Holds, Linear.Form.eval_scale] at h1 h2
  omega

theorem shiftRight_sound {arena : AssertionArena} {s : TwoState} {x k : Operand} {y : Path} {F : Linear.Form Term}
    {c d : Int} (hx : x.form = some (F, c)) (hk : k.form = some ([], d)) (hd : 0 ≤ d ∧ d < 32)
    (hop : (OperationPost.arith .shr x.witness k.witness y).Holds s) (hpx : Holds arena s x.premise)
    (hpk : Holds arena s k.premise) (hsm : Holds arena s (smallFacts F c)) : Holds arena s (shrFacts y F c d) := by
  obtain ⟨hFd, xb, hxv, hxs⟩ := Operand.sound hx hpx
  obtain ⟨-, kb, hkv, hks⟩ := Operand.sound hk hpk
  simp only [Linear.Form.eval, Int.zero_add] at hks
  obtain ⟨h0, h1⟩ := small_sound hsm
  have hy := binop_operands (by simp) hxv hkv hop
  generalize hE : Linear.Form.eval (fun t => (termAt s.afterEnv s.after.h t).getD 0) F = E at *
  have hsafe := SafeIntegers.shr_safe hxs hks h0 h1 hd.1 hd.2
  have hyv := result_term hy hsafe
  generalize hP : (2 : Int) ^ d.toNat = P at *
  have hp : (0 : Int) < P := by rw [← hP]; exact Int.pow_pos (by decide)
  have hr0 := Int.ediv_nonneg h0 (Int.le_of_lt hp)
  have hrlt := Int.emod_lt_of_pos (E + c) hp
  have hr := Int.emod_nonneg (E + c) (Int.ne_of_gt hp)
  have he := Int.emod_add_mul_ediv (E + c) P
  have hFs : ∀ t ∈ (F.scale (-1)).map (·.1), (termAt s.afterEnv s.after.h t).isSome := by
    rw [scale_vars]; exact hFd
  simp only [shrFacts, conj, Holds]
  refine ⟨(show (termAt s.afterEnv s.after.h (vt y)).isSome by rw [hyv]; rfl),
    holds_lin.mpr (factAt_cons hyv (by simp) ?_), holds_lin.mpr (factAt_cons hyv hFs ?_),
    holds_lin.mpr (factAt_cons hyv hFd ?_), trivial⟩
  · simp only [Linear.Form.eval]; omega
  · simp only [Linear.Form.eval_scale, hE, hP]; omega
  · simp only [hE, Int.neg_mul, hP]; omega

theorem mask_sound {arena : AssertionArena} {s : TwoState} {x k : Operand} {y : Path} {F : Linear.Form Term}
    {c m : Int} (hx : x.form = some (F, c)) (hk : k.form = some ([], m)) (hm : 0 ≤ m ∧ m < 2 ^ 31)
    (hop : (OperationPost.arith .bitAnd x.witness k.witness y).Holds s) (hpx : Holds arena s x.premise)
    (hpk : Holds arena s k.premise) (hsm : Holds arena s (smallFacts F c)) : Holds arena s (maskFacts y F c m) := by
  obtain ⟨hFd, xb, hxv, hxs⟩ := Operand.sound hx hpx
  obtain ⟨-, kb, hkv, hks⟩ := Operand.sound hk hpk
  simp only [Linear.Form.eval, Int.zero_add] at hks
  obtain ⟨h0, h1⟩ := small_sound hsm
  have hy := binop_operands (by simp) hxv hkv hop
  generalize hE : Linear.Form.eval (fun t => (termAt s.afterEnv s.after.h t).getD 0) F = E at *
  obtain ⟨r, hsafe, hr0, hri, hrm⟩ := SafeIntegers.bitAnd_safe hxs hks h0 h1 hm.1 hm.2
  have hyv := result_term hy hsafe
  have hFs : ∀ t ∈ (F.scale (-1)).map (·.1), (termAt s.afterEnv s.after.h t).isSome := by
    rw [scale_vars]; exact hFd
  simp only [maskFacts, conj, Holds]
  refine ⟨(show (termAt s.afterEnv s.after.h (vt y)).isSome by rw [hyv]; rfl),
    holds_lin.mpr (factAt_cons hyv (by simp) ?_), holds_lin.mpr (factAt_cons hyv (by simp) ?_),
    holds_lin.mpr (factAt_cons hyv hFs ?_), trivial⟩
  · simp only [Linear.Form.eval]; omega
  · simp only [Linear.Form.eval]; omega
  · rw [Linear.Form.eval_scale, hE]; omega

/-- `y` is the safe integer `E + c`, `E` the value of `F`: the value facts. -/
theorem valueFacts_of {arena : AssertionArena} {s : TwoState} {y : Path} {F : Linear.Form Term} {c : Int}
    (hFd : ∀ t ∈ F.map (·.1), (termAt s.afterEnv s.after.h t).isSome)
    (hyv : termAt s.afterEnv s.after.h (vt y) =
      some (Linear.Form.eval (fun t => (termAt s.afterEnv s.after.h t).getD 0) F + c)) :
    Holds arena s (valueFacts y F c) := by
  have hFs : ∀ t ∈ (F.scale (-1)).map (·.1), (termAt s.afterEnv s.after.h t).isSome := by
    rw [scale_vars]; exact hFd
  simp only [valueFacts, exactTermFacts, conj, Holds]
  refine ⟨(show (termAt s.afterEnv s.after.h (vt y)).isSome by rw [hyv]; rfl),
    holds_lin.mpr (factAt_cons hyv hFs ?_), holds_lin.mpr (factAt_cons hyv hFd ?_), trivial⟩
  · rw [Linear.Form.eval_scale]; omega
  · omega

theorem integerOperation_sound {arena : AssertionArena} {s : TwoState} {op : Arith} {l r : Operand} {y : Path}
    {fl fr F : Linear.Form Term} {cl cr c : Int} (hl : l.form = some (fl, cl)) (hr : r.form = some (fr, cr))
    (hF : resultForm op fl cl fr cr = some (F, c)) (hop : (OperationPost.arith op l.witness r.witness y).Holds s)
    (hpl : Holds arena s l.premise) (hpr : Holds arena s r.premise) (hrange : Holds arena s (rangeFacts F c)) :
    Holds arena s (valueFacts y F c) := by
  obtain ⟨hld, a, hav, has⟩ := Operand.sound hl hpl
  obtain ⟨hrd, b, hbv, hbs⟩ := Operand.sound hr hpr
  simp only [rangeFacts, conj, Holds] at hrange
  have h1 := (holds_lin.mp hrange.1).2
  have h2 := (holds_lin.mp hrange.2.1).2
  simp only [Linear.Fact.Holds, Linear.Form.eval_scale] at h1 h2
  generalize hv : (fun t => (termAt s.afterEnv s.after.h t).getD 0) = v at *
  have hsub : (∀ t ∈ F.map (·.1), t ∈ fl.map (·.1) ∨ t ∈ fr.map (·.1)) ∧
      ((op = .add ∧ Linear.Form.eval v F + c = (Linear.Form.eval v fl + cl) + (Linear.Form.eval v fr + cr)) ∨
       (op = .sub ∧ Linear.Form.eval v F + c = (Linear.Form.eval v fl + cl) - (Linear.Form.eval v fr + cr)) ∨
       (op = .mul ∧ Linear.Form.eval v F + c = (Linear.Form.eval v fl + cl) * (Linear.Form.eval v fr + cr))) := by
    unfold resultForm at hF
    split at hF
    · simp only [Option.some.injEq, Prod.mk.injEq] at hF; obtain ⟨rfl, rfl⟩ := hF
      refine ⟨fun t ht => by simpa [List.map_append] using ht, .inl ⟨rfl, ?_⟩⟩
      rw [Linear.Form.eval_append]; omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at hF; obtain ⟨rfl, rfl⟩ := hF
      refine ⟨fun t ht => by simpa [List.map_append, scale_vars] using ht, .inr (.inl ⟨rfl, ?_⟩)⟩
      rw [Linear.Form.eval_append, Linear.Form.eval_scale]; omega
    · split at hF
      · rename_i h0; subst h0
        simp only [Option.some.injEq, Prod.mk.injEq] at hF; obtain ⟨rfl, rfl⟩ := hF
        split
        · rename_i hc; subst hc
          exact ⟨fun t ht => by simp at ht, .inr (.inr ⟨rfl, by simp [Linear.Form.eval]⟩)⟩
        · refine ⟨fun t ht => .inr (by rwa [scale_vars] at ht), .inr (.inr ⟨rfl, ?_⟩)⟩
          rw [Linear.Form.eval_scale]; simp only [Linear.Form.eval, Int.zero_add, Int.mul_add]
      · split at hF
        · rename_i _ h0; subst h0
          simp only [Option.some.injEq, Prod.mk.injEq] at hF; obtain ⟨rfl, rfl⟩ := hF
          split
          · rename_i hc; subst hc
            exact ⟨fun t ht => by simp at ht, .inr (.inr ⟨rfl, by simp [Linear.Form.eval]⟩)⟩
          · refine ⟨fun t ht => .inl (by rwa [scale_vars] at ht), .inr (.inr ⟨rfl, ?_⟩)⟩
            rw [Linear.Form.eval_scale]; simp only [Linear.Form.eval, Int.zero_add, Int.add_mul, Int.mul_comm cr]
        · cases hF
    · cases hF
  obtain ⟨hvars, hcase⟩ := hsub
  have hres : ∃ q, SafeIntegers.SafeInt (arithBits op a b) q ∧ q = Linear.Form.eval v F + c := by
    rcases hcase with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩
    · exact ⟨_, SafeIntegers.add_safe has hbs (by omega), he.symm⟩
    · exact ⟨_, SafeIntegers.sub_safe has hbs (by omega), he.symm⟩
    · exact ⟨_, SafeIntegers.mul_safe has hbs (by rw [← he]; omega), he.symm⟩
  obtain ⟨q, hq, rfl⟩ := hres
  have hop' : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .shr ∨ op = .bitAnd := by
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hyv := result_term (binop_operands hop' hav hbv hop) hq
  subst hv
  exact valueFacts_of (fun t ht => (hvars t ht).elim (hld t) (hrd t)) hyv

/-- **The sum at the `2^53` boundary**: two nonnegative safe integers whose
sum is at most `2^53` add exactly, or to the double `2^53`
(`SafeIntegers.add_safe`, `add_two53`). -/
theorem add_boundary {a b : UInt64} {i j : Int} (ha : SafeIntegers.SafeInt a i) (hb : SafeIntegers.SafeInt b j)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hs : i + j ≤ 2 ^ 53) :
    SafeIntegers.SafeInt (arithBits .add a b) (i + j) ∨ arithBits .add a b = SafeIntegers.pastSafeBits := by
  by_cases hlt : (i + j).natAbs < 2 ^ 53
  · exact .inl (SafeIntegers.add_safe ha hb hlt)
  · exact .inr (SafeIntegers.add_two53 ha hb (by omega))

theorem lengthSuccessor_sound {arena : AssertionArena} (hv : arena.Valid) {s : TwoState}
    {g pg e e₀ e' e₁ e₂ : AssertionRef} {l r : Operand} {y sp : Path} {lengthLeft : Bool} {x : Path}
    {fl fr : Linear.Form Term} {cl cr : Int} {one : Formula}
    (hl : l.form = some (fl, cl)) (hr : r.form = some (fr, cr))
    (hx : (if lengthLeft then l else r) = .var x) (hone : oneFacts (if lengthLeft then r else l) = some one)
    (hg : arena.nodes[g.index]? = some (.guarded pg e)) (hpg : arena.nodes[pg.index]? = some (.atom (.pastSafe y)))
    (he : arena.nodes[e.index]? = some (.and e₀ e')) (he₀ : arena.nodes[e₀.index]? = some (.atom (.safeInt y)))
    (he' : arena.nodes[e'.index]? = some (.and e₁ e₂))
    (he₁ : arena.nodes[e₁.index]? = some (.atom (.linear (exactTermFacts y (fl ++ fr) (cl + cr)).1)))
    (he₂ : arena.nodes[e₂.index]? = some (.atom (.linear (exactTermFacts y (fl ++ fr) (cl + cr)).2)))
    (hop : (OperationPost.arith .add l.witness r.witness y).Holds s)
    (hpl : Holds arena s l.premise) (hpr : Holds arena s r.premise)
    (hlen : Holds arena s (lengthEq x sp)) (hon : Holds arena s one) :
    Holds arena s (.at .after g) := by
  obtain ⟨hld, a, hav, has⟩ := Operand.sound hl hpl
  obtain ⟨hrd, b, hbv, hbs⟩ := Operand.sound hr hpr
  have hy := binop_operands (by simp) hav hbv hop
  -- the length operand is in [0, 2^53 − 1], the other one is 1
  simp only [lengthEq, conj, Holds] at hlen
  have hl1 := holds_lin.mp hlen.1
  have hl2 := holds_lin.mp hlen.2.1
  obtain ⟨n, hn⟩ := factAt_defined hl1 (x := sp.term .strLength) (by simp [Linear.Fact.vars])
  obtain ⟨xi, hxi⟩ := factAt_defined hl1 (x := vt x) (by simp [Linear.Fact.vars])
  have hn' := hn
  simp only [termAt, Path.term, Term.now_kind, Option.bind_eq_some_iff] at hn'
  obtain ⟨w, -, hw⟩ := hn'
  have hnr := strLengthOf_range (v := w) hw
  have q1 := hl1.2
  have q2 := hl2.2
  simp only [Linear.Fact.Holds, Linear.Form.eval, hn, hxi, Option.getD_some] at q1 q2
  generalize hv' : (fun t => (termAt s.afterEnv s.after.h t).getD 0) = v at *
  have hsum : 0 ≤ Linear.Form.eval v fl + cl ∧ 0 ≤ Linear.Form.eval v fr + cr ∧
      (Linear.Form.eval v fl + cl) + (Linear.Form.eval v fr + cr) ≤ 2 ^ 53 := by
    have hxv : ∀ {o : Operand} {f c}, o = .var x → o.form = some (f, c) → Linear.Form.eval v f + c = xi := by
      intro o f c ho hf
      subst ho
      simp only [Operand.form, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      subst hv'; simp [Linear.Form.eval, hxi]
    have h1 : ∀ {o : Operand} {f c}, oneFacts o = some one → o.form = some (f, c) → Holds arena s one →
        Linear.Form.eval v f + c = 1 := by
      intro o f c ho hf hh
      cases o with
      | literal bb =>
        simp only [oneFacts] at ho
        split at ho
        · rename_i h1
          simp only [Operand.form, h1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf; simp [Linear.Form.eval]
        · cases ho
      | var p =>
        simp only [oneFacts, Option.some.injEq] at ho
        subst ho
        simp only [Operand.form, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        simp only [conj, Holds] at hh
        have k1 := holds_lin.mp hh.1
        have k2 := holds_lin.mp hh.2.1
        obtain ⟨pi, hpi⟩ := factAt_defined k1 (x := vt p) (by simp [Linear.Fact.vars])
        have z1 := k1.2
        have z2 := k2.2
        simp only [Linear.Fact.Holds, Linear.Form.eval, hpi, Option.getD_some] at z1 z2
        subst hv'; simp only [Linear.Form.eval, hpi, Option.getD_some]; omega
      | const _ _ => simp [oneFacts] at ho
    cases lengthLeft
    · simp only [Bool.false_eq_true, if_false] at hx hone
      have := hxv hx hr
      have := h1 hone hl hon
      omega
    · simp only [if_true] at hx hone
      have := hxv hx hl
      have := h1 hone hr hon
      omega
  change Sat arena s.afterEnv s.mark s.after g
  rw [sat_guarded hv hg]
  rcases add_boundary has hbs hsum.1 hsum.2.1 hsum.2.2 with hq | hq
  · right
    have hyv := result_term hy hq
    have hdef : ∀ t ∈ (fl ++ fr).map (·.1), (termAt s.afterEnv s.after.h t).isSome := by
      intro t ht
      rcases List.mem_append.mp (by simpa only [List.map_append] using ht) with ht | ht
      · exact hld t ht
      · exact hrd t ht
    have hfacts : Holds arena s (valueFacts y (fl ++ fr) (cl + cr)) := by
      subst hv'
      refine valueFacts_of hdef ?_
      rw [hyv, Linear.Form.eval_append]; congr 1; omega
    simp only [valueFacts, conj, Holds] at hfacts
    obtain ⟨hs0, hs1, hs2, -⟩ := hfacts
    refine (sat_and hv he).mpr ⟨(sat_atom he₀).mpr ?_, (sat_and hv he').mpr
      ⟨(sat_atom he₁).mpr (holds_lin.mp hs1), (sat_atom he₂).mpr (holds_lin.mp hs2)⟩⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (show (termAt s.afterEnv s.after.h (vt y)).isSome from hs0)
    rw [Path.termAt_term] at hz
    obtain ⟨u, hu, hzu⟩ := Option.bind_eq_some_iff.mp hz
    exact ⟨u, hu, by rw [show kindValue _ .value u = intValue u from rfl] at hzu; rw [hzu]; rfl⟩
  · left
    rw [hq] at hy
    exact (sat_atom hpg).mpr hy

end Arithmetic

/-! ## The common consequence theorem -/

/-- The atom `y ≤ |x|` is the index fact of (Grow) (`TolerantFrames.LowerBound`). -/
theorem lowerFact_iff (ε : EntryState) (η : Env) (h : Heap) (y x : Nat) :
    (Atom.linear (lowerFact y x)).Holds η h ↔ (lowerBoundFact y x).HoldsAt ε η h := by
  simp only [Atom.Holds, lowerBoundFact, lowerFact, IndexFact.HoldsAt, FactAt]
  have hv : ∀ t ∈ (Linear.Fact.le [(Term.value y, 1), (Term.length x, -1)] 0).vars,
      termValue ε η h t = termAt η h t := by
    intro t ht
    simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> rfl
  constructor
  · rintro ⟨hd, hh⟩
    refine ⟨fun t ht => by rw [hv t ht]; exact hd t ht, ?_⟩
    refine (Linear.Fact.holds_congr fun t ht => ?_).mp hh
    simp only [termValuation, hv t ht]
  · rintro ⟨hd, hh⟩
    refine ⟨fun t ht => by rw [← hv t ht]; exact hd t ht, ?_⟩
    refine (Linear.Fact.holds_congr fun t ht => ?_).mp hh
    simp only [termValuation, hv t ht]

/-- The atom `dense(x, k)` is `DenseAt x k` at the value `k` holds. -/
theorem dense_iff {η : Env} {h : Heap} {x k : Nat} :
    (Atom.dense (Path.var x) (Term.value k)).Holds η h ↔
      ∃ n : Int, intValue (η k) = some n ∧ 0 ≤ n ∧ Dense x n.toNat η h := by
  simp only [Atom.Holds]
  constructor
  · rintro ⟨w, st, ls, n, hw, hs, hl, hn, h0, hd⟩
    simp only [Path.read, Path.var, readPath, Option.some.injEq] at hw
    subst hw
    exact ⟨n, hn, h0, st, ls, hs, hl, hd⟩
  · rintro ⟨n, hn, h0, st, ls, hs, hl, hd⟩
    exact ⟨η x, st, ls, n, rfl, hs, hl, hn, h0, hd⟩

theorem stepValue_shiftVar (s : TwoState) (p : Phase) (x : Val) (v : StepVar) :
    stepValue (s.withEnv p (push x (s.env p))) (shiftVar p v) = stepValue s v := by
  cases p <;> cases v <;> rfl

theorem OperationPost.holds_shift (s : TwoState) (x : Val) (q : OperationPost) :
    q.shift.Holds (s.withEnv .after (push x (s.env .after))) ↔ q.Holds s := by
  cases q <;> simp only [OperationPost.shift, OperationPost.Holds, TwoState.withEnv, TwoState.env,
    Witness.value_shift] <;> rfl

/-- **A formula read one slot further holds where the formula holds at the
valuation without the eigenvariable.** -/
theorem holds_shiftFormula {arena : AssertionArena} {p : Phase} {n : Nat} {s : TwoState} {x : Val} :
    ∀ {F F' : Formula}, shiftFormula arena.nodes p n F F' = true →
      (Holds arena (s.withEnv p (push x (s.env p))) F' ↔ Holds arena s F)
  | .at q a, .at q' a', h => by
    simp only [shiftFormula, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    show Sat arena _ _ _ a' ↔ Sat arena _ _ _ a
    by_cases hq : q = p
    · subst hq
      simp only [if_true] at h
      simpa only [TwoState.env_withEnv, TwoState.state_withEnv, TwoState.mark_withEnv] using sat_shift h x
    · simp only [hq, if_false, beq_iff_eq] at h
      subst h
      have : (s.withEnv p (push x (s.env p))).env q = s.env q := by cases p <;> cases q <;> simp_all [TwoState.withEnv, TwoState.env]
      rw [this, TwoState.state_withEnv, TwoState.mark_withEnv]
  | .linear F, .linear F', h => by
    simp only [shiftFormula, beq_iff_eq] at h
    subst h
    simp only [Holds, factAt_rename]
    exact Iff.of_eq (congrArg (FactAt · F) (funext fun v => stepValue_shiftVar s p x v))
  | .defined v, .defined v', h => by
    simp only [shiftFormula, beq_iff_eq] at h
    subst h
    simp only [Holds, stepValue_shiftVar]
  | .transition Φ, .transition Φ', h => by
    simp only [shiftFormula] at h
    cases p
    · simp only [if_true, beq_iff_eq] at h
      subst h
      exact EffectAction.rename_iff _
    · simp only [beq_iff_eq, reduceCtorEq, if_false] at h
      subst h; exact Iff.rfl
  | .operation q, .operation q', h => by
    simp only [shiftFormula] at h
    cases p
    · simp only [reduceCtorEq, if_false, beq_iff_eq] at h
      subst h; exact Iff.rfl
    · simp only [if_true, beq_iff_eq] at h
      subst h; exact OperationPost.holds_shift s x q
  | .transport θ, .transport θ', h => by
    simp only [shiftFormula, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    show (Substitution.Holds _ _ _ _) ↔ _
    constructor
    · intro hθ i w hi
      have := hθ i w.shift (by simp [hi])
      exact (Witness.value_shift w x s.afterEnv s.after.h).symm.trans this
    · intro hθ i w hi
      simp only [Array.getElem?_map, Option.map_eq_some_iff] at hi
      obtain ⟨w0, hw0, rfl⟩ := hi
      show w0.shift.value (push x s.afterEnv) s.after.h = some (s.beforeEnv i)
      rw [Witness.value_shift]; exact hθ i w0 hw0
  | .and F G, .and F' G', h => by
    simp only [shiftFormula, Bool.and_eq_true] at h
    exact and_congr (holds_shiftFormula h.1) (holds_shiftFormula h.2)
  | .truth, .truth, _ => Iff.rfl
  | .falsity, .falsity, _ => Iff.rfl
  | .at _ _, .transition _, h | .at _ _, .operation _, h | .at _ _, .linear _, h | .at _ _, .defined _, h
  | .at _ _, .transport _, h | .at _ _, .and _ _, h | .at _ _, .truth, h | .at _ _, .falsity, h => by
    simp [shiftFormula] at h
  | .transition _, .at _ _, h | .transition _, .operation _, h | .transition _, .linear _, h
  | .transition _, .defined _, h | .transition _, .transport _, h | .transition _, .and _ _, h
  | .transition _, .truth, h | .transition _, .falsity, h => by simp [shiftFormula] at h
  | .operation _, .at _ _, h | .operation _, .transition _, h | .operation _, .linear _, h
  | .operation _, .defined _, h | .operation _, .transport _, h | .operation _, .and _ _, h
  | .operation _, .truth, h | .operation _, .falsity, h => by simp [shiftFormula] at h
  | .linear _, .at _ _, h | .linear _, .transition _, h | .linear _, .operation _, h
  | .linear _, .defined _, h | .linear _, .transport _, h | .linear _, .and _ _, h
  | .linear _, .truth, h | .linear _, .falsity, h => by simp [shiftFormula] at h
  | .defined _, .at _ _, h | .defined _, .transition _, h | .defined _, .operation _, h
  | .defined _, .linear _, h | .defined _, .transport _, h | .defined _, .and _ _, h
  | .defined _, .truth, h | .defined _, .falsity, h => by simp [shiftFormula] at h
  | .transport _, .at _ _, h | .transport _, .transition _, h | .transport _, .operation _, h
  | .transport _, .linear _, h | .transport _, .defined _, h | .transport _, .and _ _, h
  | .transport _, .truth, h | .transport _, .falsity, h => by simp [shiftFormula] at h
  | .and _ _, .at _ _, h | .and _ _, .transition _, h | .and _ _, .operation _, h
  | .and _ _, .linear _, h | .and _ _, .defined _, h | .and _ _, .transport _, h
  | .and _ _, .truth, h | .and _ _, .falsity, h => by simp [shiftFormula] at h
  | .truth, .at _ _, h | .truth, .transition _, h | .truth, .operation _, h | .truth, .linear _, h
  | .truth, .defined _, h | .truth, .transport _, h | .truth, .and _ _, h | .truth, .falsity, h => by
    simp [shiftFormula] at h
  | .falsity, .at _ _, h | .falsity, .transition _, h | .falsity, .operation _, h | .falsity, .linear _, h
  | .falsity, .defined _, h | .falsity, .transport _, h | .falsity, .and _ _, h | .falsity, .truth, h => by
    simp [shiftFormula] at h

/-- **The common consequence theorem** (I4, `Derivation.sound`): a checked
derivation's conclusion holds at every two-state where its premises hold. -/
theorem Derivation.sound {arena : AssertionArena} (hv : arena.Valid) {Γ : List Formula} {F : Formula}
    (d : Derivation arena Γ F) : ∀ s, (∀ p ∈ Γ, Holds arena s p) → Holds arena s F := by
  induction d with
  | assumption h => exact fun s hΓ => hΓ _ h
  | truth => exact fun _ _ => trivial
  | falseElim _ ih => exact fun s hΓ => (ih s hΓ).elim
  | andIntro _ _ ih₁ ih₂ => exact fun s hΓ => ⟨ih₁ s hΓ, ih₂ s hΓ⟩
  | andLeft _ ih => exact fun s hΓ => (ih s hΓ).1
  | andRight _ ih => exact fun s hΓ => (ih s hΓ).2
  | cut _ _ ih₁ ih₂ =>
    intro s hΓ
    exact ih₂ s fun q hq => (List.mem_cons.mp hq).elim (fun e => e ▸ ih₁ s hΓ) (hΓ q)
  | atTruth hn => exact fun _ _ => sat_truth hn
  | atFalse hn _ ih => exact fun s hΓ => (sat_falsity hn (ih s hΓ)).elim
  | atAndIntro hn _ _ ih₁ ih₂ => exact fun s hΓ => (sat_and hv hn).mpr ⟨ih₁ s hΓ, ih₂ s hΓ⟩
  | atAndLeft hn _ ih => exact fun s hΓ => ((sat_and hv hn).mp (ih s hΓ)).1
  | atAndRight hn _ ih => exact fun s hΓ => ((sat_and hv hn).mp (ih s hΓ)).2
  | guardLeft hn _ ih => exact fun s hΓ => (sat_guarded hv hn).mpr (.inl (ih s hΓ))
  | guardRight hn _ ih => exact fun s hΓ => (sat_guarded hv hn).mpr (.inr (ih s hΓ))
  | guardCases hn _ _ _ ih ihg ihb =>
    intro s hΓ
    rcases (sat_guarded hv hn).mp (ih s hΓ) with h | h
    · exact ihg s fun q hq => (List.mem_cons.mp hq).elim (fun e => e ▸ h) (hΓ q)
    · exact ihb s fun q hq => (List.mem_cons.mp hq).elim (fun e => e ▸ h) (hΓ q)
  | existsIntro w n hn hc he _ _ ihe ihc =>
    intro s hΓ
    obtain ⟨v, hw, hw'⟩ := (sat_atom he).mp (ihe s hΓ)
    exact (sat_exists hv hn).mpr ⟨v, (sat_instantiate hc (w := .path w) hw).mp (ihc s hΓ)⟩
  | existsIntroLiteral ℓ n hn hc _ ihc =>
    intro s hΓ
    exact (sat_exists hv hn).mpr ⟨ℓ, (sat_instantiate hc (w := .literal ℓ) rfl).mp (ihc s hΓ)⟩
  | @existsElim Γ Γ' p a b G G' n hn hΓ' hG _ _ ih ihe =>
    intro s hΓ
    obtain ⟨v, hb⟩ := (sat_exists hv hn).mp (ih s hΓ)
    have hb' : Holds arena (s.withEnv p (push v (s.env p))) (.at p b) := by
      show Sat arena _ _ _ b
      simpa only [TwoState.env_withEnv, TwoState.state_withEnv, TwoState.mark_withEnv] using hb
    refine (holds_shiftFormula (x := v) hG).mp (ihe (s.withEnv p (push v (s.env p))) fun q hq => ?_)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hb'
    · obtain ⟨F, hF, hsh⟩ := List.any_eq_true.mp (List.all_eq_true.mp hΓ' q hq)
      exact (holds_shiftFormula (x := v) hsh).mpr (hΓ F hF)
  | equalitySubst w w' n h₁ h₂ he _ _ ihe ih =>
    intro s hΓ
    obtain ⟨v, hw, hw'⟩ := (sat_atom he).mp (ihe s hΓ)
    exact (sat_instantiate h₂ (w := .path w') hw').mpr ((sat_instantiate h₁ (w := .path w) hw).mp (ih s hΓ))
  | oldLift hΓ' hF _ ih =>
    intro s hΓ
    refine (holds_swap hF).mp (ih s.swap fun q hq => ?_)
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hq
    exact (holds_swap (List.all_eq_true.mp hΓ' G hG)).mpr (hΓ G hG)
  | boxElim hn _ ih => exact fun s hΓ => (sat_box hv hn).mp (ih s hΓ) _ (EffectAction.refl _ _ _)
  | boxAndIntro hn hc hl hr _ _ ihl ihr =>
    intro s hΓ
    exact (sat_box hv hn).mpr fun s' ha =>
      (sat_and hv hc).mpr ⟨(sat_box hv hl).mp (ihl s hΓ) s' ha, (sat_box hv hr).mp (ihr s hΓ) s' ha⟩
  | boxAndLeft hn hc hl _ ih =>
    intro s hΓ
    exact (sat_box hv hl).mpr fun s' ha => ((sat_and hv hc).mp ((sat_box hv hn).mp (ih s hΓ) s' ha)).1
  | boxAndRight hn hc hr _ ih =>
    intro s hΓ
    exact (sat_box hv hr).mpr fun s' ha => ((sat_and hv hc).mp ((sat_box hv hn).mp (ih s hΓ) s' ha)).2
  | @boxMono Γ p a b x y Φ ha hb _ _ ihe ih =>
    intro s hΓ
    refine (sat_box hv hb).mpr fun s' act => ?_
    have hx := (sat_box hv ha).mp (ih s hΓ) s' act
    exact ihe ⟨s.env p, s.env p, s.mark, s', s'⟩ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hx
  | boxAnti ev hev ha hb _ _ ihK ih =>
    intro s hΓ
    exact (sat_box hv hb).mpr fun s' act =>
      (sat_box hv ha).mp (ih s hΓ) s' (ev.sound hev _ _ _ _ (ihK s hΓ) act)
  | boxGuard ha hbx hb hc _ ih =>
    intro s hΓ
    refine (sat_box hv hb).mpr fun s' act => (sat_guarded hv hc).mpr ?_
    rcases (sat_guarded hv ha).mp (ih s hΓ) with hg | hx
    · exact .inl (guard_invariant hv ha _ _ _ _ act.admissible hg)
    · exact .inr ((sat_box hv hbx).mp hx s' act)
  | boxIdem ev hev ha hb _ _ ihD ih =>
    intro s hΓ
    exact (sat_box hv hb).mpr fun s₁ a₁ => (sat_box hv ha).mpr fun s₂ a₂ =>
      (sat_box hv ha).mp (ih s hΓ) s₂ (ev.sound hev _ _ _ _ _ (ihD s hΓ) a₁ a₂).2
  | @tolerantFrame Γ p K A b g Φ S sev rev cev hs hr hc hb _ _ _ ihe ihK ihA =>
    intro s hΓ
    have hthrough : ContextThroughout arena K Φ (cev.ctx arena) := by
      intro η m anchor s₁ s₂ hK a₁ a₂
      have hg : Sat arena η m anchor g := ihe ⟨η, η, m, anchor, anchor⟩ fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hK
      exact cev.sound hc η m anchor s₁ s₂ hg a₁ a₂
    exact (sat_box hv hb).mpr fun s' act =>
      tolerant_frame (sev.sound hs) hthrough (rev.sound hr) _ _ _ (ihK s hΓ) (ihA s hΓ) s' act
  | @everyEmpty Γ p a d π n z body ha hd _ _ ihd ihn =>
    intro s hΓ
    obtain ⟨w, st, ls, k, hw, hst, hls, -, -, -⟩ := (sat_atom hd).mp (ihd s hΓ)
    have hn := (factAt_tag s p _).mp (ihn s hΓ)
    obtain ⟨nv, hnv⟩ := factAt_defined hn (x := n) (by simp [Linear.Fact.vars])
    have e1 := hn.2
    simp only [Linear.Fact.Holds, Linear.Form.eval, hnv, Option.getD_some] at e1
    exact (sat_atom ha).mpr ⟨w, st, ls, nv, hw, hst, hls, hnv, fun i hi => by omega⟩
  | @everyElim Γ p a π n k body G ha hG _ _ _ ih ihk ihlt =>
    intro s hΓ
    obtain ⟨w, st, ls, nv, hw, hst, hls, hnv, hall⟩ := (sat_atom ha).mp (ih s hΓ)
    have hk := (factAt_tag s p _).mp (ihk s hΓ)
    have hlt := (factAt_tag s p _).mp (ihlt s hΓ)
    obtain ⟨kv, hkv⟩ := factAt_defined hk (x := k) (by simp [Linear.Fact.vars])
    have e1 := hk.2
    have e2 := hlt.2
    simp only [Linear.Fact.Holds, Linear.Form.eval, hkv, hnv, Option.getD_some] at e1 e2
    have hi : ((kv.toNat : Nat) : Int) < nv := by omega
    obtain ⟨C, hC, hCG⟩ := List.mem_filterMap.mp hG
    cases C with
    | either _ _ => cases hCG
    | atom F =>
      have hF : F.mapVars (boundAt k) = some G := hCG
      have hFh := (hall kv.toNat hi).2 (.atom F) hC
      refine (factAt_tag s p G).mpr ((factAt_mapVars hF fun x _ y hy => ?_).mpr hFh)
      cases x with
      | index =>
        cases hy; rw [hkv]; simp only [scalarValue]; congr 1; omega
      | free t => cases hy; rfl
      | _ => cases hy
  | @grow Γ p a b y x ha hb _ ih =>
    intro s hΓ
    refine (sat_box hv hb).mpr fun s' act => ?_
    have h0 := (lowerFact_iff ⟨s.env p, (s.state p).h⟩ _ _ y x).mp ((sat_atom ha).mp (ih s hΓ))
    exact (sat_atom ha).mpr ((lowerFact_iff ⟨s.env p, (s.state p).h⟩ _ _ y x).mpr
      (TolerantFrames.grow (m := s.mark) h0 s' act))
  | dense x k ha hb _ ih =>
    intro s hΓ
    refine (sat_box hv hb).mpr fun s' act => ?_
    obtain ⟨n, hn, h0, hd⟩ := dense_iff.mp ((sat_atom ha).mp (ih s hΓ))
    exact (sat_atom ha).mpr (dense_iff.mpr ⟨n, hn, h0, TolerantFrames.dense (m := s.mark) hd s' act⟩)
  | frame θ ha hc _ _ _ ih iht ihθ =>
    intro s hΓ
    have hb := (sat_box hv ha).mp (ih s hΓ) s.after (iht s hΓ)
    exact (sat_subst hc (ihθ s hΓ)).mpr hb
  | framePlus ev hev θ ha hc _ _ _ _ ihD ih iht ihθ =>
    intro s hΓ
    have ha' : Sat arena s.beforeEnv s.mark s.after _ := (sat_box hv ha).mpr fun s₂ a₂ =>
      (sat_box hv ha).mp (ih s hΓ) s₂ (ev.sound hev _ _ _ _ _ (ihD s hΓ) (iht s hΓ) a₂).2
    exact (sat_subst hc (ihθ s hΓ)).mpr ha'
  | @linear Γ G Fs defs steps hc _ _ ih ihd =>
    intro s hΓ
    have hFs := holds_conj.mp (ih s hΓ)
    have hds := holds_conj.mp (ihd s hΓ)
    have hall : ∀ F ∈ Fs, FactAt (stepValue s) F := fun F hF => hFs (.linear F) (List.mem_map_of_mem hF)
    simp only [linearCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
      Bool.or_eq_true] at hc
    obtain ⟨hcheck, hdef⟩ := hc
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases hdef x hx with hx' | ⟨F, hF, hxF⟩
      · exact hds (.defined x) (List.mem_map_of_mem hx')
      · exact (hall F hF).1 x hxF
    · split at hcheck
      · rename_i out hout
        exact Linear.check_sound (fun F hF => (hall F hF).2) hout G (List.contains_iff_mem.mp hcheck)
      · cases hcheck
  | definedOfLinear hv _ ih => exact fun s hΓ => (ih s hΓ).1 _ hv
  | @definedToAtom Γ p a t ha _ ih =>
    intro s hΓ
    have := ih s hΓ
    simp only [Holds, stepValue_tag] at this
    exact (sat_atom ha).mpr this
  | @atomToDefined Γ p a t ha _ ih =>
    intro s hΓ
    show (stepValue s (tagVar p t)).isSome
    rw [stepValue_tag]; exact (sat_atom ha).mp (ih s hΓ)
  | @safeIntToDefined Γ p a π ha _ ih =>
    intro s hΓ
    obtain ⟨v, hv', hi⟩ := (sat_atom ha).mp (ih s hΓ)
    show (stepValue s (tagVar p (π.term .value))).isSome
    rw [stepValue_tag, Path.termAt_term, hv']; exact hi
  | @definedToSafeInt Γ p a π ha _ ih =>
    intro s hΓ
    have := ih s hΓ
    simp only [Holds, stepValue_tag, Path.termAt_term] at this
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp this
    obtain ⟨v, hv', hi⟩ := Option.bind_eq_some_iff.mp hn
    exact (sat_atom ha).mpr ⟨v, hv', by rw [show kindValue _ .value v = intValue v from rfl] at hi; rw [hi]; rfl⟩
  | atomToLinear F ha _ ih => exact fun s hΓ => (factAt_tag s _ F).mpr ((sat_atom ha).mp (ih s hΓ))
  | linearToAtom F ha _ ih => exact fun s hΓ => (sat_atom ha).mpr ((factAt_tag s _ F).mp (ih s hΓ))
  | atomClash π v R hv' he hc _ _ ihe ihc =>
    intro s hΓ
    obtain ⟨u, hu, hv₁⟩ := (sat_atom he).mp (ihe s hΓ)
    obtain ⟨u', hu', hR⟩ := (sat_atom hc).mp (ihc s hΓ)
    simp only [Witness.value, Option.some.injEq] at hv₁
    rw [hu] at hu'; cases hu'; subst hv₁
    rw [hv'] at hR; cases hR
  | shiftRight x k y F c d hx hk hd _ _ _ _ ihop ihx ihk ihs =>
    exact fun s hΓ => shiftRight_sound hx hk hd (ihop s hΓ) (ihx s hΓ) (ihk s hΓ) (ihs s hΓ)
  | mask x k y F c m hx hk hm _ _ _ _ ihop ihx ihk ihs =>
    exact fun s hΓ => mask_sound hx hk hm (ihop s hΓ) (ihx s hΓ) (ihk s hΓ) (ihs s hΓ)
  | integerOperation op l r y fl cl fr cr F c hl hr hF _ _ _ _ ihop ihl ihr ihrange =>
    exact fun s hΓ => integerOperation_sound hl hr hF (ihop s hΓ) (ihl s hΓ) (ihr s hΓ) (ihrange s hΓ)
  | lengthSuccessor l r y sp lengthLeft x fl cl fr cr one hl hr hx hone hg hpg he he₀ he' he₁ he₂
      _ _ _ _ _ ihop ihl ihr ihlen ihone =>
    exact fun s hΓ => lengthSuccessor_sound hv hl hr hx hone hg hpg he he₀ he' he₁ he₂ (ihop s hΓ) (ihl s hΓ)
      (ihr s hΓ) (ihlen s hΓ) (ihone s hΓ)
  | @stringLength Γ p a t ht ha _ ih =>
    intro s hΓ
    have hd := (sat_atom ha).mp (ih s hΓ)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hd
    have hn' := hn
    simp only [termAt, ht, Option.bind_eq_some_iff] at hn'
    obtain ⟨w, -, hw⟩ := hn'
    have hr := strLengthOf_range (v := w) hw
    have hv' : stepValue s (tagVar p t) = some n := by rw [stepValue_tag]; exact hn
    simp only [strRange, conj, Holds]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, trivial⟩
    all_goals first
      | (simp [Linear.Fact.vars, hv']; done)
      | (simp only [Linear.Fact.Holds, Linear.Form.eval, hv', Option.getD_some]; omega)
  | stringLengthRead x y _ ih =>
    intro s hΓ
    obtain ⟨str, hx, hmax, hy⟩ := ih s hΓ
    have hyv : stepValue s (av y) = some ((utf16Units str).length : Int) := by
      rw [av_eq, hy]; exact intValue_num (safeInt_nat hmax)
    have hxv : stepValue s (alen x) = some ((utf16Units str).length : Int) := by
      rw [alen_eq, hx]; simp [strLengthOf, hmax]
    simp only [lengthReadFacts, conj, Holds]
    refine ⟨(show (stepValue s (av y)).isSome by rw [hyv]; rfl), ⟨?_, ?_⟩, ⟨?_, ?_⟩, trivial⟩
    all_goals first
      | (simp [Linear.Fact.vars, hxv, hyv]; done)
      | (simp only [Linear.Fact.Holds, Linear.Form.eval, hxv, hyv, Option.getD_some]; omega)
  | stringRead x i y _ _ ihop ihi =>
    intro s hΓ
    obtain ⟨str, b, hx, hi, hy⟩ := ihop s hΓ
    have hfacts := ihi s hΓ
    simp only [stringIndexFacts, conj, Holds] at hfacts
    obtain ⟨h1, h2, h3, -⟩ := hfacts
    obtain ⟨k, hk⟩ := factAt_defined h1 (x := av i) (by simp [Linear.Fact.vars])
    obtain ⟨n, hn⟩ := factAt_defined h2 (x := alen x) (by simp [Linear.Fact.vars])
    obtain ⟨b', hb', hks⟩ := av_some hk
    simp only [Witness.value] at hi
    rw [hi] at hb'; cases hb'
    obtain ⟨str', hx', hmax, rfl⟩ := alen_some hn
    rw [hx] at hx'; cases hx'
    have e1 := h1.2
    have e2 := h2.2
    have e3 := h3.2
    simp only [Linear.Fact.Holds, Linear.Form.eval, hk, hn, Option.getD_some] at e1 e2 e3
    have hidx : indexOfBits b = some k.toNat := indexOfBits_safe hks (by omega) (by simp [maxArrayLength]; omega)
    have hlt : k.toNat < (utf16Units str).length := by omega
    obtain ⟨u, hu⟩ : ∃ u, (utf16Units str)[k.toNat]? = some u := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hcu : codeUnitAt str b = .str (unitString u) := by simp [codeUnitAt, hidx, hu]
    have hlen := unitString_length u (utf16Units_lt str u (List.mem_of_getElem? hu))
    have hyv : stepValue s (alen y) = some 1 := by
      rw [alen_eq, hy, hcu]; simp [strLengthOf, hlen, maxStringLength]
    simp only [unitFacts, conj, Holds]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, trivial⟩
    all_goals first
      | (simp [Linear.Fact.vars, hyv]; done)
      | (simp only [Linear.Fact.Holds, Linear.Form.eval, hyv, Option.getD_some]; omega)
  | stringConcat x z y _ _ _ ihop ihx ihz =>
    intro s hΓ
    obtain ⟨nx, hnx⟩ := factAt_defined (ihx s hΓ) (x := alen x) (by simp [Linear.Fact.vars])
    obtain ⟨nz, hnz⟩ := factAt_defined (ihz s hΓ) (x := alen z) (by simp [Linear.Fact.vars])
    obtain ⟨sx, hx, hmx, rfl⟩ := alen_some hnx
    obtain ⟨sz, hz, hmz, rfl⟩ := alen_some hnz
    obtain ⟨a, b, c, ha, hb, hy, hbin⟩ := ihop s hΓ
    simp only [Witness.value] at ha hb
    rw [hx] at ha; cases ha
    rw [hz] at hb; cases hb
    have hc : concatString sx sz = some c := by
      simp [binop, Arith.relational] at hbin; exact hbin.2
    unfold concatString at hc
    split at hc
    · cases hc
    · rename_i hover
      cases hc
      have hsum : (utf16Units sx).length + (utf16Units sz).length ≤ maxStringLength := by
        simpa [concatOver] using hover
      have hlen : (utf16Units (sx ++ sz)).length = (utf16Units sx).length + (utf16Units sz).length := by
        simp [utf16Units, String.toList_append]
      have hyv : stepValue s (alen y) = some (((utf16Units sx).length + (utf16Units sz).length : Nat) : Int) := by
        rw [alen_eq, hy]; simp [strLengthOf, hlen, hsum]
      simp only [concatFacts, conj, Holds]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, trivial⟩
      all_goals first
        | (simp [Linear.Fact.vars, hnx, hnz, hyv]; done)
        | (simp only [Linear.Fact.Holds, Linear.Form.eval, hnx, hnz, hyv, Option.getD_some]; omega)
/-! ## The validated boundary -/

/-- The runtime slots of the entry and of the exit environment. -/
structure Scope where
  before : Nat
  after : Nat
  deriving DecidableEq, Repr

def Scope.count (sc : Scope) : Phase → Nat
  | .before => sc.before
  | .after => sc.after

/-- A path reading runtime slots below `n`. -/
def Path.scoped (n : Nat) (p : Path) : Bool := decide (p.root < n)

def Witness.scoped (n : Nat) : Witness → Bool
  | .path p => p.scoped n
  | .literal _ => true

def StepVar.scoped (sc : Scope) : StepVar → Bool
  | .before t => !t.atEntry && decide (t.slot < sc.before)
  | .after t => !t.atEntry && decide (t.slot < sc.after)

def OperationPost.scoped (n : Nat) : OperationPost → Bool
  | .arith _ l r y => l.scoped n && r.scoped n && y.scoped n
  | .stringLength x y => x.scoped n && y.scoped n
  | .stringRead x i y => x.scoped n && i.scoped n && y.scoped n

/-- **A formula reads runtime slots within its scope**: assertions by the
identity check (their binders' eigenvariables apart), linear facts by their
terms' slots, a transition by its effect read at the entry, a transport by
an image for every entry slot read at the exit. -/
def Formula.scoped (arena : AssertionArena) (sc : Scope) : Formula → Bool
  | .at p a => scopedAt arena.nodes (sc.count p) a.index
  | .transition Φ => effectScoped sc.before Φ
  | .operation q => q.scoped sc.after
  | .linear F => F.vars.all (StepVar.scoped sc)
  | .defined v => StepVar.scoped sc v
  | .transport θ => decide (θ.images.size = sc.before) && θ.images.toList.all (Witness.scoped sc.after)
  | .and F G => F.scoped arena sc && G.scoped arena sc
  | .truth | .falsity => true

/-- **The validated checker** (I4, the checker's boundary): a derivation
is returned only for a valid arena and premises and goal scoped at the given
runtime slots. -/
def checkScoped (arena : AssertionArena) (sc : Scope) (premises : List Formula) (goal : Formula)
    (raw : RawDerivation) : Except String (Derivation arena premises goal) := do
  let ⟨_⟩ ← req (arena.check = true) "the arena is not valid"
  let ⟨_⟩ ← req ((goal :: premises).all (Formula.scoped arena sc) = true) "a formula reads a slot outside its scope"
  checkDerivation arena premises goal raw

/-- **A checked derivation is semantically valid** (I4, the common
consequence theorem for `checkDerivation`). -/
theorem checkDerivation_sound {arena : AssertionArena} (hv : arena.Valid) {Γ : List Formula} {goal : Formula}
    {raw : RawDerivation} {d : Derivation arena Γ goal} (_ : checkDerivation arena Γ goal raw = .ok d) :
    ∀ s, (∀ p ∈ Γ, Holds arena s p) → Holds arena s goal :=
  d.sound hv

/-- **The checker's acceptance is the semantic conclusion**: what
`checkScoped` returns needs no further premise. -/
theorem checkScoped_sound {arena : AssertionArena} {sc : Scope} {Γ : List Formula} {goal : Formula}
    {raw : RawDerivation} {d : Derivation arena Γ goal} (hc : checkScoped arena sc Γ goal raw = .ok d) :
    ∀ s, (∀ p ∈ Γ, Holds arena s p) → Holds arena s goal := by
  unfold checkScoped req at hc
  by_cases hv : arena.check = true
  · exact d.sound (AssertionArena.check_valid hv)
  · simp [hv, bind, Except.bind] at hc

end Verification.Parity
