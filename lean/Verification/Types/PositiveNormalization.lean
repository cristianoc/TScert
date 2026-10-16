import Verification.Types.CallableConjunctions
import Verification.Types.MethodMembers
import Verification.Programs.RestCalls

/-! Finite positive normalization with nonempty reference conjunctions. Operands
are parameters: normalization never distributes through invariant contracts or
arrow results. Taking operands to be graph-label lists supports recursive graphs.
-/
namespace Verification.PositiveNormalization
open ReferenceConjunctions MethodMembers Tower CallEffects

/-- A tuple contract: required positions, optional positions, and the contract
any further position must hold, if the array may have any. -/
structure Tuple (α : Type) where
  required : List α
  optional : List α
  rest : Option α
  readonly : Bool
  presence : ArrayPresence
  deriving DecidableEq, Repr

/-- The operand a tuple contract states for an index, as `positionFam` states
its family. -/
def Tuple.position (t : Tuple α) (i : Nat) : Option α :=
  match t.required[i]? with
  | some a => some a
  | none => match t.optional[i - t.required.length]? with
    | some a => some a
    | none => if t.required.length + t.optional.length ≤ i then t.rest else none

/-- The families a tuple contract denotes, position by position. -/
def tupleFams {α : Type} (X : α → Fam) (t : Tuple α) : TupleF :=
  ⟨t.required.map X, t.optional.map X, t.rest.map X, t.readonly, t.presence⟩

inductive Clause (α : Type) where
  | nul | bool
  /-- A location under one or more record contracts. An operand is a finite map
  from field names to labels and names only the fields it constrains, so
  operands naming different fields describe different locations of the same
  object rather than one location twice. Optional fields constrain a key
  only where the object has it (`optT`). Methods are host-relative members
  (`methodT`): read from the object and invoked on it. Each key bound says
  which keys the object may own (`ownKeysT`). -/
  | refs (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (views : List (PropKey × α)) (optional : List (OptionalField α) := [])
      (methods : List (MethodMembers.Sig α) := []) (bounds : List KeyBound := [])
  /-- A plain object with invariant named fields, readonly named views,
  index views (`dictViewT`) and writable index contracts (`dictCellT`), each
  over the keys its class admits (`IndexKeys`): every string key, the
  canonical numeric ones, or every symbol key. The index operands apply to
  every present own field under an admitted key, including named ones. A
  writable index is also listed among the views, which is what reads use. A
  first record operand fixes the object shape; it may be empty for a pure
  dictionary. -/
  | dict (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (views : List (PropKey × α)) (indexes : List (IndexKeys × α))
      (optional : List (OptionalField α) := [])
      (methods : List (MethodMembers.Sig α) := []) (bounds : List KeyBound := [])
      (cells : List (IndexKeys × α) := [])
  /-- A callable value meeting every fixed signature, `(receiver, parameters,
  result)`, and every variadic one, `(receiver, fixed parameters, element,
  result)`: the receiver a call may pass, the contract of each actual, and
  the result. They describe the calls a caller may write, not the callee's
  code; a signature indifferent to its receiver has receiver `top`. -/
  | arrs (arrows : List (Arrow α)) (variadic : List (RestArrow α))
  | boolLit (value : Bool)
  /-- Numbers, and one number. The spelling is canonical, so `numLit` singletons
  are distinct exactly when the numbers are. -/
  | num
  | numLit (bits : UInt64)
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | callable (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (arrows : List (Arrow α)) (variadic : List (RestArrow α))
  /-- Semantic top: every value. Membership grants no operation, so nothing
  reads, calls or tests through it without a narrowing fact. `unknown`
  denotes it. Source `void` denotes the union of primitives and objects. -/
  | top
  /-- Every closed JavaScript value, excluding internal stores. -/
  | source
  /-- Strings, and one string; appended last so every earlier case order holds. -/
  | str
  | strLit (value : String)
  /-- An array store under one or more tuple contracts. The array object
  holds the store in its store field; the contracts describe the store. -/
  | list (first : Tuple α) (rest : List (Tuple α))
  /-- Bigints and symbols; appended last so every earlier case order holds. -/
  | bigint
  | symbol
  /-- A class value meeting every construct signature `(parameters, result)`:
  `new` with actuals at the parameters is safe at the result; and every
  variadic one `(parameters, rest, result)`, whose actuals past the parameters
  are, as one pack, at the rest. Its code has `[[Construct]]` only, so no
  callable clause meets it. Its property bag, its static fields, is under
  the invariant record operands `first` and `rest`, as a callable object's
  (`CallableConjunctions.propsT`), and the readonly `views`
  (`CallableConjunctions.viewsT`); with none it states no field. -/
  | ctors (signatures : List (List α × α)) (variadic : List (List α × α × α) := [])
      (first : List (PropKey × α) := []) (rest : List (List (PropKey × α)) := [])
      (views : List (PropKey × α) := [])
  /-- An argument list under one or more tuple contracts: what a rest
  parameter's type says of the actuals after the fixed ones. Only a signature's
  rest meets one; no program value is one. -/
  | pack (first : Tuple α) (rest : List (Tuple α))
  /-- One bigint, below the `bigint` family as a number singleton is below
  the number family; appended last so every earlier case order holds. -/
  | bigintLit (value : Int)
  /-- One symbol, below the `symbol` family: the symbol of a `unique symbol`
  constant, by its identity; appended last so every earlier case order holds. -/
  | symbolLit (id : Nat)
  deriving Repr, DecidableEq

/-- Every value. A closed value, as every member of every family is. -/
def topT : Fam := fun _ _ v => isVal v = true ∧ Scoped 0 v

def sourceT : Fam := fun _ _ v => isSourceVal v = true ∧ Scoped 0 v

def semWithArgs (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) : Clause α → Fam
  | .top => topT
  | .source => sourceT
  | .list a bs => fun n W v => listT (tupleFams X a) n W v ∧ ∀ b ∈ bs, listT (tupleFams X b) n W v
  | .nul => nulT
  | .undef => undefT
  | .bool => boolT
  | .boolLit b => fun _ _ v => v = (if b then .tru else .fls)
  | .num => numT
  | .numLit b => fun _ _ v => v = .num b
  | .str => strT
  | .strLit s => fun _ _ v => v = .str s
  | .bigint => bigintT
  | .bigintLit i => fun _ _ v => v = .bigint i
  | .symbolLit i => fun _ _ v => v = .sym i
  | .symbol => symbolT
  | .refs a bs vs os ms ks => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧ viewsT (famsOf X vs) n W v ∧
        optT (os.map (·.map X)) n W v ∧ methodT Ξ (ms.map (Member.of X P)) n W v ∧
        ∀ K ∈ ks, ownKeysT K n W v
  | .dict a bs vs ds os ms ks cs => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧
      viewsT (famsOf X vs) n W v ∧
        ((∀ d ∈ ds, dictViewT d.1 (X d.2) n W v) ∧ ∀ d ∈ cs, dictCellT d.1 (X d.2) n W v) ∧
        optT (os.map (·.map X)) n W v ∧ methodT Ξ (ms.map (Member.of X P)) n W v ∧
        ∀ K ∈ ks, ownKeysT K n W v
  | .arrs L S => interT (CallEffects.callsT Ξ (L.map (Arrow.map X)))
      (CallEffects.restsT Ξ (S.map (RestArrow.mapWith X P)))
  | .callable a bs L S =>
      interT (CallableConjunctions.objectsT Ξ (famsOf X a) (bs.map (famsOf X))
        (L.map (Arrow.map X)))
        (CallEffects.restsT Ξ (S.map (RestArrow.mapWith X P)))
  | .ctors L S a bs vs => interT (interT (ctorsT Ξ (L.map fun p => (p.1.map X, X p.2)))
      (ctorRestsT Ξ (S.map fun s => (s.1.map X, P s.2.1, X s.2.2))))
      (interT (CallableConjunctions.propsT (famsOf X a) (bs.map (famsOf X)))
        (CallableConjunctions.viewsT (famsOf X vs)))
  -- An argument list is not a runtime value: a pack clause's members are
  -- lists, read by `clauseArguments`.
  | .pack _ _ => fun _ _ _ => False

/-- The argument-list component of a clause. Grouping arguments spends no
approximation step; only a surrounding runtime operation supplies a guard. -/
def clauseArguments (X : α → Fam) : Clause α → ArgFam
  | .pack a bs => fun n W vs => ∀ t ∈ a :: bs,
      ArgumentContracts.Fits (tupleFams X t) n W vs
  | _ => fun _ _ _ => False

def semList (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) (L : List (Clause α)) : Fam :=
  setSem (semWithArgs Ξ X P) L

/-- Intersection of clauses: preserve all constraints of the same shape. -/
def meet : Clause α → Clause α → List (Clause α)
  | .top, c | c, .top => [c]
  | .source, .list .. | .list .., .source | .source, .pack .. | .pack .., .source => []
  | .source, c | c, .source => [c]
  | .list a bs, .list c ds => [.list a (bs ++ c :: ds)]
  | .nul, .nul => [.nul]
  | .undef, .undef => [.undef]
  | .bool, .bool => [.bool]
  | .bool, .boolLit b | .boolLit b, .bool => [.boolLit b]
  | .boolLit a, .boolLit b => if a == b then [.boolLit a] else []
  | .num, .num => [.num]
  | .num, .numLit b | .numLit b, .num => [.numLit b]
  | .numLit a, .numLit b => if a == b then [.numLit a] else []
  | .str, .str => [.str]
  | .str, .strLit s | .strLit s, .str => [.strLit s]
  | .strLit a, .strLit b => if a == b then [.strLit a] else []
  | .bigint, .bigint => [.bigint]
  | .bigint, .bigintLit i | .bigintLit i, .bigint => [.bigintLit i]
  | .bigintLit a, .bigintLit b => if a == b then [.bigintLit a] else []
  | .symbol, .symbol => [.symbol]
  | .symbol, .symbolLit i | .symbolLit i, .symbol => [.symbolLit i]
  | .symbolLit a, .symbolLit b => if a == b then [.symbolLit a] else []
  -- Object contracts meet on one object: their first operands are one record
  -- (`ReferenceConjunctions.flatten`), whose named fields the read rules find.
  | .refs a bs vs os ms ks, .refs c ds ws ps ns ls =>
      [.refs (a ++ c) (bs ++ ds) (vs ++ ws) (os ++ ps) (ms ++ ns) (ks ++ ls)]
  | .refs a bs vs os ms ks, .dict c ds ws ix ps ns ls cy =>
      [.dict (a ++ c) (bs ++ ds) (vs ++ ws) ix (os ++ ps) (ms ++ ns) (ks ++ ls) cy]
  | .dict a bs vs ix os ms ks cx, .refs c ds ws ps ns ls =>
      [.dict (a ++ c) (bs ++ ds) (vs ++ ws) ix (os ++ ps) (ms ++ ns) (ks ++ ls) cx]
  | .dict a bs vs ix os ms ks cx, .dict c ds ws iy ps ns ls cy =>
      [.dict (a ++ c) (bs ++ ds) (vs ++ ws) (ix ++ iy) (os ++ ps) (ms ++ ns) (ks ++ ls) (cx ++ cy)]
  | .arrs L S, .arrs M T => [.arrs (L ++ M) (S ++ T)]
  -- Two bags on one object are both; two bagless ones stay bagless.
  | .ctors L S [] [] [], .ctors M T [] [] [] => [.ctors (L ++ M) (S ++ T)]
  | .ctors L S a bs vs, .ctors M T c ds ws => [.ctors (L ++ M) (S ++ T) a (bs ++ c :: ds) (vs ++ ws)]
  | .pack a bs, .pack c ds => [.pack a (bs ++ c :: ds)]
  | .callable a bs L S, .callable c ds M T => [.callable a (bs ++ c :: ds) (L ++ M) (S ++ T)]
  | .callable a bs L S, .arrs M T => [.callable a bs (L ++ M) (S ++ T)]
  | .arrs L S, .callable a bs M T => [.callable a bs (M ++ L) (T ++ S)]
  | _, _ => []

/-- The primitive clause whose values a class's keys are the `ToPropertyKey`
of: strings for every string key, numbers for the canonical numeric ones
(`numeric_admits_number`), symbols for the symbol keys. A computed key of
that clause reads through an index over that class. -/
def keyClause : IndexKeys → Clause α
  | .strings => .str
  | .numeric => .num
  | .symbols => .symbol

/-- A dictionary's indexes, the canonical numeric keys' first: where a key
is admitted by both a number index and a string one, the number index's
contract is the narrower (TypeScript requires it within the string index's),
so a read through it is the more precise. -/
def numericFirst (ix : List (IndexKeys × α)) : List (IndexKeys × α) :=
  ix.filter (·.1 == .numeric) ++ ix.filter (·.1 != .numeric)

/-- **The array shape**, the one definition every layer reads arrays from: an
object holding its store under the store key, invariantly or, readonly, as a
view; holding `Array.prototype` as a view under the prototype key; and owning
none of `excluded`, the keys the prototype provides, so a read of one of them
continues at the prototype. Any other own key it may have: an array may carry
further keys, such as a runtime's hidden marker. -/
def arrayClauseOf (store proto : α) (excluded : List PropKey) (readonly : Bool) : Clause α :=
  .refs (if readonly then [] else [(CallArguments.arrayStoreField, store)]) []
    ((if readonly then [(CallArguments.arrayStoreField, store)] else []) ++
      [(CallArguments.protoField, proto)])
    [] [] [⟨false, excluded⟩]

/-- A record or dictionary clause: the clauses the array invariant applies to
(`PositiveGraphs.builtinInvariant`). The source-value universe constrains only
the outer value form and carries no record invariant. -/
def Clause.record : Clause α → Bool
  | .refs .. | .dict .. => true
  | _ => false

/-- The clauses the built-in array invariant applies to in a row
(`PositiveGraphs.builtinInvariant`): records, dictionaries and `source`, the
builtins's `unknown`. -/
def Clause.carriesInvariant : Clause α → Bool
  | .refs .. | .dict .. | .source => true
  | _ => false

/-- The keys an object clause says its object owns: its fields' and views'. -/
def Clause.presentKeys : Clause α → List PropKey
  | .refs a bs vs .. | .dict a bs vs .. => ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).map (·.1)
  | _ => []

/-- An object clause's key bounds. -/
def Clause.keyBounds : Clause α → List KeyBound
  | .refs _ _ _ _ _ ks | .dict _ _ _ _ _ _ ks _ => ks
  | _ => []

/-- A clause whose bounds admit every key it says the object owns. Any other
has no member: a meet in which one operand owns a key another's bound
excludes, such as an array with an own `map`, is empty. -/
def Clause.consistent (c : Clause α) : Bool :=
  c.presentKeys.all fun k => c.keyBounds.all (·.admits k)

/-- The meet of two clause lists: each pair's meet, without clauses a bound
contradicts. -/
def meetLists (A B : List (Clause α)) : List (Clause α) :=
  A.flatMap fun a => B.flatMap fun b => (meet a b).filter Clause.consistent

private theorem singleton_sem (X : α → Fam) (P : α → ArgFam) (c : Clause α) (n W v) :
    semList Ξ X P [c] n W v ↔ semWithArgs Ξ X P c n W v := by simp [semList, setSem]

private theorem nil_sem (X : α → Fam) (P : α → ArgFam) (n W v) : ¬ semList Ξ X P [] n W v := by
  simp [semList, setSem]

def shape : Clause α → Nat
  | .nul => 0 | .bool | .boolLit _ => 1 | .refs .. | .dict .. => 2 | .arrs .. | .callable .. => 3
  | .undef => 4 | .num | .numLit _ => 5 | .str | .strLit _ => 6
  | .top => 7 | .list .. => 8 | .bigint | .bigintLit _ => 9 | .symbol | .symbolLit _ => 10 | .ctors .. => 11
  | .pack .. => 12
  | .source => 7

def valueShape : Val → Nat
  | .nul => 0 | .tru | .fls => 1 | .objAt _ .absent _ => 2 | .undef => 4
  | .objAt _ (.bound _ _ _) _ | .objAt _ (.graph _ _ _ _ _ .call _) _
  | .objAt _ (.graph _ _ _ _ _ .sloppy _) _ => 3
  | .objAt _ (.graph _ _ _ _ _ .construct _) _ => 11
  | .num _ => 5
  | .str _ => 6
  | .arr _ => 8
  | .bigint _ => 9
  | .sym _ => 10
  | _ => 7

/-- Every member of a clause is a closed value; top says nothing more. -/
theorem semWithArgs_value {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs Ξ X P c n W v) : isVal v = true ∧ Scoped 0 v := by
  cases c with
  | top => exact h
  | source => exact ⟨sourceVal_isVal h.1, h.2⟩
  | list a bs => obtain ⟨ls, rfl, _⟩ := h.1; exact ⟨rfl, trivial⟩
  | nul => subst v; exact ⟨rfl, trivial⟩
  | bool => rcases h with rfl | rfl <;> exact ⟨rfl, trivial⟩
  | boolLit b => cases b <;> cases h <;> exact ⟨rfl, trivial⟩
  | num => obtain ⟨b, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | numLit b => subst v; exact ⟨rfl, trivial⟩
  | refs a rest => obtain ⟨flds, _, rfl, _⟩ := h.1.1; exact ⟨rfl, trivial⟩
  | dict a rest vs ds os ms ks cs => obtain ⟨flds, _, rfl, _⟩ := h.1.1; exact ⟨rfl, trivial⟩
  | arrs L S => exact ⟨h.1.1.val, h.1.1.scoped⟩
  | callable a bs L S => exact ⟨h.1.2.1.val, h.1.2.1.scoped⟩
  | undef => subst v; exact ⟨rfl, trivial⟩
  | str => obtain ⟨s, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | strLit s => subst v; exact ⟨rfl, trivial⟩
  | bigint => obtain ⟨i, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | bigintLit i => subst v; exact ⟨rfl, trivial⟩
  | symbolLit i => subst v; exact ⟨rfl, trivial⟩
  | symbol => obtain ⟨i, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | ctors L S a bs vs => obtain ⟨_, _, _, _, _, _, _, _, rfl, hs⟩ := h.1.1.1; exact ⟨rfl, hs⟩
  | pack a bs => exact h.elim


/-- A member's shape is its clause's, except under the two value universes. -/
theorem semWithArgs_shape {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : c ≠ .top) (hj : c ≠ .source) (h : semWithArgs Ξ X P c n W v) : valueShape v = shape c := by
  cases c with
  | top => exact absurd rfl hc
  | source => exact absurd rfl hj
  | list a bs => obtain ⟨ls, rfl, _⟩ := h.1; rfl
  | nul => cases h; rfl
  | bool => rcases h with h | h <;> cases h <;> rfl
  | boolLit b => cases b <;> cases h <;> rfl
  | num => obtain ⟨b, rfl⟩ := h; rfl
  | numLit b => cases h; rfl
  | refs a bs => obtain ⟨flds, _, rfl, _⟩ := h.1.1; rfl
  | dict a bs vs ds os ms ks cs => obtain ⟨flds, _, rfl, _⟩ := h.1.1; rfl
  | arrs L S =>
    obtain ⟨fs, code, _, rfl, hc, -⟩ := h.1.1
    cases code
    case graph kind _ => cases kind <;> simp_all [valueShape, shape, CallCode.callable]
    all_goals simp_all [valueShape, shape, CallCode.callable]
  | undef => cases h; rfl
  | callable a bs L S =>
    obtain ⟨fs, code, _, rfl, hc, -⟩ := h.1.2.1
    cases code
    case graph kind _ => cases kind <;> simp_all [valueShape, shape, CallCode.callable]
    all_goals simp_all [valueShape, shape, CallCode.callable]
  | str => obtain ⟨s, rfl⟩ := h; rfl
  | strLit s => cases h; rfl
  | bigint => obtain ⟨i, rfl⟩ := h; rfl
  | bigintLit i => cases h; rfl
  | symbolLit i => cases h; rfl
  | symbol => obtain ⟨i, rfl⟩ := h; rfl
  | ctors L S a bs vs =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := h.1.1.1
    rfl
  | pack a bs => exact h.elim

/-- Every inhabited clause other than calculus top or an element-store clause
contains only JavaScript values. Argument-pack clauses have no term members. -/
theorem semWithArgs_source {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (ht : c ≠ .top) (hl : ∀ a bs, c ≠ .list a bs)
    (h : semWithArgs Ξ X P c n W v) : sourceT n W v := by
  have hv := semWithArgs_value h
  refine ⟨?_, hv.2⟩
  by_cases hj : c = .source
  · subst c; exact h.1
  have hs := semWithArgs_shape ht hj h
  cases v <;> simp_all [isSourceVal, isVal, valueShape]
  cases c <;> simp_all [shape]

/-- The property bag a clause states of a value with code: a callable
object's fields, or a class value's static fields. -/
def Clause.bag : Clause α → Option (List (PropKey × α) × List (List (PropKey × α)))
  | .callable a bs _ _ | .ctors _ _ a bs _ => some (a, bs)
  | _ => none

/-- The readonly fields a clause states of a value with code: a class
value's readonly static fields. -/
def Clause.bagViews : Clause α → List (PropKey × α)
  | .ctors _ _ _ _ vs => vs
  | _ => []

/-- The first operand of a clause's bag: the fields a read or write finds. -/
def Clause.bagFields (c : Clause α) : List (PropKey × α) :=
  match c.bag with
  | some (P, _) => P
  | none => []

theorem bag_sem {X : α → Fam} {P : α → ArgFam} {c : Clause α} {a : List (PropKey × α)}
    {bs : List (List (PropKey × α))} (hc : c.bag = some (a, bs)) {n W v}
    (h : semWithArgs Ξ X P c n W v) :
    CallableConjunctions.propsT (famsOf X a) (bs.map (famsOf X)) n W v := by
  cases c <;> simp only [Clause.bag, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  · obtain ⟨rfl, rfl⟩ := hc; exact h.1.1
  · obtain ⟨rfl, rfl⟩ := hc; exact h.2.1

theorem bagViews_sem {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs Ξ X P c n W v) (hne : c.bagViews ≠ []) :
    CallableConjunctions.viewsT (famsOf X c.bagViews) n W v := by
  cases c <;> simp only [Clause.bagViews, ne_eq, not_true_eq_false] at hne
  exact h.2.2

/-- An empty bag adds nothing to a family of object values. -/
theorem bag_nil_absorb {A : Fam} {X : α → Fam}
    (hA : ∀ n W v, A n W v → ∃ fs code oid, v = Tm.objAt fs code oid) :
    interT A (interT (CallableConjunctions.propsT (famsOf X [])
      (([] : List (List (PropKey × α))).map (famsOf X)))
      (CallableConjunctions.viewsT (famsOf X []))) = A := by
  funext n W v
  apply propext
  constructor
  · exact And.left
  · intro h
    obtain ⟨fs, code, oid, rfl⟩ := hA n W v h
    exact ⟨h, CallableConjunctions.props_nil, CallableConjunctions.views_nil⟩

/-- A clause whose term members are source values. -/
def sourceClause : Clause α → Bool
  | .top | .list .. => false
  | _ => true

theorem sourceClause_sound {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : sourceClause c = true) (h : semWithArgs Ξ X P c n W v) : sourceT n W v := by
  apply semWithArgs_source (by intro e; subst c; cases hc) (by intros a bs e; subst c; cases hc) h

private theorem meet_source (X : α → Fam) (P : α → ArgFam) (c : Clause α) (n W v) :
    semList Ξ X P (meet .source c) n W v ↔ sourceT n W v ∧ semWithArgs Ξ X P c n W v := by
  unfold meet
  cases c with
  | top =>
    simp only [singleton_sem, semWithArgs]
    exact ⟨fun h => ⟨h, sourceVal_isVal h.1, h.2⟩, And.left⟩
  | source => simp [singleton_sem, semWithArgs]
  | list a bs =>
    simp only [semList, setSem, List.not_mem_nil, false_and, exists_false, false_iff]
    rintro ⟨hj, hv⟩
    obtain ⟨ls, rfl, _⟩ := hv.1
    exact Bool.noConfusion hj.1
  | pack a bs => simp [semList, setSem, semWithArgs]
  | _ =>
    simp only [singleton_sem]
    exact ⟨fun h => ⟨semWithArgs_source (by simp) (by intros; simp) h, h⟩, And.right⟩

theorem meet_ctors (L M : List (List α × α)) (S T : List (List α × α × α))
    (a c : List (PropKey × α)) (bs ds : List (List (PropKey × α))) (vs ws : List (PropKey × α)) :
    meet (.ctors L S a bs vs) (.ctors M T c ds ws) =
      if a = [] ∧ bs = [] ∧ vs = [] ∧ c = [] ∧ ds = [] ∧ ws = [] then [.ctors (L ++ M) (S ++ T)]
      else [.ctors (L ++ M) (S ++ T) a (bs ++ c :: ds) (vs ++ ws)] := by
  cases a <;> cases bs <;> cases vs <;> cases c <;> cases ds <;> cases ws <;> simp [meet]

theorem meet_sound (X : α → Fam) (P : α → ArgFam) (a b : Clause α) (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet a b) n W v ↔ interT (semWithArgs Ξ X P a) (semWithArgs Ξ X P b) n W v := by
  by_cases ha : a = .top
  · subst ha
    rw [show meet .top b = [b] from rfl, singleton_sem]
    exact ⟨fun h => ⟨semWithArgs_value h, h⟩, fun h => h.2⟩
  by_cases hb : b = .top
  · subst hb
    have hm : meet a .top = [a] := by
      cases a <;> first | exact absurd rfl ha | rfl
    rw [hm, singleton_sem]
    exact ⟨fun h => ⟨h, semWithArgs_value h⟩, fun h => h.1⟩
  by_cases hja : a = .source
  · subst a; exact meet_source X P b n W v
  by_cases hjb : b = .source
  · subst b
    have hm : meet a .source = meet .source a := by cases a <;> rfl
    rw [hm, meet_source]
    exact and_comm
  by_cases hs : shape a = shape b
  · unfold meet
    cases a <;> cases b <;> simp only [shape] at hs
    all_goals try contradiction
    · simp [singleton_sem, semWithArgs, interT]
    · simp [singleton_sem, semWithArgs, interT]
    · rename_i b
      cases b <;> simp [singleton_sem, semWithArgs, interT, boolT]
      all_goals intro hv; subst v; simp
    · simp only [singleton_sem, semWithArgs, List.map_append]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, interT,
        List.mem_append, or_imp, forall_and]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩ =>
          ⟨⟨r1, v1, o1, m1, k1⟩, ⟨r2, v2, o2, m2, k2⟩⟩,
        fun ⟨⟨r1, v1, o1, m1, k1⟩, ⟨r2, v2, o2, m2, k2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩⟩
    · -- refs ∩ dictionary
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, interT,
        List.mem_append, or_imp, forall_and]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d2, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩ =>
          ⟨⟨r1, v1, o1, m1, k1⟩, ⟨r2, v2, d2, o2, m2, k2⟩⟩,
        fun ⟨⟨r1, v1, o1, m1, k1⟩, ⟨r2, v2, d2, o2, m2, k2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d2, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩⟩
    · -- dictionary ∩ refs
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, interT,
        List.mem_append, or_imp, forall_and]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d1, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩ =>
          ⟨⟨r1, v1, d1, o1, m1, k1⟩, ⟨r2, v2, o2, m2, k2⟩⟩,
        fun ⟨⟨r1, v1, d1, o1, m1, k1⟩, ⟨r2, v2, o2, m2, k2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d1, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩⟩
    · -- dictionary ∩ dictionary
      simp only [singleton_sem, semWithArgs, List.map_append,
        List.mem_append, or_imp, forall_and]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, interT]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨⟨d1, d2⟩, ⟨c1, c2⟩⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩ =>
          ⟨⟨r1, v1, ⟨d1, c1⟩, o1, m1, k1⟩, ⟨r2, v2, ⟨d2, c2⟩, o2, m2, k2⟩⟩,
        fun ⟨⟨r1, v1, ⟨d1, c1⟩, o1, m1, k1⟩, ⟨r2, v2, ⟨d2, c2⟩, o2, m2, k2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨⟨d1, d2⟩, ⟨c1, c2⟩⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩⟩⟩
    · -- arrs ∩ arrs
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [interT, CallEffects.callsT_append, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    · -- arrs ∩ callable
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [interT, CallableConjunctions.calls_merge, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, c⟩, t, r⟩ => ⟨⟨c, r⟩, o, t⟩, fun ⟨⟨c, r⟩, o, t⟩ => ⟨⟨o, c⟩, t, r⟩⟩
    · rename_i b
      cases b <;> simp [singleton_sem, semWithArgs, interT, boolT]
      all_goals intro hv; subst v; simp
    · rename_i b c
      cases b <;> cases c <;> simp [semWithArgs, interT, semList, setSem]
      all_goals intro hv; subst v; simp
    · -- num ∩ num
      simp [singleton_sem, semWithArgs, interT, numT]
    · -- num ∩ numLit: the singleton already implies the family
      rename_i b
      simp [singleton_sem, semWithArgs, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ num
      rename_i b
      simp [singleton_sem, semWithArgs, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ numLit: equal spellings are equal numbers
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · simp [singleton_sem, semWithArgs, interT]
    · -- callable ∩ arrs
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [interT, CallableConjunctions.calls_merge, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, c⟩, r, t⟩ => ⟨⟨o, r⟩, c, t⟩, fun ⟨⟨o, r⟩, c, t⟩ => ⟨⟨o, c⟩, r, t⟩⟩
    · -- callable ∩ callable
      simp only [singleton_sem, semWithArgs, List.map_append, List.map_cons]
      rw [interT, CallableConjunctions.merge, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨o, p⟩, r, t⟩ => ⟨⟨o, r⟩, p, t⟩, fun ⟨⟨o, r⟩, p, t⟩ => ⟨⟨o, p⟩, r, t⟩⟩
    · -- str ∩ str
      simp [singleton_sem, semWithArgs, interT, strT]
    · -- str ∩ strLit
      rename_i s
      simp [singleton_sem, semWithArgs, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ str
      rename_i s
      simp [singleton_sem, semWithArgs, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ strLit
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · -- list ∩ list: every contract of both, on the one store
      simp only [singleton_sem, semWithArgs, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq, interT]
      exact ⟨fun ⟨ha, hb, hc, hd⟩ => ⟨⟨ha, hb⟩, hc, hd⟩, fun ⟨⟨ha, hb⟩, hc, hd⟩ => ⟨ha, hb, hc, hd⟩⟩
    · -- bigint ∩ bigint
      simp [singleton_sem, semWithArgs, interT, bigintT]
    · -- bigint ∩ bigintLit: the singleton already implies the family
      rename_i i
      simp [singleton_sem, semWithArgs, interT, bigintT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- symbol ∩ symbol
      simp [singleton_sem, semWithArgs, interT, symbolT]
    · -- symbol ∩ symbolLit: the singleton already implies the family
      rename_i i
      simp [singleton_sem, semWithArgs, interT, symbolT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- ctors ∩ ctors: every construct signature of both, both bags
      rename_i L S a bs vs M T c ds ws
      show semList Ξ X P (meet (.ctors L S a bs vs) (.ctors M T c ds ws)) n W v ↔ _
      rw [meet_ctors]
      split
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ‹_ ∧ _›
        simp only [singleton_sem, semWithArgs, List.map_append, List.map_nil, interT]
        rw [ctorsT_append, ctorRestsT_append]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hb⟩
          exact ⟨⟨⟨h1, h3⟩, hb⟩, ⟨h2, h4⟩, hb⟩
        · rintro ⟨⟨⟨h1, h3⟩, hb⟩, ⟨h2, h4⟩, -⟩
          exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, hb⟩
      · simp only [singleton_sem, semWithArgs, List.map_append, List.map_cons, interT]
        rw [ctorsT_append, ctorRestsT_append, CallableConjunctions.props_merge, famsOf_append]
        simp only [interT]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨hp, hq⟩, hv⟩
          obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := h1.1
          obtain ⟨hv1, hv2⟩ := (CallableConjunctions.views_append _ _).mp hv
          exact ⟨⟨⟨h1, h3⟩, hp, hv1⟩, ⟨h2, h4⟩, hq, hv2⟩
        · rintro ⟨⟨⟨h1, h3⟩, hp, hv1⟩, ⟨h2, h4⟩, hq, hv2⟩
          obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := h1.1
          exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨hp, hq⟩, (CallableConjunctions.views_append _ _).mpr ⟨hv1, hv2⟩⟩
    · -- pack ∩ pack: every contract of both, on the one list
      rename_i a bs c ds
      simp [singleton_sem, semWithArgs, interT]
    · -- bigintLit ∩ bigint
      rename_i i
      simp [singleton_sem, semWithArgs, interT, bigintT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- bigintLit ∩ bigintLit: equal integers are equal bigints
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · -- symbolLit ∩ symbol
      rename_i i
      simp [singleton_sem, semWithArgs, interT, symbolT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- symbolLit ∩ symbolLit: equal identities are equal symbols
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
  · have hm : meet a b = [] := by
      cases a <;> cases b <;> first
        | rfl | exact absurd rfl hs | exact absurd rfl ha | exact absurd rfl hb
        | exact absurd rfl hja | exact absurd rfl hjb
    rw [hm]
    constructor
    · intro h; exact False.elim (nil_sem X P n W v h)
    · rintro ⟨hva, hvb⟩
      exact False.elim (hs ((semWithArgs_shape ha hja hva).symm.trans (semWithArgs_shape hb hjb hvb)))

/-- Every key a member's clause says it owns, each bound admits: a clause
with a member is consistent. -/
theorem semWithArgs_consistent {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs Ξ X P c n W v) : c.consistent = true := by
  -- What an object clause says: its fields and views are at locations of its
  -- one object, whose own keys each bound admits.
  have present : ∀ (a : List (PropKey × α)) (bs : List (List (PropKey × α)))
      (vs : List (PropKey × α)) (ks : List KeyBound),
      ReferenceConjunctions.refsT (famsOf X a) (bs.map (famsOf X)) n W v →
      viewsT (famsOf X vs) n W v → (∀ K ∈ ks, ownKeysT K n W v) →
      (((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).map (·.1)).all (fun k => ks.all (·.admits k)) = true := by
    intro a bs vs ks hr hw hk
    simp only [List.all_eq_true, List.mem_map]
    rintro k ⟨p, hp, rfl⟩ K hK
    have hat : ∃ (flds : List (PropKey × Nat)) (l : Nat) (oid : Nat), v = .objAt flds .absent oid ∧
        flds.lookup p.1 = some l := by
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
        have hrec : recT (famsOf X L) n W v := by
          rcases List.mem_cons.mp hL with rfl | hL
          · exact hr.1
          · exact hr.2 _ (List.mem_map_of_mem hL)
        obtain ⟨flds, l, -, oid, he, hl, -⟩ := recT_at (mem_famsOf.mpr ⟨p.2, hpL, rfl⟩) hrec
        exact ⟨flds, l, oid, he, hl⟩
      · obtain ⟨hp, hpl⟩ := List.mem_filter.mp hp
        obtain ⟨flds, l, -, oid, he, hl, -⟩ := viewsT_at (mem_famsOf.mpr ⟨p.2, hp, rfl⟩) (by simpa using hpl) hw
        exact ⟨flds, l, oid, he, hl⟩
    obtain ⟨flds, l, oid, rfl, hl⟩ := hat
    exact ownKeysT_admits (hk K hK) hl
  cases c with
  | refs a bs vs os ms ks => exact present a bs vs ks h.1 h.2.1 h.2.2.2.2
  | dict a bs vs ds os ms ks cs => exact present a bs vs ks h.1 h.2.1 h.2.2.2.2.2
  | _ => simp [Clause.consistent, Clause.presentKeys]

/-- A member of an object clause owns every key the clause says it owns. -/
theorem semWithArgs_owns {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v} {k : PropKey}
    (h : semWithArgs Ξ X P c n W v) (hk : k ∈ c.presentKeys) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (oid : Nat), v = .objAt flds .absent oid ∧ flds.lookup k = some l := by
  have present : ∀ (a : List (PropKey × α)) (bs : List (List (PropKey × α)))
      (vs : List (PropKey × α)),
      ReferenceConjunctions.refsT (famsOf X a) (bs.map (famsOf X)) n W v →
      viewsT (famsOf X vs) n W v → k ∈ ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).map (·.1) →
      ∃ (flds : List (PropKey × Nat)) (l : Nat) (oid : Nat), v = .objAt flds .absent oid ∧ flds.lookup k = some l := by
    intro a bs vs hr hw hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
      have hrec : recT (famsOf X L) n W v := by
        rcases List.mem_cons.mp hL with rfl | hL
        · exact hr.1
        · exact hr.2 _ (List.mem_map_of_mem hL)
      obtain ⟨flds, l, -, oid, he, hl, -⟩ := recT_at (mem_famsOf.mpr ⟨p.2, hpL, rfl⟩) hrec
      exact ⟨flds, l, oid, he, hl⟩
    · obtain ⟨hp, hpl⟩ := List.mem_filter.mp hp
      obtain ⟨flds, l, -, oid, he, hl, -⟩ := viewsT_at (mem_famsOf.mpr ⟨p.2, hp, rfl⟩) (by simpa using hpl) hw
      exact ⟨flds, l, oid, he, hl⟩
  cases c with
  | refs a bs vs os ms ks => exact present a bs vs h.1 h.2.1 hk
  | dict a bs vs ds os ms ks cs => exact present a bs vs h.1 h.2.1 hk
  | _ => simp [Clause.presentKeys] at hk

/-- A member of an object clause meets each of the clause's key bounds. -/
theorem semWithArgs_bounded {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v} {K : KeyBound}
    (h : semWithArgs Ξ X P c n W v) (hK : K ∈ c.keyBounds) : ownKeysT K n W v := by
  cases c with
  | refs a bs vs os ms ks => exact h.2.2.2.2 K hK
  | dict a bs vs ds os ms ks cs => exact h.2.2.2.2.2 K hK
  | _ => simp [Clause.keyBounds] at hK

/-- All constructors remain admissible, without assumptions on the operand
families. Invariant comparison and arrow guards supply the required stability. -/
theorem semWithArgs_adm (X : α → Fam) (P : α → ArgFam) (c : Clause α) : Adm (semWithArgs Ξ X P c) := by
  cases c with
  | nul => exact nulT_adm
  | bool => exact boolT_adm
  | boolLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | num => exact numT_adm
  | numLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | refs a bs vs os ms ks => exact ⟨fun n W v h => ⟨(adm _ _).down n W v h.1, (viewsT_adm _).down n W v h.2.1,
        (optT_adm _).down n W v h.2.2.1, (methodT_adm _).down n W v h.2.2.2.1,
        fun K hK => (ownKeysT_adm K).down n W v (h.2.2.2.2 K hK)⟩,
      fun n W U hx v h => ⟨(adm _ _).mono n W U hx v h.1, (viewsT_adm _).mono n W U hx v h.2.1,
        (optT_adm _).mono n W U hx v h.2.2.1, (methodT_adm _).mono n W U hx v h.2.2.2.1,
        fun K hK => (ownKeysT_adm K).mono n W U hx v (h.2.2.2.2 K hK)⟩⟩
  | dict a bs vs ds os ms ks cs =>
    refine ⟨?_, ?_⟩
    · intro n W v h
      exact ⟨(adm _ _).down n W v h.1, (viewsT_adm _).down n W v h.2.1,
        ⟨fun d hd => (dictViewT_adm _ _).down n W v (h.2.2.1.1 d hd),
          fun d hd => (dictCellT_adm _ _).down n W v (h.2.2.1.2 d hd)⟩, (optT_adm _).down n W v h.2.2.2.1,
        (methodT_adm _).down n W v h.2.2.2.2.1,
        fun K hK => (ownKeysT_adm K).down n W v (h.2.2.2.2.2 K hK)⟩
    · intro n W U hx v h
      exact ⟨(adm _ _).mono n W U hx v h.1, (viewsT_adm _).mono n W U hx v h.2.1,
        ⟨fun d hd => (dictViewT_adm _ _).mono n W U hx v (h.2.2.1.1 d hd),
          fun d hd => (dictCellT_adm _ _).mono n W U hx v (h.2.2.1.2 d hd)⟩, (optT_adm _).mono n W U hx v h.2.2.2.1,
        (methodT_adm _).mono n W U hx v h.2.2.2.2.1,
        fun K hK => (ownKeysT_adm K).mono n W U hx v (h.2.2.2.2.2 K hK)⟩
  | arrs L S => exact interT_adm _ _ (CallEffects.callsT_adm _) (CallEffects.restsT_adm _)
  | callable a bs L S => exact interT_adm _ _ (CallableConjunctions.adm _ _ _) (CallEffects.restsT_adm _)
  | ctors L S a bs vs =>
    exact interT_adm _ _ (interT_adm _ _ (ctorsT_adm _) (ctorRestsT_adm _))
      (interT_adm _ _ (CallableConjunctions.props_adm _ _) (CallableConjunctions.views_adm _))
  | pack a bs => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | bigintLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | symbolLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | undef => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | top | source => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | list a bs => exact ⟨fun n W v h => ⟨(listT_adm _).down n W v h.1,
        fun b hb => (listT_adm _).down n W v (h.2 b hb)⟩,
      fun n W U hx v h => ⟨(listT_adm _).mono n W U hx v h.1,
        fun b hb => (listT_adm _).mono n W U hx v (h.2 b hb)⟩⟩
  | str => exact strT_adm
  | strLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | bigint => exact bigintT_adm
  | symbol => exact symbolT_adm


theorem positionFam_tupleFams (X : α → Fam) (t : Tuple α) (i : Nat) :
    positionFam (tupleFams X t) i = (t.position i).map X := by
  simp only [positionFam, Tuple.position, tupleFams, List.getElem?_map, List.length_map]
  cases t.required[i]? <;> simp
  cases t.optional[i - t.required.length]? <;> simp
  split <;> simp

/-- Past the required and optional positions, every index has the rest. -/
theorem Tuple.position_beyond {t : Tuple α} {i : Nat}
    (h : t.required.length + t.optional.length ≤ i) : t.position i = t.rest := by
  simp only [Tuple.position, List.getElem?_eq_none (show t.required.length ≤ i by omega),
    List.getElem?_eq_none (show t.optional.length ≤ i - t.required.length by omega), h, if_true]

/-- An index without a position is past the fixed positions of a contract
without a rest. -/
theorem Tuple.position_none {t : Tuple α} {i : Nat} (h : t.position i = none) :
    t.required.length + t.optional.length ≤ i ∧ t.rest = none := by
  simp only [Tuple.position] at h
  cases hr : t.required[i]? <;> simp only [hr, reduceCtorEq] at h
  cases ho : t.optional[i - t.required.length]? <;> simp only [ho, reduceCtorEq] at h
  rw [List.getElem?_eq_none_iff] at hr ho
  have hi : t.required.length + t.optional.length ≤ i := by omega
  simp only [hi, if_true] at h
  exact ⟨hi, h⟩

/-- Current-level tuple membership preserves current-level agreement. -/
theorem arguments_congr (X Y : α → Fam) (t : Tuple α) (n : Nat) {W : WorldT n}
    (h : ∀ a v, X a n W v ↔ Y a n W v) (vs : List Val) :
    ArgumentContracts.Fits (tupleFams X t) n W vs ↔
      ArgumentContracts.Fits (tupleFams Y t) n W vs := by
  apply TupleFits.congr (by simp [tupleFams]) (by simp [tupleFams]) (by simp [tupleFams])
  intro i
  simp only [positionFam_tupleFams]
  refine ⟨by simp, fun A B hA hB v => ?_⟩
  cases hp : t.position i <;> simp [hp] at hA hB
  subst hA; subst hB
  exact h _ v

theorem clauseArguments_congr (X Y : α → Fam) (c : Clause α) (n : Nat) (W : WorldT n)
    (h : ∀ a v, X a n W v ↔ Y a n W v) (vs : List Val) :
    clauseArguments X c n W vs ↔ clauseArguments Y c n W vs := by
  cases c <;> try exact Iff.rfl
  rename_i a bs
  exact forall_congr' fun t => forall_congr' fun _ => arguments_congr X Y t n h vs

theorem storePresence_congr (X Y : α → Fam) (t : Tuple α) (j : Nat)
    (h : ∀ a (U : WorldT j), X a j U .undef ↔ Y a j U .undef) (ls : List (Option Nat)) :
    StorePresence (tupleFams X t) ls j ↔ StorePresence (tupleFams Y t) ls j := by
  cases ht : t.presence with
  | dense => simp [StorePresence, tupleFams, ht]
  | sparse => simp [StorePresence, tupleFams, ht]
  | readable =>
    simp only [StorePresence, show (tupleFams X t).presence = .readable from ht,
      show (tupleFams Y t).presence = .readable from ht, positionFam_tupleFams]
    constructor
    · intro hp i hi A hA U
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hA
      exact (h a U).mp (hp i hi (X a) (by simp [ha]) U)
    · intro hp i hi A hA U
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hA
      exact (h a U).mpr (hp i hi (Y a) (by simp [ha]) U)

/-- Position by position, a tuple contract's meaning depends on its labels'
meanings only below the budget, as a record's does. -/
theorem list_congr_below (X Y : α → Fam) (t : Tuple α) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    listT (tupleFams X t) n W v ↔ listT (tupleFams Y t) n W v := by
  constructor <;> rintro ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩ <;>
    simp only [listT, tupleFams, List.length_map, List.getElem?_map, Option.map_eq_none_iff,
      Option.map_eq_some_iff] at hlen hbound hreq hopt hrest ⊢ <;>
    refine ⟨ls, rfl, ?_, hlen, hbound, ?_, ?_, ?_⟩
  · intro j hj
    exact (storePresence_congr X Y t j (fun a U => h a j hj U .undef) ls).mp (hd j hj)
  · rintro i A ⟨a, ha, rfl⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (X a) ⟨a, ha, rfl⟩
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u)⟩
  · rintro i A l ⟨a, ha, rfl⟩ hl
    obtain ⟨c, hw, hag⟩ := hopt i (X a) l ⟨a, ha, rfl⟩ hl
    exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u)⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l hi hl
    exact ⟨Y e, c, ⟨e, he, rfl⟩, hw, fun j hj W' u => (hag j hj W' u).congr (h e j hj W' u)⟩
  · intro j hj
    exact (storePresence_congr X Y t j (fun a U => h a j hj U .undef) ls).mpr (hd j hj)
  · rintro i A ⟨a, ha, rfl⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (Y a) ⟨a, ha, rfl⟩
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u).symm⟩
  · rintro i A l ⟨a, ha, rfl⟩ hl
    obtain ⟨c, hw, hag⟩ := hopt i (Y a) l ⟨a, ha, rfl⟩ hl
    exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u).symm⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l hi hl
    exact ⟨X e, c, ⟨e, he, rfl⟩, hw, fun j hj W' u => (hag j hj W' u).congr (h e j hj W' u).symm⟩

theorem semWithArgs_congr {Ξ Ξ' : Fam} (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat)
    (hexc : Agree Ξ Ξ' n) (h : ∀ a, Agree (X a) (Y a) n)
    (hP : ∀ a, Agree (P a) (Q a) n) (c : Clause α) (W : WorldT n) (v : Val) :
    semWithArgs Ξ X P c n W v ↔ semWithArgs Ξ' Y Q c n W v := by
  cases c with
  | nul => rfl
  | bool => rfl
  | boolLit _ => rfl
  | num => rfl
  | numLit _ => rfl
  | str => rfl
  | strLit _ => rfl
  | bigint => rfl
  | bigintLit _ => rfl
  | symbol => rfl
  | symbolLit _ => rfl
  | undef => rfl
  | top | source => rfl
  | list a bs =>
    exact and_congr (list_congr_below X Y a n h W v) (forall_congr' fun b => forall_congr' fun _ => list_congr_below X Y b n h W v)
  | refs a bs vs os ms ks =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (views_congr_below X Y vs n h W v)
        (and_congr (opt_congr_below X Y os n h W v)
          (and_congr (methodT_congr X Y P Q n hexc h hP ms W v) Iff.rfl)))
  | dict a bs vs ds os ms ks cs =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (views_congr_below X Y vs n h W v)
        (and_congr (and_congr (forall_congr' fun d => forall_congr' fun _ => dictViewT_congr (h d.2) W v)
            (forall_congr' fun d => forall_congr' fun _ => dictCellT_congr (h d.2) W v))
          (and_congr (opt_congr_below X Y os n h W v)
            (and_congr (methodT_congr X Y P Q n hexc h hP ms W v) Iff.rfl))))
  | arrs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (CallEffects.callsT_congr L (Arrow.map X) (Arrow.map Y) hexc (fun _ _ => rfl)
      (fun p _ => ⟨h p.receiver, hd p.arguments, h p.result⟩) W v)
      (CallEffects.restsT_congr S (RestArrow.mapWith X P) (RestArrow.mapWith Y Q) hexc (fun _ _ => rfl)
        (fun s _ => ⟨h s.receiver, hd s.arguments.1, hP s.arguments.2, h s.result⟩) W v)
  | callable a bs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (CallableConjunctions.congr_below X Y a bs L n hexc h W v)
      (CallEffects.restsT_congr S (RestArrow.mapWith X P) (RestArrow.mapWith Y Q) hexc (fun _ _ => rfl)
        (fun s _ => ⟨h s.receiver, hd s.arguments.1, hP s.arguments.2, h s.result⟩) W v)
  | ctors L S a bs vs =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (and_congr (ctorsT_congr L _ _ hexc (fun p _ => ⟨hd p.1, h p.2⟩) W v)
      (ctorRestsT_congr S _ _ hexc (fun s _ => ⟨hd s.1, hP s.2.1, h s.2.2⟩) W v))
      (and_congr (CallableConjunctions.props_congr_below X Y a bs n h W v)
        (CallableConjunctions.views_congr_below X Y vs n h W v))
  | pack a bs => rfl

/-! ## Renaming operands

`Clause.map` renames every operand; the meaning of a renamed clause is the
clause read through the renaming (`semWithArgs_map`). A renaming fixing every operand
changes nothing (`map_of_operands`). -/

def Tuple.map (f : α → β) (t : Tuple α) : Tuple β :=
  ⟨t.required.map f, t.optional.map f, t.rest.map f, t.readonly, t.presence⟩

def Tuple.operands (t : Tuple α) : List α := t.required ++ t.optional ++ t.rest.toList

def mapFields {κ : Type} (f : α → β) (fs : List (κ × α)) : List (κ × β) :=
  fs.map fun q => (q.1, f q.2)

def Clause.map (f : α → β) : Clause α → Clause β
  | .top => .top
  | .source => .source
  | .nul => .nul
  | .undef => .undef
  | .bool => .bool
  | .boolLit b => .boolLit b
  | .num => .num
  | .numLit v => .numLit v
  | .str => .str
  | .strLit v => .strLit v
  | .bigint => .bigint
  | .bigintLit v => .bigintLit v
  | .symbol => .symbol
  | .symbolLit v => .symbolLit v
  | .list a bs => .list (a.map f) (bs.map (·.map f))
  | .refs a bs vs os ms ks => .refs (mapFields f a) (bs.map (mapFields f)) (mapFields f vs)
      (os.map (·.map f)) (ms.map (Sig.map f)) ks
  | .dict a bs vs ds os ms ks cs => .dict (mapFields f a) (bs.map (mapFields f)) (mapFields f vs)
      (mapFields f ds) (os.map (·.map f)) (ms.map (Sig.map f)) ks (mapFields f cs)
  | .arrs L S => .arrs (L.map (Arrow.map f))
      (S.map (RestArrow.map f))
  | .callable a bs L S => .callable (mapFields f a) (bs.map (mapFields f))
      (L.map (Arrow.map f))
      (S.map (RestArrow.map f))
  | .ctors L S a bs vs => .ctors (L.map fun q => (q.1.map f, f q.2))
      (S.map fun q => (q.1.map f, f q.2.1, f q.2.2)) (mapFields f a) (bs.map (mapFields f))
      (mapFields f vs)
  | .pack a bs => .pack (a.map f) (bs.map (·.map f))

/-- Renaming operands keeps a clause a record's or not. -/
@[simp] theorem Clause.record_map (f : α → β) (c : Clause α) : (c.map f).record = c.record := by
  cases c <;> rfl

theorem Clause.carriesInvariant_of_record {c : Clause α} (h : c.record = true) : c.carriesInvariant = true := by
  cases c <;> simp_all [Clause.record, Clause.carriesInvariant]

@[simp] theorem Clause.carriesInvariant_map (f : α → β) (c : Clause α) : (c.map f).carriesInvariant = c.carriesInvariant := by
  cases c <;> rfl

/-- A clause of a meet the built-ins' invariant applies to comes from an operand
it applies to. -/
theorem carriesInvariant_of_meet {a b d : Clause α} (h : d ∈ meet a b) (hd : d.carriesInvariant = true) :
    a.carriesInvariant = true ∨ b.carriesInvariant = true := by
  cases a <;> cases b <;> unfold meet at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h <;>
    (try split at h) <;> (try simp only [List.mem_singleton, List.not_mem_nil] at h) <;>
    (try subst h) <;> simp_all [Clause.carriesInvariant]

/-- Only top meets top in top. -/
theorem top_of_meet {a b : Clause α} (h : Clause.top ∈ meet a b) : a = .top ∧ b = .top := by
  cases a <;> cases b <;> unfold meet at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h <;>
    (try split at h) <;> (try simp only [List.mem_singleton, List.not_mem_nil] at h) <;>
    simp_all

/-- A member of a clause other than top that the built-ins' invariant does not
apply to is no plain object: its shape is a primitive's, a store's or a
callable's. -/
theorem semWithArgs_not_plain {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : c ≠ .top) (hr : c.carriesInvariant = false) (h : semWithArgs Ξ X P c n W v) :
    ∀ flds oid, v ≠ .objAt flds .absent oid := by
  intro flds oid he
  subst he
  have hs := semWithArgs_shape hc (by rintro rfl; cases hr) h
  cases c <;> simp_all [valueShape, shape, Clause.carriesInvariant]

/-- Every operand of a clause. -/
def Clause.operands : Clause α → List α
  | .list a bs => a.operands ++ bs.flatMap Tuple.operands
  | .refs a bs vs os ms _ => (a ++ bs.flatten ++ vs).map (·.2) ++ os.map (·.type) ++
      ms.flatMap Sig.operands
  | .dict a bs vs ds os ms _ cs => (a ++ bs.flatten ++ vs).map (·.2) ++ os.map (·.type) ++
      ds.map (·.2) ++ ms.flatMap Sig.operands ++ cs.map (·.2)
  | .arrs L S => L.flatMap Arrow.operands ++
      S.flatMap RestArrow.operands
  | .callable a bs L S => (a ++ bs.flatten).map (·.2) ++
      L.flatMap Arrow.operands ++
      S.flatMap RestArrow.operands
  | .ctors L S a bs vs => L.flatMap (fun q => q.1 ++ [q.2]) ++ S.flatMap (fun q => q.1 ++ [q.2.1, q.2.2]) ++
      (a ++ bs.flatten ++ vs).map (·.2)
  | .pack a bs => a.operands ++ bs.flatMap Tuple.operands
  | _ => []

private theorem famsOf_fun (X : α → Fam) :
    famsOf X = fun fs => fs.map fun p => (p.1, X p.2) := rfl

theorem tupleFams_map (Y : β → Fam) (f : α → β) (t : Tuple α) :
    tupleFams Y (t.map f) = tupleFams (fun a => Y (f a)) t := by
  simp [tupleFams, Tuple.map, Function.comp_def]

/-- Operand substitution transports value and list operands independently.
-/
theorem semWithArgs_map (Y : β → Fam) (P : β → ArgFam) (f : α → β) (c : Clause α) :
    semWithArgs Ξ Y P (c.map f) = semWithArgs Ξ (fun a => Y (f a)) (fun a => P (f a)) c := by
  cases c
  case dict =>
    simp only [semWithArgs, Clause.map, mapFields, List.forall_mem_map]
    simp [mapFields, famsOf_fun, Function.comp_def, Member.of_map, OptionalField.map]
  all_goals simp [semWithArgs, Clause.map, mapFields, famsOf_fun, tupleFams, Tuple.map, Function.comp_def,
    Member.of_map, OptionalField.map, Arrow.map, RestArrow.map, RestArrow.mapWith, Contract.map] <;> rfl


/-- The same syntactic operand substitution preserves the argument component,
read at the current level. -/
theorem clauseArguments_map (Y : β → Fam) (f : α → β) (c : Clause α) :
    clauseArguments Y (c.map f) = clauseArguments (fun a => Y (f a)) c := by
  cases c <;> try rfl
  rename_i a bs
  funext n W vs
  apply propext
  simp [clauseArguments, Clause.map, tupleFams_map]

private theorem map_self {l : List α} {f : α → α} (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [h.1, ih h.2]

private theorem mapFields_self {κ : Type} {fs : List (κ × α)} {f : α → α}
    (h : ∀ a ∈ fs.map (·.2), f a = a) : mapFields f fs = fs :=
  map_self fun q hq => by
    have := h q.2 (List.mem_map_of_mem hq)
    simp [this]

private theorem opt_self {os : List (OptionalField α)} {f : α → α}
    (h : ∀ a ∈ os.map (·.type), f a = a) : os.map (·.map f) = os :=
  map_self fun q hq => by
    have := h q.type (List.mem_map_of_mem hq)
    simp [OptionalField.map, this]

private theorem tuple_self {t : Tuple α} {f : α → α} (h : ∀ a ∈ t.operands, f a = a) :
    t.map f = t := by
  obtain ⟨r, o, e, b⟩ := t
  simp only [Tuple.operands, List.mem_append] at h
  have h1 := map_self (l := r) fun a ha => h a (.inl (.inl ha))
  have h2 := map_self (l := o) fun a ha => h a (.inl (.inr ha))
  have h3 : e.map f = e := by cases e <;> simp_all
  simp [Tuple.map, h1, h2, h3]

private theorem sig_self {m : Sig α} {f : α → α} (h : ∀ a ∈ m.operands, f a = a) :
    m.map f = m := by
  obtain ⟨k, cs, rs, ss, os⟩ := m
  simp only [Sig.operands, List.mem_append, List.mem_flatMap] at h
  simp only [Sig.map, Sig.mk.injEq, true_and]
  refine ⟨?_, ?_, map_self fun a ha => h a (.inl (.inr ha)), map_self fun a ha => h a (.inr ha)⟩
  · exact map_self fun p hp => MethodArrow.map_of_operands fun x hx =>
      h x (.inl (.inl (.inl ⟨p, hp, hx⟩)))
  · exact map_self fun p hp => MethodRestArrow.map_of_operands fun x hx =>
      h x (.inl (.inl (.inr ⟨p, hp, hx⟩)))

/-- A renaming fixing every operand fixes the clause. -/
theorem map_of_operands {c : Clause α} {f : α → α} (h : ∀ a ∈ c.operands, f a = a) :
    c.map f = c := by
  cases c with
  | list a bs =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.list.injEq]
    exact ⟨tuple_self fun x hx => h x (.inl hx),
      map_self fun t ht => tuple_self fun x hx => h x (.inr ⟨t, ht, hx⟩)⟩
  | refs a bs vs os ms ks =>
    simp only [Clause.operands, List.map_append, List.mem_append] at h
    simp only [Clause.map, Clause.refs.injEq, and_true]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl hx)))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inl (.inr ?_)))),
      mapFields_self fun x hx => h x (.inl (.inl (.inr hx))),
      opt_self fun x hx => h x (.inl (.inr hx)),
      map_self fun m hm => sig_self fun x hx => h x (.inr (List.mem_flatMap.mpr ⟨m, hm, hx⟩))⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | dict a bs vs ds os ms ks cs =>
    simp only [Clause.operands, List.map_append, List.mem_append] at h
    simp only [Clause.map, Clause.dict.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl (.inl (.inl hx)))))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl (.inl (.inr ?_)))))),
      mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl (.inr hx))))),
      mapFields_self fun x hx => h x (.inl (.inl (.inr hx))),
      opt_self fun x hx => h x (.inl (.inl (.inl (.inr hx)))),
      map_self fun m hm => sig_self fun x hx => h x (.inl (.inr (List.mem_flatMap.mpr ⟨m, hm, hx⟩))),
      trivial, mapFields_self fun x hx => h x (.inr hx)⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | arrs L S =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.arrs.injEq]
    exact ⟨map_self fun p hp => Arrow.map_of_operands fun x hx => h x (.inl ⟨p, hp, hx⟩),
      map_self fun p hp => RestArrow.map_of_operands fun x hx => h x (.inr ⟨p, hp, hx⟩)⟩
  | callable a bs L S =>
    simp only [Clause.operands, List.map_append, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.callable.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl hx))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inr ?_))),
      map_self fun p hp => Arrow.map_of_operands fun x hx => h x (.inl (.inr ⟨p, hp, hx⟩)),
      map_self fun p hp => RestArrow.map_of_operands fun x hx => h x (.inr ⟨p, hp, hx⟩)⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | ctors L S a bs vs =>
    simp only [Clause.operands, List.map_append, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.ctors.injEq]
    refine ⟨map_self fun q hq => ?_, map_self fun q hq => ?_,
      mapFields_self fun x hx => h x (.inr (.inl (.inl hx))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inr (.inl (.inr ?_))),
      mapFields_self fun x hx => h x (.inr (.inr hx))⟩
    · have h2 := h q.2 (.inl (.inl ⟨q, hq, by simp⟩))
      have h1 := map_self (l := q.1) fun x hx => h x (.inl (.inl ⟨q, hq, by simp [hx]⟩))
      simp [h1, h2]
    · have h2 := h q.2.1 (.inl (.inr ⟨q, hq, by simp⟩))
      have h3 := h q.2.2 (.inl (.inr ⟨q, hq, by simp⟩))
      have h1 := map_self (l := q.1) fun x hx => h x (.inl (.inr ⟨q, hq, by simp [hx]⟩))
      simp [h1, h2, h3]
    · simp only [List.mem_map, List.mem_flatten] at hx ⊢
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | pack a bs =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.pack.injEq]
    exact ⟨tuple_self fun x hx => h x (.inl hx),
      map_self fun t ht => tuple_self fun x hx => h x (.inr ⟨t, ht, hx⟩)⟩
  | _ => rfl

end Verification.PositiveNormalization
