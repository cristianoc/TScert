import Verification.Types.GraphRows

/-! A finite presentation of an application-indexed graph. An application
retains its arguments, and a local parameter is identified by its owning
application and slot. Unfolding a row does not unfold the rows it references.
This module supplies graphs to the existing semantics, not another semantics.
-/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveNormalization CallEffects

structure Binder where
  name : String
  kind : ParameterKind
  deriving Repr, DecidableEq

/-- How an application may vary in one parameter (RECURSIVE-EQUATIONS §4.3):
covariantly, contravariantly, invariantly, or not at all because the body
does not read it. Computed and checked by the checker, never assumed. -/
inductive Variance where
  | co
  | contra
  | inv
  | none
  deriving Repr, DecidableEq

/-- The finite signature fixes both application arity and local binder kinds.
Binder names are only diagnostic metadata. `kinds` gives each parameter's
kind; variances are computed by the checker (`Variances`). -/
structure Header where
  parameters : Nat
  binders : List Binder
  kinds : List ParameterKind := []
  deriving Repr, DecidableEq

abbrev Signature := List Header

deriving instance Hashable for ParameterKind

-- Explicit mutually recursive spines let Lean derive executable equality.
-- They represent ordinary lists, not additional type-language constructs.
mutual
inductive Tree where
  | app (head : Nat) (args : Args)
  | bound (head : Nat) (args : Args) (slot : Nat)
  | argument (slot : Nat)
  | local (slot : Nat)
  /-- A family variable: a parameter owned by a family entry, not by an
  application, so no scheme binds it (RECURSIVE-EQUATIONS §7.1). It carries
  its kind. Templates cannot contain one. -/
  | var (owner : Nat) (slot : Nat) (kind : ParameterKind)
  /-- An intersection (RECURSIVE-EQUATIONS §3.3): it means exactly the
  intersection of its parts' values. No part is itself a meet. -/
  | meet (parts : Types)
  deriving Repr, DecidableEq, Hashable
inductive Types where
  | nil
  | cons (head : Tree) (tail : Types)
  deriving Repr, DecidableEq, Hashable
inductive Args where
  | nil
  | cons (head : Types) (tail : Args)
  deriving Repr, DecidableEq, Hashable
end

def Types.toList : Types → List Tree
  | .nil => []
  | .cons t ts => t :: ts.toList

@[simp] theorem Types.toList_nil : Types.nil.toList = [] := rfl
@[simp] theorem Types.toList_cons (t : Tree) (ts : Types) : (Types.cons t ts).toList = t :: ts.toList := rfl

private def kindOrder : ParameterKind → Nat
  | .value => 0
  | .arguments => 1
  | .packed => 2

/- A total order on trees, lexicographic on constructors and fields. It fixes
the canonical order of a meet's parts. -/
mutual
def Tree.cmp : Tree → Tree → Ordering
  | .app h a, .app h' a' => (compare h h').then (Args.cmp a a')
  | .app .., _ => .lt
  | _, .app .. => .gt
  | .bound h a i, .bound h' a' i' => (compare h h').then ((Args.cmp a a').then (compare i i'))
  | .bound .., _ => .lt
  | _, .bound .. => .gt
  | .meet ps, .meet ps' => Types.cmp ps ps'
  | .meet _, _ => .lt
  | _, .meet _ => .gt
  | .var o i k, .var o' i' k' =>
    (compare o o').then ((compare i i').then (compare (kindOrder k) (kindOrder k')))
  | .var .., _ => .lt
  | _, .var .. => .gt
  | .argument i, .argument i' => compare i i'
  | .argument _, _ => .lt
  | _, .argument _ => .gt
  | .local i, .local i' => compare i i'
def Types.cmp : Types → Types → Ordering
  | .nil, .nil => .eq
  | .nil, .cons .. => .lt
  | .cons .., .nil => .gt
  | .cons t ts, .cons t' ts' => (Tree.cmp t t').then (Types.cmp ts ts')
def Args.cmp : Args → Args → Ordering
  | .nil, .nil => .eq
  | .nil, .cons .. => .lt
  | .cons .., .nil => .gt
  | .cons t ts, .cons t' ts' => (Types.cmp t t').then (Args.cmp ts ts')
end

instance : Ord Tree := ⟨Tree.cmp⟩

/-- Tree equality with a pointer-equality fast path: shared subtrees compare
in constant time. Extensionally it is the derived equality (`Tree.beq_eq`);
`withPtrEq` is the standard `ptrEq` pattern and adds no axiom. -/
def Tree.beq (a b : Tree) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (fun h => decide_eq_true h)

@[simp] theorem Tree.beq_eq (a b : Tree) : Tree.beq a b = decide (a = b) := rfl

instance : BEq Tree := ⟨Tree.beq⟩

instance : LawfulBEq Tree where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Whether a tree is a meet. -/
def Tree.isMeet : Tree → Bool
  | .meet _ => true
  | _ => false

/-- A meet's parts, or the tree itself: flattening one level. -/
def Tree.meetParts : Tree → List Tree
  | .meet ps => ps.toList
  | t => [t]


def Args.toList : Args → List Types
  | .nil => []
  | .cons t ts => t :: ts.toList

def Types.ofList : List Tree → Types
  | [] => .nil
  | t :: ts => .cons t (ofList ts)

def Args.ofList : List Types → Args
  | [] => .nil
  | t :: ts => .cons t (ofList ts)

@[simp] theorem Types.toList_ofList (ts : List Tree) : (ofList ts).toList = ts := by
  induction ts <;> simp_all [ofList]

@[simp] theorem Args.toList_ofList (ts : List Types) : (ofList ts).toList = ts := by
  induction ts <;> simp_all [ofList, toList]

private def arityOk (sig : Signature) (head : Nat) (args : Args) : Bool :=
  sig[head]?.any fun h => args.toList.length == h.parameters

private def binderOk (sig : Signature) (head slot : Nat) : Bool :=
  sig[head]?.any fun h => slot < h.binders.length

/- Scope checks apply at every nested application. Closed labels have no
argument or local placeholders: only a well-scoped equation may contain them. -/
mutual
def Tree.scoped (sig : Signature) (parameters locals : Nat) : Tree → Bool
  | .app h args => arityOk sig h args && args.scoped sig parameters locals
  | .bound h args i => arityOk sig h args && binderOk sig h i && args.scoped sig parameters locals
  | .argument i => i < parameters
  | .local i => i < locals
  | .var .. => true
  | .meet ps => ps.scoped sig parameters locals && ps.toList.all fun t => !t.isMeet
def Types.scoped (sig : Signature) (parameters locals : Nat) : Types → Bool
  | .nil => true
  | .cons t ts => t.scoped sig parameters locals && ts.scoped sig parameters locals
def Args.scoped (sig : Signature) (parameters locals : Nat) : Args → Bool
  | .nil => true
  | .cons t ts => t.scoped sig parameters locals && ts.scoped sig parameters locals
end

/- Templates capture parameter references through their argument environment.
They cannot manufacture a parameter belonging to some other application. -/
mutual
def Tree.lexical (locals : Bool) : Tree → Bool
  | .app _ args => args.lexical locals
  | .bound .. => false
  | .argument _ => true
  | .local _ => locals
  | .var .. => false
  | .meet ps => ps.lexical locals
def Types.lexical (locals : Bool) : Types → Bool
  | .nil => true
  | .cons t ts => t.lexical locals && ts.lexical locals
def Args.lexical (locals : Bool) : Args → Bool
  | .nil => true
  | .cons t ts => t.lexical locals && ts.lexical locals
end

abbrev Label (sig : Signature) := { t : Tree // t.scoped sig 0 0 = true }
abbrev Expression (sig : Signature) (h : Header) :=
  { t : Tree // t.scoped sig h.parameters h.binders.length = true ∧ t.lexical true = true }

/-- Unlike a type operand, a binding position cannot name a parameter's union. -/
def Tree.single : Tree → Bool
  | .argument _ | .var .. | .meet _ => false
  | .app .. | .bound .. | .local .. => true

abbrev Reference (sig : Signature) (h : Header) :=
  { e : Expression sig h // e.1.single = true }

/-- Arguments are already closed labels, and arity is a construction premise.
The same scope creates both its application label and its bound parameters. -/
structure Scope (sig : Signature) where
  head : Fin sig.length
  arguments : List (List (Label sig))
  arity : arguments.length = sig[head].parameters

def Scope.rawArgs (scope : Scope sig) : Args :=
  Args.ofList (scope.arguments.map fun ts => Types.ofList (ts.map Subtype.val))

private theorem Types.scoped_of_labels (ts : List (Label sig)) :
    (Types.ofList (ts.map Subtype.val)).scoped sig 0 0 = true := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, Types.ofList, Types.scoped, t.2, ih, Bool.and_self]

private theorem Scope.args_closed (scope : Scope sig) :
    scope.rawArgs.scoped sig 0 0 = true := by
  unfold rawArgs
  induction scope.arguments with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, Args.ofList, Args.scoped, Types.scoped_of_labels, ih, Bool.and_self]

private theorem Scope.arity_ok (scope : Scope sig) :
    arityOk sig scope.head.val scope.rawArgs = true := by
  simp [arityOk, rawArgs, scope.arity]

def Scope.label (scope : Scope sig) : Label sig :=
  ⟨.app scope.head.val scope.rawArgs, by
    simp [Tree.scoped, scope.arity_ok, scope.args_closed]⟩

def Scope.bound (scope : Scope sig) (slot : Fin sig[scope.head].binders.length) : Label sig :=
  ⟨.bound scope.head.val scope.rawArgs slot.val, by
    simp [Tree.scoped, scope.arity_ok, scope.args_closed, binderOk]⟩

/-- A scope's local parameters in their declared order. -/
def Scope.binders (scope : Scope sig) : List (Label sig) :=
  (List.finRange sig[scope.head].binders.length).map scope.bound

@[simp] theorem Scope.binders_length (scope : Scope sig) :
    scope.binders.length = sig[scope.head].binders.length := by simp [binders]

@[simp] theorem Scope.mem_binders {scope : Scope sig} {p : Label sig} :
    p ∈ scope.binders ↔ ∃ slot, p = scope.bound slot := by
  simp [binders, eq_comm]

theorem Scope.bound_injective (scope : Scope sig) : Function.Injective scope.bound := by
  intro a b h
  have he := congrArg Subtype.val h
  simp only [bound, Tree.bound.injEq] at he
  exact Fin.ext he.2.2

theorem Scope.binders_nodup (scope : Scope sig) : scope.binders.Nodup :=
  (List.nodup_finRange _).map scope.bound (fun _ _ h he => h (scope.bound_injective he))

/-- Concatenating unions does not inspect or unfold their labels. -/
def Types.append : Types → Types → Types
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

theorem Types.scoped_append (xs ys : Types)
    (hx : xs.scoped sig p l = true) (hy : ys.scoped sig p l = true) :
    (xs.append ys).scoped sig p l = true := by
  cases xs with
  | nil => exact hy
  | cons x xs =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨h1, scoped_append xs ys h2 hy⟩

/-- The canonical meet of trees (RECURSIVE-EQUATIONS §3.3): a part that is
itself a meet is flattened, and the parts are sorted and deduplicated.
The meet wrapper remains even for one part: `meet(L)` contains only values,
whereas `L` may also admit argument lists. -/
def canonMeet (ts : List Tree) : Tree :=
  .meet (Types.ofList ((ts.flatMap Tree.meetParts).mergeSort fun a b => compare a b != .gt).eraseDups)

/-- Every choice of one member from each list, in order: distribution of a
meet over unions. -/
def choices : List (List α) → List (List α)
  | [] => [[]]
  | A :: rest => A.flatMap fun a => (choices rest).map (a :: ·)

theorem mem_choices {As : List (List α)} {c : List α} :
    c ∈ choices As ↔ c.length = As.length ∧ ∀ i (hc : i < c.length) (hA : i < As.length), c[i] ∈ As[i] := by
  induction As generalizing c with
  | nil => cases c <;> simp [choices]
  | cons A rest ih =>
    cases c with
    | nil => simp [choices]
    | cons a c =>
      simp only [choices, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons,
        Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨a', ha', c', hc', rfl, rfl⟩
        obtain ⟨hl, hc⟩ := ih.mp hc'
        refine ⟨hl, fun i hi hj => ?_⟩
        cases i with
        | zero => simpa using ha'
        | succ i =>
          have := hc i (by simpa using hi) (by simpa using hj)
          simpa only [List.getElem_cons_succ] using this
      · rintro ⟨hl, hc⟩
        refine ⟨a, by simpa using hc 0 (by simp) (by simp), c, ih.mpr ⟨hl, fun i hi hj => ?_⟩, rfl, rfl⟩
        have := hc (i + 1) (by simpa using hi) (by simpa using hj)
        simpa only [List.getElem_cons_succ] using this

/-- A property holds of some choice's members exactly when each list has a
member with it. -/
theorem exists_choice {As : List (List α)} {P : α → Prop} :
    (∃ c ∈ choices As, ∀ x ∈ c, P x) ↔ ∀ A ∈ As, ∃ x ∈ A, P x := by
  induction As with
  | nil => simp [choices]
  | cons A rest ih =>
    simp only [choices, List.mem_flatMap, List.mem_map, List.forall_mem_cons]
    constructor
    · rintro ⟨_, ⟨a, ha, c, hc, rfl⟩, hp⟩
      simp only [List.forall_mem_cons] at hp
      exact ⟨⟨a, ha, hp.1⟩, ih.mp ⟨c, hc, hp.2⟩⟩
    · rintro ⟨⟨a, ha, hpa⟩, hr⟩
      obtain ⟨c, hc, hp⟩ := ih.mpr hr
      refine ⟨a :: c, ⟨a, ha, c, hc, rfl⟩, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpa
      · exact hp x hx

theorem Types.scoped_iff : ∀ {ts : Types},
    ts.scoped sig p l = true ↔ ∀ t ∈ ts.toList, t.scoped sig p l = true
  | .nil => by simp [Types.scoped]
  | .cons t ts => by simp [Types.scoped, Types.scoped_iff (ts := ts)]

theorem Types.scoped_ofList' {ts : List Tree} :
    (Types.ofList ts).scoped sig p l = true ↔ ∀ t ∈ ts, t.scoped sig p l = true := by
  rw [Types.scoped_iff, Types.toList_ofList]

/-- A canonical meet of scoped trees is scoped: its parts are scoped and none
is a meet. -/
theorem Tree.scoped_canonMeet (ts : List Tree) (h : ∀ t ∈ ts, t.scoped sig p l = true) :
    (canonMeet ts).scoped sig p l = true := by
  have parts : ∀ t ∈ ts, ∀ u ∈ t.meetParts, u.scoped sig p l = true ∧ u.isMeet = false := by
    intro t ht u hu
    cases t with
    | meet ps =>
      have hv := h _ ht
      simp only [Tree.scoped, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hv
      exact ⟨Types.scoped_iff.mp hv.1 u hu, hv.2 u hu⟩
    | _ =>
      simp only [Tree.meetParts, List.mem_singleton] at hu
      subst hu
      exact ⟨h _ ht, rfl⟩
  simp only [canonMeet, Tree.scoped, Bool.and_eq_true, Types.toList_ofList, List.all_eq_true,
    List.mem_eraseDups, List.mem_mergeSort, Bool.not_eq_true']
  refine ⟨Types.scoped_ofList'.mpr fun u hu => ?_, fun u hu => ?_⟩
  all_goals
    obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp (by simpa only [List.mem_eraseDups, List.mem_mergeSort] using hu)
    first | exact (parts t ht u hu).1 | exact (parts t ht u hu).2

abbrev ClosedTypes (sig : Signature) := { ts : Types // ts.scoped sig 0 0 = true }

/-- The canonical meet of closed labels, itself a closed label. -/
def Label.meetOf (c : List (Label sig)) : Label sig :=
  ⟨canonMeet (c.map Subtype.val), Tree.scoped_canonMeet _ fun u hu => by
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hu
    exact l.2⟩

/-- Recover the closed labels of a union, retaining each scope proof. -/
def Types.labels (ts : Types) (valid : ts.scoped sig 0 0 = true) : List (Label sig) :=
  match ts with
  | .nil => []
  | .cons t ts => ⟨t, (Bool.and_eq_true_iff.mp valid).1⟩ :: ts.labels (Bool.and_eq_true_iff.mp valid).2

/- Instantiation traverses the finite expression, never its referenced
rows. The result is closed by construction; missing arguments are impossible
under the expression's scope proof and the application's arity proof. -/
mutual
def Tree.instantiate (scope : Scope sig) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    ClosedTypes sig :=
  match t with
  | .app h args =>
    let a := Args.instantiate scope args (Bool.and_eq_true_iff.mp valid).2
    ⟨.cons (.app h a.1) .nil, by
      have ha := (Bool.and_eq_true_iff.mp valid).1
      have : arityOk sig h a.1 = true := by simpa [arityOk, a.2.2] using ha
      simp [Types.scoped, Tree.scoped, this, a.2.1]⟩
  | .bound h args i =>
    let a := Args.instantiate scope args (Bool.and_eq_true_iff.mp valid).2
    ⟨.cons (.bound h a.1 i) .nil, by
      have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
      have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
      have : arityOk sig h a.1 = true := by simpa [arityOk, a.2.2] using ha
      simp [Types.scoped, Tree.scoped, this, hb, a.2.1]⟩
  | .argument i =>
    have hi : i < scope.arguments.length := by
      have : i < sig[scope.head].parameters := of_decide_eq_true valid
      simpa only [scope.arity] using this
    ⟨Types.ofList (scope.arguments[i].map Subtype.val), Types.scoped_of_labels _⟩
  | .local i =>
    let b := scope.bound ⟨i, of_decide_eq_true valid⟩
    ⟨.cons b.1 .nil, by simp [Types.scoped, b.2]⟩
  | .var o i k => ⟨.cons (.var o i k) .nil, by simp [Types.scoped, Tree.scoped]⟩
  | .meet parts =>
    -- Intersection distributes over the parts' unions: one canonical meet
    -- per choice of a label from each part.
    let ps := Types.instantiateParts scope parts (Bool.and_eq_true_iff.mp valid).1
    ⟨Types.ofList (((choices ps).map Label.meetOf).map Subtype.val),
      Types.scoped_ofList'.mpr fun t ht => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp ht
        exact l.2⟩
/-- Each part of a meet instantiated to its union of closed labels. -/
def Types.instantiateParts (scope : Scope sig) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    List (List (Label sig)) :=
  match ts with
  | .nil => []
  | .cons t ts =>
    let a := Tree.instantiate scope t (Bool.and_eq_true_iff.mp valid).1
    a.1.labels a.2 :: Types.instantiateParts scope ts (Bool.and_eq_true_iff.mp valid).2
def Types.instantiate (scope : Scope sig) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    ClosedTypes sig :=
  match ts with
  | .nil => ⟨.nil, rfl⟩
  | .cons t ts =>
    let a := Tree.instantiate scope t (Bool.and_eq_true_iff.mp valid).1
    let b := Types.instantiate scope ts (Bool.and_eq_true_iff.mp valid).2
    ⟨a.1.append b.1, Types.scoped_append _ _ a.2 b.2⟩
def Args.instantiate (scope : Scope sig) (args : Args)
    (valid : args.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true) :
    { out : Args // out.scoped sig 0 0 = true ∧ out.toList.length = args.toList.length } :=
  match args with
  | .nil => ⟨.nil, by simp [Args.scoped, Args.toList]⟩
  | .cons ts args =>
    let a := Types.instantiate scope ts (Bool.and_eq_true_iff.mp valid).1
    let b := Args.instantiate scope args (Bool.and_eq_true_iff.mp valid).2
    ⟨.cons a.1 b.1, by
      simp [Args.scoped, Args.toList, a.2, b.2.1, b.2.2]⟩
end

theorem Types.labels_append (xs ys : Types) (hx : xs.scoped sig 0 0 = true)
    (hy : ys.scoped sig 0 0 = true) (hxy : (xs.append ys).scoped sig 0 0 = true) :
    (xs.append ys).labels hxy = xs.labels hx ++ ys.labels hy := by
  cases xs with
  | nil => rfl
  | cons t ts =>
    simp only [append, labels, List.cons_append,
      labels_append ts ys (Bool.and_eq_true_iff.mp hx).2 hy]

@[simp] theorem Types.labels_length (ts : Types) (valid : ts.scoped sig 0 0 = true) :
    (ts.labels valid).length = ts.toList.length := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [labels, toList, List.length_cons,
      labels_length ts (Bool.and_eq_true_iff.mp valid).2]

def Expression.instantiate (scope : Scope sig) (e : Expression sig sig[scope.head]) : List (Label sig) :=
  let out := Tree.instantiate scope e.1 e.2.1
  out.1.labels out.2

private theorem Tree.instantiate_single (scope : Scope sig) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (single : t.single = true) :
    (Tree.instantiate scope t valid).1.toList.length = 1 := by
  cases t <;> simp_all [Tree.single, Tree.instantiate, Types.toList]

/-- A binding reference denotes exactly one closed label, never the first
member of a union or a fallback for a missing argument. -/
def Reference.instantiate (scope : Scope sig) (r : Reference sig sig[scope.head]) : Label sig :=
  let out := r.1.instantiate scope
  have hlen : out.length = 1 := by
    simp only [out, Expression.instantiate, Types.labels_length]
    exact Tree.instantiate_single scope r.1.1 r.1.2.1 r.2
  out[0]'(by omega)

/-- A constructor-headed equation row, before checking its binder interface.
Type operands may expand a parameter's union; binding positions remain single
references. Non-constructor source aliases must be normalized by the compiler. -/
abbrev RowTemplate (sig : Signature) (head : Fin sig.length) :=
  GraphRow (Reference sig sig[head]) (List (Expression sig sig[head]))

/-- Only a scheme introduces local parameters, exactly those in its header.
Its bounds are read outside those parameters. Parameter and dependent-meet
rows are not declaration heads: parameters come from a scope; intersections
require normalization rather than pretending an arbitrary argument is rigid. -/
def RowTemplate.wellBound (head : Fin sig.length) : RowTemplate sig head → Bool
  | .clauses _ => sig[head].binders.isEmpty
  | .scheme bs _ bounds _ _ _ =>
    decide (bs.map (fun b => b.1.1) = (List.range sig[head].binders.length).map Tree.local) &&
      bounds.all (fun (b, T) => (bs.any fun p => decide (p = b)) &&
        T.all (fun t => t.1.lexical false))
  | .param .. | .meet .. => false

abbrev Template (sig : Signature) (head : Fin sig.length) :=
  { body : RowTemplate sig head // body.wellBound head = true }

def Template.instantiate (scope : Scope sig) (body : Template sig scope.head) : GraphRow (Label sig) :=
  body.1.map (Reference.instantiate scope) (fun ts => ts.flatMap (Expression.instantiate scope))

def Args.labels (args : Args) (valid : args.scoped sig 0 0 = true) : List (List (Label sig)) :=
  match args with
  | .nil => []
  | .cons ts args => ts.labels (Bool.and_eq_true_iff.mp valid).1 ::
      args.labels (Bool.and_eq_true_iff.mp valid).2

@[simp] theorem Args.labels_length (args : Args) (valid : args.scoped sig 0 0 = true) :
    (args.labels valid).length = args.toList.length := by
  cases args with
  | nil => rfl
  | cons ts args => simp only [labels, toList, List.length_cons,
      labels_length args (Bool.and_eq_true_iff.mp valid).2]

theorem Types.labels_ofList (ts : List (Label sig))
    (valid : (ofList (ts.map Subtype.val)).scoped sig 0 0 = true) :
    (ofList (ts.map Subtype.val)).labels valid = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, ofList, labels, ih]

private theorem Args.labels_ofList (args : List (List (Label sig)))
    (valid : (ofList (args.map fun ts => Types.ofList (ts.map Subtype.val))).scoped sig 0 0 = true) :
    (ofList (args.map fun ts => Types.ofList (ts.map Subtype.val))).labels valid = args := by
  induction args with
  | nil => rfl
  | cons ts args ih => simp only [List.map_cons, ofList, labels, Types.labels_ofList, ih]

private theorem Scope.labels_rawArgs (scope : Scope sig)
    (valid : scope.rawArgs.scoped sig 0 0 = true) :
    scope.rawArgs.labels valid = scope.arguments := Args.labels_ofList scope.arguments valid

private theorem arityOk_exists (valid : arityOk sig head args = true) : head < sig.length := by
  by_cases h : head < sig.length
  · exact h
  · have : sig[head]? = none := List.getElem?_eq_none (by omega)
    simp [arityOk, this] at valid

/-- Reading a closed application recovers the very same scope that built it;
no argument is inferred again or replaced by a default. -/
def Scope.ofRaw (head : Nat) (args : Args) (arity : arityOk sig head args = true)
    (closed : args.scoped sig 0 0 = true) : Scope sig :=
  { head := ⟨head, arityOk_exists arity⟩
    arguments := args.labels closed
    arity := by simpa [arityOk, arityOk_exists arity] using arity }

@[ext] theorem Scope.ext {a b : Scope sig} (hhead : a.head = b.head)
    (hargs : a.arguments = b.arguments) : a = b := by
  cases a
  cases b
  cases hhead
  cases hargs
  rfl

@[simp] theorem Scope.ofRaw_rawArgs (scope : Scope sig)
    (ha : arityOk sig scope.head.val scope.rawArgs = true)
    (hc : scope.rawArgs.scoped sig 0 0 = true) :
    Scope.ofRaw scope.head.val scope.rawArgs ha hc = scope := by
  apply Scope.ext
  · apply Fin.ext; rfl
  · exact scope.labels_rawArgs hc

/-- A family variable as a closed label. -/
def Label.familyVar (owner slot : Nat) (kind : ParameterKind) : Label sig :=
  ⟨.var owner slot kind, rfl⟩

/-- Whether a label is a family variable. -/
def Label.isVariable (label : Label sig) : Bool :=
  match label.1 with
  | .var .. => true
  | _ => false

inductive View (sig : Signature) where
  | application (scope : Scope sig)
  | parameter (scope : Scope sig) (slot : Fin sig[scope.head].binders.length)
  | familyVar (owner slot : Nat) (kind : ParameterKind)
  | meet (parts : List (Label sig))

def Label.view (label : Label sig) : View sig :=
  match label with
  | ⟨.app h args, valid⟩ =>
    .application (Scope.ofRaw h args (Bool.and_eq_true_iff.mp valid).1 (Bool.and_eq_true_iff.mp valid).2)
  | ⟨.bound h args i, valid⟩ =>
    let ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
    let hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
    let scope := Scope.ofRaw h args ha (Bool.and_eq_true_iff.mp valid).2
    .parameter scope ⟨i, by simpa [binderOk, scope, Scope.ofRaw, arityOk_exists ha] using hb⟩
  | ⟨.var o i k, _⟩ => .familyVar o i k
  | ⟨.meet ps, valid⟩ => .meet (ps.labels (Bool.and_eq_true_iff.mp valid).1)
  | ⟨.argument _, valid⟩ => False.elim (by simp [Tree.scoped] at valid)
  | ⟨.local _, valid⟩ => False.elim (by simp [Tree.scoped] at valid)

@[simp] theorem Scope.view_label (scope : Scope sig) : scope.label.view = .application scope := by
  simp [label, Label.view]

@[simp] theorem Scope.view_bound (scope : Scope sig) (slot : Fin sig[scope.head].binders.length) :
    (scope.bound slot).view = .parameter scope slot := by
  simp [bound, Label.view, Scope.ofRaw, Scope.labels_rawArgs]
  apply Fin.ext
  rfl

@[simp] theorem Label.view_familyVar (owner slot : Nat) (kind : ParameterKind) :
    (Label.familyVar owner slot kind : Label sig).view = .familyVar owner slot kind := rfl

theorem Types.labels_val (ts : Types) (valid : ts.scoped sig 0 0 = true) :
    Types.ofList ((ts.labels valid).map Subtype.val) = ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [labels, List.map_cons, ofList,
      labels_val ts (Bool.and_eq_true_iff.mp valid).2]

private theorem Args.labels_val (args : Args) (valid : args.scoped sig 0 0 = true) :
    Args.ofList ((args.labels valid).map fun ts => Types.ofList (ts.map Subtype.val)) = args := by
  cases args with
  | nil => rfl
  | cons ts args => simp only [labels, List.map_cons, ofList, Types.labels_val,
      labels_val args (Bool.and_eq_true_iff.mp valid).2]

theorem Scope.ofRaw_args (head : Nat) (args : Args) (ha hc) :
    (Scope.ofRaw (sig := sig) head args ha hc).rawArgs = args := by
  exact Args.labels_val args hc

/-- Every closed label is an application, one of its owned parameters, a
family variable or a meet. -/
theorem Label.cases {P : Label sig → Prop} (label : Label sig)
    (app : ∀ scope : Scope sig, P scope.label)
    (bound : ∀ (scope : Scope sig) slot, P (scope.bound slot))
    (family : ∀ owner slot kind, P (Label.familyVar owner slot kind))
    (meet : ∀ parts valid, P ⟨.meet parts, valid⟩) : P label := by
  rcases label with ⟨t, valid⟩
  cases t with
  | app h args =>
    let scope := Scope.ofRaw h args (Bool.and_eq_true_iff.mp valid).1 (Bool.and_eq_true_iff.mp valid).2
    have he : scope.label = (⟨.app h args, valid⟩ : Label sig) := by
      apply Subtype.ext
      simp only [scope, Scope.label, Scope.ofRaw_args]
      rfl
    exact he ▸ app scope
  | bound h args i =>
    let scope := Scope.ofRaw h args (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
      (Bool.and_eq_true_iff.mp valid).2
    have slot : i < sig[scope.head].binders.length := by
      have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
      have hh := arityOk_exists (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
      simpa [binderOk, scope, Scope.ofRaw, hh] using hb
    have he : scope.bound ⟨i, slot⟩ = (⟨.bound h args i, valid⟩ : Label sig) := by
      apply Subtype.ext
      simp only [scope, Scope.bound, Scope.ofRaw_args]
      rfl
    exact he ▸ bound scope ⟨i, slot⟩
  | var o i k => exact family o i k
  | meet ps => exact meet ps valid
  | argument i => simp [Tree.scoped] at valid
  | «local» i => simp [Tree.scoped] at valid

/-- A finite list of templates presents every application at its arguments.
There is no depth, colour or unfolding budget in the graph definition. -/
structure Equations where
  signature : Signature
  body : (head : Fin signature.length) → Template signature head
  builtins : Option (ArrayBuiltins (Label signature)) := none
  domain : SchemeDomain (Label signature) .mixed := .ordinary

/-- The row of a label that is not a meet. -/
def Equations.baseRow (equations : Equations) (label : Label equations.signature) :
    GraphRow (Label equations.signature) :=
  match label.view with
  | .application scope => (equations.body scope.head).instantiate scope
  | .parameter scope slot =>
    let b := equations.signature[scope.head].binders[slot]
    .param label b.name b.kind
  | .familyVar _ _ kind => .param label "var" kind
  | .meet _ => .clauses []

/-- Whether a clause can hold a value: an argument-list clause cannot. -/
def Clause.isValue : Clause α → Bool
  | .pack .. => false
  | _ => true

/-- The normalized conjunction of clause lists (`meetLists`); of none, every
value. -/
def meetAll : List (List (Clause α)) → List (Clause α)
  | [] => [.top]
  | A :: rest => meetLists A (meetAll rest)

/-- A meet's parts whose rows are not clause rows: parameters and schemes. -/
def meetRigid : List (ι × GraphRow ι) → List ι
  | [] => []
  | (_, .clauses _) :: rest => meetRigid rest
  | (q, _) :: rest => q :: meetRigid rest

/-- A meet's clause parts' clauses. -/
def meetClauseLists : List (ι × GraphRow ι) → List (List (Clause (List ι)))
  | [] => []
  | (_, .clauses cs) :: rest => cs :: meetClauseLists rest
  | _ :: rest => meetClauseLists rest

/-- A property of a meet part: `Q` of a clause part's clauses, `P` of any
other part. -/
def partCase (P : ι → Prop) (Q : List (Clause (List ι)) → Prop) : ι × GraphRow ι → Prop
  | (_, .clauses cs) => Q cs
  | (q, _) => P q

/-- Reading a meet's parts is reading its rigid parts and its clause parts. -/
theorem meet_partition (parts : List (ι × GraphRow ι)) (P : ι → Prop)
    (Q : List (Clause (List ι)) → Prop) :
    ((∀ q ∈ meetRigid parts, P q) ∧ ∀ C ∈ meetClauseLists parts, Q C) ↔
      ∀ x ∈ parts, partCase P Q x := by
  induction parts with
  | nil => simp [meetRigid, meetClauseLists]
  | cons x rest ih =>
    obtain ⟨q, r⟩ := x
    rw [List.forall_mem_cons, ← ih]
    cases r <;> simp only [meetRigid, meetClauseLists, partCase, List.forall_mem_cons, and_assoc,
      and_left_comm]

/-- A meet label's row from its parts' rows (RECURSIVE-EQUATIONS §3.3): the
normalized conjunction of its clause parts' clauses, within its parameter and
scheme parts when it has any. A meet means values only: without such parts,
argument-list clauses are left out. -/
def meetRowOf [DecidableEq ι] (parts : List (ι × GraphRow ι)) : GraphRow ι :=
  match meetRigid parts with
  | [] => .clauses ((meetAll ((meetClauseLists parts).eraseDups)).filter Clause.isValue)
  | p :: ps => .meet p (meetAll ((meetClauseLists parts).eraseDups)) ps

/-- A label's row: a meet's is computed from its parts' rows, read at the
same level; no part is a meet, so this is one step, not a recursion. -/
def Equations.row (equations : Equations) (label : Label equations.signature) :
    GraphRow (Label equations.signature) :=
  match label.view with
  | .meet parts => meetRowOf (parts.map fun q => (q, equations.baseRow q))
  | _ => equations.baseRow label

def Equations.graph (equations : Equations) : NormalGraph (Label equations.signature) :=
  NormalGraph.ofRowMap equations.row equations.builtins equations.domain

/-- Unfolding an application substitutes into its one finite template. -/
@[simp] theorem Equations.row_application (equations : Equations) (scope : Scope equations.signature) :
    equations.row scope.label = (equations.body scope.head).instantiate scope := by
  simp [row, baseRow]

/-- A bound parameter has the kind declared at its own lexical owner. -/
@[simp] theorem Equations.kind_bound (equations : Equations) (scope : Scope equations.signature)
    (slot : Fin equations.signature[scope.head].binders.length) :
    equations.graph.parameterKinds (scope.bound slot) =
      some equations.signature[scope.head].binders[slot].kind := by
  simp [graph, NormalGraph.ofRowMap, row, baseRow]

/-- A family variable is a parameter row of the kind it carries. -/
@[simp] theorem Equations.kind_familyVar (equations : Equations) (owner slot : Nat)
    (kind : ParameterKind) :
    equations.graph.parameterKinds (Label.familyVar owner slot kind) = some kind := by
  simp [graph, NormalGraph.ofRowMap, row, baseRow, Label.view, Label.familyVar]

/- An application's free parameter names are those carried by its arguments.
A parameter name is atomic: its owner identifies it, but changing an assignment
at a name occurring inside that owner does not change the parameter's value. -/
mutual
def Tree.free : Tree → List Tree
  | .app _ args => args.free
  | t@(.bound ..) | t@(.var ..) => [t]
  | .argument _ | .local _ => []
  | .meet ps => ps.free
def Types.free : Types → List Tree
  | .nil => []
  | .cons t ts => t.free ++ ts.free
def Args.free : Args → List Tree
  | .nil => []
  | .cons ts args => ts.free ++ args.free
end

mutual
private theorem Tree.free_size (t p : Tree) (h : p ∈ t.free) : sizeOf p ≤ sizeOf t := by
  cases t with
  | app head args =>
    have hs := Args.free_size args p h
    have he : sizeOf (Tree.app head args) = 1 + sizeOf head + sizeOf args := rfl
    omega
  | bound head args slot =>
    have : p = Tree.bound head args slot := List.mem_singleton.mp h
    subst this
    exact Nat.le_refl _
  | var o i k =>
    have : p = Tree.var o i k := List.mem_singleton.mp h
    subst this
    exact Nat.le_refl _
  | argument _ => simp [Tree.free] at h
  | «local» _ => simp [Tree.free] at h
  | meet ps =>
    have hs := Types.free_size ps p h
    have he : sizeOf (Tree.meet ps) = 1 + sizeOf ps := rfl
    omega
private theorem Types.free_size (ts : Types) (p : Tree) (h : p ∈ ts.free) :
    sizeOf p < sizeOf ts := by
  cases ts with
  | nil => simp [Types.free] at h
  | cons t ts =>
    have he : sizeOf (Types.cons t ts) = 1 + sizeOf t + sizeOf ts := rfl
    rcases List.mem_append.mp h with h | h
    · have hs := Tree.free_size t p h; omega
    · have hs := Types.free_size ts p h; omega
private theorem Args.free_size (args : Args) (p : Tree) (h : p ∈ args.free) :
    sizeOf p < sizeOf args := by
  cases args with
  | nil => simp [Args.free] at h
  | cons ts args =>
    have he : sizeOf (Args.cons ts args) = 1 + sizeOf ts + sizeOf args := rfl
    rcases List.mem_append.mp h with h | h
    · have hs := Types.free_size ts p h; omega
    · have hs := Args.free_size args p h; omega
end

/-- The binder introduced by a scope cannot already occur in its captured
arguments. Its name contains those arguments; such an occurrence would require
a finite syntax tree to contain itself as a proper subtree. -/
theorem Scope.bound_fresh (scope : Scope sig) (slot : Fin sig[scope.head].binders.length) :
    (scope.bound slot).1 ∉ scope.rawArgs.free := by
  intro h
  have hs := Args.free_size scope.rawArgs (scope.bound slot).1 h
  have he : sizeOf (scope.bound slot).1 =
      1 + sizeOf scope.head.val + sizeOf scope.rawArgs + sizeOf slot.val := rfl
  omega

/-- Constructor applications do not secretly introduce an unquantified
parameter. Only an owned bound label has a parameter kind. -/
theorem Equations.kind_application (equations : Equations) (scope : Scope equations.signature) :
    equations.graph.parameterKinds scope.label = none := by
  simp only [graph, NormalGraph.ofRowMap, row, baseRow, Scope.view_label, Template.instantiate]
  have hv := (equations.body scope.head).2
  cases h : (equations.body scope.head).1 <;>
    simp_all [RowTemplate.wellBound, GraphRow.map]

#print axioms Equations.row_application
#print axioms Equations.kind_bound
#print axioms Equations.kind_familyVar
#print axioms Equations.kind_application
#print axioms Scope.bound_fresh

end Verification.EquationGraphs
