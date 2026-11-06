import Verification.Types.PositiveNormalization

/-! Normalize each body of a guarded recursive graph without unfolding cycles
or allocating new labels. A label names a whole positive formula; normalized
labels name finite unions of clauses. Operands remain lists of labels. -/
namespace Verification.PositiveGraphs
open CallEffects
open PositiveNormalization Tower

/-! ## Rows of a normal graph

A label's row is one of four kinds. A clause row means a finite union of
clauses. A parameter row is a binder of some scheme and means what the graph's
assignment gives it. A scheme row is a generic callable, such as `Promise<T>`'s
`then<R1, R2>`: a value meeting its signatures at every instantiation of its
binders. A meet row is a value parameter row intersected with clauses, such as
`V & DepSafe`: what the assignment gives the parameter, within the clauses.

The assignment is part of the graph. No check reads it; it enters only the
semantics. A theorem proved for every graph therefore holds at every
assignment, which is what typing a generic body once, for all of its
instances, needs. -/

/-- Semantic binders distinguish a runtime value from an argument list. A
packed binder is both: a value binder whose values are arrays, and the
argument lists their elements form (`Packable`). -/
inductive ParameterKind where
  | value
  | arguments
  | packed
  deriving DecidableEq, BEq, Repr, Inhabited

deriving instance ReflBEq for ParameterKind
deriving instance LawfulBEq for ParameterKind

abbrev ParameterKind.Carrier : ParameterKind → Type
  | .value => Val
  | .arguments => List Val
  | .packed => Val

abbrev ParameterKind.Closed : (k : ParameterKind) → k.Carrier → Prop
  | .value => fun (v : Val) => isVal v = true ∧ Scoped 0 v
  | .arguments => fun (vs : List Val) => ∀ v ∈ vs, isVal v = true ∧ Scoped 0 v
  | .packed => fun (v : Val) => isVal v = true ∧ Scoped 0 v

/-- **Packable values.** Arrays whose elements, read from the store any
satisfying heap of any future world holds, form a list `P` admits two levels
down, its contents being typed one level down: reading the store and
spreading it are a step each. A packed binder's
values are its value component's members that are packable by its list
component, so a spread of one is a list of the binder (PROGRAM-TYPING.md,
"Packed binders"). -/
def Packable (P : WorldFamily (List Val)) : Fam := fun n W v =>
  ∀ j (hj : j + 1 ≤ n) (U : WorldT (j + 1)), WExt (trunc (j + 1) hj W) U → ∀ h, HeapOk (j + 1) U h →
    ∃ fs c oid l ls vs, v = .objAt fs c oid ∧ fs.lookup CallArguments.arrayStoreField = some l ∧
      h[l]? = some (.arr ls) ∧ readElems h ls = some vs ∧
      ∀ i (hi : i + 1 ≤ j), P i (trunc i (by omega) U) vs

theorem Packable_adm (P : WorldFamily (List Val)) : Adm (Packable P) :=
  ⟨fun n W v hv j hj U hx h hh => hv j (by omega) U (by rwa [trunc_trunc] at hx) h hh,
   fun n W W' hw v hv j hj U hx h hh =>
    hv j hj U (WExt_trans (WExt_trunc hj hw) hx) h hh⟩

/-- Packable values depend on `P` only two levels down. -/
theorem Packable_congr {P Q : WorldFamily (List Val)} {n : Nat}
    (h : ∀ j, j < n → ∀ (W : WorldT j) vs, P j W vs ↔ Q j W vs) (W : WorldT n) (v : Val) :
    Packable P n W v ↔ Packable Q n W v := by
  constructor <;> intro hv j hj U hx hh hok <;>
    obtain ⟨fs, c, oid, l, ls, vs, h1, h2, h3, h4, h5⟩ := hv j hj U hx hh hok <;>
    refine ⟨fs, c, oid, l, ls, vs, h1, h2, h3, h4, fun i hi => ?_⟩
  · exact (h i (by omega) _ vs).mp (h5 i hi)
  · exact (h i (by omega) _ vs).mpr (h5 i hi)

theorem Packable_mono {P Q : WorldFamily (List Val)} (h : ∀ n W vs, P n W vs → Q n W vs)
    {n : Nat} {W : WorldT n} {v : Val} (hp : Packable P n W v) : Packable Q n W v := by
  intro j hj U hx hh hok
  obtain ⟨fs, c, oid, l, ls, vs, h1, h2, h3, h4, h5⟩ := hp j hj U hx hh hok
  exact ⟨fs, c, oid, l, ls, vs, h1, h2, h3, h4, fun i hi => h _ _ _ (h5 i hi)⟩

/-- The assignment algebra depends on a carrier and its closedness predicate,
not on every binder in a scheme having the same source-language kind. -/
structure ParameterSpace where
  Carrier : Type
  Closed : Carrier → Prop

abbrev ParameterSpace.value : ParameterSpace :=
  ⟨ParameterKind.Carrier .value, ParameterKind.Closed .value⟩
abbrev ParameterSpace.arguments : ParameterSpace :=
  ⟨ParameterKind.Carrier .arguments, ParameterKind.Closed .arguments⟩

/-- A semantic sum, not a calculus value constructor. It permits a single
substitution to contain both ordinary types and whole argument-list types. -/
abbrev ParameterSpace.mixed : ParameterSpace :=
  ⟨Val ⊕ List Val, fun
    | .inl v => ParameterKind.Closed .value v
    | .inr vs => ParameterKind.Closed .arguments vs⟩

/-- Both sorts obey the same approximation and world-extension laws. List
membership is at the current level; changing sorts does not insert a guard. -/
def ParameterValid (k : ParameterSpace) (A : WorldFamily k.Carrier) : Prop :=
  Adm A ∧ ∀ n W v, A n W v → k.Closed v

abbrev ParameterFamily (k : ParameterSpace) := { A : WorldFamily k.Carrier // ParameterValid k A }
abbrev ParameterAssignment (k : ParameterSpace) (ι : Type) :=
  { η : ι → WorldFamily k.Carrier // ∀ i, ParameterValid k (η i) }

/-- The production value environment is the value instance of the shared
assignment algebra, rather than a separate implementation. -/
abbrev ValueFam (A : Fam) : Prop := ParameterValid .value A
abbrev ValueFamily := ParameterFamily .value

abbrev MixedFamily := ParameterFamily .mixed
abbrev MixedAssignment (ι : Type) := ParameterAssignment .mixed ι

/-- Project a value contract without interpreting a list as a runtime value. -/
def MixedFamily.value (A : MixedFamily) : ValueFamily :=
  ⟨fun n W v => A.1 n W (.inl v),
    ⟨⟨fun n W v h => A.2.1.down n W (.inl v) h,
      fun n W U hx v h => A.2.1.mono n W U hx (.inl v) h⟩,
      fun n W v h => A.2.2 n W (.inl v) h⟩⟩

/-- An ordinary substitution argument has no argument-list members. -/
def MixedFamily.ofValue (A : ValueFamily) : MixedFamily :=
  ⟨fun n W x => match x with | .inl v => A.1 n W v | .inr _ => False,
    ⟨⟨fun n W x h => by cases x with
          | inl v => exact A.2.1.down n W v h
          | inr vs => exact h,
        fun n W U hx x h => by cases x with
          | inl v => exact A.2.1.mono n W U hx v h
          | inr vs => exact h⟩,
      fun n W x h => by cases x with
        | inl v => exact A.2.2 n W v h
        | inr vs => exact h.elim⟩⟩

def ParameterAssignment.empty (k : ParameterSpace) : ParameterAssignment k ι :=
  ⟨fun _ _ _ _ => False,
    fun _ => ⟨⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩, fun _ _ _ h => h.elim⟩⟩

/-- A binder observes only the component selected by its declared kind.
The other component of a mixed semantic family cannot constrain its meaning. -/
def selectParameter (kind : Option ParameterKind) (A : WorldFamily ParameterSpace.mixed.Carrier) :
    WorldFamily ParameterSpace.mixed.Carrier := fun n W x => match x with
  | .inl v => (kind = some .value ∧ A n W (.inl v)) ∨
      (kind = some .packed ∧ A n W (.inl v) ∧ Packable (fun j U vs => A j U (.inr vs)) n W v)
  | .inr vs => (kind = some .arguments ∨ kind = some .packed) ∧ A n W (.inr vs)

theorem selectParameter_adm (kind : Option ParameterKind) {A : WorldFamily ParameterSpace.mixed.Carrier}
    (h : Adm A) : Adm (selectParameter kind A) := by
  constructor
  · intro n W x hx
    cases x with
    | inl v =>
      rcases hx with ⟨hk, ha⟩ | ⟨hk, ha, hp⟩
      · exact Or.inl ⟨hk, h.down _ _ _ ha⟩
      · exact Or.inr ⟨hk, h.down _ _ _ ha, (Packable_adm _).down _ _ _ hp⟩
    | inr vs => exact ⟨hx.1, h.down _ _ _ hx.2⟩
  · intro n W U hw x hx
    cases x with
    | inl v =>
      rcases hx with ⟨hk, ha⟩ | ⟨hk, ha, hp⟩
      · exact Or.inl ⟨hk, h.mono _ _ _ hw _ ha⟩
      · exact Or.inr ⟨hk, h.mono _ _ _ hw _ ha, (Packable_adm _).mono _ _ _ hw _ hp⟩
    | inr vs => exact ⟨hx.1, h.mono _ _ _ hw _ hx.2⟩

/-- Selection is nonexpansive: it reads its family at the same levels and,
for a packed binder's spread, below them. -/
theorem selectParameter_agree (kind : Option ParameterKind) {A B : WorldFamily ParameterSpace.mixed.Carrier}
    {n : Nat} (h : Agree A B n) : Agree (selectParameter kind A) (selectParameter kind B) n := by
  intro m hm W x
  cases x with
  | inr vs => exact and_congr Iff.rfl (h m hm W (.inr vs))
  | inl v =>
    have hp := Packable_congr (P := fun j U vs => A j U (.inr vs)) (Q := fun j U vs => B j U (.inr vs))
      (n := m) (fun j hj U vs => h j (by omega) U (.inr vs)) W v
    simp only [selectParameter]
    rw [h m hm W (.inl v), hp]

@[simp] theorem selectParameter_value {A : WorldFamily ParameterSpace.mixed.Carrier} {n W v} :
    selectParameter (some .value) A n W (.inl v) ↔ A n W (.inl v) := by
  simp [selectParameter]

/-- Positions of a retained resolution input, literal observation and associated
result among a scheme's binders. An observation-only group (`Awaitable`) has no
result slot. Positions survive label renaming. -/
structure ResolutionSlots where
  input : Nat
  observation : Nat
  result : Option Nat
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The associated slots of a group: its observation, and its result if any. -/
def ResolutionSlots.associated (g : ResolutionSlots) : List Nat :=
  g.observation :: g.result.toList

/-- A quantified callable: its binders, which are parameter rows, and the
signatures `(receiver, parameters, result)` each of its instances meets. -/
structure SchemeRow (ι : Type) where
  binders : List ι
  signatures : List (Arrow (List ι))
  /-- Upper bounds `(binder, type)`: an instance gives the binder a family below
  the type, read at the scheme's own assignment (a bound does not mention the
  scheme's binders). -/
  bounds : List (ι × List ι) := []
  /-- Variadic signatures `(receiver, parameters, rest, result)`, the rest an
  argument-list type; a binder may be one. -/
  variadic : List (RestArrow (List ι)) := []
  /-- Associated slots are part of the generic contract. -/
  resolution : List ResolutionSlots := []
  /-- A construct scheme: its signatures are construct signatures, each an
  arrow's arguments, result and effect (`ctorOf`), and its members class values. -/
  construct : Bool := false
  deriving DecidableEq, Repr

/-- Associated observation and result slots have no independent bounds.
Input bounds retain the associated contracts when narrowing a substitution. -/
def SchemeRow.protectedSlots (s : SchemeRow ι) : Prop :=
  ∀ g ∈ s.resolution, ∀ p ∈ g.associated,
    ∀ b, s.binders[p]? = some b → ∀ B, (b, B) ∉ s.bounds

/-- The finite graph boundary checks position identity and all protected
bounds separately from semantic instance membership. -/
@[nospecialize] def SchemeRow.resolutionValid [DecidableEq ι] (s : SchemeRow ι) : Bool :=
  s.resolution.isEmpty ||
    (decide s.binders.Nodup &&
      decide (s.resolution.flatMap (fun g => g.input :: g.associated)).Nodup &&
      s.resolution.all (fun g =>
        g.input < s.binders.length && g.associated.all (· < s.binders.length) &&
        s.bounds.all (fun b => g.associated.all fun p => s.binders[p]? != some b.1)))

open Classical in
/-- The assignment with each binder given the family at its position. -/
noncomputable def assign (η : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) :
    ParameterAssignment k ι :=
  ⟨fun i => match (bs.zip As).lookup i with
      | some A => A.1
      | none => η.1 i,
   fun i => by
      cases h : (bs.zip As).lookup i with
      | some A => simpa [h] using A.2
      | none => simpa [h] using η.2 i⟩

open Classical in
/-- A binder is given the family at its position. -/
theorem assign_map_mem (η : ParameterAssignment k ι) (bs : List ι) (F : ι → ParameterFamily k) {i : ι}
    (h : i ∈ bs) : (assign η bs (bs.map F)).1 i = (F i).1 := by
  have hl : (bs.zip (bs.map F)).lookup i = some (F i) := by
    induction bs with
    | nil => cases h
    | cons b bs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
      by_cases hb : i = b
      · subst hb; simp
      · have hi : i ∈ bs := (List.mem_cons.mp h).resolve_left hb
        rw [beq_false_of_ne hb]; simp [ih hi]
  simp [assign, hl]

open Classical in
/-- Any other row keeps its family. -/
theorem assign_map_nmem (η : ParameterAssignment k ι) (bs : List ι) (F : ι → ParameterFamily k) {i : ι}
    (h : i ∉ bs) : (assign η bs (bs.map F)).1 i = η.1 i := by
  have hl : (bs.zip (bs.map F)).lookup i = none := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
      have hb : i ≠ b := fun e => h (e ▸ List.mem_cons_self)
      have hi : i ∉ bs := fun hi => h (List.mem_cons_of_mem _ hi)
      rw [beq_false_of_ne hb]; simp [ih hi]
  simp [assign, hl]

open Classical in
/-- A row that is no binder keeps its family, whatever the binders are given. -/
theorem assign_nmem (η : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) {i : ι}
    (h : i ∉ bs) : (assign η bs As).1 i = η.1 i := by
  have hl : (bs.zip As).lookup i = none := by
    induction bs generalizing As with
    | nil => rfl
    | cons b bs ih =>
      cases As with
      | nil => rfl
      | cons A As =>
        simp only [List.zip_cons_cons, List.lookup_cons]
        have hb : i ≠ b := fun e => h (e ▸ List.mem_cons_self)
        rw [beq_false_of_ne hb]
        exact ih As fun hi => h (List.mem_cons_of_mem _ hi)
  simp [assign, hl]

open Classical in
private theorem lookup_zip_some {bs : List ι} {As : List (ParameterFamily k)} {p : ι}
    (h : p ∈ bs) (hl : As.length = bs.length) : ∃ A, (bs.zip As).lookup p = some A := by
  induction bs generalizing As with
  | nil => cases h
  | cons b bs ih =>
    cases As with
    | nil => simp at hl
    | cons A As =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      by_cases hb : p = b
      · subst hb; simp
      · rw [beq_false_of_ne hb]
        exact ih ((List.mem_cons.mp h).resolve_left hb) (by simpa using hl)

open Classical in
/-- A binder is given the same family whatever the rest of the assignment. -/
theorem assign_mem_eq (η η' : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) {p : ι}
    (h : p ∈ bs) (hl : As.length = bs.length) :
    (assign η bs As).1 p = (assign η' bs As).1 p := by
  obtain ⟨A, hA⟩ := lookup_zip_some h hl
  simp [assign, hA]

open Classical in
theorem assign_cons_head (η : ParameterAssignment k ι) (b : ι) (bs : List ι) (A : ParameterFamily k)
    (As : List (ParameterFamily k)) : (assign η (b :: bs) (A :: As)).1 b = A.1 := by
  simp [assign, List.lookup_cons]

open Classical in
theorem assign_cons_ne (η : ParameterAssignment k ι) {b p : ι} (bs : List ι) (A : ParameterFamily k)
    (As : List (ParameterFamily k)) (h : p ≠ b) :
    (assign η (b :: bs) (A :: As)).1 p = (assign η bs As).1 p := by
  have : ((b :: bs).zip (A :: As)).lookup p = (bs.zip As).lookup p := by
    rw [List.zip_cons_cons, List.lookup_cons, beq_false_of_ne h]
  simp only [assign, this]

/-- An instance is bounded below `n`: each bounded binder's family lies below
its bound at every level under `n`. Only levels below `n` are read, which keeps
the fixed point contractive. -/
def Bounded (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (As : List (ParameterFamily k)) (n : Nat) : Prop :=
  ∀ b ∈ s.bounds, b.1 ∈ s.binders → ∀ j, j < n → ∀ (U : WorldT j) u,
    (assign η s.binders As).1 b.1 j U u → D η b.2 j U u

/-- A fixed universe of allowed substitutions. The universe reads no recursive
graph approximation or ambient assignment. -/
structure SchemeDomain (ι : Type) (k : ParameterSpace) where
  allowed : SchemeRow ι → List (ParameterFamily k) → Prop
  /-- Every unqualified row admits its ordinary substitutions. -/
  ordinary_allowed : ∀ s As, s.resolution = [] → allowed s As
  /-- Renaming labels preserves the positional qualification contract. -/
  congr : ∀ s t, s.resolution = t.resolution →
    (s.protectedSlots ↔ t.protectedSlots) → ∀ As, allowed s As ↔ allowed t As
/-- Ordinary quantification permits ordinary rows. A qualified row requires an
explicit domain whose substitutions retain its associated contracts. -/
def SchemeDomain.ordinary : SchemeDomain ι k where
  allowed s _ := s.resolution = []
  ordinary_allowed _ _ h := h
  congr s t h _ As := by rw [h]

/-- What the built-in arrays are, as a graph states it: the type of
`Array.prototype` (`ArrayProto`) and the keys that prototype provides, none
of which an array owns. It is what the array invariant (`arrayInvariant`)
reads. -/
structure ArrayBuiltins (ι : Type) where
  proto : List ι
  /-- The built-ins' `unknown`: the type of an array's elements, and of a thrown value. -/
  unknown : List ι
  keys : List PropKey
  deriving DecidableEq, Repr

/-- A literal a tag set's element is: a number by bit pattern, or a string. -/
inductive LitKey where
  | num (bits : UInt64)
  | str (value : String)
  deriving DecidableEq, Repr, Hashable

structure NormalGraph (ι : Type) where
  /-- A clause row's clauses. -/
  rows : ι → List (Clause (List ι))
  schemes : ι → Option (SchemeRow ι) := fun _ => none
  parameterKinds : ι → Option ParameterKind := fun _ => none
  /-- A meet row's value parameter row and the clauses it is intersected with
  (`V & DepSafe`). -/
  meets : ι → Option (ι × List (Clause (List ι))) := fun _ => none
  /-- A meet row's further value parameter rows: its value is what the
  assignment gives each of them as well (`U ⊓ T` for `U extends T`, `T & U`). -/
  meetParams : ι → List ι := fun _ => []
  /-- What the parameter rows mean. Semantic only. -/
  env : MixedAssignment ι := ParameterAssignment.empty .mixed
  /-- The reviewed substitution universe is fixed across the graph's tower. -/
  domain : SchemeDomain ι .mixed := .ordinary
  /-- The built-in arrays, where the graph states them: then every record and
  dictionary type is of objects meeting the array invariant
  (`builtinInvariant`). A graph without arrays states none. -/
  builtins : Option (ArrayBuiltins ι) := none
  /-- A label of the graph whose row is one literal, where the graph has one:
  how a tag set splits into its elements (HOST-FAMILIES.md, "Tag sets"). A
  reader checks the label's row before reading it so; nothing else depends on
  this lookup. -/
  literal : LitKey → Option ι := fun _ => none
  /-- A hash of labels, for lookups that compare by equality within the
  bucket it names: any function serves, meaning reads none. -/
  labelHash : ι → UInt64 := fun _ => 0
  /-- Labels whose clauses overlap, as a hint a fact's filter reads to keep
  a label of the slot's type without comparing its clauses
  (`BranchRefinement.factFilter`): any function serves, since keeping a
  label is sound, and meaning reads none. -/
  overlapping : ι → Bool := fun _ => false

/-- Whether a row is a parameter is derived from its kind, never maintained
separately. -/
def NormalGraph.params (G : NormalGraph ι) (i : ι) : Bool :=
  (G.parameterKinds i).isSome

/-- A parameter row with argument-list members: a pack binder, or a packed one. -/
def NormalGraph.listParam (G : NormalGraph ι) (i : ι) : Bool :=
  G.parameterKinds i == some .arguments || G.parameterKinds i == some .packed

theorem NormalGraph.listParam_iff {G : NormalGraph ι} {i : ι} :
    G.listParam i = true ↔ G.parameterKinds i = some .arguments ∨ G.parameterKinds i = some .packed := by
  simp [NormalGraph.listParam]

/-- A clause row: neither a parameter, a scheme nor a meet. -/
def NormalGraph.plain (G : NormalGraph ι) (i : ι) : Bool :=
  !G.params i && (G.schemes i).isNone && (G.meets i).isNone

theorem NormalGraph.listParam_of_plain {G : NormalGraph ι} {i : ι} (h : G.plain i = true) :
    G.listParam i = false := by
  cases hk : G.parameterKinds i <;> simp_all [NormalGraph.plain, NormalGraph.params, NormalGraph.listParam]

/-- A clause row's three conditions. -/
theorem NormalGraph.plain_iff {G : NormalGraph ι} {i : ι} :
    G.plain i = true ↔ G.params i = false ∧ G.schemes i = none ∧ G.meets i = none := by
  simp [NormalGraph.plain, and_assoc]

/-- A label's clauses. A parameter, scheme or meet row has none: whatever
`rows` holds there is never read. -/
def NormalGraph.clauses (G : NormalGraph ι) (i : ι) : List (Clause (List ι)) :=
  if G.plain i then G.rows i else []

instance : CoeFun (NormalGraph ι) (fun _ => ι → List (Clause (List ι))) := ⟨NormalGraph.clauses⟩

/-- The sort of a type reference comes from its parameter or clause rows.
The empty union is bottom at either sort; a union cannot mix value and pack
rows. This checks only the outer sort, not recursive operand well-formedness. -/
def NormalGraph.hasKind (G : NormalGraph ι) (kind : ParameterKind) (S : List ι) : Bool :=
  S.all fun i => match G.parameterKinds i with
    | some k => k == kind
    | none => if (G.schemes i).isSome || (G.meets i).isSome then kind == .value else
      (G.rows i).all fun c => match c with
        | .pack .. => kind == .arguments
        | _ => kind == .value

/-- A label with clauses is a clause row. -/
theorem NormalGraph.plain_of_clauses {G : NormalGraph ι} {i : ι} {c}
    (h : c ∈ G i) : G.plain i = true := by
  show G.plain i = true
  cases hp : G.plain i
  · simp [NormalGraph.clauses, hp] at h
  · rfl

/-- Every label of a type is a clause row. -/
def NormalGraph.plainTy (G : NormalGraph ι) (S : List ι) : Bool := S.all G.plain

/-! ## The array invariant

An object owning the array store key is a built-in array: its store may have holes, it holds `Array.prototype` under the prototype key, and it owns no key
that prototype provides. Every array a program allocates is one; every object
it receives at a record or dictionary type is assumed to be one (the
environment premise, through `meaning`). The store key is a key no source
spells and no step adds, so the invariant is a fact of the object's identity:
it reads the world's contracts only, never the heap. -/

/-- The store a built-in array holds: possibly sparse, each element a
value of `U`, the built-ins' `unknown`. -/
def builtinStoreT (U : Fam) : Fam := listT ⟨[], [], some U, true, .sparse⟩

/-- A store under a tuple contract whose positions are within `U` is a store
of the built-ins. -/
theorem listT_builtinStore {U : Fam} {T : TupleF}
    (hT : ∀ A, (A ∈ T.required ∨ A ∈ T.optional ∨ T.rest = some A) →
      ∀ j (W : WorldT j) u, A j W u → U j W u)
    {k : Nat} {W : WorldT k} {v : Val} (h : listT T k W v) : builtinStoreT U k W v := by
  obtain ⟨ls, rfl, hd, hlen, hmax, hbound, hreq, hopt, hrest⟩ := h
  refine ⟨ls, rfl, (by simp [StorePresence]), by simp, hmax, by simp, by simp, by simp, ?_⟩
  intro i l _ hl
  refine ⟨U, ?_⟩
  simp only [true_and]
  by_cases hi : i < T.required.length
  · obtain ⟨l', c, hl', hw, hag⟩ := hreq i (T.required[i]) (List.getElem?_eq_getElem hi)
    rw [hl] at hl'
    cases hl'
    exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hT _ (.inl (List.getElem_mem hi)) j W' u
      ((hag j hj W' u).1 hu), fun h => nomatch h⟩⟩
  · by_cases ho : i < T.required.length + T.optional.length
    · have hoi : i - T.required.length < T.optional.length := by omega
      have hl2 : ls[T.required.length + (i - T.required.length)]? = some (some l) := by
        rw [show T.required.length + (i - T.required.length) = i by omega]; exact hl
      obtain ⟨c, hw, hag⟩ := hopt (i - T.required.length) (T.optional[i - T.required.length])
        l (List.getElem?_eq_getElem hoi) hl2
      exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hT _ (.inr (.inl (List.getElem_mem hoi))) j W' u
        ((hag j hj W' u).1 hu), fun h => nomatch h⟩⟩
    · obtain ⟨E, c, hE, hw, hag⟩ := hrest i l (by omega) hl
      exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hT _ (.inr (.inr hE)) j W' u
        ((hag j hj W' u).1 hu), fun h => nomatch h⟩⟩

/-- A store of the built-ins reads its element type below the level. -/
theorem builtinStoreT_congr {U U' : Fam} {n : Nat} (h : Agree U U' n) (W : WorldT n) (v : Val) :
    builtinStoreT U n W v → builtinStoreT U' n W v := by
  rintro ⟨ls, rfl, hd, hlen, hmax, hbound, hreq, hopt, hrest⟩
  refine ⟨ls, rfl, (by simp [StorePresence]), by simp, hmax, by simp, by simp, by simp, ?_⟩
  intro i l hi hl
  obtain ⟨E, c, hE, hw, hag⟩ := hrest i l hi hl
  cases hE
  exact ⟨U', c, rfl, hw, fun j hj W' u => (hag j hj W' u).congr (h j hj W' u)⟩

/-- **An array's own fields at canonical numeric keys hold its elements'
type**, as `Array<T>`'s declared `[n: number]: T` says: a value such a
field's contract admits at a level is in every family `A` such that the
store's contract, one level up, is within the possibly sparse stores of `A`
(an element's contract at a level is stated by the store's one level up).
So an array of a type whose store holds `T` holds `T` there too, below the
level (`numeric_of_inv`). It reads the world's contracts only. -/
def numericOwn (k : Nat) (W : WorldT k) (flds : List (PropKey × Nat)) : Prop :=
  ∃ (ls : Nat) (cs : Ctr k), flds.lookup CallArguments.arrayStoreField = some ls ∧ lookup W ls = some cs ∧
    ∀ key l, IndexKeys.numeric.Admits key → flds.lookup key = some l → ∃ c : Ctr k, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j + 1 < k) (U : WorldT j) (u : Val), c j (by omega) U u →
        ∀ A : Fam, (∀ (U' : WorldT (j + 1)) (s : Val), cs (j + 1) hj U' s → builtinStoreT A (j + 1) U' s) →
          A j U u

theorem numericOwn_down {n : Nat} {W : WorldT (n + 1)} {flds : List (PropKey × Nat)}
    (h : numericOwn (n + 1) W flds) : numericOwn n (trunc n (Nat.le_succ n) W) flds := by
  obtain ⟨ls, cs, hs, hcs, hk⟩ := h
  refine ⟨ls, _, hs, lookup_trunc (Nat.le_succ n) W ls cs hcs, fun key l hkey hl => ?_⟩
  obtain ⟨c, hc, hag⟩ := hk key l hkey hl
  exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hc, fun j hj U u hu A hA =>
    hag j (by omega) U u hu A fun U' s hs' => hA U' s hs'⟩

theorem numericOwn_mono {n : Nat} {W W' : WorldT n} (hx : WExt W W') {flds : List (PropKey × Nat)}
    (h : numericOwn n W flds) : numericOwn n W' flds := by
  obtain ⟨ls, cs, hs, hcs, hk⟩ := h
  refine ⟨ls, cs, hs, WExt_lookup hx hcs, fun key l hkey hl => ?_⟩
  obtain ⟨c, hc, hag⟩ := hk key l hkey hl
  exact ⟨c, WExt_lookup hx hc, hag⟩

/-- An object owning no field at a canonical numeric key states nothing
there. -/
theorem numericOwn_of_none {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)} {ls : Nat}
    {cs : Ctr k} (hs : flds.lookup CallArguments.arrayStoreField = some ls) (hcs : lookup W ls = some cs)
    (hn : ∀ key, IndexKeys.numeric.Admits key → flds.lookup key = none) : numericOwn k W flds :=
  ⟨ls, cs, hs, hcs, fun key l hkey hl => by rw [hn key hkey] at hl; cases hl⟩

/-- The values a store location holds: lists. -/
def listValT : Fam := fun _ _ u => ∃ ls, u = .arr ls

/-- **An array's store is a list**: an object owning the store key holds a
list under it. Every array of a builtins meets it (`builtinStoreT` is of lists);
without a builtins, it is all the graph asks of an array. -/
def storeListT : Fam := fun k W v =>
  ∀ flds oid, v = .objAt flds .absent oid → (flds.lookup CallArguments.arrayStoreField).isSome = true →
    viewT [(CallArguments.arrayStoreField, listValT)] k W v

theorem storeListT_adm : Adm storeListT := by
  constructor
  · intro n W v h flds oid hv hs
    exact (viewT_adm _).down n W v (h flds oid hv hs)
  · intro n W W' hx v h flds oid hv hs
    exact (viewT_adm _).mono n W W' hx v (h flds oid hv hs)

/-- **The array invariant**, with `P` the prototype's type, `U` the built-ins'
`unknown`, the type of an array's elements, and `N` the keys the prototype
provides. -/
def arrayInvariant (P U : Fam) (N : List PropKey) : Fam := fun k W v =>
  ∀ flds oid, v = .objAt flds .absent oid → (flds.lookup CallArguments.arrayStoreField).isSome = true →
    viewT [(CallArguments.arrayStoreField, builtinStoreT U), (CallArguments.protoField, P)] k W v ∧
      ownKeysT ⟨false, N⟩ k W v ∧ numericOwn k W flds

/-- What a row asks of the members of one of its clauses beyond the clause:
the array invariant, where the graph states the built-ins and the clause is one it
applies to (`Clause.carriesInvariant`: a record, a dictionary, `source`). -/
def builtinInvariant (G : NormalGraph ι) (X : List ι → Fam) (c : Clause (List ι)) : Fam :=
  match G.builtins with
  | some r => if c.carriesInvariant then arrayInvariant (X r.proto) (X r.unknown) r.keys else fun _ _ _ => True
  | none => if c.carriesInvariant then storeListT else fun _ _ _ => True

/-- **The graph's exception family**: the values of the built-ins' `unknown`,
JavaScript values meeting what the built-ins asks of a `source` clause, its
prototype type read by `A`. A throw in the graph's code, and in every
function a type of the graph promises, is one of them (`Safe`'s `Thrown`). -/
def builtinExc (G : NormalGraph ι) (A : List ι → Fam) : Fam :=
  fun n W v => sourceT n W v ∧ builtinInvariant G A .source n W v

/-- **A clause, read in a row**: its members that meet the built-ins' invariant.
The operands are read by `X` and `P`; the built-in prototype type by `A`, at one
fixed assignment (`ParameterInterpretation.builtinsAt`). -/
def rowSem (G : NormalGraph ι) (A X : List ι → Fam) (P : List ι → ArgFam) (c : Clause (List ι)) : Fam :=
  fun n W v => semWithArgs (builtinExc G A) X P c n W v ∧ builtinInvariant G A c n W v

theorem arrayInvariant_adm (P U : Fam) (N : List PropKey) : Adm (arrayInvariant P U N) := by
  constructor
  · intro n W v h flds oid hv hs
    obtain ⟨h1, h2, h3⟩ := h flds oid hv hs
    exact ⟨(viewT_adm _).down n W v h1, (ownKeysT_adm _).down n W v h2, numericOwn_down h3⟩
  · intro n W W' hx v h flds oid hv hs
    obtain ⟨h1, h2, h3⟩ := h flds oid hv hs
    exact ⟨(viewT_adm _).mono n W W' hx v h1, (ownKeysT_adm _).mono n W W' hx v h2, numericOwn_mono hx h3⟩

/-- The invariant reads the prototype's type only below the budget, through
the contract of the prototype key. -/
theorem arrayInvariant_congr {P Q U U' : Fam} (N : List PropKey) {n : Nat} (h : Agree P Q n)
    (hu : Agree U U' n) (W : WorldT n) (v : Val) :
    arrayInvariant P U N n W v ↔ arrayInvariant Q U' N n W v := by
  have side : ∀ (P Q U U' : Fam), Agree P Q n → Agree U U' n →
      arrayInvariant P U N n W v → arrayInvariant Q U' N n W v := by
    intro P Q U U' h hu hv flds oid he hs
    obtain ⟨h1, h2, h3⟩ := hv flds oid he hs
    refine ⟨fun f T hm => ?_, h2, h3⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨flds', l, c, oid', he', hf, hl, hag⟩ := h1 CallArguments.arrayStoreField (builtinStoreT U) (by simp)
      exact ⟨flds', l, c, oid', he', hf, hl, fun j hj W' u hu' =>
        builtinStoreT_congr (fun m hm W'' w => hu m (by omega) W'' w) W' u (hag j hj W' u hu')⟩
    · obtain ⟨flds', l, c, oid', he', hf, hl, hag⟩ := h1 CallArguments.protoField P (by simp)
      exact ⟨flds', l, c, oid', he', hf, hl, fun j hj W' u hu => (h j hj W' u).mp (hag j hj W' u hu)⟩
  exact ⟨side P Q U U' h hu, side Q P U' U (fun j hj W' u => (h j hj W' u).symm)
    (fun j hj W' u => (hu j hj W' u).symm)⟩

theorem builtinInvariant_adm (G : NormalGraph ι) (X : List ι → Fam) (c : Clause (List ι)) :
    Adm (builtinInvariant G X c) := by
  unfold builtinInvariant
  cases G.builtins with
  | none =>
    cases c.carriesInvariant
    · exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
    · exact storeListT_adm
  | some r =>
    cases c.carriesInvariant
    · exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
    · exact arrayInvariant_adm _ _ _

theorem builtinInvariant_congr (G : NormalGraph ι) (X Y : List ι → Fam) (n : Nat)
    (h : ∀ a, Agree (X a) (Y a) n) (c : Clause (List ι)) (W : WorldT n) (v : Val) :
    builtinInvariant G X c n W v ↔ builtinInvariant G Y c n W v := by
  unfold builtinInvariant
  cases G.builtins with
  | none => exact Iff.rfl
  | some r =>
    cases c.carriesInvariant
    · exact Iff.rfl
    · exact arrayInvariant_congr _ (h _) (h _) W v

/-- **An array's store is a list**, in every graph: a member of a clause the
invariant applies to that owns the store key holds a list under it. -/
theorem builtinInvariant_store {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    (hc : c.carriesInvariant = true) {n W flds oid} (h : builtinInvariant G X c n W (.objAt flds .absent oid))
    (hs : (flds.lookup CallArguments.arrayStoreField).isSome = true) :
    ∃ (l : Nat) (c' : Ctr n), flds.lookup CallArguments.arrayStoreField = some l ∧ lookup W l = some c' ∧
      ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val), c' j hj W' u → ∃ ls, u = .arr ls := by
  unfold builtinInvariant at h
  cases hr : G.builtins with
  | none =>
    rw [hr] at h
    simp only [hc, ite_true] at h
    obtain ⟨flds', l, c', oid', he, hf, hl, hag⟩ := viewT_at (List.mem_singleton_self _) (h flds oid rfl hs)
    cases he
    exact ⟨l, c', hf, hl, hag⟩
  | some r =>
    rw [hr] at h
    simp only [hc, ite_true] at h
    obtain ⟨hview, -, -⟩ := h flds oid rfl hs
    obtain ⟨flds', l, c', oid', he, hf, hl, hag⟩ := viewT_at (List.mem_cons_self) hview
    cases he
    exact ⟨l, c', hf, hl, fun j hj W' u hu => by
      obtain ⟨ls, rfl, -⟩ := hag j hj W' u hu
      exact ⟨ls, rfl⟩⟩

/-- Two graphs of one builtins whose prototype and `unknown` types mean the same
have one exception family. -/
theorem builtinExc_eq {G H : NormalGraph ι} {A B : List ι → Fam} (hr : H.builtins = G.builtins)
    (h : ∀ r, G.builtins = some r → A r.proto = B r.proto ∧ A r.unknown = B r.unknown) :
    builtinExc H A = builtinExc G B := by
  funext n W v
  unfold builtinExc builtinInvariant
  rw [hr]
  cases hg : G.builtins with
  | none => rfl
  | some r =>
    obtain ⟨h1, h2⟩ := h r hg
    simp only [h1, h2]

theorem builtinExc_adm (G : NormalGraph ι) (A : List ι → Fam) : Adm (builtinExc G A) :=
  interT_adm _ _ ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩ (builtinInvariant_adm G A .source)

/-- The exception family reads its prototype type below the level. -/
theorem builtinExc_congr (G : NormalGraph ι) (A B : List ι → Fam) (n : Nat)
    (h : ∀ a, Agree (A a) (B a) n) : Agree (builtinExc G A) (builtinExc G B) n :=
  fun m hm W v => and_congr Iff.rfl
    (builtinInvariant_congr G A B m (fun a k hk W' u => h a k (by omega) W' u) .source W v)

theorem rowSem_adm (G : NormalGraph ι) (A X : List ι → Fam) (P : List ι → ArgFam)
    (c : Clause (List ι)) : Adm (rowSem G A X P c) :=
  interT_adm _ _ (semWithArgs_adm X P c) (builtinInvariant_adm G A c)

theorem rowSem_congr (G : NormalGraph ι) (A B X Y : List ι → Fam) (P Q : List ι → ArgFam) (n : Nat)
    (hA : ∀ a, Agree (A a) (B a) n)
    (h : ∀ a, Agree (X a) (Y a) n) (hP : ∀ a, Agree (P a) (Q a) n) (c : Clause (List ι))
    (W : WorldT n) (v : Val) : rowSem G A X P c n W v ↔ rowSem G B Y Q c n W v :=
  and_congr (semWithArgs_congr X Y P Q n (builtinExc_congr G A B n hA) h hP c W v)
    (builtinInvariant_congr G A B n hA c W v)

/-- A clause the built-ins' invariant does not apply to asks nothing more in a row. -/
theorem builtinInvariant_of_withoutInvariant {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    (hc : c.carriesInvariant = false) (n W v) : builtinInvariant G X c n W v := by
  unfold builtinInvariant
  cases G.builtins with
  | none => simp [hc]
  | some r => simp [hc]

/-- Clauses none of which the invariant applies to mean in a row what they
mean alone. -/
theorem setSem_row_plain {G : NormalGraph ι} {A X : List ι → Fam} {P : List ι → ArgFam}
    {cs : List (Clause (List ι))} (hc : ∀ c ∈ cs, c.carriesInvariant = false) (n W v) :
    setSem (rowSem G A X P) cs n W v ↔ semList (builtinExc G A) X P cs n W v := by
  constructor
  · rintro ⟨c, hm, hv, -⟩; exact ⟨c, hm, hv⟩
  · rintro ⟨c, hm, hv⟩; exact ⟨c, hm, hv, builtinInvariant_of_withoutInvariant (hc c hm) n W v⟩

/-- An object that does not own the store key meets the invariant. -/
theorem arrayInvariant_of_lookup {P U : Fam} {N : List PropKey} {n W flds code}
    (h : flds.lookup CallArguments.arrayStoreField = none) :
    arrayInvariant P U N n W (.objAt flds code oid) := by
  intro flds' oid' he hs
  cases he
  simp [h] at hs

/-- A value that is not a plain object meets the invariant. -/
theorem arrayInvariant_of_not_plain {P U : Fam} {N : List PropKey} {n W v}
    (h : ∀ flds oid, v ≠ .objAt flds .absent oid) : arrayInvariant P U N n W v :=
  fun flds oid he _ => absurd he (h flds oid)

/-- A row's clause without the store key, or not a plain object, asks nothing
it does not already have. -/
theorem builtinInvariant_of_lookup {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    {n W flds code} (h : flds.lookup CallArguments.arrayStoreField = none) :
    builtinInvariant G X c n W (.objAt flds code oid) := by
  unfold builtinInvariant
  cases G.builtins with
  | none =>
    cases c.carriesInvariant
    · trivial
    · intro flds' oid' he hs
      cases he
      simp [h] at hs
  | some r =>
    cases c.carriesInvariant
    · trivial
    · exact arrayInvariant_of_lookup h

theorem builtinInvariant_of_not_plain {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    {n W v} (h : ∀ flds oid, v ≠ .objAt flds .absent oid) : builtinInvariant G X c n W v := by
  unfold builtinInvariant
  cases G.builtins with
  | none =>
    cases c.carriesInvariant
    · trivial
    · exact fun flds oid he _ => absurd he (h flds oid)
  | some r =>
    cases c.carriesInvariant
    · trivial
    · exact arrayInvariant_of_not_plain h

/-- The errors the host throws are of every graph's exception family: a
fresh object owning no key. -/
theorem builtinExc_errors (G : NormalGraph ι) (A : List ι → Fam) : ErrorsIn (builtinExc G A) :=
  fun _ _ _ => ⟨⟨rfl, by simp [thrownError, Scoped]⟩, builtinInvariant_of_lookup (by simp)⟩

/-- Two clauses the invariant applies to ask the same of their members. -/
theorem builtinInvariant_carriesInvariant {G : NormalGraph ι} {X : List ι → Fam} {c d : Clause (List ι)}
    (hc : c.carriesInvariant = true) (hd : d.carriesInvariant = true) {n W v} :
    builtinInvariant G X c n W v ↔ builtinInvariant G X d n W v := by
  unfold builtinInvariant
  cases G.builtins with
  | none => simp [hc, hd]
  | some r => simp [hc, hd]

/-- A member of a clause of a row meets what the built-ins asks of every clause
but top: the clause's own invariant where it is one the invariant applies to,
nothing otherwise, its member being no plain object. -/
theorem builtinInvariant_of_member {G : NormalGraph ι} {Z X : List ι → Fam} {P : List ι → ArgFam}
    {c d : Clause (List ι)} {n W v} (hv : rowSem G Z X P c n W v) (hc : c ≠ .top)
    (hd : d.carriesInvariant = true) : builtinInvariant G Z d n W v := by
  cases hcr : c.carriesInvariant
  · exact builtinInvariant_of_not_plain (semWithArgs_not_plain hc hcr hv.1)
  · exact (builtinInvariant_carriesInvariant hcr hd).mp hv.2

/-- A JavaScript value meets the built-ins' `unknown` where it is a member of a
row's clause other than top. -/
theorem builtinExc_of_member {G : NormalGraph ι} {Z X : List ι → Fam} {P : List ι → ArgFam}
    {c : Clause (List ι)} {n W v} (hv : rowSem G Z X P c n W v) (hc : sourceClause c = true) :
    builtinExc G Z n W v :=
  ⟨sourceClause_sound hc hv.1, builtinInvariant_of_member hv (by rintro rfl; cases hc) rfl⟩

/-- Renaming a clause's operands keeps what the built-ins asks of it. -/
theorem builtinInvariant_map (G : NormalGraph ι) (X : List ι → Fam) (f : List ι → List ι)
    (c : Clause (List ι)) : builtinInvariant G X (c.map f) = builtinInvariant G X c := by
  unfold builtinInvariant
  rw [Clause.carriesInvariant_map]

/-- A meet of rows, read in a row, is the meet of what each asks. -/
theorem meetLists_row (G : NormalGraph ι) (Z X : List ι → Fam) (P : List ι → ArgFam)
    (A B : List (Clause (List ι))) (n W v) :
    setSem (rowSem G Z X P) (meetLists A B) n W v ↔
      setSem (rowSem G Z X P) A n W v ∧ setSem (rowSem G Z X P) B n W v := by
  constructor
  · rintro ⟨c, hc, hv, hinv⟩
    obtain ⟨a, ha, b, hb, hm⟩ : ∃ a ∈ A, ∃ b ∈ B, c ∈ meet a b := by
      simp only [meetLists, List.mem_flatMap, List.mem_filter] at hc
      obtain ⟨a, ha, b, hb, hm, -⟩ := hc
      exact ⟨a, ha, b, hb, hm⟩
    have hh := (meet_sound X P a b n W v).mp ⟨c, hm, hv⟩
    -- What the built-ins asks of a carriesInvariant operand: the meet's clause is not top.
    have side : ∀ d, d.carriesInvariant = true → (d = a ∨ d = b) → builtinInvariant G Z d n W v := by
      intro d hd hdab
      refine builtinInvariant_of_member ⟨hv, hinv⟩ ?_ hd
      rintro rfl
      obtain ⟨rfl, rfl⟩ := top_of_meet hm
      rcases hdab with rfl | rfl <;> cases hd
    refine ⟨⟨a, ha, hh.1, ?_⟩, ⟨b, hb, hh.2, ?_⟩⟩
    · cases har : a.carriesInvariant
      · exact builtinInvariant_of_withoutInvariant har n W v
      · exact side a har (.inl rfl)
    · cases hbr : b.carriesInvariant
      · exact builtinInvariant_of_withoutInvariant hbr n W v
      · exact side b hbr (.inr rfl)
  · rintro ⟨⟨a, ha, hva, hia⟩, ⟨b, hb, hvb, hib⟩⟩
    obtain ⟨c, hc, hv⟩ := (meet_sound X P a b n W v).mpr ⟨hva, hvb⟩
    refine ⟨c, ?_, hv, ?_⟩
    · simp only [meetLists, List.mem_flatMap, List.mem_filter]
      exact ⟨a, ha, b, hb, hc, semWithArgs_consistent hv⟩
    · cases hcr : c.carriesInvariant
      · exact builtinInvariant_of_withoutInvariant hcr n W v
      · rcases carriesInvariant_of_meet hc hcr with har | hbr
        · exact (builtinInvariant_carriesInvariant har hcr).mp hia
        · exact (builtinInvariant_carriesInvariant hbr hcr).mp hib

/-! ## The denotation, at every assignment

The fixed point is over `(assignment, label)`: a scheme row reads its
signatures' rows at reassignments of its binders. -/

variable {k : ParameterSpace}

/-- Argument contracts may read the current assignment directly, as well as
recursive value meanings. This keeps a pack parameter independent of the
value denotation of a graph row. -/
abbrev ArgumentInterpreter (ι : Type) (k : ParameterSpace := .value) :=
  ParameterAssignment k ι → (List ι → Fam) → List ι → ArgFam

/-- Neither grouping arguments nor reading a pack assignment adds a guard.
Agreement must be preserved in both the assignment and recursive meanings. -/
def ArgumentNonExp {k : ParameterSpace} (P : ArgumentInterpreter ι k) : Prop :=
  ∀ η θ X Y n, (∀ p, Agree (η.1 p) (θ.1 p) n) →
    (∀ S, Agree (X S) (Y S) n) → ∀ S, Agree (P η X S) (P θ Y S) n

/-- Interpret argument rows from their shapes and parameter assignments.
Ordinary value rows and value parameters have no argument-list members.
Tuple positions use the recursive value meanings at the current level. -/
def graphArguments (G : NormalGraph ι) : ArgumentInterpreter ι .mixed :=
  fun η X S n W vs => ∃ i ∈ S,
    if G.listParam i then η.1 i n W (.inr vs)
    else ∃ c ∈ G i, clauseArguments X c n W vs

theorem graphArguments_nonexp (G : NormalGraph ι) : ArgumentNonExp (graphArguments G) := by
  intro η θ X Y n hη hX S j hj W vs
  unfold graphArguments
  apply exists_congr fun i => and_congr Iff.rfl ?_
  split
  · exact hη i j hj W (.inr vs)
  · apply exists_congr fun c => and_congr Iff.rfl ?_
    exact clauseArguments_congr X Y c j W (fun a v => hX a j hj W v) vs

/-- Same-level argument interpretation preserves admissibility even for the
unrestricted approximations used to construct the recursive fixed point. -/
theorem graphArguments_adm (G : NormalGraph ι) (η : MixedAssignment ι)
    (X : List ι → Fam) (hX : ∀ S, Adm (X S)) (S : List ι) :
    Adm (graphArguments G η X S) := by
  have position : ∀ t i A, positionFam (tupleFams X t) i = some A → Adm A := by
    intro t i A h
    rw [positionFam_tupleFams] at h
    cases hp : t.position i <;> simp [hp] at h
    subst h
    exact hX _
  apply Adm.of_transfer
  intro n W vs h j hj U hx
  obtain ⟨i, hi, h⟩ := h
  refine ⟨i, hi, ?_⟩
  by_cases hp : G.listParam i = true
  · simp only [hp, if_true] at h ⊢
    exact (η.2 i).1.transfer h j hj U hx
  · simp only [hp, if_false, Bool.false_eq_true] at h ⊢
    obtain ⟨c, hc, h⟩ := h
    refine ⟨c, hc, ?_⟩
    cases c <;> try exact h.elim
    rename_i a bs
    intro t ht
    exact (ArgumentContracts.fits_adm (fun i A hA => position t i A hA)).transfer
      (h t ht) j hj U hx

/-- Argument rows produce admissible contracts on closed lists, so they may
serve as genuine pack substitutions rather than as ordinary value types. -/
theorem graphArguments_valid (G : NormalGraph ι) (η : MixedAssignment ι)
    (X : List ι → Fam) (hX : ∀ S, ValueFam (X S)) (S : List ι) :
    ParameterValid .arguments (graphArguments G η X S) := by
  have position : ∀ t i A, positionFam (tupleFams X t) i = some A → ValueFam A := by
    intro t i A h
    rw [positionFam_tupleFams] at h
    cases hp : t.position i <;> simp [hp] at h
    subst h
    exact hX _
  constructor
  · exact graphArguments_adm G η X (fun S => (hX S).1) S
  · intro n W vs h
    obtain ⟨i, hi, h⟩ := h
    by_cases hp : G.listParam i = true
    · simp only [hp, if_true] at h
      exact (η.2 i).2 n W (.inr vs) h
    · simp only [hp, if_false, Bool.false_eq_true] at h
      obtain ⟨c, hc, h⟩ := h
      cases c <;> try exact h.elim
      rename_i a bs
      exact ArgumentContracts.fits_bound
        (fun i A hA n W v hv => (position a i A hA).2 n W v hv)
        (h a List.mem_cons_self)

/-- One instance's signatures, their rows read at the reassignment. -/
noncomputable def instanceSigs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k)) : List (Arrow Fam) :=
  let η' := assign η s.binders As
  s.signatures.map (Arrow.map (D η'))

/-- One instance's variadic signatures, their rows read at the reassignment. -/
noncomputable def instanceRestsWithArgs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k))
    (P : ArgumentInterpreter ι k) : List RestSignature :=
  let η' := assign η s.binders As
  s.variadic.map (RestArrow.mapWith (D η') (P η' (D η')))

/-- A construct signature as an arrow states it: its arguments, its result
and its effect. A construct signature has no receiver. -/
def ctorOf (a : CallEffects.Contract α β γ) : CallEffects.Contract Unit β γ := a.withReceiver ()

/-- What a scheme's instances meet, as a clause: its call signatures, or its
construct signatures for a construct scheme. -/
def SchemeRow.body (s : SchemeRow ι) : Clause (List ι) :=
  if s.construct then .ctors (s.signatures.map ctorOf) (s.variadic.map ctorOf)
  else .arrs s.signatures s.variadic

/-- The signatures `L` and variadic signatures `S` of one value: call
signatures, as a call clause's are, or construct signatures, as a construct
clause's are. -/
noncomputable def sigsT (Ξ : Fam) (construct : Bool) (L : List (Arrow Fam))
    (S : List CallEffects.RestSignature) : Fam :=
  if construct then interT (ctorsT Ξ (L.map ctorOf)) (ctorRestsT Ξ (S.map ctorOf))
  else interT (CallEffects.callsT Ξ L) (CallEffects.restsT Ξ S)

theorem sigsT_adm (construct : Bool) (L : List (Arrow Fam)) (S : List CallEffects.RestSignature) :
    Adm (sigsT Ξ construct L S) := by
  unfold sigsT
  split
  · exact interT_adm _ _ (ctorsT_adm _) (ctorRestsT_adm _)
  · exact interT_adm _ _ (CallEffects.callsT_adm _) (CallEffects.restsT_adm _)

/-- Signatures whose operands agree below `n` give contracts agreeing there,
call and construct signatures alike. -/
theorem sigsT_congr {Ξ Ξ' : Fam} (construct : Bool) {α β : Type} (l : List α) (f g : α → Arrow Fam)
    (r : List β) (f' g' : β → CallEffects.RestSignature) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments (g x).arguments ∧ Agree (f x).result (g x).result n)
    (he' : ∀ x ∈ r, (f' x).effect = (g' x).effect)
    (h' : ∀ x ∈ r, Agree (f' x).receiver (g' x).receiver n ∧
      ArgsAgree n (f' x).arguments.1 (g' x).arguments.1 ∧
      Agree (f' x).arguments.2 (g' x).arguments.2 n ∧ Agree (f' x).result (g' x).result n)
    (W : WorldT n) (v : Val) :
    sigsT Ξ construct (l.map f) (r.map f') n W v ↔ sigsT Ξ' construct (l.map g) (r.map g') n W v := by
  unfold sigsT
  split
  · simp only [interT, List.map_map]
    exact and_congr
      (ctorsT_congr l (ctorOf ∘ f) (ctorOf ∘ g) hexc
        (fun x hx => ⟨he x hx, (h x hx).2.1, (h x hx).2.2⟩) W v)
      (ctorRestsT_congr r (ctorOf ∘ f') (ctorOf ∘ g') hexc
        (fun x hx => ⟨he' x hx, (h' x hx).2.1, (h' x hx).2.2.1, (h' x hx).2.2.2⟩) W v)
  · exact and_congr (CallEffects.callsT_congr l f g hexc he h W v) (CallEffects.restsT_congr r f' g' hexc he' h' W v)

/-- One instance's contract: its fixed and its variadic signatures, as a call
clause's are, or as a construct clause's are for a construct scheme. -/
noncomputable def instanceTWithArgs (Ξ : Fam) (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k))
    (P : ArgumentInterpreter ι k) : Fam :=
  sigsT Ξ s.construct (instanceSigs D η s As) (instanceRestsWithArgs D η s As (P := P))

theorem instanceTWithArgs_adm (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (As : List (ParameterFamily k)) (P : ArgumentInterpreter ι k) :
    Adm (instanceTWithArgs Ξ D η s As (P := P)) :=
  sigsT_adm _ _ _

private theorem argsAgree_of {X Y : List ι → Fam} {m : Nat} (h : ∀ S, Agree (X S) (Y S) m) :
    ∀ Ss : List (List ι), ArgsAgree m (Ss.map X) (Ss.map Y)
  | [] => .nil
  | S :: Ss => .cons (h S) (argsAgree_of h Ss)

/-- Instances whose rows agree below `m` have contracts agreeing there. -/
theorem instanceT_congrWithArgs {Ξ Ξ' : Fam} (P : ArgumentInterpreter ι k) (hP : ArgumentNonExp P) {D D' : ParameterAssignment k ι → List ι → Fam} {η η' : ParameterAssignment k ι}
    {s : SchemeRow ι} {As As' : List (ParameterFamily k)} {m : Nat}
    (hexc : Agree Ξ Ξ' m)
    (hη : ∀ p, Agree ((assign η s.binders As).1 p) ((assign η' s.binders As').1 p) m)
    (h : ∀ S, Agree (D (assign η s.binders As) S) (D' (assign η' s.binders As') S) m)
    (W : WorldT m) (v : Val) :
    instanceTWithArgs Ξ D η s As (P := P) m W v ↔ instanceTWithArgs Ξ' D' η' s As' (P := P) m W v := by
  unfold instanceTWithArgs instanceSigs instanceRestsWithArgs
  exact sigsT_congr s.construct s.signatures
      (Arrow.map (D (assign η s.binders As))) (Arrow.map (D' (assign η' s.binders As')))
      s.variadic
      (RestArrow.mapWith (D (assign η s.binders As)) (P (assign η s.binders As) (D (assign η s.binders As))))
      (RestArrow.mapWith (D' (assign η' s.binders As')) (P (assign η' s.binders As') (D' (assign η' s.binders As'))))
      hexc
      (fun _ _ => rfl) (fun p _ => ⟨h p.receiver, argsAgree_of h p.arguments, h p.result⟩)
      (fun _ _ => rfl)
      (fun p _ => ⟨h p.receiver, argsAgree_of h p.arguments.1, hP _ _ _ _ m hη h p.arguments.2, h p.result⟩) W v

/-- A scheme's members: values with call code, or class values for a construct
scheme. -/
def Callee (construct : Bool) (v : Val) : Prop :=
  if construct then Constructible v else Invocable v

theorem Callee.obj {c : Bool} {v : Val} (h : Callee c v) :
    ∃ fs code oid, v = .objAt fs code oid ∧ Scoped 0 v := by
  unfold Callee at h
  split at h
  · obtain ⟨fs, n, E, K, s, caps, rest, oid, rfl, hs⟩ := h; exact ⟨_, _, _, rfl, hs⟩
  · obtain ⟨fs, code, oid, rfl, -, hs⟩ := h; exact ⟨_, _, _, rfl, hs⟩

theorem Callee.val {c : Bool} {v : Val} (h : Callee c v) : isVal v = true ∧ Scoped 0 v := by
  unfold Callee at h
  split at h
  · obtain ⟨fs, n, E, K, s, caps, rest, oid, rfl, hs⟩ := h; exact ⟨rfl, hs⟩
  · exact ⟨h.val, h.scoped⟩


/-- A scheme's member has code: it is no plain object. -/
theorem Callee.not_plain {c : Bool} {v : Val} (h : Callee c v) : ∀ flds oid, v ≠ .objAt flds .absent oid := by
  intro flds oid he
  subst he
  unfold Callee at h
  split at h
  · obtain ⟨fs, n, E, K, s, caps, rest, oid', he, -⟩ := h; cases he
  · obtain ⟨fs, code, oid', he, hc, -⟩ := h; cases he; cases hc
/-- Universal quantification has one implementation for both semantic sorts.
The body still denotes a runtime callable; its parameters may denote lists. -/
noncomputable def boundedSem
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (body : List (ParameterFamily k) → Fam)
    (domain : SchemeDomain ι k := .ordinary) : Fam := fun n W v =>
  Callee s.construct v ∧ ∀ j (hj : j ≤ n) As, As.length = s.binders.length →
    domain.allowed s As → Bounded D η s As j → body As j (trunc j hj W) v

/-- The assignment carrier is independent of recursive value outputs. A domain
projects parameter values and derives bounds from those outputs at the same
level. These laws are precisely what the shared guarded fixed point needs. -/
structure ParameterInterpretation (ι : Type) (k : ParameterSpace) where
  domain : SchemeDomain ι k := .ordinary
  parameter : ι → WorldFamily k.Carrier → WorldFamily k.Carrier
  arguments : ArgumentInterpreter ι k
  arguments_nonexp : ArgumentNonExp arguments
  value : ι → WorldFamily k.Carrier → Fam
  value_parameter : ∀ i A B, parameter i A = parameter i B → value i A = value i B
  value_adm : ∀ i A, Adm A → Adm (value i A)
  value_congr : ∀ i A B n, Agree A B n → Agree (value i A) (value i B) n
  bound : ParameterAssignment k ι → (List ι → Fam) → List ι → WorldFamily k.Carrier
  bound_adm : ∀ η X, (∀ S, Adm (X S)) → ∀ S, Adm (bound η X S)
  bound_congr : ∀ η θ X Y n, (∀ p, Agree (η.1 p) (θ.1 p) n) →
    (∀ S, Agree (X S) (Y S) n) → ∀ S, Agree (bound η X S) (bound θ Y S) n
  /-- The assignment the built-in prototype type is read at (`builtinInvariant`).
  That type is `ArrayProto`'s, a declaration without parameters whose generic
  methods bind their own, so it reads no parameter row and means the same at
  every assignment; reading it at one fixed assignment keeps a graph's meaning
  independent of its own assignment, as every check is (`Parametricity`). -/
  builtinsAt : ParameterAssignment k ι

/-- Mixed bounds retain both components. Projecting only their value part would
make a pack bound vacuous. Argument rows are derived, never unfolded again. -/
def mixedParameters (G : NormalGraph ι) : ParameterInterpretation ι .mixed where
  domain := G.domain
  parameter := fun i A => selectParameter (G.parameterKinds i) A
  arguments := graphArguments G
  arguments_nonexp := graphArguments_nonexp G
  value := fun i A n W v => selectParameter (G.parameterKinds i) A n W (.inl v)
  value_parameter := by
    intro i A B h
    funext n W v
    exact congrFun (congrFun (congrFun h n) W) (.inl v)
  value_adm := fun i A h =>
    ⟨fun n W v hv => (selectParameter_adm (G.parameterKinds i) h).down n W (.inl v) hv,
     fun n W U hx v hv => (selectParameter_adm (G.parameterKinds i) h).mono n W U hx (.inl v) hv⟩
  value_congr := fun i _ _ _ h j hj W v => selectParameter_agree (G.parameterKinds i) h j hj W (.inl v)
  bound := fun η X S n W x => match x with
    | .inl v => X S n W v
    | .inr vs => graphArguments G η X S n W vs
  bound_adm := by
    intro η X h S
    have ha := graphArguments_adm G η X h S
    constructor
    · intro n W x hx
      cases x with
      | inl v => exact (h S).down n W v hx
      | inr vs => exact ha.down n W vs hx
    · intro n W U hw x hx
      cases x with
      | inl v => exact (h S).mono n W U hw v hx
      | inr vs => exact ha.mono n W U hw vs hx
  bound_congr := by
    intro η θ X Y n hη hX S j hj W x
    cases x with
    | inl v => exact hX S j hj W v
    | inr vs => exact graphArguments_nonexp G η θ X Y n hη hX S j hj W vs
  builtinsAt := ParameterAssignment.empty .mixed

/-- **A scheme row.** A callable meeting its signatures at every instantiation
of its binders within their bounds: the same value, in the same world, at all
of them. -/
noncomputable def schemeSemWithArgs (I : ParameterInterpretation ι k) (Ξ : Fam) (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) : Fam :=
  boundedSem (fun θ S => I.bound θ (D θ) S) η s (fun As => instanceTWithArgs Ξ D η s As I.arguments) I.domain

/-- A meet row's part, read at the meet's own level (RECURSIVE-EQUATIONS §2.2):
a parameter's family, a scheme row's instances, or a clause row's clauses. It
is the step's reading of a row that is not a meet row, so a meet reads its
parts by one unfolding: a part is never itself a meet row. -/
noncomputable def partSemWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (η : ParameterAssignment k ι) (q : ι) : Fam :=
  if G.params q then I.value q (η.1 q) else
  match G.schemes q with
  | some s => schemeSemWithArgs I (builtinExc G (setSem fun l => X (I.builtinsAt, l))) (fun η' S => setSem (fun l => X (η', l)) S) η s
  | none => setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (η, l))
      (I.arguments η (setSem fun l => X (η, l)))) (G q)

/-- One step of the assignment-indexed denotation. -/
noncomputable def qLayerWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k) (X : ParameterAssignment k ι × ι → Fam) :
    ParameterAssignment k ι × ι → Fam := fun ηi =>
  if G.params ηi.2 then I.value ηi.2 (ηi.1.1 ηi.2) else
  match G.schemes ηi.2 with
  | some s => schemeSemWithArgs I (builtinExc G (setSem fun l => X (I.builtinsAt, l))) (fun η' S => setSem (fun l => X (η', l)) S) ηi.1 s
  | none =>
    match G.meets ηi.2 with
    -- A meet row: each part's values, within the clauses.
    | some (p, cs) => fun n W v =>
        (partSemWithArgs G I X ηi.1 p n W v ∧
          ∀ q ∈ G.meetParams ηi.2, partSemWithArgs G I X ηi.1 q n W v) ∧
        setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (ηi.1, l))
          (I.arguments ηi.1 (setSem fun l => X (ηi.1, l)))) cs n W v
    | none => setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (ηi.1, l))
        (I.arguments ηi.1 (setSem fun l => X (ηi.1, l)))) (G ηi.2)

/-- A parameter part is its assigned family, as in a meet row of parameters. -/
@[simp] theorem partSemWithArgs_param {G : NormalGraph ι} {I : ParameterInterpretation ι k}
    {X : ParameterAssignment k ι × ι → Fam} {η : ParameterAssignment k ι} {q : ι}
    (h : G.params q = true) : partSemWithArgs G I X η q = I.value q (η.1 q) := by
  simp [partSemWithArgs, h]

/-- Outside a meet row, the step reads a row as a part. -/
theorem qLayer_part {G : NormalGraph ι} {I : ParameterInterpretation ι k}
    {X : ParameterAssignment k ι × ι → Fam} {η : ParameterAssignment k ι} {i : ι}
    (h : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none) :
    qLayerWithArgs G I X (η, i) = partSemWithArgs G I X η i := by
  unfold qLayerWithArgs partSemWithArgs
  by_cases hp : G.params i = true
  · simp [hp]
  · simp only [hp, Bool.false_eq_true, ite_false]
    cases hs : G.schemes i with
    | some s => rfl
    | none =>
      have hm : G.meets i = none := by simpa [hp, hs] using h
      simp only [hm]

theorem Agree.mono {A B : WorldFamily α} {n m : Nat} (h : Agree A B n) (hm : m ≤ n) : Agree A B m :=
  fun k hk W v => h k (by omega) W v

/-- A part reads its operands below the level. -/
theorem partSem_congrWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    {X Y : ParameterAssignment k ι × ι → Fam} {n : Nat} (h : ∀ ηi, Agree (X ηi) (Y ηi) n)
    (η : ParameterAssignment k ι) (i : ι) (W : WorldT n) (v : Val) :
    partSemWithArgs G I X η i n W v ↔ partSemWithArgs G I Y η i n W v := by
  unfold partSemWithArgs
  by_cases hp : G.params i = true
  · simp [hp]
  · simp only [hp]
    cases hq : G.schemes i with
    | none =>
      have hS := fun S => setSem_congr n (fun l => h (η, l)) S
      have hE := fun S => setSem_congr n (fun l => h (I.builtinsAt, l)) S
      constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
      · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mp hv
      · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mpr hv
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => forall_congr' fun _ => forall_congr' fun _ => ?_)
      refine imp_congr ?_ ?_
      · unfold Bounded
        refine forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
          forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
          forall_congr' fun u => imp_congr Iff.rfl ?_
        exact I.bound_congr _ _ _ _ n (fun _ _ _ _ _ => Iff.rfl)
          (fun S => setSem_congr n (fun l => h (_, l)) S) b.2 j (by omega) U u
      · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp
          (Agree.mono (builtinExc_congr G _ _ n fun S => setSem_congr n (fun l => h (I.builtinsAt, l)) S) hq)
          (fun _ _ _ _ _ => Iff.rfl) (fun S => Agree.mono (setSem_congr n (fun l => h (_, l)) S) hq) (trunc q hq W) v

theorem qLayer_congrWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    : LayerCongr (fun X => qLayerWithArgs G I X) := by
  intro X Y n h ηi W v
  obtain ⟨η, i⟩ := ηi
  by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
  · dsimp only
    rw [qLayer_part hmeet, qLayer_part hmeet]
    exact partSem_congrWithArgs G I h η i W v
  · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
    obtain ⟨hp, hq, hm⟩ := hmeet
    obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
    unfold qLayerWithArgs
    simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
    have hS := fun S => setSem_congr n (fun l => h (η, l)) S
    have hE := fun S => setSem_congr n (fun l => h (I.builtinsAt, l)) S
    refine and_congr (and_congr (partSem_congrWithArgs G I h η p W v)
      (forall_congr' fun q => imp_congr_right fun _ => partSem_congrWithArgs G I h η q W v)) ?_
    constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
    · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mp hv
    · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mpr hv

/-! ### Non-expansiveness in the assignment

A bounded scheme's admissibility needs more than each step's: an instance
bounded only below a level is replaced by one bounded everywhere, which agrees
with it below that level, so the families read at the two instances must agree
below it too. Every approximation of the fixed point has that property. -/

/-- Assignments agreeing below `m` give families agreeing below `m`. -/
def NonExp (X : ParameterAssignment k ι × ι → Fam) : Prop :=
  ∀ (η η' : ParameterAssignment k ι) (i : ι) (m : Nat), (∀ p, Agree (η.1 p) (η'.1 p) m) →
    Agree (X (η, i)) (X (η', i)) m

/-- The invariant of the approximations: admissible and non-expansive. -/
def QInv (X : ParameterAssignment k ι × ι → Fam) : Prop := (∀ ηi, Adm (X ηi)) ∧ NonExp X

/-- Each smaller approximation retains its own bounded instances. -/
theorem boundedSem_adm
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (body : List (ParameterFamily k) → Fam)
    (_hD : ∀ S, Adm (D η S)) (hbody : ∀ As, Adm (body As))
    (_hcongr : ∀ As Bs m,
      (∀ p, Agree ((assign η s.binders As).1 p) ((assign η s.binders Bs).1 p) m) →
      ∀ W v, body As m W v ↔ body Bs m W v)
    (domain : SchemeDomain ι k := .ordinary) :
    Adm (boundedSem D η s body domain) := by
  constructor
  · intro n W v h
    refine ⟨h.1, fun j hj As hl ha hb => ?_⟩
    simpa only [trunc_trunc] using h.2 j (by omega) As hl ha hb
  · intro n W W' hx v h
    exact ⟨h.1, fun j hj As hl ha hb =>
      (hbody As).mono j _ _ (WExt_trunc hj hx) v (h.2 j hj As hl ha hb)⟩

/-- A part is admissible, and non-expansive in the assignment. -/
theorem partSem_invWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (hX : QInv X) :
    (∀ η i, Adm (partSemWithArgs G I X η i)) ∧
    ∀ η η' i m, (∀ p, Agree (η.1 p) (η'.1 p) m) →
      Agree (partSemWithArgs G I X η i) (partSemWithArgs G I X η' i) m := by
  obtain ⟨hadm, hne⟩ := hX
  have hD : ∀ (η : ParameterAssignment k ι) S, Adm (setSem (fun l => X (η, l)) S) :=
    fun η S => setSem_adm (fun l => hadm (η, l)) S
  -- Families read at assignments agreeing below `m` agree below `m`.
  have sets : ∀ (η η' : ParameterAssignment k ι) m, (∀ p, Agree (η.1 p) (η'.1 p) m) → ∀ S,
      Agree (setSem (fun l => X (η, l)) S) (setSem (fun l => X (η', l)) S) m :=
    fun η η' m h S => setSem_congr m (fun l => hne η η' l m h) S
  -- Reassigning the same binders keeps agreement.
  have reassign : ∀ (η η' : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) m,
      (∀ p, Agree (η.1 p) (η'.1 p) m) →
      ∀ p, Agree ((assign η bs As).1 p) ((assign η' bs As).1 p) m := by
    intro η η' bs As m h p
    classical
    simp only [assign]
    split
    · exact fun j _ W v => Iff.rfl
    · exact h p
  refine ⟨fun η i => ?_, fun η η' i m h => ?_⟩
  · -- admissible
    unfold partSemWithArgs
    by_cases hp : G.params i = true
    · simpa [hp] using I.value_adm i (η.1 i) (η.2 i).1
    · simp only [hp]
      cases hq : G.schemes i with
      | none => exact setSem_adm (fun c => rowSem_adm G _ _ _ c) (G i)
      | some s =>
        exact boundedSem_adm _ η s _ (I.bound_adm η _ (hD η))
          (fun As => instanceTWithArgs_adm _ η s As I.arguments)
          (fun As Bs m h W v => instanceT_congrWithArgs I.arguments I.arguments_nonexp (fun _ _ _ _ => Iff.rfl) h (fun S => sets _ _ m h S) W v) I.domain
  · -- non-expansive
    intro k hk W v
    unfold partSemWithArgs
    by_cases hp : G.params i = true
    · simp only [hp, if_true]; exact I.value_congr i _ _ m (h i) k hk W v
    · simp only [hp]
      cases hq : G.schemes i with
      | none =>
        have cl : ∀ cs : List (Clause (List ι)),
            setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (η, l)) (I.arguments η (setSem fun l => X (η, l)))) cs k W v ↔
              setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (η', l)) (I.arguments η' (setSem fun l => X (η', l)))) cs k W v := by
          intro cs
          constructor
          · rintro ⟨c, hc, hv⟩
            exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
              (fun a => Agree.mono (sets η η' m h a) (by omega))
              (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mp hv⟩
          · rintro ⟨c, hc, hv⟩
            exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
              (fun a => Agree.mono (sets η η' m h a) (by omega))
              (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mpr hv⟩
        exact cl _
      | some s =>
        refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => forall_congr' fun _ => forall_congr' fun _ => ?_)
        have hre := reassign η η' s.binders As m h
        refine imp_congr ?_ ?_
        · unfold Bounded
          refine forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
            forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
            forall_congr' fun u => imp_congr (hre b.1 j (by omega) U u)
              (I.bound_congr η η' _ _ m h (sets η η' m h) b.2 j (by omega) U u)
        · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp (fun _ _ _ _ => Iff.rfl) (fun p => Agree.mono (hre p) (by omega)) (fun S => Agree.mono (sets _ _ m hre S) (by omega)) (trunc q hq W) v

theorem qLayer_invWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (hX : QInv X) :
    QInv (qLayerWithArgs G I X) := by
  obtain ⟨hpa, hpn⟩ := partSem_invWithArgs G I X hX
  obtain ⟨hadm, hne⟩ := hX
  have sets : ∀ (η η' : ParameterAssignment k ι) m, (∀ p, Agree (η.1 p) (η'.1 p) m) → ∀ S,
      Agree (setSem (fun l => X (η, l)) S) (setSem (fun l => X (η', l)) S) m :=
    fun η η' m h S => setSem_congr m (fun l => hne η η' l m h) S
  refine ⟨fun ηi => ?_, fun η η' i m h => ?_⟩
  · obtain ⟨η, i⟩ := ηi
    by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
    · rw [qLayer_part hmeet]; exact hpa η i
    · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
      obtain ⟨hp, hq, hm⟩ := hmeet
      obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
      unfold qLayerWithArgs
      simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
      have hqs : Adm (fun n W v => ∀ q ∈ G.meetParams i, partSemWithArgs G I X η q n W v) :=
        ⟨fun n W v h q hq => (hpa η q).down n W v (h q hq),
         fun n W U hx v h q hq => (hpa η q).mono n W U hx v (h q hq)⟩
      exact interT_adm _ _ (interT_adm _ _ (hpa η p) hqs)
        (setSem_adm (fun c => rowSem_adm G _ _ _ c) cs)
  · intro k hk W v
    by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
    · rw [qLayer_part hmeet, qLayer_part hmeet]; exact hpn η η' i m h k hk W v
    · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
      obtain ⟨hp, hq, hm⟩ := hmeet
      obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
      unfold qLayerWithArgs
      simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
      refine and_congr (and_congr (hpn η η' p m h k hk W v)
        (forall_congr' fun q => imp_congr_right fun _ => hpn η η' q m h k hk W v)) ?_
      constructor
      · rintro ⟨c, hc, hv⟩
        exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
          (fun a => Agree.mono (sets η η' m h a) (by omega))
          (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mp hv⟩
      · rintro ⟨c, hc, hv⟩
        exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
          (fun a => Agree.mono (sets η η' m h a) (by omega))
          (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mpr hv⟩

/-- One assignment-indexed fixed point for both value and argument
interpretations. The latter's agreement law supplies no extra delay. -/
noncomputable def qDenoteWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k) :
    ParameterAssignment k ι × ι → Fam := Tower.denote (fun X => qLayerWithArgs G I X)

theorem qDenoteWithArgs_unfold (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (ηi : ParameterAssignment k ι × ι) (n : Nat) (W : WorldT n) (v : Val) :
    qDenoteWithArgs G I ηi n W v ↔ qLayerWithArgs G I (qDenoteWithArgs G I) ηi n W v :=
  Tower.denote_unfold (qLayer_congrWithArgs G I) ηi n W v

theorem qDenoteWithArgs_adm (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (ηi : ParameterAssignment k ι × ι) : Adm (qDenoteWithArgs G I ηi) :=
  Tower.denote_adm_inv (qLayer_congrWithArgs G I) QInv
    ⟨fun _ => topF_adm, fun _ _ _ _ _ _ _ _ _ => Iff.rfl⟩
    (qLayer_invWithArgs G I) (fun _ h => h.1) ηi

/-- Both semantic components of a type, derived from one recursive value
interpretation. Argument rows are evaluated at that same level. -/
noncomputable def mixedMeaning (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι) :
    WorldFamily ParameterSpace.mixed.Carrier :=
  (mixedParameters G).bound η
    (setSem fun i => qDenoteWithArgs G (mixedParameters G) (η, i)) S

/-- The shared fixed point still produces only closed runtime values. -/
theorem mixedDenote_value (G : NormalGraph ι) (η : MixedAssignment ι) (i : ι) {n W v}
    (h : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    isVal v = true ∧ Scoped 0 v := by
  rw [qDenoteWithArgs_unfold] at h
  unfold qLayerWithArgs at h
  split at h
  · rcases h with ⟨_, h⟩ | ⟨_, h, _⟩ <;> exact (η.2 i).2 n W (.inl v) h
  · cases hs : G.schemes i with
    | some s => simp only [hs] at h; exact h.1.val
    | none =>
      simp only [hs] at h
      cases hm : G.meets i with
      | none =>
        simp only [hm] at h
        obtain ⟨c, _, hc⟩ := h
        exact semWithArgs_value hc.1
      | some pc =>
        simp only [hm] at h
        obtain ⟨c, _, hc⟩ := h.2
        exact semWithArgs_value hc.1

theorem mixedMeaning_valid (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι) :
    ParameterValid .mixed (mixedMeaning G η S) := by
  let X := fun S => setSem (fun i => qDenoteWithArgs G (mixedParameters G) (η, i)) S
  have hX : ∀ S, ValueFam (X S) := fun S =>
    ⟨setSem_adm (fun i => qDenoteWithArgs_adm G (mixedParameters G) (η, i)) S,
     fun _ _ _ ⟨i, _, hi⟩ => mixedDenote_value G η i hi⟩
  refine ⟨(mixedParameters G).bound_adm η X (fun S => (hX S).1) S, ?_⟩
  intro n W x h
  cases x with
  | inl v => exact (hX S).2 n W v h
  | inr vs => exact (graphArguments_valid G η X hX S).2 n W vs h

/-- A parameter's two-component row meaning is exactly its selected component,
not the whole (potentially mixed) family assigned to that binder. -/
theorem mixedMeaning_parameter (G : NormalGraph ι) (η : MixedAssignment ι) (i : ι)
    (kind : ParameterKind) (hi : G.parameterKinds i = some kind) :
    mixedMeaning G η [i] = selectParameter (some kind) (η.1 i) := by
  have hp : G.params i = true := by simp [NormalGraph.params, hi]
  have hc : G i = [] := by simp [NormalGraph.clauses, NormalGraph.plain, hp]
  funext n W x
  apply propext
  cases x with
  | inl v =>
    change (∃ j ∈ [i], qDenoteWithArgs G (mixedParameters G) (η, j) n W v) ↔ _
    simp only [List.mem_singleton, exists_eq_left]
    rw [qDenoteWithArgs_unfold]
    simp [qLayerWithArgs, hp, mixedParameters, selectParameter, hi]
  | inr vs =>
    change graphArguments G η _ [i] n W vs ↔ _
    cases kind <;> simp [graphArguments, hc, hi, selectParameter, NormalGraph.listParam]

/-- A sorted pack type cannot contribute runtime-value members, including
unions of pack rows and pack parameters. -/
theorem mixedMeaning_noValues (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι)
    (hs : G.hasKind .arguments S = true) (n : Nat) (W : WorldT n) (v : Val) :
    ¬ mixedMeaning G η S n W (.inl v) := by
  rintro ⟨i, hi, hv⟩
  have hk := List.all_eq_true.mp hs i hi
  rw [qDenoteWithArgs_unfold] at hv
  unfold qLayerWithArgs at hv
  cases hp : G.parameterKinds i with
  | some k =>
    cases k <;> simp [hp] at hk
    simp [NormalGraph.params, hp, mixedParameters, selectParameter] at hv
  | none =>
    cases hq : G.schemes i with
    | some sch => simp [hp, hq] at hk
    | none =>
      cases hm : G.meets i with
      | some pc => simp [hp, hq, hm] at hk
      | none =>
      simp only [NormalGraph.params, hp, Option.isSome_none, Bool.false_eq_true, ite_false, hq, hm] at hv
      obtain ⟨c, hc, hcv⟩ := hv
      have hplain : G.plain i = true := by simp [NormalGraph.plain, NormalGraph.params, hp, hq, hm]
      have hr : c ∈ G.rows i := by simpa [NormalGraph.clauses, hplain] using hc
      have ht := List.all_eq_true.mp (show (G.rows i).all
        (fun c => match c with | .pack .. => true | _ => false) = true by simpa [hp, hq, hm, (show (ParameterKind.arguments == ParameterKind.value) = false from rfl)] using hk) c hr
      cases c <;> simp_all [rowSem, semWithArgs]

/-- A sorted value type cannot contribute argument-list members. -/
theorem mixedMeaning_noArguments (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι)
    (hs : G.hasKind .value S = true) (n : Nat) (W : WorldT n) (vs : List Val) :
    ¬ mixedMeaning G η S n W (.inr vs) := by
  rintro ⟨i, hi, hv⟩
  have hk := List.all_eq_true.mp hs i hi
  by_cases hp : G.listParam i = true
  · rcases NormalGraph.listParam_iff.mp hp with hp | hp <;> simp [hp] at hk
  · simp only [hp, if_false, Bool.false_eq_true] at hv
    obtain ⟨c, hc, hv⟩ := hv
    have hplain := NormalGraph.plain_of_clauses hc
    have hparts := NormalGraph.plain_iff.mp hplain
    have hn : G.parameterKinds i = none := by
      simpa [NormalGraph.params] using hparts.1
    have hr : c ∈ G.rows i := by simpa [NormalGraph.clauses, hplain] using hc
    have ht := List.all_eq_true.mp (show (G.rows i).all
      (fun c => match c with | .pack .. => false | _ => true) = true by
        simpa [hn, hparts.2.1, hparts.2.2, (show (ParameterKind.value == ParameterKind.arguments) = false from rfl)] using hk) c hr
    cases c <;> simp_all [clauseArguments]

/-- The existing sort check guarantees that a type image equals its selected
component. This connects the wire's kind check to semantic correspondence. -/
theorem mixedMeaning_selected (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι)
    (kind : ParameterKind) (hs : G.hasKind kind S = true) :
    selectParameter (some kind) (mixedMeaning G η S) = mixedMeaning G η S := by
  funext n W x
  apply propext
  cases kind <;> cases x
  · simp [selectParameter]
  · simp [selectParameter, mixedMeaning_noArguments G η S hs]
  · simp [selectParameter, mixedMeaning_noValues G η S hs]
  · simp [selectParameter]
  · -- A packed-sorted type is a union of packed parameter rows, each of
    -- whose values is packable by its own lists, so by the union's.
    rename_i v
    simp only [selectParameter]
    constructor
    · rintro (⟨hk, _⟩ | ⟨_, h, _⟩)
      · cases hk
      · exact h
    · intro h
      refine Or.inr ⟨by simp, h, ?_⟩
      obtain ⟨i, hi, hv⟩ := h
      have hk := List.all_eq_true.mp hs i hi
      rw [qDenoteWithArgs_unfold] at hv
      unfold qLayerWithArgs at hv
      cases hp : G.parameterKinds i with
      | some k =>
        cases k <;> simp [hp] at hk
        simp [NormalGraph.params, hp, mixedParameters, selectParameter] at hv
        refine Packable_mono ?_ hv.2
        intro m U vs hvs
        exact ⟨i, hi, by simpa [NormalGraph.listParam, hp] using hvs⟩
      | none =>
        cases hq : G.schemes i with
        | some sch => simp [hp, hq] at hk
        | none =>
          cases hm : G.meets i with
          | some pc => simp [hp, hq, hm] at hk
          | none =>
          simp only [NormalGraph.params, hp, Option.isSome_none, Bool.false_eq_true, ite_false, hq, hm] at hv
          obtain ⟨c, hc, _⟩ := hv
          have hplain : G.plain i = true := by simp [NormalGraph.plain, NormalGraph.params, hp, hq, hm]
          have hr : c ∈ G.rows i := by simpa [NormalGraph.clauses, hplain] using hc
          simp only [hp, hq, hm, Option.isSome_none, Bool.or_false, Bool.false_eq_true, ite_false,
            List.all_eq_true] at hk
          have := hk c hr
          cases c <;> simp at this
  · simp [selectParameter]

/-- A graph's meaning reads its parameter rows at its own assignment. -/
noncomputable def normalDenote (G : NormalGraph ι) (i : ι) : Fam :=
  qDenoteWithArgs G (mixedParameters G) (G.env, i)

theorem normalDenote_adm (G : NormalGraph ι) (i : ι) : Adm (normalDenote G i) :=
  qDenoteWithArgs_adm G (mixedParameters G) _

/-- The argument lists a type admits: a pack parameter's assigned contract, or
a pack clause's tuple contracts, at the current level. -/
noncomputable def argMeaning (G : NormalGraph ι) (S : List ι) : ArgFam :=
  graphArguments G G.env (setSem (normalDenote G)) S

/-- A clause row means its clauses. -/
theorem unfold_plain {G : NormalGraph ι} {i : ι} (hi : G.plain i = true) (n W v) :
    normalDenote G i n W v ↔ setSem (rowSem G (setSem fun l => qDenoteWithArgs G (mixedParameters G)
      (ParameterAssignment.empty .mixed, l)) (setSem (normalDenote G)) (argMeaning G)) (G i) n W v := by
  simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hi
  unfold normalDenote
  rw [qDenoteWithArgs_unfold]
  simp only [qLayerWithArgs, hi.1, hi.2, Bool.false_eq_true, ite_false]
  rfl

/-- Every label means closed values only, whatever its kind. -/
theorem normalDenote_value {G : NormalGraph ι} {i : ι} {n W v}
    (h : normalDenote G i n W v) : isVal v = true ∧ Scoped 0 v :=
  mixedDenote_value G G.env i h

end Verification.PositiveGraphs
