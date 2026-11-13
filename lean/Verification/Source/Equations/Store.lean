import Verification.Source.Equations.Lowering
-- ResolutionCapabilities.lean classifies stable, native and union resolution inputs over the native Promise constructor; without it source requests have no descriptor domain.
import Verification.Source.ResolutionCapabilities
-- ../Types/EquationDomains.lean proves that installing the descriptor domain preserves the native Promise region's meaning; without it the store cannot use qualified generics.
import Verification.Types.EquationDomains
-- ../Types/NativePromiseSeparation.lean proves from the source graph that no native Promise type lies within the stable bound; without it native lifting cannot meet stable exactness.
import Verification.Types.NativePromiseSeparation

/-! The label store over recursive equations (RECURSIVE-EQUATIONS §8;
REQUEST-PROTOCOL.md, "Equations and tree labels").
Extraction grows the lowering's heads (`EquationLowering.State`), its labels
closed trees (`Tree`): a union of clauses, a scheme over fresh binders and a
bounded binder's meet become heads with lifted templates, and a binder the
source spells by its name is read as the label a unit or closure gives it
(`rebind`). A label's row is its head's template instantiated at its
arguments, which leaves every application inside unexpanded, exactly as
`Equations.row` reads it, so no family is enumerated.

A checked request is over the equations the extracted heads present,
validated by `Equations.ofRaw` once extraction is done (`freeze`): its labels
are the closed labels of those equations, and its graph is their
`Equations.graph` (`Checked`). -/
namespace Verification.EquationStore
open Lean EquationGraphs EquationLowering PositiveGraphs PositiveNormalization PositiveRules
  PositiveCertificates LabelStore RequestJson CallEffects

abbrev State := EquationLowering.State

/-! ### Rows -/

/-- A label's row, not a meet's (`Equations.baseRow`). -/
def baseRow (s : State) (t : Tree) : GraphRow Tree :=
  match t with
  | .app h args => match s.heads[h]?.bind (·.body) with
    | some body => instantiateRow h args body
    | none => .clauses []
  | .bound h _ j => match s.heads[h]?.bind (·.binders[j]?) with
    | some b => .param t b.name b.kind
    | none => .clauses []
  | .var _ _ k => .param t "var" k
  | _ => .clauses []

/-- A label's row (`Equations.row`): a meet's from its parts' rows. -/
def rowOf (s : State) (t : Tree) : GraphRow Tree :=
  match t with
  | .meet ps => meetRowOf (ps.toList.map fun q => (q, baseRow s q))
  | t => baseRow s t

/- Whether a tree is a closed label of the heads (`Tree.scoped` at no
parameter and no local). -/
mutual
partial def closedTree (s : State) : Tree → Bool
  | .app h args => (s.heads[h]?.any fun d => d.kinds.length == args.toList.length) && closedArgs s args
  | .bound h args j =>
    (s.heads[h]?.any fun d => d.kinds.length == args.toList.length && j < d.binders.length) &&
      closedArgs s args
  | .argument _ | .local _ => false
  | .var .. => true
  | .meet ps => ps.toList.all fun t => closedTree s t && !t.isMeet
partial def closedArgs (s : State) (args : Args) : Bool :=
  args.toList.all fun ts => ts.toList.all (closedTree s)
end

/-- The built-in arrays, where the heads state any: `ArrayProto` and the keys
it provides. -/
def builtins (s : State) : Option (ArrayBuiltins Tree) :=
  if s.arrays then s.proto.bind fun p => (s.keys.get? unknownKey).map fun u =>
    ⟨[mkApp p []], [mkApp u []], s.excluded⟩ else none

/-! ### Growing the store -/

/-- Run a lowering step on the store. A step that fails leaves an open tree,
which no store holds (`closedTree`), so a request mentioning it is refused
rather than read at another type. -/
def grow (s : State) (m : M Tree) : State × Tree :=
  match m.run s with
  | .ok (t, s) => (s, t)
  | .error _ => (s, .argument 0)

/-- Whether a clause is an array's: it owns the array store. -/
def arrayShaped (c : Clause (List Tree)) : Bool :=
  c.presentKeys.contains CallArguments.arrayStoreField

def intern (s : State) (cs : List (Clause (List Tree))) : State × Tree :=
  let s := if cs.any arrayShaped then { s with arrays := true } else s
  grow s (internLifted "type" cs)

def lookup (s : State) (cs : List (Clause (List Tree))) : Option Tree :=
  let (key, args) := internKey s.heads cs
  (s.keys.get? key).map fun h => mkApp h args

/-- A label's row form (`rowOf`'s), read without instantiating a template:
an instance has its template's form (`GraphRow.map` keeps it), and a meet is
a meet row exactly when one of its parts is no clause row (`meetRowOf`). -/
def baseForm (s : State) (t : Tree) : RowForm :=
  match t with
  | .app h _ => match s.heads[h]?.bind (·.body) with
    | some body => GraphRow.form body
    | none => .clauses
  | .bound h _ j => if (s.heads[h]?.bind (·.binders[j]?)).isSome then .param else .clauses
  | .var .. => .param
  | _ => .clauses

def rowForm (s : State) (t : Tree) : RowForm :=
  match t with
  | .meet ps => if ps.toList.all (baseForm s · == .clauses) then .clauses else .meet
  | t => baseForm s t

/-- A label's row, a nullary head's read from the state's (`State.nullary`). -/
def cachedRow (s : State) (t : Tree) : GraphRow Tree :=
  match t with
  | .app h .nil => match s.nullary[h]? with
    | some r => r.get
    | none => rowOf s t
  | t => rowOf s t

/-- The rows' graph, read through two shortcuts: a field at a label of
another form is answered from the label's form alone, so a test of a row's
form (`NormalGraph.plain`) instantiates no template, and a nullary head's
row is instantiated at most once while its head is unchanged, which a search
reads at every step. Equal to `rowGraph` (`graph_eq`). -/
def graph (s : State) : NormalGraph Tree :=
  NormalGraph.ofRowMapForms (cachedRow s) (rowForm s) (builtins s) .ordinary
    fun | .num b => lookup s [.numLit b] | .str v => lookup s [.strLit v]

/-- A value parameter within clauses and further parameters, `p ⊓ cs ⊓ also`:
the meet label of its parts (§3.3), the clauses a head of their own. -/
def bounded (s : State) (p : Tree) (cs : List (Clause (List Tree))) (also : List Tree) : State × Tree :=
  let (s, part) := if cs == [.top] then (s, none) else
    let (s, l) := intern s cs
    (s, some l)
  match also ++ part.toList with
  | [] => (s, p)
  | rest => (s, canonMeet (p :: rest))

/-- A name placeholder's name, if it is one. -/
def placeholderName (s : State) : Tree → Option String
  | .var o i _ => if o == nameOwner then (s.names[i]?).map (·.1) else none
  | _ => none

/-- A label with the named binders read as `θ` gives them. -/
def rebind (s : State) (θ : List (String × List Tree)) (t : Tree) : List Tree :=
  normUnion (treeReplace (fun u => (placeholderName s u).bind fun n => θ.lookup n) t)

/-! ### What a diagnostic shows (OBLIGATION-DIAGNOSTICS, "The label projection") -/

/-- A label's spelling: an application as its head's name at its arguments
(`Promise<number | R>`), an owned parameter as its binder's name. -/
partial def spell (s : State) : Tree → String
  | .app h args =>
    let name := ((s.heads[h]?).map (·.name)).getD s!"#{h}"
    if args.toList.isEmpty then name
    else name ++ "<" ++ ", ".intercalate (args.toList.map fun ts => spellUnion s ts.toList) ++ ">"
  | .bound h _ j => (((s.heads[h]?).bind (·.binders[j]?)).map (·.name)).getD s!"#{h}.{j}"
  | .meet ps => " & ".intercalate (ps.toList.map (spell s))
  | .var o i _ => if o == nameOwner then ((s.names[i]?).map (·.1)).getD "?" else
      if o == freshOwner then ((s.fresh[i]?)).getD "?" else s!"?{o}.{i}"
  | .argument i => s!"arg {i}"
  | .local j => s!"local {j}"
where
  spellUnion (s : State) (U : List Tree) : String :=
    if U.isEmpty then "never" else " | ".intercalate (U.map (spell s))

/-- Whether a label is shown by a name: anything but a nullary head's
application. -/
def named : Tree → Bool
  | .app _ args => !args.toList.isEmpty
  | _ => true

/-- The labels a row names. -/
def rowLabels (r : GraphRow Tree) : List Tree :=
  match r with
  | .clauses cs => cs.flatMap fun c => c.operands.flatten
  | .scheme bs sigs bounds rests _ _ =>
    bs ++ sigs.flatMap (fun a => a.operands.flatten) ++ bounds.flatMap (fun (b, U) => b :: U) ++
      rests.flatMap fun a => a.operands.flatten
  | .param l _ _ => [l]
  | .meet p cs ps => p :: ps ++ cs.flatMap fun c => c.operands.flatten

/-- The projection of `mentioned`: positions for them and for the labels
their rows name, `depth` row references deep; past that, a label is an
opaque named row. -/
def projectWith (row : Tree → GraphRow Tree) (name : Tree → String) (mentioned : List Tree)
    (depth : Nat) : Projection Tree := Id.run do
  let mut order : Array Tree := #[]
  let mut index : Std.HashMap Tree Nat := {}
  let mut expanded : Std.HashMap Tree Unit := {}
  let mut frontier : List Tree := []
  for t in mentioned do
    if !index.contains t then
      index := index.insert t order.size
      order := order.push t
      frontier := frontier ++ [t]
  for _ in [0:depth] do
    let mut next : List Tree := []
    for t in frontier do
      expanded := expanded.insert t ()
      for u in rowLabels (row t) do
        if !index.contains u then
          index := index.insert u order.size
          order := order.push u
          next := next ++ [u]
    frontier := next
  let at_ (t : Tree) : Nat := (index.get? t).getD 0
  let rows := order.toList.map fun t =>
    if expanded.contains t then (row t).map at_ (·.map at_) else .clauses []
  let names := order.toList.zipIdx.filterMap fun (t, i) =>
    if named t || !expanded.contains t then some (i, name t) else none
  return { rows, position := at_, names }

/-! ### The store -/

instance : ToJson State where
  toJson s := .arr (s.heads.map fun d => Json.mkObj ([
      ("name", toJson d.name),
      ("parameters", toJson (d.kinds.zipIdx.map fun (k, i) =>
        Json.mkObj [("name", toJson s!"T{i}"), ("kind", toJson k)]))] ++
    (if d.binders.isEmpty then [] else [("binders", toJson (d.binders.map fun b =>
        Json.mkObj [("name", toJson b.name), ("kind", toJson b.kind)]))]) ++
    [("body", match d.body with
      | some b => toJson b
      | none => .null)]))

/-- The equations' own spelling (REQUEST-PROTOCOL.md, "Equations and tree
labels"): each head's name, parameters, binders
and template. The built-ins is what the templates state: the prototype an
array's clause views, and the keys that prototype's row provides. -/
instance : FromJson State where
  fromJson? j := do
    let heads ← (← j.getArr?).mapM fun h => do
      let fields := ["name", "parameters", "body"] ++ if (h.getObjVal? "binders").isOk then ["binders"] else []
      fieldsExactly h fields
      let kinds ← (← (← h.getObjVal? "parameters").getArr?).mapM fun p => do
        fieldsExactly p ["name", "kind"]
        let _ ← p.getObjValAs? String "name"
        p.getObjValAs? ParameterKind "kind"
      let binders ← match h.getObjVal? "binders" with
        | .ok bs => (← bs.getArr?).mapM fun b => do
          fieldsExactly b ["name", "kind"]
          return (⟨← b.getObjValAs? String "name", ← b.getObjValAs? ParameterKind "kind"⟩ : Binder)
        | .error _ => pure #[]
      if (h.getObjVal? "binders").isOk && binders.isEmpty then throw "binders are left out when there are none"
      let body : GraphRow Tree (List Tree) ← fromJson? (← h.getObjVal? "body")
      let kind : HeadKind := match body with
        | .clauses _ => if kinds.isEmpty then .primitive else .literal
        | _ => .scheme
      return ({ name := ← h.getObjValAs? String "name", kind, kinds := kinds.toList,
                binders := binders.toList, body := some body } : Draft)
    let keys := (List.range heads.size).foldl (fun (m : Std.HashMap String Nat) h =>
      match heads[h]!.kind, heads[h]!.body with
      | .primitive, some (.clauses cs) => if m.contains s!"ground|{spelling cs}" then m
          else m.insert s!"ground|{spelling cs}" h
      | _, _ => m) {}
    let arrayProtos : List (List Tree) := heads.toList.flatMap fun d => match d.body with
      | some (.clauses cs) => cs.filterMap fun c => if arrayShaped c then
          (match c with
            | .refs a bs vs .. => (Stored.views (a :: bs).flatten ++ vs).lookup CallArguments.protoField
            | _ => none)
          else none
      | _ => []
    let (arrays, proto, excluded) ← match arrayProtos.eraseDups with
      | [] => pure (false, none, [])
      | [[.app p args]] =>
        if !args.toList.isEmpty then throw "an array's prototype is a nullary head's application"
        let cs := match heads[p]?.bind (·.body) with
          | some (.clauses cs) => cs
          | _ => []
        pure (true, some p, arrayExcludedKeysOf cs)
      | _ => throw "every array views one prototype, a nullary head's application"
    -- The built-ins' `unknown`, the type of an array's elements, where arrays are.
    let unknown : Draft := { name := "unknown", kind := .primitive, kinds := [], body := some (.clauses [.source]) }
    let (heads, keys) := if arrays && !keys.contains unknownKey then
        (heads.push unknown, keys.insert unknownKey heads.size)
      else (heads, keys)
    return { doc := #[], heads, keys, arrays, proto, excluded }

/-- Fresh value parameters, one per name, for a scheme's binders. They stand
for the scheme's binders until `scheme` binds them: the scheme's own binders
are its row's (`GraphRow.scheme`), which may be other labels. -/
def binders (s : State) (names : List String) (packed : List String := []) : State × List Tree :=
  names.foldl (fun (s, ls) n =>
    let (s, l) := grow s (freshBinder n (if packed.contains n then .packed else .value)); (s, ls ++ [l])) (s, [])

/-- A scheme over binders from `binders`: its signatures, its binders' bounds
and its variadic signatures, call signatures or, for a construct scheme,
construct signatures. -/
def scheme (s : State) (bs : List Tree) (sigs : List (Arrow (List Tree))) (bounds : List (Tree × List Tree))
    (rests : List (RestArrow (List Tree))) (construct : Bool := false) : State × Tree :=
  grow s (schemeOver bs sigs bounds rests construct)

/-- A label with the labels `σ` names read as the labels it pairs them with:
a scheme's fresh binders read as its own (`scheme`). The union a label
becomes. -/
def substitute (σ : List (Tree × Tree)) (t : Tree) : List Tree :=
  normUnion (treeReplace (fun u => (σ.lookup u).map ([·])) t)

/-- The meet of unions, lowered as a source intersection is: the exact meet
labels over their product (§3.3); an empty part is the empty intersection,
refused. -/
def meet (parts : List (List Tree)) : StateT State (Except String) (List Tree) := do
  if parts.any List.isEmpty then throw emptyMeet
  return meetUnions parts

/-- What checking reads of the store. A store only grows: every operation
above keeps the labels it had and their rows. -/
instance : StoreView State Tree where
  graph := graph
  row := rowOf
  valid := closedTree
  wellFormed s := s.heads.all (·.body.isSome)
  labels s := (List.range s.heads.size).filterMap fun h =>
    if s.heads[h]!.kinds.isEmpty then some (mkApp h []) else none
  -- Rows reach infinitely many labels: a closure over them is search's.
  bound _ := CertificateProducer.searchLimit
  arrayProto s := match s.proto with
    | some p => mkApp p []
    | none => mkApp 0 []
  lookup := lookup
  project s mentioned depth := projectWith (rowOf s) (spell s) mentioned depth
  images s := { finiteInstanceImages (graph s) with budget := s.subtypeBudget }

/-! ### Checked requests: the equations, frozen -/

/-- The four primitive values' heads are nullary heads 0 to 3. -/
structure Primitive (E : Equations) : Prop where
  nul : (Tree.app 0 .nil).scoped E.signature 0 0 = true
  tru : (Tree.app 1 .nil).scoped E.signature 0 0 = true
  fls : (Tree.app 2 .nil).scoped E.signature 0 0 = true
  undef : (Tree.app 3 .nil).scoped E.signature 0 0 = true

def primitive (E : Equations) : Except String (PLift (Primitive E)) :=
  if h : (Tree.app 0 .nil).scoped E.signature 0 0 = true ∧ (Tree.app 1 .nil).scoped E.signature 0 0 = true ∧
      (Tree.app 2 .nil).scoped E.signature 0 0 = true ∧ (Tree.app 3 .nil).scoped E.signature 0 0 = true then
    .ok ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  else .error "the equations' first four heads are the primitive values"

/-- A closed label of `E`. `p` fixes the primitive values' labels. -/
def CheckedLabel (E : Equations) (_ : Primitive E) : Type := Label E.signature

/-- A checked label's tree. -/
def CheckedLabel.tree {E : Equations} {p : Primitive E} (l : CheckedLabel E p) : Tree :=
  (l : Label E.signature).1

/-- Whether a tree holds a placeholder: a binder no unit or closure read. -/
partial def hasPlaceholder : Tree → Bool
  | t@(.var ..) => isPlaceholder t
  | .app _ args | .bound _ args _ => args.toList.any fun ts => ts.toList.any hasPlaceholder
  | .meet ps => ps.toList.any hasPlaceholder
  | _ => false

section
variable {E : Equations} {p : Primitive E}

instance : Labels (CheckedLabel E p) where
  toHashable := ⟨fun l => hash l.tree⟩
  toOrd := ⟨fun a b => compare a.tree b.tree⟩
  toToJson := ⟨fun l => Tree.toJson l.tree⟩
  toFromJson := ⟨fun j => do
    let t ← Tree.fromJson j
    if hasPlaceholder t then throw "a label names a binder no unit or closure reads"
    let l : Label E.signature ← Label.ofTreeIn E.signature E.headers E.headers_eq t
    return l⟩
  toRepr := ⟨fun l n => reprPrec l.tree n⟩
  -- Two applications of different heads are compared through the
  -- equations' unfolding of each.
  toInstantiates := ⟨fun s L M => (proposeLabels (sig := E.signature)
    (fun t => (Label.ofTreeIn? (sig := E.signature) E.headers E.headers_eq t).map fun l =>
      (E.graph l).map (Clause.map (List.map (·.1)))) s L M)⟩
  decEq := inferInstanceAs (DecidableEq (Label E.signature))
  nul := (⟨.app 0 .nil, p.nul⟩ : Label E.signature)
  tru := (⟨.app 1 .nil, p.tru⟩ : Label E.signature)
  fls := (⟨.app 2 .nil, p.fls⟩ : Label E.signature)
  undef := (⟨.app 3 .nil, p.undef⟩ : Label E.signature)

end

/-- Either image check: both are proved, so accepting what either accepts is
sound. -/
def eitherImages {ι : Type} [DecidableEq ι] {G : NormalGraph ι} (a b : InstanceImageCheck G) :
    InstanceImageCheck G where
  compare bs c := (a.compare bs c).orElse fun _ => b.compare bs c
  sound bs c hlen hkinds h η := by
    simp only [ComparisonResult.accepted_orElse] at h
    cases ha : (a.compare bs c).accepted
    · simp only [ha, Bool.false_or] at h
      exact b.sound bs c hlen hkinds h η
    · exact a.sound bs c hlen hkinds ha η
  compareAllowed s c := (a.compareAllowed s c).orElse fun _ => b.compareAllowed s c
  allowed_sound s c h η := by
    simp only [ComparisonResult.accepted_orElse] at h
    cases ha : (a.compareAllowed s c).accepted
    · simp only [ha, Bool.false_or] at h
      exact b.allowed_sound s c h η
    · exact a.allowed_sound s c ha η
  -- The second's renaming, variances and `Var` proposal: the finite check
  -- has none.
  sub := b.sub
  base := b.base
  gen := b.gen
  budget := b.budget

/-- The equations' checks with exact substitution images and the store's
budget. -/
def exactImages (E : Equations) (v : Variances E) (budget : SearchBudget := {}) : InstanceImageCheck E.graph :=
  { E.images v with budget }

/-- The native Promise declaration selected by declaration identity. Its
application has one value argument. -/
structure NativePromise (E : Equations) where
  head : Fin E.signature.length
  arity : E.signature[head].parameters = 1
  kinds : E.signature[head].kinds = [.value]
  region : OrdinaryRegion E
  head_mem : head.val ∈ region.heads

namespace NativePromise

/-- A semantic argument is assigned to a family variable, independent of
source binder names. -/
def parameter (E : Equations) : Label E.signature :=
  ⟨.var 3000000 0 .value, rfl⟩

def application (p : NativePromise E) (A : List (Label E.signature)) : Scope E.signature :=
  ⟨p.head, [A], by simpa using p.arity.symm⟩

noncomputable def applyFamily (p : NativePromise E) (A : ValueFamily) : Fam :=
  let η := assign (ParameterAssignment.empty .mixed) [parameter E] [MixedFamily.ofValue A]
  fun n W v => mixedMeaning E.graph η [(p.application [parameter E]).label] n W (.inl v)

open Classical in
/-- Extension to arbitrary families for the resolution relation. Descriptors
supply value families, for which the first branch is selected. -/
noncomputable def constructor (p : NativePromise E) (A : Fam) : Fam :=
  if h : ValueFam A then p.applyFamily ⟨A, h⟩ else fun _ _ _ => False

theorem constructor_valid (p : NativePromise E) (A : Fam) (h : ValueFam A) :
    ValueFam (p.constructor A) := by
  classical
  simp only [constructor, dif_pos h]
  exact (MixedFamily.value ⟨_, mixedMeaning_valid _ _ _⟩).2

/-- The actual source application denotes the fixed native constructor at
its argument's value meaning. The sort check excludes argument packs. -/
theorem application_meaning (p : NativePromise E)
    (η : MixedAssignment (Label E.signature)) (A : List (Label E.signature))
    (kind : sortTy E.graph .value A = true) :
    (fun n W v => mixedMeaning E.graph η [(p.application A).label] n W (.inl v)) =
      p.constructor (fun n W v => mixedMeaning E.graph η A n W (.inl v)) := by
  classical
  let V : ValueFamily := MixedFamily.value ⟨_, mixedMeaning_valid E.graph η A⟩
  have valid : ValueFam (fun n W v => mixedMeaning E.graph η A n W (.inl v)) := V.2
  simp only [constructor, dif_pos valid]
  change _ = p.applyFamily V
  let θ := assign (ParameterAssignment.empty .mixed) [parameter E] [MixedFamily.ofValue V]
  have kp : E.graph.parameterKinds (parameter E) = some .value := by
    simp [parameter, Equations.graph, NormalGraph.ofRowMap, Equations.row,
      Equations.baseRow, Label.view]
  have argument : mixedMeaning E.graph η A = mixedMeaning E.graph θ [parameter E] := by
    rw [mixedMeaning_parameter _ _ _ _ kp]
    simp only [θ, assign_cons_head]
    funext n W x
    cases x with
    | inl v => simp [selectParameter, MixedFamily.ofValue, V, MixedFamily.value]
    | inr vs => simp [selectParameter, mixedMeaning_noArguments E.graph η A (sortTy_hasKind kind)]
  have same := E.application_congr (p.application A) (p.application [parameter E]) η θ
    rfl rfl (by
      intro i hi hj
      have : i = 0 := by simpa [application] using hi
      subst i
      exact argument)
  exact congrArg (fun F => fun n W v => F n W (.inl v)) same

/-- Install a source descriptor domain while retaining the checked native
dependency region. -/
def withDomain (p : NativePromise E) (domain : SchemeDomain (Label E.signature) .mixed) :
    NativePromise { E with domain := domain } where
  head := p.head
  arity := p.arity
  kinds := p.kinds
  region := ⟨p.region.heads, p.region.closed,
    fun h hh => by simpa only [Equations.ordinaryTemplate_domain] using p.region.ordinary h hh,
    p.region.builtins⟩
  head_mem := p.head_mem

theorem applyFamily_domain (p : NativePromise E)
    (domain : SchemeDomain (Label E.signature) .mixed) (A : ValueFamily) :
    (p.withDomain domain).applyFamily A = p.applyFamily A := by
  let root := (p.application [parameter E]).label
  have hroot : root.withinHeads (· ∈ p.region.heads) := by
    intro h hh
    have he : h = p.head.val := by
      simpa [root, application, Scope.label, Scope.rawArgs, parameter, Tree.dependencyHeads,
        Args.ofList, Types.ofList, Args.dependencyHeads, Types.dependencyHeads] using hh
    exact he ▸ p.head_mem
  let η := assign (ParameterAssignment.empty .mixed) [parameter E] [MixedFamily.ofValue A]
  have he := p.region.denote domain η root hroot
  funext n W v
  change (∃ i ∈ [root], qDenoteWithArgs _ _ (η,i) n W v) =
    (∃ i ∈ [root], qDenoteWithArgs _ _ (η,i) n W v)
  simp only [List.mem_singleton, exists_eq_left]
  simpa only [Equations.graph_domain] using congrFun (congrFun (congrFun he n) W) v

/-- The native constructor is fixed before the descriptor domain is installed. -/
theorem constructor_domain (p : NativePromise E)
    (domain : SchemeDomain (Label E.signature) .mixed) :
    (p.withDomain domain).constructor = p.constructor := by
  classical
  funext A
  unfold constructor
  split
  · exact p.applyFamily_domain domain _
  · rfl

/-- The native arm reads the exact constructor application and checks the
payload sort. The certificate cannot substitute a structural lookalike. -/
def payload (p : NativePromise E) (l : Label E.signature) :
    Option { A : List (Label E.signature) //
      l = (p.application A).label ∧ sortTy E.graph .value A = true } :=
  match l.view with
  | .application scope => match scope.arguments with
    | [A] => if h : l = (p.application A).label ∧ sortTy E.graph .value A = true then
        some ⟨A, h⟩ else none
    | _ => none
  | _ => none

/-- Native descriptor construction uses the actual source application's
meaning, and retains the child's literal observation and stable result. -/
def descriptor (p : NativePromise E) {N U : Fam}
    (h : ResolutionCapabilities.NativeSeparation p.constructor N U)
    (d : ResolutionDescriptors.Descriptor (ResolutionCapabilities.capabilities h)) :
    ResolutionDescriptors.Descriptor (ResolutionCapabilities.capabilities h) :=
  ResolutionCapabilities.native h d

theorem descriptor_input (p : NativePromise E) {N U : Fam}
    (h : ResolutionCapabilities.NativeSeparation p.constructor N U)
    (η : MixedAssignment (Label E.signature)) (l : Label E.signature)
    (A : { A : List (Label E.signature) //
      l = (p.application A).label ∧ sortTy E.graph .value A = true })
    (d : ResolutionDescriptors.Descriptor (ResolutionCapabilities.capabilities h))
    (child : d.input = fun n W v => mixedMeaning E.graph η A.1 n W (.inl v)) :
    (p.descriptor h d).input =
      (fun n W v => mixedMeaning E.graph η [l] n W (.inl v)) := by
  obtain ⟨A, rfl, kind⟩ := A
  change p.constructor d.input = _
  rw [child]
  exact (p.application_meaning η A kind).symm

end NativePromise

/-- The native constructor and the closed stable-value bound used by source
resolution descriptors. Both belong to the checked ordinary region. -/
structure ResolutionContext (E : Equations) where
  promise : NativePromise E
  stable : List (Label E.signature)
  within : ∀ l ∈ stable, l.withinHeads (· ∈ promise.region.heads)
  closed : ∀ l ∈ stable, l.free = []
  shape : NativePromiseSeparation.Shape E.graph (promise.application [NativePromise.parameter E]).label stable
  source : Label E.signature
  sourceSource : ProgramTyping.SourceValues E.graph [source]
  nativeSource : ProgramTyping.SourceValues E.graph [(promise.application [NativePromise.parameter E]).label]
  stableSource : ProgramTyping.SourceValues E.graph stable

namespace ResolutionContext

noncomputable def stableFamily (c : ResolutionContext E) : Fam :=
  fun n W v => mixedMeaning E.graph (ParameterAssignment.empty .mixed) c.stable n W (.inl v)

theorem nativeSeparate (c : ResolutionContext E) (A : Fam) (valid : ValueFam A) :
    ¬ FamLe (c.promise.constructor A) c.stableFamily := by
  classical
  unfold NativePromise.constructor
  rw [dif_pos valid]
  exact c.shape.separate _ _

theorem source_values {G : NormalGraph ι} {A : List ι}
    (h : ProgramTyping.SourceValues G A) (η : MixedAssignment ι) :
    FamLe (mixedValues G η A) (excOf G) := sourceTy_exc h η

theorem native (c : ResolutionContext E) :
    ResolutionCapabilities.NativeSeparation c.promise.constructor c.stableFamily (excOf E.graph) where
  valid := c.promise.constructor_valid
  separate := c.nativeSeparate
  native_source A valid := by
    classical
    unfold NativePromise.constructor
    rw [dif_pos valid]
    exact source_values c.nativeSource _
  stable_source := source_values c.stableSource _

def capabilities (c : ResolutionContext E) :
    ResolutionDescriptors.Capabilities (excOf E.graph) c.stableFamily :=
  ResolutionCapabilities.capabilities c.native

def domain (c : ResolutionContext E) : SchemeDomain (Label E.signature) .mixed :=
  ResolutionDescriptors.descriptorDomain c.capabilities

def withDomain (c : ResolutionContext E) (D : SchemeDomain (Label E.signature) .mixed) :
    ResolutionContext { E with domain := D } where
  promise := c.promise.withDomain D
  stable := c.stable
  within := c.within
  closed := c.closed
  source := c.source
  sourceSource := by
    rw [Equations.graph_domain]
    dsimp only [ProgramTyping.SourceValues, sourceTy, sourceRow,
      NormalGraph.plain, NormalGraph.params, NormalGraph.clauses]
    exact c.sourceSource
  nativeSource := by
    rw [Equations.graph_domain]
    dsimp only [ProgramTyping.SourceValues, sourceTy, sourceRow,
      NormalGraph.plain, NormalGraph.params, NormalGraph.clauses]
    exact c.nativeSource
  stableSource := by
    rw [Equations.graph_domain]
    dsimp only [ProgramTyping.SourceValues, sourceTy, sourceRow,
      NormalGraph.plain, NormalGraph.params, NormalGraph.clauses]
    exact c.stableSource
  shape := by
    rw [Equations.graph_domain]
    exact ⟨c.shape.views, c.shape.methods, c.shape.bounds, c.shape.plain, c.shape.row,
      c.shape.proto, c.shape.admitted, c.shape.noArray, c.shape.stablePlain, c.shape.reject⟩

theorem stableFamily_domain (c : ResolutionContext E)
    (D : SchemeDomain (Label E.signature) .mixed) :
    (c.withDomain D).stableFamily = c.stableFamily := by
  funext n W v
  change (∃ l ∈ c.stable, qDenoteWithArgs _ _ (_,l) n W v) =
    (∃ l ∈ c.stable, qDenoteWithArgs _ _ (_,l) n W v)
  apply propext
  constructor <;> rintro ⟨l, hl, hv⟩ <;> refine ⟨l, hl, ?_⟩
  · have he := c.promise.region.denote D (ParameterAssignment.empty .mixed) l (c.within l hl)
    simpa only [Equations.graph_domain, he] using hv
  · have he := c.promise.region.denote D (ParameterAssignment.empty .mixed) l (c.within l hl)
    simpa only [Equations.graph_domain, he] using hv

/-- The built-ins' `unknown` means the same in either domain: its rows and its
prototype's are in the native promise's ordinary region. -/
theorem excOf_domain (c : ResolutionContext E)
    (D : SchemeDomain (Label E.signature) .mixed) :
    excOf ({ E with domain := D } : Equations).graph = excOf E.graph := by
  have hv : ∀ S, (∀ l ∈ S, l.withinHeads (· ∈ c.promise.region.heads)) →
      builtinValues ({ E with domain := D } : Equations).graph S = builtinValues E.graph S := by
    intro S hS
    funext n W v
    change (∃ l ∈ S, qDenoteWithArgs _ _ (_,l) n W v) =
      (∃ l ∈ S, qDenoteWithArgs _ _ (_,l) n W v)
    apply propext
    constructor <;> rintro ⟨l, hl, hv⟩ <;> refine ⟨l, hl, ?_⟩
    · have he := c.promise.region.denote D (ParameterAssignment.empty .mixed) l (hS l hl)
      simpa only [Equations.graph_domain, he] using hv
    · have he := c.promise.region.denote D (ParameterAssignment.empty .mixed) l (hS l hl)
      simpa only [Equations.graph_domain, he] using hv
  refine builtinExc_eq (by rw [Equations.graph_domain]) fun r hr => ?_
  have hin : r ∈ E.builtins.toList := by
    have hr' : E.builtins = some r := hr
    simp [hr']
  exact ⟨hv r.proto (fun l hl => c.promise.region.builtins r hin l (List.mem_append_left _ hl)),
    hv r.unknown (fun l hl => c.promise.region.builtins r hin l (List.mem_append_right _ hl))⟩

theorem domain_fixed (c : ResolutionContext E)
    (D : SchemeDomain (Label E.signature) .mixed) :
    (c.withDomain D).domain = c.domain := by
  exact ResolutionCapabilities.domain_congr _ _
    (NativePromise.constructor_domain c.promise D) (stableFamily_domain c D)
    (excOf_domain c D)

theorem stable_meaning (c : ResolutionContext E)
    (η : MixedAssignment (Label E.signature)) :
    (fun n W v => mixedMeaning E.graph η c.stable n W (.inl v)) = c.stableFamily := by
  have he := E.agree_free η (ParameterAssignment.empty .mixed) c.stable (by
    intro l hl p hp
    simp only [c.closed l hl, List.not_mem_nil] at hp)
  exact congrArg (fun F => fun n W v => F n W (.inl v)) he

end ResolutionContext

/-- Validate the retained intrinsic bound against the native dependency region. -/
def resolutionContext (s : State) (p : NativePromise E) :
    Except String (Option (ResolutionContext E)) := do
  let some raw := s.nativeStable | return none
  let stable ← closedUnion E "native stable-value bound" raw
  if checked : (∀ l ∈ stable, l.withinHeads (· ∈ p.region.heads)) ∧
      (∀ l ∈ stable, l.free = []) then
    let some shape := NativePromiseSeparation.check E.graph (p.application [NativePromise.parameter E]).label stable
      | throw "native Promise Ξ structure does not establish separation from stable values"
    let some h := (List.range s.heads.size).find? (fun h =>
      (s.heads[h]?).any fun d => d.kinds.isEmpty && d.binders.isEmpty && d.body == some (.clauses [.source]))
      | throw "native resolution requires the JavaScript value universe"
    let source ← closedLabel E "JavaScript value universe" (mkApp h [])
    if hs : ProgramTyping.SourceValues E.graph [source] ∧
        ProgramTyping.SourceValues E.graph [(p.application [NativePromise.parameter E]).label] ∧
        ProgramTyping.SourceValues E.graph stable then
      return some ⟨p, stable, checked.1, checked.2, shape, source, hs.1, hs.2.1, hs.2.2⟩
    else throw "native resolution inputs must contain only JavaScript values"
  else throw "native stable-value bound must be closed within the ordinary dependency region"

/-- The keys a record clause names: its fields, views, optional fields and
methods. -/
private def clauseKeys : Clause (List Tree) → List PropKey
  | .refs fs rs vs os ms _ _ => (fs ++ rs.flatten).map (·.1) ++ vs.map (·.1) ++ os.map (·.key) ++ ms.map (·.key)
  | .dict fs rs vs _ os ms _ _ _ => (fs ++ rs.flatten).map (·.1) ++ vs.map (·.1) ++ os.map (·.key) ++ ms.map (·.key)
  | _ => []

/-- The prototype operands a clause states under `[[proto]]`. -/
private def protoOperands : Clause (List Tree) → List (List Tree)
  | .refs _ _ vs .. | .dict _ _ vs .. => vs.filterMap fun (k, P) => if k == CallArguments.protoField then some P else none
  | _ => []

private def headClauses (s : State) (g : Nat) : List (Clause (List Tree)) :=
  match (s.heads[g]?).bind (·.body) with
  | some (.clauses cs) => cs
  | _ => []

/-- The heads a prototype operand applies, through its meets; none where a
part is no head's application. -/
private partial def prototypeHeads : Tree → Option (List Nat)
  | .app g _ => some [g]
  | .meet ps => (ps.toList.mapM prototypeHeads).map List.flatten
  | _ => none

/-- **The prototype tag.** Every prototype a lowered head's row states under
`[[proto]]`, through its bases, intersections and instances as lowering
resolved them, is a head's application whose row is records (`refs` or
`dict` clauses), and the only heads holding
`Symbol.toStringTag` among them are the native `Promise`'s prototype records:
no other contract states a prototype holding the tag. -/
def tagPrototypes (s : State) : Except String Unit := do
  let native := (List.range s.heads.size).filter fun h =>
    match (s.heads[h]?).map Draft.kind with
    | some (.declaration i) => s.doc[i]?.any fun d => ImplicitDependency.promise.selects d.identity
    | _ => false
  let heads (h : Nat) : Except String (List Nat) :=
    ((headClauses s h).flatMap protoOperands).flatten.foldlM (fun acc t => match prototypeHeads t with
      | some gs => pure (acc ++ gs)
      | none => throw s!"{(s.heads[h]?).map (·.name) |>.getD "a head"}: a prototype is stated as no record") []
  let nativeProtos ← native.foldlM (fun acc h => do return acc ++ (← heads h)) []
  let tagged (g : Nat) := (headClauses s g).any fun c => (clauseKeys c).any fun k => match k with
    | .sym i => s.tags.contains i
    | _ => false
  for h in List.range s.heads.size do
    for g in ← heads h do
      -- A prototype is a record: its row's clauses are records, whose keys
      -- `clauseKeys` reads, never a callable object or another shape.
      let record := match (s.heads[g]?).bind (·.body) with
        | some (.clauses cs@(_ :: _)) => cs.all fun c => match c with | .refs .. | .dict .. => true | _ => false
        | _ => false
      if !record then
        throw s!"{(s.heads[h]?).map (·.name) |>.getD "a head"}: a prototype is stated as no record"
      if tagged g && !nativeProtos.contains g then
        throw s!"{(s.heads[h]?).map (·.name) |>.getD "a head"}: a prototype holding `Symbol.toStringTag` other than the native Promise's"

/-- Native identity comes from the declaration document; a user declaration
with the same display name does not select a native constructor. -/
def nativePromise (s : State) (E : Equations) : Except String (Option (NativePromise E)) := do
  let candidates := (List.range s.heads.size).filter fun h =>
    match (s.heads[h]?).map Draft.kind with
    | some (.declaration i) => s.doc[i]?.any fun d => ImplicitDependency.promise.selects d.identity
    | _ => false
  match candidates with
  | [] => return none
  | [h] =>
    if hi : h < E.signature.length then
      if ha : E.signature[h].parameters = 1 then
        if hk : E.signature[h].kinds = [.value] then
          let some region := E.checkOrdinaryRegion (h :: (s.nativeStable.getD []).flatMap Tree.dependencyHeads)
            | throw "native Promise Ξ dependencies require ordinary quantified library definitions"
          return some ⟨⟨h, hi⟩, ha, hk, region.1, region.2 h List.mem_cons_self⟩
        else throw "native Promise Ξ requires one value parameter"
      else throw "native Promise Ξ requires one type argument"
    else throw "native Promise Ξ head is outside the frozen equations"
  | _ => throw "multiple native Promise Ξ declarations"

/-- The store of a checked request: the extracted heads, whose validated
equations are `E`, and their variances, computed as checks ask for them and
shared by every request over the store. It no longer grows. -/
structure Checked (E : Equations) (p : Primitive E) where
  heads : State
  variances : Variances E := E.variances
  promise : Option (NativePromise E) := none
  resolution : Option { c : ResolutionContext E // E.domain = c.domain } := none

section
variable {E : Equations} {p : Primitive E}

instance : ToJson (Checked E p) := ⟨fun c => toJson c.heads⟩
instance : FromJson (Checked E p) := ⟨fun j => do return { heads := ← fromJson? j }⟩

/-- A tree as a label of `E`, if it is one. -/
def Checked.label? (t : Tree) : Option (CheckedLabel E p) := Label.ofTree? t

instance : StoreView (Checked E p) (CheckedLabel E p) where
  graph _ := E.graph
  row _ l := E.row l
  valid _ _ := true
  wellFormed _ := true
  labels _ := (List.range E.signature.length).filterMap fun h => Checked.label? (mkApp h [])
  bound _ := CertificateProducer.searchLimit
  arrayProto _ := ((E.builtins.bind (·.proto.head?)) : Option (Label E.signature)).getD
    (Labels.nul : CheckedLabel E p)
  lookup c cs := (lookup c.heads (cs.map (Clause.map (·.map Subtype.val)))).bind Checked.label?
  project c mentioned depth :=
    let pr := projectWith (fun t => match (Label.ofTree? t : Option (Label E.signature)) with
        | some l => (E.row l).map Subtype.val (·.map Subtype.val)
        | none => .clauses []) (spell c.heads)
      (mentioned.map CheckedLabel.tree) depth
    { rows := pr.rows, position := fun l => pr.position l.tree, names := pr.names }
  images c := eitherImages (finiteInstanceImages E.graph) (exactImages E c.variances c.heads.subtypeBudget)


/-- A checked store's graph is its equations': it reads none of the store's
fields. -/
theorem Checked.graph_eq (c : Checked E p) : StoreView.graph c = E.graph := rfl

/-- A checked store's image check reads the equations, the store's variances
and its budget only: two stores agreeing on those have one image check, so
every search in one answers as in the other, its whole result (an exhaustion
included) the same. -/
theorem Checked.images_eq (c c' : Checked E p) (hv : c.variances = c'.variances)
    (hb : c.heads.subtypeBudget = c'.heads.subtypeBudget) :
    StoreView.images c = StoreView.images c' := by
  show eitherImages _ (exactImages E c.variances c.heads.subtypeBudget) =
    eitherImages _ (exactImages E c'.variances c'.heads.subtypeBudget)
  rw [hv, hb]

end

/-- Extracted heads, frozen: their validated equations and the store over
them. -/
structure Frozen where
  equations : Equations
  primitive : Primitive equations
  store : Checked equations primitive

/-- **Freezing.** The heads become equations only through the validator
(`Equations.ofRaw`): scope, arity and lexicality, constructor-headed
templates binding exactly their locals, meet normal form, a kind per
parameter. Variances are the checker's, computed when a check asks
(`Equations.variances`). -/
def freeze (s : State) : Except String Frozen := do
  let bodies ← s.heads.mapM fun d => match d.body with
    | some b => pure b
    | none => throw s!"{d.name}: its row was never lowered"
  let E ← Equations.ofRaw (rawHeads s.heads bodies)
  let E := { E with builtins := if s.arrays then builtinsOf E s.proto (s.keys.get? unknownKey) s.excluded else none }
  let E := E.memo.withOverlaps
  let ⟨p⟩ ← primitive E
  tagPrototypes s
  let promise ← nativePromise s E
  match promise with
  | none => return ⟨E, p, { heads := s }⟩
  | some native =>
    match ← resolutionContext s native with
    | none => return ⟨E, p, { heads := s, promise := some native }⟩
    | some context =>
      let D := context.domain
      let E' := { E with domain := D }
      let p' : Primitive E' := ⟨p.nul, p.tru, p.fls, p.undef⟩
      let context' := context.withDomain D
      let store : Checked E' p' := {
        heads := s
        promise := some context'.promise
        resolution := some ⟨context', (context.domain_fixed D).symm⟩ }
      return ⟨E', p', store⟩

end Verification.EquationStore
