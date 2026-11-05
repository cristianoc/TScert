import Verification.Types.EquationCertificates

/-! Family subtyping on recursive equations (RECURSIVE-EQUATIONS §4). The
equation graph supplies what the generic rules need (`Renaming`): structural
substitution and free support with their proved laws, family variables,
which are labels of their own (`Tree.var`), so no scheme binds one, label
sizes and a matcher for renamed bound rows. Each head's variance is a
family entry the checker computes from the equations (`Variances`), and the
`Var` rule relates two applications of one head by an instance of its
entry, without unfolding it. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveRules PositiveCertificates PositiveNormalization CallEffects

/-! ## The renaming of equation graphs -/

/- Whether a tree occurs anywhere in another: the claim discipline of RECURSIVE-EQUATIONS §4.2. -/
mutual
def Tree.subtrees : Tree → List Tree
  | .app h args => .app h args :: args.subtrees
  | .bound h args i => .bound h args i :: args.subtrees
  | .meet ps => .meet ps :: ps.subtrees
  | t => [t]
def Types.subtrees : Types → List Tree
  | .nil => []
  | .cons t ts => t.subtrees ++ ts.subtrees
def Args.subtrees : Args → List Tree
  | .nil => []
  | .cons ts args => ts.subtrees ++ args.subtrees
end

/- A tree's size: an application is larger than each of its arguments'
labels (`Inst`'s premises decrease, RECURSIVE-EQUATIONS §4.2). -/
mutual
def Tree.size : Tree → Nat
  | .app _ args => args.size + 1
  | .bound _ args _ => args.size + 1
  | .meet ps => ps.size + 1
  | _ => 1
def Types.size : Types → Nat
  | .nil => 0
  | .cons t ts => t.size + ts.size
def Args.size : Args → Nat
  | .nil => 0
  | .cons ts args => ts.size + args.size
end

/- The bound rows of a tree matched against another's (`TabRen`): where the
two differ at a bound row, the first's row to the second's. An application
is matched argument by argument, a meet part by part; a bound row is atomic.
Untrusted: the checker checks the renaming and its images. -/
mutual
def Tree.matchBound (sig : Signature) : Tree → Tree → List (Label sig × List (Label sig))
  | t@(.bound ..), u@(.bound ..) =>
    if t == u then [] else
    if h : t.scoped sig 0 0 = true then
      if h' : u.scoped sig 0 0 = true then [(⟨t, h⟩, [⟨u, h'⟩])] else []
    else []
  | .app g args, .app h args' => if g == h then Args.matchBound sig args args' else []
  | .meet ps, .meet qs => Types.matchBound sig ps qs
  | _, _ => []
def Types.matchBound (sig : Signature) : Types → Types → List (Label sig × List (Label sig))
  | .cons t ts, .cons u us => Tree.matchBound sig t u ++ Types.matchBound sig ts us
  | _, _ => []
def Args.matchBound (sig : Signature) : Args → Args → List (Label sig × List (Label sig))
  | .cons ts args, .cons us args' => Types.matchBound sig ts us ++ Args.matchBound sig args args'
  | _, _ => []
end

/-- The renaming carrying a pair's labels, position by position, onto
another pair's. -/
def renameBound (p : List (Label sig) × List (Label sig)) (A B : List (Label sig)) :
    List (Label sig × List (Label sig)) :=
  (((p.1.zip A) ++ (p.2.zip B)).flatMap fun (l, m) => Tree.matchBound sig l.1 m.1).eraseDups

/-- Substitution into a type: the union of its labels' substitutions. -/
def substituteAll (σ : List (Label sig × List (Label sig))) (A : List (Label sig)) :
    List (Label sig) :=
  A.flatMap fun l => l.substitute (replace σ)

/-- `substituteAll`, returning the type itself where nothing is substituted
and its meets are canonical (`substituteAll_eq_self`). -/
def substituteAllSelf (σ : List (Label sig × List (Label sig))) (A : List (Label sig)) :
    List (Label sig) :=
  if σ.isEmpty && A.all (·.1.canonical) then A else A.flatMap fun l => l.substitute (replace σ)

@[csimp] theorem substituteAll_eq_self : @substituteAll = @substituteAllSelf := by
  funext sig σ A
  unfold substituteAll substituteAllSelf
  split
  · next h =>
    simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
    obtain ⟨rfl, hc⟩ := h
    have hσ : ∀ l : Label sig, replace [] l = [l] := fun _ => rfl
    induction A with
    | nil => rfl
    | cons l A ih =>
      rw [List.flatMap_cons, Label.substitute_self _ hσ l (hc l List.mem_cons_self),
        ih fun l hl => hc l (List.mem_cons_of_mem _ hl)]
      rfl
  · rfl

private theorem meaning_cons (G : NormalGraph ι) (η : MixedAssignment ι) (l : ι) (A : List ι)
    (n : Nat) (W : WorldT n) (x : ParameterSpace.mixed.Carrier) :
    mixedMeaning G η (l :: A) n W x ↔ mixedMeaning G η [l] n W x ∨ mixedMeaning G η A n W x := by
  rw [mixedMeaning_union G η (l :: A), mixedMeaning_union G η [l], mixedMeaning_union G η A]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]

private theorem meaning_append (G : NormalGraph ι) (η : MixedAssignment ι) (A B : List ι)
    (n : Nat) (W : WorldT n) (x : ParameterSpace.mixed.Carrier) :
    mixedMeaning G η (A ++ B) n W x ↔ mixedMeaning G η A n W x ∨ mixedMeaning G η B n W x := by
  rw [mixedMeaning_union G η (A ++ B), mixedMeaning_union G η A, mixedMeaning_union G η B]
  simp only [List.mem_append, or_and_right, exists_or]

/-- Substitution into a union means the union of its labels' meanings at the
images (`Label.substitute_meaning`). -/
theorem Equations.substituteAll_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature))
    (σ : List (Label equations.signature × List (Label equations.signature)))
    (images : ∀ p, equations.graph.params p = true →
      mixedMeaning equations.graph η [p] = mixedMeaning equations.graph θ (replace σ p)) :
    ∀ A, mixedMeaning equations.graph η A = mixedMeaning equations.graph θ (substituteAll σ A)
  | [] => by simp only [substituteAll, List.flatMap_nil, mixedMeaning_nil]
  | l :: A => by
    have hl := Label.substitute_meaning equations η θ (replace σ) images l
    have hA := equations.substituteAll_meaning η θ σ images A
    funext n W x
    apply propext
    rw [meaning_cons, show substituteAll σ (l :: A) = l.substitute (replace σ) ++ substituteAll σ A
      from List.flatMap_cons .., meaning_append, hl, hA]

/-- A scheme row of an equation graph binds its application's owned labels,
never a family variable. -/
theorem Equations.scheme_binders (equations : Equations) (i : Label equations.signature)
    (s : SchemeRow (Label equations.signature)) (hs : equations.graph.schemes i = some s) :
    ∀ x ∈ s.binders, x.isVariable = false := by
  revert hs
  apply i.cases
  · intro scope hs
    have hv := (equations.body scope.head).2
    cases hb : (equations.body scope.head).1 with
    | scheme bs sigs bounds rests resolution =>
      simp only [hb, RowTemplate.wellBound, Bool.and_eq_true_iff, decide_eq_true_eq] at hv
      simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Scope.view_label,
        Template.instantiate, hb, GraphRow.map, Option.some.injEq] at hs
      subst hs
      intro x hx
      rw [scope.instantiate_binders bs hv.1] at hx
      obtain ⟨slot, rfl⟩ := Scope.mem_binders.mp hx
      rfl
    | clauses cs =>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, hb,
        GraphRow.map] at hs
    | param p name kind =>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, hb,
        GraphRow.map] at hs
    | meet p cs ps =>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, hb,
        GraphRow.map] at hs
  · intro scope slot hs
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow] at hs
  · intro o i k hs
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow] at hs
  · intro ps valid hs
    rw [(equations.meet_rigid ps valid).1] at hs
    cases hs

/-- A family variable is a parameter row. -/
theorem Equations.variable_param (equations : Equations) (x : Label equations.signature)
    (hx : x.isVariable = true) : equations.graph.params x = true := by
  obtain ⟨t, valid⟩ := x
  cases t with
  | var o i k =>
    simp [NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Label.view]
  | _ => simp [Label.isVariable] at hx

/-- **The equation graph's renaming.** Substitution is `Label.substitute`,
free support `Label.free`, and family variables are `Tree.var` labels. -/
def Equations.renaming (equations : Equations) : Renaming equations.graph where
  substitute := substituteAll
  free A := A.flatMap Label.free
  familyVar := Label.isVariable
  mentions A x := A.any fun l => decide (x.1 ∈ l.1.subtrees)
  substitute_meaning η θ σ images := equations.substituteAll_meaning η θ σ images
  agree_free η θ A h := equations.agree_free η θ A fun l hl p hp =>
    h p (List.mem_flatMap.mpr ⟨l, hl, hp⟩)
  familyVar_param x hx := equations.variable_param x hx
  familyVar_unbound i s x hs hx hin := by
    have := equations.scheme_binders i s hs x hin
    rw [hx] at this
    cases this
  size l := l.1.size
  rename := renameBound
  head l := match l.1 with
    | .app h _ => some h
    | _ => none

/-! ## Variance, computed by the checker (RECURSIVE-EQUATIONS §4.3)

A variance assigns each parameter of a head one of `co`, `contra`, `inv`,
`none`, and stands for the entry `h(x⃗) ≤ h(y⃗)` whose hypotheses it states
(`varianceEntry`). The checker computes the variances of the heads a check
compares from the equations alone: the reference graph's strongly connected
components, dependencies first; each component's candidates the least
fixpoint of the polarity equations; each member checked by `Valid`
(`checkEntries`) with the component's candidates as the guarded assumption;
a failing member made `inv` at every parameter, and the check repeated.
What the loop keeps is checked, so the result is valid whatever the loop
does (`Variances.sound`, by Theorem 1); nothing is proposed from outside.
Each component is computed once, when a check first asks for one of its
heads. -/

/-- The variables of `h`'s entry: for parameter `i`, the family variable owned
by `h` at slot `2i + side`, of the parameter's kind. -/
def varianceArgs (h : Fin sig.length) (side : Nat) : List (List (Label sig)) :=
  sig[h].kinds.mapIdx fun i k => [Label.familyVar h.val (2 * i + side) k]

/-- One side of `h`'s entry: `h` applied to its variables. A header whose
kinds are not one per parameter has none. -/
def varianceSide (h : Fin sig.length) (side : Nat) : List (Label sig) :=
  if hl : sig[h].kinds.length = sig[h].parameters then
    [(Scope.mk h (varianceArgs h side) (by simp only [varianceArgs, List.length_mapIdx]; exact hl)).label]
  else []

/-- The hypotheses a variance states: `x ≤ y` for `co`, `y ≤ x` for
`contra`, both for `inv`, none for `none` (`Π_D^V`). -/
def varianceHypotheses (h : Fin sig.length) (vs : List Variance) : List (Label sig × Label sig) :=
  ((sig[h].kinds.zip vs).mapIdx fun i (k, v) =>
    let x := Label.familyVar h.val (2 * i) k
    let y := Label.familyVar h.val (2 * i + 1) k
    match v with
    | .co => [(x, y)]
    | .contra => [(y, x)]
    | .inv => [(x, y), (y, x)]
    | .none => []).flatten

/-- The variables of `h`'s entry, in the order `Var` instantiates them:
`x₀, y₀, x₁, y₁, …`. -/
def varianceVariables (h : Fin sig.length) : List (Label sig) :=
  (sig[h].kinds.mapIdx fun i k =>
    [Label.familyVar h.val (2 * i) k, Label.familyVar h.val (2 * i + 1) k]).flatten

/-- The assumption `a_h^V`: `h(x⃗) ≤ h(y⃗)` under the hypotheses `vs`
states, with an empty table. -/
def varianceEntry (h : Fin sig.length) (vs : List Variance) : Entry (Label sig) where
  source := varianceSide h 0
  target := varianceSide h 1
  variables := varianceVariables h
  hypotheses := varianceHypotheses h vs

def interleave : List α → List α → List α
  | a :: as, b :: bs => a :: b :: interleave as bs
  | _, _ => []

/-- **`Var` as a premise.** A label `h(A⃗)` and a label `h(B⃗)` of the target
propose the instance of `h`'s entry at `x⃗ := A⃗`, `y⃗ := B⃗`. Only a
proposal: the premise holds when it is checked like any instance. -/
def varGen (l : Label sig) (B : List (Label sig)) : List (Nat × List (List (Label sig))) :=
  match l.view with
  | .application a => B.filterMap fun b => match b.view with
    | .application c => if a.head = c.head then some (a.head.val, interleave a.arguments c.arguments)
      else none
    | _ => none
  | _ => []

/-! ### Candidates: the polarity equations -/

/-- The variance at a position of polarity `p` under a head of variance `q`
at that argument. -/
def compose : Variance → Variance → Variance
  | _, .none => .none
  | .none, _ => .none
  | .co, q => q
  | .contra, .co => .contra
  | .contra, .contra => .co
  | .contra, .inv => .inv
  | .inv, _ => .inv

/-- The join of the lattice `none < co, contra < inv`. -/
def join : Variance → Variance → Variance
  | .none, v => v
  | v, .none => v
  | .co, .co => .co
  | .contra, .contra => .contra
  | _, _ => .inv

private def arrowPolar (a : Arrow α) : List (Variance × α) :=
  (.contra, a.receiver) :: a.arguments.map (.contra, ·) ++ [(.co, a.result)]

private def restPolar (a : RestArrow α) : List (Variance × α) :=
  (.contra, a.receiver) :: a.arguments.1.map (.contra, ·) ++
    [(.contra, a.arguments.2), (.co, a.result)]

private def sigPolar (s : MethodMembers.Sig α) : List (Variance × α) :=
  s.calls.flatMap (fun m => m.arguments.map (.contra, ·) ++ [(.co, m.result)]) ++
    s.rests.flatMap (fun m => m.arguments.1.map (.contra, ·) ++
      [(.contra, m.arguments.2), (.co, m.result)]) ++
    s.schemes.map (.co, ·) ++ s.receivers.map (.contra, ·)

/-- Each operand of a clause with the polarity of its position: `co` under
results and readonly positions, `contra` under parameters and receivers,
`inv` under writable fields, cells and mutable elements. -/
def clausePolar : Clause α → List (Variance × α)
  | .list a bs => (a :: bs).flatMap fun t => t.operands.map ((if t.readonly then .co else .inv), ·)
  | .pack a bs => (a :: bs).flatMap fun t => t.operands.map (.co, ·)
  | .refs a bs vs os ms _ _ =>
    (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ vs.map (fun f => (.co, f.2)) ++
      os.map (fun o => ((if o.readonly then .co else .inv), o.type)) ++ ms.flatMap sigPolar
  | .dict a bs vs ds os ms _ cs _ =>
    (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ vs.map (fun f => (.co, f.2)) ++
      ds.map (fun f => (.co, f.2)) ++
      os.map (fun o => ((if o.readonly then .co else .inv), o.type)) ++ ms.flatMap sigPolar ++
      cs.map (fun f => (.inv, f.2))
  | .arrs L S => L.flatMap arrowPolar ++ S.flatMap restPolar
  | .callable a bs L S ms =>
    (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ L.flatMap arrowPolar ++ S.flatMap restPolar ++
      ms.flatMap sigPolar
  | .ctors L S a bs vs =>
      L.flatMap (fun q => q.arguments.map (.contra, ·) ++ [(.co, q.result)]) ++
      S.flatMap (fun q => q.arguments.1.map (.contra, ·) ++ [(.contra, q.arguments.2), (.co, q.result)]) ++
      (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ vs.map (fun f => (.co, f.2))
  | _ => []

/-- A template's operands with their polarities; a scheme's bounds are `inv`. -/
def rowPolar : GraphRow Tree (List Tree) → List (Variance × List Tree)
  | .clauses cs => cs.flatMap clausePolar
  | .scheme _ sigs bounds rests _ _ =>
    sigs.flatMap arrowPolar ++ bounds.map (fun b => (.inv, b.2)) ++ rests.flatMap restPolar
  | _ => []

/-- The parameters a tree reads at polarity `p`, an application's argument
composed with its head's variance there (`vOf`). -/
partial def treePolar (vOf : Nat → Nat → Variance) (p : Variance) : Tree → List (Nat × Variance)
  | .argument i => [(i, p)]
  | .app g args =>
    (args.toList.zipIdx).flatMap fun (ts, k) =>
      let q := compose p (vOf g k)
      if q == .none then [] else ts.toList.flatMap (treePolar vOf q)
  | .meet ps => ps.toList.flatMap (treePolar vOf p)
  | _ => []

/-- A head's template as trees. -/
def Equations.rawBody (equations : Equations) (h : Fin equations.signature.length) :
    GraphRow Tree (List Tree) :=
  (equations.body h).1.map (fun r => r.1.1) (·.map (·.1))

/-- The heads a tree applies. -/
partial def Tree.heads : Tree → List Nat
  | .app g args => g :: args.toList.flatMap fun ts => ts.toList.flatMap Tree.heads
  | .meet ps => ps.toList.flatMap Tree.heads
  | _ => []

/-- The heads a head's template applies: its edges in the reference graph. -/
def Equations.references (equations : Equations) (h : Fin equations.signature.length) : List Nat :=
  (((equations.rawBody h).operands).flatten.flatMap Tree.heads).eraseDups

/-- One round of the polarity equations for a component's members, the
other heads at their variances. -/
def Equations.polarityRound (equations : Equations) (vOf : Nat → Nat → Variance)
    (members : List (Fin equations.signature.length)) (v : List (Nat × List Variance)) :
    List (Nat × List Variance) :=
  let current (g k : Nat) : Variance := match v.lookup g with
    | some vs => vs.getD k .inv
    | none => vOf g k
  members.map fun h =>
    let reads := (rowPolar (equations.rawBody h)).flatMap fun (p, U) => U.flatMap (treePolar current p)
    (h.val, (List.range equations.signature[h].parameters).map fun i =>
      reads.foldl (fun acc (j, q) => if j == i then join acc q else acc) .none)

/-- The least fixpoint from `none`. Each round that changes something raises
an entry of a lattice of height two, so `2 × entries + 1` rounds reach it;
without a fixpoint the candidates are `inv`, which the check then decides. -/
def Equations.polarity (equations : Equations) (vOf : Nat → Nat → Variance)
    (members : List (Fin equations.signature.length)) : List (Nat × List Variance) :=
  let start := members.map fun h =>
    (h.val, (List.range equations.signature[h].parameters).map fun _ => Variance.none)
  let rounds := 2 * (start.map (·.2.length)).sum + 1
  let rec go : Nat → List (Nat × List Variance) → List (Nat × List Variance)
    | 0, v => v.map fun (h, vs) => (h, vs.map fun _ => .inv)
    | n + 1, v =>
      let next := equations.polarityRound vOf members v
      if next == v then v else go n next
  go rounds start

/-! ### The check -/

/-- Arrow evidence for a family's pairs: every source signature for every
target signature, the target's renamed to the source's binders. Only
proposed: `checkEntries` accepts the evidence it checks. -/
def Equations.arrowCandidates (equations : Equations)
    (pairs : List (List (Label equations.signature) × List (Label equations.signature))) :
    Evidence (Label equations.signature) :=
  pairs.flatMap fun (A, B) =>
    ((sourceClauses equations.graph A).flatMap fun a => (clausesOf equations.graph B).flatMap fun b =>
      match a, b with
      | .arrs L _, .arrs M _ => M.flatMap fun q => L.map fun p => (L, (q, ArrowCert.source p))
      | _, _ => []) ++
    (A.flatMap fun i => B.flatMap fun j => match equations.graph.schemes i, equations.graph.schemes j with
      | some s, some s' =>
        let σ := s'.binders.zip (s.binders.map fun p => [p])
        (s'.signatures.map (Arrow.map (equations.renaming.substitute σ)) ++ s'.signatures).flatMap fun q =>
          s.signatures.map fun p => (s.signatures, (q, ArrowCert.source p))
      | _, _ => [])

/-- Variance entries already checked, each sound, by head. -/
structure CheckedVariances (equations : Equations) where
  entries : List (Nat × List Variance × Entry (Label equations.signature)) := []
  sound : ∀ p ∈ entries, EntrySound equations.graph p.2.2 ∧ HypParams equations.graph p.2.2 := by
    intro _ h; cases h

def CheckedVariances.entry {equations : Equations} (c : CheckedVariances equations) (k : Nat) :
    Option (Entry (Label equations.signature)) :=
  (c.entries.lookup k).map (·.2)

theorem CheckedVariances.entry_sound {equations : Equations} (c : CheckedVariances equations)
    {k : Nat} {e : Entry (Label equations.signature)} (h : c.entry k = some e) :
    EntrySound equations.graph e ∧ HypParams equations.graph e := by
  unfold CheckedVariances.entry at h
  cases hl : c.entries.lookup k with
  | none => simp [hl] at h
  | some p =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    subst h
    exact c.sound (k, p) (mem_of_lookup hl)

/-- The entries of candidates, by head. -/
def candidateEntries (equations : Equations) (cands : List (Nat × List Variance)) :
    List (Nat × List Variance × Entry (Label equations.signature)) :=
  cands.filterMap fun (h, vs) =>
    if hh : h < equations.signature.length then some (h, vs, varianceEntry ⟨h, hh⟩ vs) else none

/-- The entries a component's check cites: its members' candidates, then the
components checked before it. -/
def componentLook (equations : Equations)
    (F : List (Nat × List Variance × Entry (Label equations.signature)))
    (dep : Nat → Option (Entry (Label equations.signature))) : Lookup (Label equations.signature) :=
  fun k => match F.lookup k with
    | some p => some p.2
    | none => dep k

/-- `Valid` for the entries `F`, citing `F` and the earlier components. -/
def Equations.validVariances (equations : Equations)
    (F : List (Nat × List Variance × Entry (Label equations.signature)))
    (dep : Nat → Option (Entry (Label equations.signature))) (checked : List (Entry (Label equations.signature))) :
    Bool :=
  checkEntries equations.graph (some equations.renaming) [] varGen (componentLook equations F dep)
    checked (equations.arrowCandidates (checked.flatMap (·.pairs)))

/-- Steps 3 and 4: check each member against the candidates; a failing
member becomes `inv` at every parameter, and one failing at `inv` is dropped
(it has no variance, and `Var` does not apply to it). -/
def Equations.settle (equations : Equations)
    (dep : Nat → Option (Entry (Label equations.signature))) :
    Nat → List (Nat × List Variance) → List (Nat × List Variance)
  | 0, _ => []
  | n + 1, cands =>
    let F := candidateEntries equations cands
    let failing := F.filter fun p => !equations.validVariances F dep [p.2.2]
    if failing.isEmpty then cands else
    equations.settle dep n (cands.filterMap fun (h, vs) =>
      if failing.any (·.1 == h) then
        if vs.all (· == .inv) then none else some (h, vs.map fun _ => .inv)
      else some (h, vs))

theorem componentLook_cases (equations : Equations)
    (F : List (Nat × List Variance × Entry (Label equations.signature)))
    (dep : Nat → Option (Entry (Label equations.signature)))
    (hdep : ∀ k e, dep k = some e → EntrySound equations.graph e ∧ HypParams equations.graph e)
    (k : Nat) (e : Entry (Label equations.signature)) (h : componentLook equations F dep k = some e) :
    e ∈ F.map (·.2.2) ∨ (EntrySound equations.graph e ∧ HypParams equations.graph e) := by
  unfold componentLook at h
  cases hl : F.lookup k with
  | none => simp only [hl] at h; exact .inr (hdep k e h)
  | some p =>
    simp only [hl, Option.some.injEq] at h
    subst h
    exact .inl (List.mem_map.mpr ⟨(k, p), mem_of_lookup hl, rfl⟩)

/-- **One component's variances.** Candidates from the polarity equations,
settled, and the result checked as a whole; what fails that check keeps no
variance. A head of another component is read through `earlier`, the
checked variances of its own component (empty for one not checked before). -/
def Equations.componentVariances (equations : Equations) (members : List (Fin equations.signature.length))
    (earlier : Nat → CheckedVariances equations) : CheckedVariances equations :=
  let dep (g : Nat) : Option (Entry (Label equations.signature)) := (earlier g).entry g
  let vOf (g k : Nat) : Variance := match ((earlier g).entries.lookup g) with
    | some p => p.1.getD k .inv
    | none => .inv
  let generic := members.filter fun h => equations.signature[h].parameters > 0
  let cands := equations.settle dep (2 * generic.length + 1) (equations.polarity vOf generic)
  let F := candidateEntries equations cands
  if hv : variablesOk (some equations.renaming) (F.map (·.2.2)) = true ∧
      equations.validVariances F dep (F.map (·.2.2)) = true then
    { entries := F
      sound := by
        intro p hp
        have hall := checkEntries_entries_sound hv.2 hv.1
          (componentLook_cases equations F dep fun k e h => (earlier k).entry_sound h)
        exact ⟨hall p.2.2 (List.mem_map.mpr ⟨p, hp, rfl⟩),
          (variablesOk_sound hv.1).params (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩ }
  else {}

/-! ### Strongly connected components -/

structure Tarjan where
  index : Array (Option Nat)
  low : Array Nat
  onStack : Array Bool
  stack : List Nat := []
  next : Nat := 0
  /-- Components as found: each after every component it reaches. -/
  components : Array (List Nat) := #[]

/-- Tarjan's algorithm from `v`. Untrusted: a component list that is wrong
only leaves a dependency unchecked when its dependents are checked, so they
fail the check and become invariant or keep no variance. -/
partial def Tarjan.visit (succ : Nat → List Nat) (v : Nat) : StateM Tarjan Unit := do
  let s ← get
  set { s with index := s.index.set! v (some s.next), low := s.low.set! v s.next,
               onStack := s.onStack.set! v true, stack := v :: s.stack, next := s.next + 1 }
  for w in succ v do
    let s ← get
    match s.index[w]? with
    | some none =>
      Tarjan.visit succ w
      let s ← get
      set { s with low := s.low.set! v (min s.low[v]! s.low[w]!) }
    | some (some iw) =>
      if s.onStack[w]! then set { s with low := s.low.set! v (min s.low[v]! iw) }
    | none => pure ()
  let s ← get
  if some s.low[v]! == s.index[v]! then
    let (comp, rest) := s.stack.span (· != v)
    let comp := v :: comp
    let rest := rest.drop 1
    set { s with stack := rest, onStack := comp.foldl (fun a w => a.set! w false) s.onStack,
                 components := s.components.push comp }

/-- The strongly connected components of the reference graph, dependencies
first. -/
def Equations.components (equations : Equations) : Array (List Nat) :=
  let n := equations.signature.length
  let succ (h : Nat) : List Nat :=
    if hh : h < n then (equations.references ⟨h, hh⟩).filter (· < n) else []
  let init : Tarjan := { index := Array.replicate n none, low := Array.replicate n 0,
                         onStack := Array.replicate n false }
  let run : StateM Tarjan Unit := (List.range n).forM fun v => do
    if (← get).index[v]!.isNone then Tarjan.visit succ v
  (run.run init).2.components

/-! ### Variances, on demand -/

/-- **The heads' variances**, one lazily computed value per component. A
component's value is computed the first time a check reads one of its heads
(or of a component depending on it), and then reused. -/
structure Variances (equations : Equations) where
  /-- The component of each head. -/
  component : Array Nat
  /-- Per component, its checked variances. -/
  results : Array (Thunk (CheckedVariances equations))

/-- Compute the components; their variances wait until read. -/
def Equations.variances (equations : Equations) : Variances equations :=
  let comps := equations.components
  let component := comps.size.fold (init := Array.replicate equations.signature.length 0)
    fun c _ acc => (comps[c]!).foldl (fun a h => a.set! h c) acc
  let members (c : Nat) : List (Fin equations.signature.length) :=
    (comps[c]!).filterMap fun h =>
      if hh : h < equations.signature.length then some ⟨h, hh⟩ else none
  let results := comps.size.fold (init := (#[] : Array (Thunk (CheckedVariances equations))))
    fun c _ acc =>
      -- Components are found dependencies first: a head read by this one
      -- belongs to an earlier component or to this one.
      let earlier (g : Nat) : CheckedVariances equations := match component[g]? with
        | some c' => if c' < c then (match acc[c']? with
          | some t => t.get
          | none => {}) else {}
        | none => {}
      acc.push (Thunk.mk fun _ => equations.componentVariances (members c) earlier)
  { component, results }

/-- The checked variances of the component holding `k`. -/
def Variances.checkedAt {equations : Equations} (v : Variances equations) (k : Nat) :
    CheckedVariances equations :=
  match v.component[k]? with
  | some c => match v.results[c]? with
    | some t => t.get
    | none => {}
  | none => {}

/-- Head `k`'s entry, if its variance checked. -/
def Variances.entry {equations : Equations} (v : Variances equations) (k : Nat) :
    Option (Entry (Label equations.signature)) :=
  (v.checkedAt k).entry k

/-- **Computed variances are valid** (Theorem 1, RECURSIVE-EQUATIONS §4.3):
each entry the computation keeps holds wherever its hypotheses do. -/
theorem Variances.sound {equations : Equations} (v : Variances equations) {k : Nat}
    {e : Entry (Label equations.signature)} (h : v.entry k = some e) :
    EntrySound equations.graph e ∧ HypParams equations.graph e :=
  (v.checkedAt k).entry_sound h

/-- The computed variances as the entries instances cite, by head index. -/
def Variances.base {equations : Equations} (v : Variances equations) : Base equations.graph where
  size := equations.signature.length
  entry := v.entry
  sound _ _ h := v.sound h

/-- The equations' checks with their variances: substitution images, the
renaming, the computed variances as the entries `Var` cites, and `Var`'s
proposal. Every request certificate over the equations reads these. -/
def Equations.images (equations : Equations) (v : Variances equations) :
    InstanceImageCheck equations.graph :=
  { equations.instanceImageCheck with sub := some equations.renaming, base := v.base, gen := varGen }

end Verification.EquationGraphs
