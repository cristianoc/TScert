import Verification.Programs.ControlFlow

/-! Bounded, untrusted evidence search. Supplied point claims are immutable.
Search fuel and the finite type vocabulary affect success, never acceptance.
The final consumer checks the actual program and exact supplied claims again. -/
namespace Verification.CertificateProducer
open ProgramTyping PositiveGraphs PositiveNormalization PositiveRules
open ProgramCertificates PointClaims ControlFlow
open CallEffects (Arrow RestArrow Contract Effect)
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)


/-- How many types search gathers by following a graph's rows: an equation
graph's rows reach infinitely many (a recursive family, each member naming
larger ones), of which a proof relates only those near its pair. Search
only; acceptance reads no such bound. -/
def searchLimit : Nat := 120

/-- The types the rows of `S` reach, breadth first: every one when they are
fewer than `searchLimit`, as `readsFrom` gives them, else the nearest. -/
@[nospecialize] def searchReads [DecidableEq ι] (G : NormalGraph ι) (S : List ι) : List ι := Id.run do
  let mut seen := S.eraseDups
  let mut frontier := seen
  for _ in [0:searchLimit] do
    if frontier.isEmpty || seen.length ≥ searchLimit then break
    let fresh := (frontier.flatMap (reads G)).foldl (fun acc l =>
      if seen.contains l || acc.contains l then acc else l :: acc) []
    seen := seen ++ fresh.reverse
    frontier := fresh.reverse
  return seen

/-- A free map over `D`, iterated to its fixed point. -/
@[nospecialize] def searchFree [DecidableEq ι] (G : NormalGraph ι) (D : List ι) : FreeMap ι :=
  freeMapOf G D (D.length + 1) []

/-- What a label representation proposes for an instance of a scheme row at
given arrows: the binders' instances, and a table of the images of the
scheme's signatures' operands under them, each computed from the
representation's own syntax (an equation label's structural substitution,
RECURSIVE-EQUATIONS §4.3). Untrusted: the image check decides
(`InstanceImageCheck`). A representation with nothing to propose, a finite
table, gives none. -/
class Instantiates (ι : Type) where
  propose : SchemeRow ι → PositiveRules.Ops ι → List (RestArrow (List ι)) →
    Option (List (List ι) × InstTable ι)

structure PointClaim (ι : Type) where
  context : List (Ty ι)
  type : Ty ι
  deriving DecidableEq, Repr

@[nospecialize] def signature (c : NodeEvidence ι) : PointClaim ι := ⟨entry c, result c⟩

/-- Claims are part of the request, not facts the producer may replace. -/
@[nospecialize] def acceptResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : Ty ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (C.map signature = claims))).bind fun _ =>
  checkEntryResult (checker := checker) G images R P C start inputs codes

@[nospecialize] def acceptUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : Ty ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : Bool :=
  (acceptResult (checker := checker) G images R P claims C start inputs codes).accepted

theorem acceptUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : Ty ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι)) (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    acceptUsing (checker := checker) G images R P claims C start inputs codes = (
  decide (C.map signature = claims) && checkEntryUsing (checker := checker) G images R P C start inputs codes
  ) := by
  simp only [acceptUsing, acceptResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, checkEntryUsing]

theorem accepted_from_inputs [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {R P claims C start inputs}
    {codes : CodeEntry ι → Bool} (hc : acceptUsing (checker := checker) G images R P claims C start inputs codes = true) (n W h ρ)
    (he : EnvOk G inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : ProgramCertificates.CodesSound G codes := by exact Verification.ProgramCertificates.codesSound_none _) :
    SafeGraph (excOf G) P (meaning G R) n W h (.at start ρ) := by
  simp only [acceptUsing_eq, Bool.and_eq_true] at hc
  exact ControlFlow.accepted_inputs_safe hc.2 n W h ρ he hw hh hcodes

/-- Known rows with the instances proving them. -/
abbrev KnownInstances (ι : Type) :=
  List (List ι × PositiveRules.Ops ι × List (RestArrow (List ι)) ×
    PositiveCertificates.Instance ι)

/-- The table built while matching, and the instances found for the
instantiated binders. -/
structure InstState (ι : Type) where
  table : InstTable ι := []
  found : Ctx ι := []
  /-- Meet rows of binders not yet found, matched against a clause row: the
  meet's parameters, its clauses and the row. A binder's instance is a type
  whose meet with the other parameters' instances and the clauses that row
  holds. -/
  meets : List (List ι × List (Clause (List ι)) × ι) := []

/-- Match the scheme-side type `S` against the graph's type `T` under context
`κ`, adding table entries: a parameter row to its context image, a top binder
to `T` (recorded as its instance), a row free of the context to itself, a
clause row to a clause row matched operand by operand, a meet row to the meet
row or clause row its binder's image makes it, and a scheme row to a
scheme row, its binders standing for the other's. Untrusted:
`compareInstancesState` validates the candidate's images and bounds. -/
@[nospecialize] def matchRow [DecidableEq ι] [Instantiates ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) :
    Nat → InstState ι → Ctx ι → List ι → List ι → Option (InstState ι)
  | 0, _, _, _, _ => none
  | fuel + 1, st, κ, S, T =>
    let add (st : InstState ι) (p : ι) (T : List ι) : InstState ι :=
      { st with table := (p, κ, T) :: st.table }
    let pairs (st : InstState ι) (κ : Ctx ι) (xs ys : List (List ι)) : Option (InstState ι) :=
      if xs.length = ys.length then
        (xs.zip ys).foldlM (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st
      else none
    -- Instantiation replaces operands, not effects, density, field keys or
    -- other clause structure. Check that structure before selecting an
    -- overload: matching operands alone can choose a wrong first candidate
    -- and hide a valid later signature from the independent checker.
    let clauses (st : InstState ι) (κ : Ctx ι)
        (a b : Clause (List ι)) : Option (InstState ι) :=
      if a.map (fun _ => ()) == b.map (fun _ => ()) then
        pairs st κ a.operands b.operands
      else none
    match S with
    | [p] =>
      match entryImg st.table κ p with
      | some U => if U = T then some st else none
      | none =>
        if G.params p then
          match κ.lookup p with
          | some U => if U = T then some (add st p T) else none
          | none =>
            if bs.contains p then
              match st.found.lookup p with
              | some U => if U = T then some st else none
              | none => some { st with found := (p, T) :: st.found }
            else if T = [p] then some (add st p T) else none
        else if T = [p] && fixedBy G κ V p then some (add st p T)
        else match G.schemes p, T with
          | some s, [j] =>
            match G.schemes j with
            | some s2 =>
              if s2.binders.length = s.binders.length ∧
                  s2.signatures.length = s.signatures.length ∧
                  s2.variadic.length = s.variadic.length ∧
                  s2.bounds.length = s.bounds.length then
                let κ' := enter V p κ s.binders s2.binders
                -- Bounds are read outside the binders, so under `κ`.
                ((s.bounds.zip s2.bounds).foldlM (fun st pq =>
                  matchRow G bs V fuel st κ pq.1.2 pq.2.2) (add st p [j])).bind fun st =>
                ((s.signatures.zip s2.signatures).foldlM (fun st pq =>
                  if pq.1.effect != pq.2.effect then none else pairs st κ' pq.1.operands pq.2.operands)
                  st).bind fun st =>
                (s.variadic.zip s2.variadic).foldlM (fun st pq =>
                  if pq.1.effect != pq.2.effect then none else pairs st κ' pq.1.operands pq.2.operands) st
              else none
            | none => none
          | none, [j] =>
            match G.meets p with
            | some (q, cs) =>
              -- A meet row: its parameters' images decide its own. Before
              -- every binder's instance is found, nothing is matched.
              let qs := q :: G.meetParams p
              let ops := cs.flatMap Clause.operands
              let fixed (st : InstState ι) : Option (InstState ι) :=
                ops.foldlM (fun st S => matchRow G bs V fuel st κ S S) st
              let image (q : ι) := (κ.lookup q).orElse fun _ => if bs.contains q then none else some [q]
              match qs.mapM image, G.meets j with
              | none, _ => some { st with meets := (qs, cs, j) :: st.meets }
              | some Us, some (r, ds) =>
                let rs := r :: G.meetParams j
                if Us.all (fun U => rs.any (U == [·])) ∧ rs.all (fun r => Us.contains [r]) ∧
                    ds.length = cs.length then
                  (cs.zip ds).foldlM (fun st cd => clauses st κ cd.1 cd.2)
                    (add st p [j])
                else if Us.contains [j] then fixed (add st p [j]) else none
              | some _, none => fixed (add st p [j])
            | none =>
              if (G p).length = (G j).length then
                ((G p).zip (G j)).foldlM (fun st cd => clauses st κ cd.1 cd.2)
                  (add st p [j])
              else none
          | _, _ => none
    | _ =>
      let positional := if S.length = T.length then
          (S.zip T).foldlM (fun st xy => matchRow G bs V fuel st κ [xy.1] [xy.2]) st
        else none
      -- A union is a set of labels: its fixed labels match themselves in `T`,
      -- and its one other label takes the rest (`undefined | T` against
      -- `boolean | undefined`).
      let fixed := S.filter fun p => T.contains p && !G.params p &&
        fixedBy G κ V p
      let bySet := match S.filter (!fixed.contains ·) with
        | [p] => matchRow G bs V fuel (fixed.foldl (fun st q => add st q [q]) st) κ [p]
            (T.filter (!fixed.contains ·))
        | _ => none
      -- A union of binders and fixed rows (`T | U`): its image is theirs
      -- together. Before the binders' instances are found, nothing is matched.
      let byParts : Option (InstState ι) := do
        let (st, img, deferred) ← S.foldlM (fun (acc : InstState ι × List ι × Bool) l =>
          let (st, img, deferred) := acc
          if G.params l then
            match κ.lookup l with
            | some U => some (add st l U, img ++ U, deferred)
            | none =>
              if bs.contains l then
                match st.found.lookup l with
                | some U => some (st, img ++ U, deferred)
                | none => some (st, img, true)
              else some (add st l [l], img ++ [l], deferred)
          else if fixedBy G κ V l then some (add st l [l], img ++ [l], deferred)
          else none) (st, [], false)
        if deferred || (img.all (· ∈ T) && T.all (· ∈ img)) then some st else none
      positional.orElse fun _ => bySet.orElse fun _ => byParts

@[nospecialize] def matchSig [DecidableEq ι] [Instantiates ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) (fuel : Nat)
    (st : InstState ι) (κ : Ctx ι) (p q : Arrow (List ι)) :
    Option (InstState ι) := do
  if !p.effect.covers q.effect || p.arguments.length != q.arguments.length then none
  -- A scheme receiver admitting every value admits the target's
  -- (`instSig`): it is not matched.
  let pairs := if receiverUniverse G p.receiver q.receiver then (p.result :: p.arguments).zip (q.result :: q.arguments)
    else (p.receiver :: p.result :: p.arguments).zip (q.receiver :: q.result :: q.arguments)
  pairs.foldlM (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st

@[nospecialize] def matchRest [DecidableEq ι] [Instantiates ι] (G : NormalGraph ι) (bs : List ι) (V : FreeMap ι) (fuel : Nat)
    (st : InstState ι) (κ : Ctx ι) (p q : RestArrow (List ι)) :
    Option (InstState ι) := do
  if !p.effect.covers q.effect || p.arguments.1.length != q.arguments.1.length then none
  let pairs := if receiverUniverse G p.receiver q.receiver then (p.arguments.2 :: p.result :: p.arguments.1).zip (q.arguments.2 :: q.result :: q.arguments.1)
    else (p.receiver :: p.arguments.2 :: p.result :: p.arguments.1).zip (q.receiver :: q.arguments.2 :: q.result :: q.arguments.1)
  pairs.foldlM (fun st xy => matchRow G bs V fuel st κ xy.1 xy.2) st


/-- Propose a substitution by matching the rows read by a scheme and its target. -/
@[nospecialize] def matchedInstance [DecidableEq ι] [Hashable ι] [Instantiates ι]
    (G : NormalGraph ι) (fuel : Nat) (s : SchemeRow ι)
    (L : PositiveRules.Ops ι) (M : List (RestArrow (List ι))) : Option (PositiveCertificates.Instance ι) := do
  let roots := (s.signatures.flatMap Arrow.operands ++ s.variadic.flatMap RestArrow.operands ++
    L.flatMap Arrow.operands ++ M.flatMap RestArrow.operands).flatten
  let D := searchReads G roots
  let V := searchFree G D
  -- Each target signature matched against one of the scheme's, fixed
  -- against fixed and variadic against variadic.
  let each (κ : Ctx ι) (st : InstState ι) : Option (InstState ι) := do
    let st ← L.foldlM (fun st q =>
      s.signatures.findSome? fun p => matchSig G s.binders V fuel st κ p q) st
    M.foldlM (fun st q =>
      s.variadic.findSome? fun p => matchRest G s.binders V fuel st κ p q) st
  let first ← each [] {}
  -- A binder read only through meet rows: an instance whose meet with the
  -- other parameters' instances and the row's clauses is the target row.
  -- The target itself is a candidate even when it is opaque; image equality
  -- and bound validation decide whether that proposal establishes inclusion.
  let targetOps := (L.flatMap Arrow.operands ++ M.flatMap RestArrow.operands).eraseDups
  let throughMeet (found : Ctx ι) (b : ι) : Option (Ty ι) := first.meets.findSome? fun (qs, cs, j) =>
    if !qs.contains b then none else ([j] :: targetOps).find? fun U =>
      match qs.mapM (fun q => if q == b then some U else
          (found.lookup q).orElse fun _ => if s.binders.contains q then none else some [q]) with
      | some Us =>
        let Ls := Us.map (PositiveRules.clausesOf G) ++ [cs]
        U == [j] || (Us.all G.plainTy &&
          (PositiveRules.sameClauses (G j) (PositiveRules.meetMany Ls) ||
            PositiveRules.sameClauses (G j) (PositiveRules.meetMany Ls.reverse)))
      | none => false
  let mut found := first.found
  for _ in [:s.binders.length] do
    for b in s.binders do
      if (found.lookup b).isNone then
        if let some U := throughMeet found b then found := (b, U) :: found
  let θs := s.binders.map fun b => (found.lookup b).getD [b]
  let κ₀ := s.binders.zip θs
  -- An instance found through a meet row is named by no target row: the
  -- table's domain holds it too.
  let (D, V) := if first.meets.isEmpty then (D, V) else
    let D := searchReads G (roots ++ θs.flatten)
    (D, searchFree G D)
  let each (κ : Ctx ι) (st : InstState ι) : Option (InstState ι) := do
    let st ← L.foldlM (fun st q =>
      s.signatures.findSome? fun p => matchSig G s.binders V fuel st κ p q) st
    M.foldlM (fun st q =>
      s.variadic.findSome? fun p => matchRest G s.binders V fuel st κ p q) st
  let final ← each κ₀ {}
  some ⟨final.table, θs, D, V⟩


/-- Untrusted instance alternatives from syntax, equivalent spellings and row
matching. Only the common comparison operation validates these choices. -/
@[nospecialize] def instanceCandidates [DecidableEq ι] [Hashable ι] [Instantiates ι]
    (G : NormalGraph ι) (sub : Option (Renaming G)) (fuel : Nat) (s : SchemeRow ι)
    (L : PositiveRules.Ops ι) (M : List (RestArrow (List ι))) : List (PositiveCertificates.Instance ι) :=
  -- Where the target's operands are other spellings of the instance's (a
  -- result `Pair<[number, string]>` for `Pair<[T, U]>`), the binders are
  -- found from the signatures without their results, and the instance's own
  -- signatures, by the renaming's substitution, are proposed instead.
  let exact : Option (PositiveRules.Ops ι) := do
    let r ← sub
    let noResult (a : Arrow (List ι)) : Arrow (List ι) := { a with result := [] }
    let (θs, _) ← Instantiates.propose { s with signatures := s.signatures.map noResult }
      (L.map noResult) []
    some (s.signatures.map (Arrow.map (r.substitute (s.binders.zip θs))))
  let proposal := (Instantiates.propose s L M).orElse fun _ => do
    let L' ← exact
    let (θs, table) ← Instantiates.propose s L' M
    some (θs, table)
  let syntactic : List (PositiveCertificates.Instance ι) := match proposal with
    | none => []
    | some (θs, table) =>
      let c : PositiveCertificates.Instance ι := ⟨table, θs, [], []⟩
      let κ₀ := s.binders.zip θs
      -- An operand whose image is another spelling of the target's (a
      -- result `Pair<[number, string]>` for `Pair<[T, U]>` at `string`, a
      -- callback the target states as a definition of its own): the
      -- target's as the image of the one label whose image is not among the
      -- target's, which the image check accepts only when the two are
      -- proved equal.
      let respell (P Q : List ι) : InstTable ι :=
        match tyImg table κ₀ P with
        | some img =>
          if PositiveRules.sameLabels img Q then [] else
          let open_ := if P.length == 1 then P
            else P.filter fun l => !((entryImg table κ₀ l).getD []).all (· ∈ Q)
          match open_ with
          | [l] =>
            let others := (P.filter (· != l)).flatMap fun m => (entryImg table κ₀ m).getD []
            [(l, κ₀, Q.filter (!others.contains ·))]
          | _ => []
        | none => []
      let fixedPatch (p q : Arrow (List ι)) : InstTable ι :=
        let operands := if receiverUniverse G p.receiver q.receiver then
          (p.result :: p.arguments).zip (q.result :: q.arguments)
        else (p.receiver :: p.result :: p.arguments).zip (q.receiver :: q.result :: q.arguments)
        operands.flatMap fun (P, Q) => respell P Q
      let restPatch (p q : RestArrow (List ι)) : InstTable ι :=
        let operands := if receiverUniverse G p.receiver q.receiver then
          (p.arguments.2 :: p.result :: p.arguments.1).zip (q.arguments.2 :: q.result :: q.arguments.1)
        else (p.receiver :: p.arguments.2 :: p.result :: p.arguments.1).zip
          (q.receiver :: q.arguments.2 :: q.result :: q.arguments.1)
        operands.flatMap fun (P, Q) => respell P Q
      -- Each target chooses one overload. Images of an unused overload need
      -- not equal that target's operands; the checker validates each choice.
      let patches := L.foldl (fun patches q => patches.flatMap fun patch =>
        s.signatures.filterMap fun p =>
          if p.arguments.length == q.arguments.length && p.effect.covers q.effect then
            some (patch ++ fixedPatch p q) else none) ([[]] : List (InstTable ι))
      let patches := M.foldl (fun patches q => patches.flatMap fun patch =>
        s.variadic.filterMap fun p =>
          if p.arguments.1.length == q.arguments.1.length && p.effect.covers q.effect then
            some (patch ++ restPatch p q) else none) patches
      c :: (patches.filter (! ·.isEmpty)).map fun patch =>
        ⟨patch.eraseDups ++ table, θs, [], []⟩
  syntactic ++ (matchedInstance G fuel s L M).toList

/-- How deep instance matching follows a type's rows: search only. -/
def instanceFuel : Nat := 64

/-- A scheme row below an arrow type. -/
@[nospecialize] def instantiationUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (fuel : Nat) (A B : Ty ι) :
    List (PositiveCertificates.Instance ι) :=
  match A, PositiveCertificates.instanceTarget G B with
  | [i], some (L, M, _) =>
    match G.schemes i with
    | some s => instanceCandidates G images.sub fuel s L M
    | none => []
  | _, _ => []

/-- Instances of prototype members a table's rows ask for: for a row whose
source's prototype chain holds, under a target method's key, a scheme row,
instances whose signatures are the method's with either host as receiver. -/
@[nospecialize] def rowInstances [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (fuel : Nat) (table : Table ι) : KnownInstances ι :=
  (table.flatMap fun (A, B) =>
    let methods := (expand G B).flatMap fun c => match c with
      | .refs _ _ _ _ ns _ | .dict _ _ _ _ _ ns _ _ => ns
      | _ => []
    (expand G A).flatMap fun c => match c with
      | .refs a bs vs _ _ _ =>
        match ((a :: bs).flatten ++ vs).lookup CallArguments.protoField with
        | some P => (PositiveCertificates.protoChain G PositiveRules.protoChainDepth P).flatMap fun P => methods.flatMap fun q =>
            match PositiveRules.viewOf G P q.key with
            | some [i] => match G.schemes i with
              | some s =>
                -- The target host can expose the declaration application
                -- needed to infer a receiver-dependent scheme instance.
                -- Coverage still checks the source against that receiver.
                let hosts := [A, B].eraseDups.flatMap fun receiver =>
                  let L := q.calls.map (·.withReceiver receiver)
                  let M := q.rests.map (·.withReceiver receiver)
                  (instanceCandidates G images.sub fuel s L M).map fun c => ([i], L, M, c)
                -- Arguments and results can determine an inherited method's
                -- instance even when its receiver is a proper base type.
                -- Infer without the receiver, then check the full signatures.
                let inferred := match images.sub with
                  | none => []
                  | some r =>
                    let shape := { s with
                      signatures := s.signatures.map (·.withReceiver [])
                      variadic := s.variadic.map (·.withReceiver []) }
                    (instanceCandidates G images.sub fuel shape
                      (q.calls.map (·.withReceiver [])) (q.rests.map (·.withReceiver []))).flatMap fun c =>
                      let subst := r.substitute (s.binders.zip c.instances)
                      let L := s.signatures.map (Arrow.map subst)
                      let M := s.variadic.map (RestArrow.map subst)
                      (instanceCandidates G images.sub fuel s L M).map fun c => ([i], L, M, c)
                hosts ++ inferred
              | none => []
            | _ => []
        | none => []
      | _ => [])

/-- The common subtype operation with candidate instances found by matching. -/
@[nospecialize] def comparisonUsing [DecidableEq ι] [Hashable ι] [Instantiates ι]
    (G : NormalGraph ι) (images : InstanceImageCheck G) (A B : Ty ι) :
    PositiveCertificates.ComparisonResult (PositiveCertificates.SubtypeChoices ι) :=
  PositiveCertificates.compareUsing G images A B
    (instantiationUsing G images instanceFuel)
    (rowInstances G images instanceFuel)

theorem comparisonUsing_sound [DecidableEq ι] [Hashable ι] [Instantiates ι]
    {G : NormalGraph ι} {images : InstanceImageCheck G} {A B}
    (h : (comparisonUsing G images A B).accepted = true) :
    ∀ η, FamLe (mixedMeaning G η A) (mixedMeaning G η B) :=
  PositiveCertificates.compareUsing_sound h

/-- Instantiation choices, or the typed reason subtype search is unfinished. -/
@[nospecialize] def subtypeUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) : CheckResult ι (PositiveCertificates.SubtypeChoices ι) :=
  CheckResult.fromComparison images.budget.rounds A B (comparisonUsing G images A B)

/-- Proofs that the member of key `k` on `O` covers each signature of `F`:
for each fixed one, a member signature of as many parameters, each claimed
parameter within the member's and the member's result within the claimed;
for each variadic one, a member's of as many fixed parameters, likewise, the
claimed rest within the member's too. -/
@[nospecialize] def memberProofsUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (O : Ty ι) (k : PropKey)
    (F : Ty ι) : CheckResult ι (List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) ×
      List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι × PositiveCertificates.SubtypeChoices ι) ×
      List (PositiveCertificates.SubtypeChoices ι)) := do
  let m ← ProgramTyping.memberOf G O k
  -- At a quantified signature, the member bound to its host is the scheme.
  if expand G F = [] && m.schemes.contains F then return ([], [], [])
  let [.arrs L S] := expand G F | none
  let calls ← L.mapM fun q => m.calls.findCheck? fun c => do
    if q.arguments.length != c.arguments.length || !c.effect.covers q.effect then none
    let ps ← (q.arguments.zip c.arguments).mapM fun (D, C) => subtypeUsing G images D C
    let pr ← subtypeUsing G images c.result q.result
    pure (ps, pr)
  let rests ← S.mapM fun s => m.rests.findCheck? fun c => do
    if s.arguments.1.length != c.arguments.1.length || !c.effect.covers s.effect then none
    let ps ← (s.arguments.1.zip c.arguments.1).mapM fun (D, C) => subtypeUsing G images D C
    let pe ← subtypeUsing G images s.arguments.2 c.arguments.2
    let pr ← subtypeUsing G images c.result s.result
    pure (ps, pe, pr)
  -- The object's type within each type the member's host must meet.
  let receivers ← m.receivers.mapM fun T => subtypeUsing G images O T
  pure (calls, rests, receivers)

/-- A subsumption step to `A`. Where the types are not comparable as they are,
search proposes a comparison with each aliased label read as its alias, which
only a body check that admits those aliases accepts. -/
@[nospecialize] def coerce [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (aliases : List (ι × ι)) (e : ProgramCertificates.Evidence ι) (A : Ty ι) :
    CheckResult ι (ProgramCertificates.Evidence ι) := do
  if (claim e).type = A then return e
  let p ← (subtypeUsing G images (claim e).type A).orElse fun _ =>
    if aliases.isEmpty then none else
      subtypeUsing G images (ProgramCertificates.renameTy aliases (claim e).type)
        (ProgramCertificates.renameTy aliases A)
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

instance [DecidableEq ι] (G : NormalGraph ι) (B : Ty ι) (tag : Tag) (q : Bool) :
    Decidable (Answers G B tag q) := by unfold Answers; infer_instance

/-- Search ordinary typing rules. Every recursive expression request decreases
search fuel, including implicit let typing. Suggestions only prioritize candidate
types; every premise is proved in the actual context, even when the suggestion
came from a different context. No execution budget is inspected. -/
@[nospecialize] def expressionWithUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (suggestions : List (Sequent ι)) (aliases : List (ι × ι)) :
    Nat → List (Ty ι) → Tm → Ty ι → CheckResult ι (ProgramCertificates.Evidence ι)
  | 0, _, _, _ => none
  | fuel+1, Γ, t, A => Id.run do
    -- A slot no value meets makes the context unsatisfiable: splitting it
    -- leaves no case, so the sequent holds whatever the term and its type.
    -- This is a node a refinement proved unreachable (`unionVar`).
    if let some i := Γ.findIdx? List.isEmpty then
      return some (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) [])
    let leaf := fun B r => ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ r []
    let leaf' := fun (i : Nat) (C : Ty ι) => ProgramCertificates.Evidence.node ⟨Γ,.var i,C⟩ .var []
    let recur := expressionWithUsing G images pool suggestions aliases fuel
    -- A slot of the empty type holds no value: the point is unreachable, and
    -- eliminating that union leaves no premise.
    if let some i := Γ.findIdx? (·.isEmpty) then
      return some (.node ⟨Γ,t,A⟩ (.unionVar i) [])
    -- Union elimination refines an immutable receiver slot in each premise;
    -- it neither evaluates the operation twice nor inserts a runtime tag test.
    let splitReceiver := fun receiver => do
      let .var i := receiver | none
      let B ← Γ[i]?
      if B.length ≤ 1 then none else do
        let ps ← B.mapM fun b => recur (Γ.set i [b]) t A
        pure (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    -- The types an operand may be read at as a string: a slot's own, then
    -- the pool's, each all strings.
    let stringOperands := fun (a : Tm) =>
      ((match a with | .var i => (Γ[i]?).toList | _ => []) ++ pool).filter fun S =>
        decide (Answers G S .isStr true)
    match t with
    | .var i => return (CheckResult.fromOption Γ[i]?).bind fun B => coerce G images aliases (leaf B .var) A
    | .nul | .undef | .tru | .fls =>
      let r := match t with | .nul => Rule.nul | .undef => .undef | .tru => .tru | _ => .fls
      return (A :: pool).findCheck? fun B =>
        let r := if expand G B = [.boolLit true] && t == .tru then Rule.truLit
          else if expand G B = [.boolLit false] && t == .fls then Rule.flsLit else r
        (checkTreeResult G images (leaf B r)).bind fun _ => coerce G images aliases (leaf B r) A
    -- A number has one rule: its own singleton. Reaching `number`, or any
    -- union above it, is the coercion's job, exactly as for a boolean literal.
    | .num _ =>
      -- Its own singleton where the claim names one, the family where it does
      -- not: a literal claimed at `number` has no singleton label to coerce
      -- from, exactly as a Boolean claimed at `boolean` has none.
      return (A :: pool).findCheck? fun B =>
        if checkTreeUsing G images (leaf B .numLit) then coerce G images aliases (leaf B .numLit) A
        else if checkTreeUsing G images (leaf B .num) then coerce G images aliases (leaf B .num) A
        else none
    | .str _ =>
      return (A :: pool).findCheck? fun B =>
        if checkTreeUsing G images (leaf B .strLit) then coerce G images aliases (leaf B .strLit) A
        else if checkTreeUsing G images (leaf B .str) then coerce G images aliases (leaf B .str) A
        else none
    | .bigint _ =>
      return (A :: pool).findCheck? fun B =>
        if checkTreeUsing G images (leaf B .bigintLit) then coerce G images aliases (leaf B .bigintLit) A
        else if checkTreeUsing G images (leaf B .bigint) then coerce G images aliases (leaf B .bigint) A
        else none
    -- Graph code: its captures at their slots' types, the code the unit's
    -- table checked; the claim or a pool type. A function's (`Rule.funGraph`)
    -- has a fresh bag; with a rest, each variadic signature's store is at a
    -- pool type that is its rest store. A class value's (`Rule.ctorGraph`)
    -- has its receiver slot at a pool type that is exactly `undefined`, what
    -- `new` passes there. A callable object's (`Rule.callableGraph`) has the
    -- bag's initializers, then the captures.
    | .makeAt (.graph _ _ _ _ caps kind rest) ns inits =>
      let some slots := ProgramCertificates.varSlots caps | return none
      let some ps := slots.mapM (fun i => (Γ[i]?).map fun C => leaf' i C) | return none
      let arraysOf := fun (S : List (RestArrow (Ty ι))) =>
        if rest then S.mapM fun p => pool.find? fun R => decide (RestStore G R p.arguments.2) else some []
      let fresh := ns == [codeField] && inits == [.nul]
      let classFields := ns.head? == some codeField && inits.head? == some .nul
      return (A :: pool).findCheck? fun F => do
        match kind, expand G F with
        | .call, [.arrs _ S] =>
          if !fresh then none else do
          coerce G images aliases (.node ⟨Γ,t,F⟩ (.funGraph (← arraysOf S)) ps) A
        | .construct, [.ctors _ [] P []] =>
          if !classFields || P.map Prod.fst != ns.tail || inits.length != ns.length then none else do
          let U ← pool.find? fun U => decide (expand G U = [.undef])
          let eas ← (inits.tail.zip (P.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images aliases (.node ⟨Γ,t,F⟩ (.ctorGraph U) (eas ++ ps)) A
        | .call, [.callable P [] _ S] =>
          if P.map Prod.fst != ns || inits.length != ns.length then none else do
          let eas ← (inits.zip (P.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images aliases (.node ⟨Γ,t,F⟩ (.callableGraph (← arraysOf S)) (eas ++ ps)) A
        | _, _ => none
    -- `new f(args)`: a construct signature of the constructor's type taking at
    -- least as many parameters as there are actuals; each omitted position
    -- proves `undefined`, as a call's does.
    | .construct f args =>
      let own := match f with | .var i => (Γ[i]?).toList | _ => []
      return (own ++ pool).eraseDups.findCheck? fun F => do
        let [.ctors L S _ _ _] := expand G F | none
        let flags := args.map fun a => match a with | .spread _ => true | _ => false
        let candidates : List ((List (Ty ι) × Ty ι) ⊕ (List (Ty ι) × Ty ι × Ty ι)) :=
          (if flags.any id then [] else L.map .inl) ++ S.map .inr
        candidates.findCheck? fun c => match c with
        | .inl p => do
          if args.length > p.1.length then none else do
          let _ ← subtypeUsing G images p.2 A
          let ef ← recur Γ f F
          let eas ← (args.zip p.1).mapM fun (a,D) => recur Γ a D
          let eus ← (p.1.drop args.length).mapM fun D => recur Γ .undef D
          coerce G images aliases (.node ⟨Γ,t,p.2⟩ .construct (ef :: eas ++ eus)) A
        -- A variadic construct signature: the fixed actuals at its
        -- parameters, then the further parts as a variadic call's.
        | .inr ⟨Ps, P, B⟩ => do
          let k := Ps.length
          if args.length < k || (flags.take k).any id then none else do
          let _ ← subtypeUsing G images B A
          let ef ← recur Γ f F
          let eas ← (args.zip Ps).mapM fun (a,D) => recur Γ a D
          let parts := args.drop k
          let partFlags := flags.drop k
          let eps ← if partFlags.any id then do
              let E ← restElem G P
              parts.mapM fun a => match a with
                | .spread s => pool.findCheck? fun S =>
                    if decide (SpreadsInto G S E) then recur Γ s S else none
                | a => recur Γ a E
            else do
              let [.pack T []] := expand G P | none
              parts.zipIdx.mapM fun (a, i) => do recur Γ a (← positionTy T i)
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ (.constructRest k partFlags P) (ef :: eas ++ eps)
          (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
    -- `.bind`'s forwarding descriptor: a leaf whose checker reads the saved
    -- slots from the context; the claimed type, or a pool type, is its result.
    | .makeAt (.bound (.var _) (.var _) _) [] [] =>
      return (A :: pool).findCheck? fun F =>
        if checkTreeUsing G images (leaf F .bindE) then coerce G images aliases (leaf F .bindE) A
        else if checkTreeUsing G images (leaf F .bindRestE) then coerce G images aliases (leaf F .bindRestE) A
        else none
    -- A member bound to its host: a leaf whose checker reads the object's type
    -- from the context; the claimed type, or a pool type, is its result.
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var _) []) [] []) =>
      let schemes := match Γ[i]? with
        | some O => ProgramTyping.memberSchemes G O k
        | none => []
      return (A :: schemes ++ pool).findCheck? fun F => do
        let (ps, rs, vs) ← memberProofsUsing G images (← Γ[i]?) k F
        (checkTreeResult G images (leaf F (.bindMember ps rs vs))).bind fun _ =>
          coerce G images aliases (leaf F (.bindMember ps rs vs)) A
    | .letE a b =>
      let exactTypes := suggestions.reverse.filterMap fun j =>
        if j.context == Γ && j.term == a then some j.type else none
      let termTypes := suggestions.reverse.filterMap fun j =>
        if j.term == a then some j.type else none
      let variableType := match a with | .var i => (Γ[i]?).toList | _ => []
      let preferred := variableType ++ exactTypes ++ termTypes
      return (preferred ++ pool).eraseDups.findCheck? (fun B => do
        let ea ← recur Γ a B
        let eb ← recur (B :: Γ) b A
        return ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .letE [ea,eb])
    | .invoke f recv args =>
      -- A callee read from a slot is tried first at the slot's own type, a
      -- fixed signature before any variadic one of the pool: coercing it to
      -- each of those first, where its own type is fixed, fails at the cost
      -- of a table over the pool each time. Order only; every premise is
      -- still proved.
      let own := match f with | .var i => (Γ[i]?).toList | _ => []
      -- A variadic callee: the receiver at the signature's receiver, the fixed
      -- actuals at its parameters, then the further parts: with a spread, each
      -- at the element rest's element, or a spread of a pool store type whose
      -- elements are; without one, each at its position in the rest's tuple.
      let variadic := fun (candidates : List (Ty ι)) => candidates.findCheck? fun F => do
        (restSigs G F).findCheck? fun ⟨Rt, (Ps, P), B, effect⟩ => do
          -- Fixed actuals first; a shorter call omits trailing fixed positions,
          -- each proving `undefined`, and writes no further part.
          let k := min args.length Ps.length
          let omitted := Ps.drop k
          let parts := args.drop k
          if !omitted.isEmpty && !parts.isEmpty then none else do
          let _ ← subtypeUsing G images B A
          let ef ← recur Γ f F
          let er ← recur Γ recv Rt
          let eas ← (args.zip Ps).mapM fun (a,D) => recur Γ a D
          let eus ← omitted.mapM fun D => recur Γ .undef D
          let flags := parts.map fun a => match a with | .spread _ => true | _ => false
          -- A rest that is a packed binder takes one spread of the store of
          -- one of its values, after the fixed actuals.
          if let ([.spread (.readAt key a)], some q) :=
              (parts, P.find? fun l => G.parameterKinds l == some .packed) then
            if key == CallArguments.arrayStoreField && omitted.isEmpty then
              let ea ← ((Γ ++ pool).filter fun C => decide (PackedBy G C q)).findCheck? fun C => recur Γ a C
              let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩
                (.callPacked effect k q P) (ef :: er :: eas ++ [ea])
              return ← (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
          let eps ← if flags.any id then do
              let E ← restElem G P
              parts.mapM fun a => match a with
                | .spread s => pool.findCheck? fun S =>
                    if decide (SpreadsInto G S E) then recur Γ s S else none
                | a => recur Γ a E
            else do
              let [.pack T []] := expand G P | none
              parts.zipIdx.mapM fun (a, i) => do recur Γ a (← positionTy T i)
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩
            (.callRest effect k omitted.length flags P) (ef :: er :: eas ++ eus ++ eps)
          (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
      let direct := fun (candidates : List (Ty ι)) => candidates.findCheck? fun F => do
        let (L,r) ← match expand G F with
          | [.arrs L _] => some (L,Rule.app)
          | [.callable _ _ L _] => some (L,Rule.callCallable)
          | _ => none
        L.findCheck? fun p => do
          -- Require every operand before searching the premises. A signature
          -- with more positions than the call writes is usable when each
          -- remaining contract admits `undefined`, the value bound there.
          if args.length > p.arguments.length then none else do
            let omitted := p.arguments.drop args.length
            let _ ← subtypeUsing G images p.result A
            let ef ← recur Γ f F
            let er ← recur Γ recv p.receiver
            let eas ← (args.zip p.arguments).mapM fun (a,D) => recur Γ a D
            let eus ← omitted.mapM fun D => recur Γ .undef D
            coerce G images aliases (.node ⟨Γ,t,p.result⟩ (r p.effect) (ef :: er :: eas ++ eus)) A
      if let some e := variadic own <|> direct own <|> variadic pool <|> direct pool then return some e
      -- A callee or, for a method dispatched on its object, the receiver.
      return splitReceiver f <|> splitReceiver recv
    | .makeAt .absent ns inits =>
      return (A :: pool).findCheck? fun R => do
        if !(decide ns.Nodup) then none else do
        if inits.length != ns.length then none else do
        match expand G R with
        | [.refs B [] [] [] [] ks] =>
          if B.map Prod.fst != ns || !ks.all (fun K => ns.all K.admits) then none else do
          let ps ← (inits.zip (B.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images aliases (.node ⟨Γ,t,R⟩ .alloc ps) A
        -- A literal allocated directly at a dictionary, each field an index
        -- may admit at that index's type.
        | [.dict B [] [] ix os [] [] cs] =>
          if B.map Prod.fst != ns || ns.contains CallArguments.protoField ||
            !B.all (fun f => (ix ++ cs).all fun y => !y.1.may f.1 || f.2 == y.2) ||
            !os.all (fun o => !ns.contains o.key && cs.all fun y => !y.1.may o.key ||
              o.type == y.2 || (G.plainTy y.2 && (expand G y.2).isEmpty)) then none else do
          let ps ← (inits.zip (B.map Prod.snd)).mapM fun (a,D) => recur Γ a D
          coerce G images aliases (.node ⟨Γ,t,R⟩ .alloc ps) A
        | _ => none
    | .indexAt a key =>
      -- A key of a class within an index's reads through it: a string
      -- through a string index, a number through a number or string index, a
      -- symbol through a symbol index.
      return (A :: pool).findCheck? fun R => do
        let [.dict _ [] _ ix _ _ _ _] := expand G R | none
        ix.findCheck? fun (Kx, E) =>
        [IndexKeys.strings, .numeric, .symbols].findCheck? fun KK => do
          if !KK.within Kx then none else do
          (A :: pool).findCheck? fun K => do
            if expand G K != [keyClause KK] then none else do
            (A :: pool).findCheck? fun U => do
              if expand G U != [.undef] then none else do
              let B := E ++ U
              let _ ← subtypeUsing G images B A
              let ea ← recur Γ a R
              let ek ← recur Γ key K
              coerce G images aliases (.node ⟨Γ,t,B⟩ (.indexDict Kx KK E U) [ea, ek]) A
    | .readAt f a =>
      let direct := pool.findCheck? fun R => do
        -- An invariant field reads at its contract; a view field at its bound;
        -- an optional field, writable or readonly, at its type or `undefined`; a key a
        -- bound does not admit at the prototype's field or view.
        let (B,r) ← (show Option (Ty ι × Rule ι) from match expand G R with
          | [.refs fs [] vs os _ ks] =>
            (fs.lookup f).map (·,Rule.read) <|>
              ((vs.lookup f).bind fun B => if f == lengthKey && !lengthExcluded G B then none else some (B, Rule.readView)) <|>
              (((os.find? (·.key == f)).map (·.type)).bind fun E => pool.findSome? fun U =>
                if expand G U == [.undef] then some (E ++ U, Rule.readOptional E U) else none) <|>
              (if ks.any (fun K => !K.admits f) then
                ((fs ++ vs).lookup CallArguments.protoField).bind fun P =>
                  match expand G P with
                  | [.refs gs [] ws _ _ _] =>
                    ((gs ++ ws.filter (·.1 != lengthKey)).lookup f).map (·, Rule.readProto P)
                  | _ => none
              else none)
          | [.callable fs _ _ _] => (fs.lookup f).map (·,Rule.readCallable)
          | [.ctors _ _ fs _ vs] => (fs.lookup f).map (·,Rule.readCallable) <|> (vs.lookup f).map (·,Rule.readBagView)
          -- A dictionary's named field or view, else its index, which may miss.
          -- The index holds of every present field, an optional one included.
          | [.dict fs [] vs ix _ _ _ _] =>
            (fs.lookup f).map (·,Rule.read) <|>
            ((vs.lookup f).bind fun B => if f == lengthKey && !lengthExcluded G B then none else some (B, Rule.readView)) <|>
            (numericFirst ix).findSome? fun (K, B) => if !K.surely f then none else
              pool.findSome? fun U =>
                if expand G U == [.undef] then some (B ++ U, Rule.readDict K B U) else none
          | _ => none )
        let _ ← subtypeUsing G images B A
        let ea ← recur Γ a R
        coerce G images aliases (.node ⟨Γ,t,B⟩ r [ea]) A
      return direct.orElse fun _ => splitReceiver a
    | .writeAt f a b =>
      let direct := pool.findCheck? fun R => do
        let (fs,r) ← match expand G R with
          | [.refs fs [] _ _ _ _] => some (fs,Rule.write)
          | [.callable fs _ _ _] | [.ctors _ _ fs _ _] => some (fs,Rule.writeCallable)
          | _ => none
        let B ← fs.lookup f
        let ea ← recur Γ a R
        let eb ← recur Γ b B
        (A :: pool).findCheck? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ r [ea,eb]
          (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
      return direct.orElse fun _ => splitReceiver a
    | .arith op a b =>
      -- Each operand at a pool type of the operand clauses the operator
      -- takes (numbers and bigints; for a comparison also strings and the
      -- other primitives `ToNumeric` converts, every printable primitive for
      -- `+`), or any pool type for an equality, the
      -- right one only where the pair classifies or one operand decides the
      -- equality; the rule then checks every pair and the result, at the
      -- requested type when it holds the result's kind, else coerced.
      let equality := op == .eq || op == .looseEq
      let operands := pool.filter fun R => equality || G.plainTy R && !(expand G R).isEmpty &&
        (expand G R).all fun c => numberClause c || bigintClause c
          || (op.relational && (stringClause c || numericClause c))
          || (op == .add && printableClause c)
      return operands.findCheck? fun R => do
        let ea ← recur Γ a R
        (operands.filter fun S => (operandsResult G op R S).isSome ||
            decide (EqualityDecided G op R) || decide (EqualityDecided G op S)).findCheck? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findCheck? fun N =>
            let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .arith [ea,eb]
            (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
    -- A literal with spreads: a store type of any length at some element
    -- type, each plain part at it, and for each spread a pool store type
    -- whose elements it admits.
    | .arrLit inits =>
      let flags := inits.map fun a => match a with | .spread _ => true | _ => false
      if flags.any id then
        return (A :: pool).findCheck? fun L => do
          let [.list ⟨[], [], some E, _, _⟩ []] := expand G L | none
          let es ← inits.mapM fun a => match a with
            | .spread src => pool.findCheck? fun S =>
                if decide (SpreadsInto G S E) then recur Γ src S else none
            | a => recur Γ a E
          coerce G images aliases (.node ⟨Γ,t,L⟩ (.arrParts E flags) es) A
      -- Without a spread, the claimed type, or a pool type, names the tuple;
      -- each initializer is typed at its position's contract.
      return (A :: pool).findCheck? fun L => do
        let [.list T []] := expand G L | none
        if inits.length < T.required.length then none else
        if T.rest.isNone && T.required.length + T.optional.length < inits.length then none else do
        let ps ← inits.zipIdx.mapM fun (a, k) => do
          let B ← positionTy T k
          recur Γ a B
        let e := ProgramCertificates.Evidence.node ⟨Γ,t,L⟩ .arrLit ps
        (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
    | .elemAt a i =>
      -- A store read through a union of array objects splits the receiver.
      let direct := pool.findCheck? fun L => do
        let [.list T []] := expand G L | none
        let ea ← recur Γ a L
        pool.findCheck? fun I => do
          let ei ← recur Γ i I
          match expand G I with
          | [.numLit b] => do
            let k ← indexOfBits b
            match T.required[k]? with
            | some B => coerce G images aliases (.node ⟨Γ,t,B⟩ .elem [ea,ei]) A
            | none => do
              let B ← positionTy T k
              (A :: pool).findCheck? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,B ++ U⟩ (.elemOpt U) [ea,ei]
                (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
          | _ =>
            match T with
            | ⟨[], [], some E, _, _⟩ =>
              (A :: pool).findCheck? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,E ++ U⟩ (.elemAny U) [ea,ei]
                (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
            | _ => none
      -- A string's code unit at a numeric key: a string or `undefined`.
      let string := (stringOperands a).findCheck? fun S => do
        let ea ← recur Γ a S
        pool.findCheck? fun I => do
          if !decide (Answers G I .isNum true) then none else do
          let ei ← recur Γ i I
          (A :: pool).findCheck? fun T => do
            if expand G T != [.str] then none else do
            (A :: pool).findCheck? fun U =>
              if expand G U != [.undef] then none else
              coerce G images aliases (.node ⟨Γ,t,T ++ U⟩ (.elemStr T U) [ea,ei]) A
      return direct.orElse fun _ => string.orElse fun _ => do
        let .readAt _ receiver := a | none
        splitReceiver receiver
    | .setElem a i v =>
      return pool.findCheck? fun L => do
        let [.list T []] := expand G L | none
        let ea ← recur Γ a L
        pool.findCheck? fun I => do
          let [.numLit b] := expand G I | none
          let ei ← recur Γ i I
          let k ← indexOfBits b
          let B ← positionTy T k
          let ev ← recur Γ v B
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,L⟩ .setElem [ea,ei,ev]
          (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
    | .lenOf a =>
      let store := pool.findCheck? fun L => do
        let [.list _ []] := expand G L | none
        let ea ← recur Γ a L
        (A :: pool).findCheck? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .len [ea]
          (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
      -- A string's own `length`.
      return store <|> (stringOperands a).findCheck? fun S => do
        let ea ← recur Γ a S
        (A :: pool).findCheck? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .lenStr [ea]
          (checkTreeResult G images e).bind fun _ => coerce G images aliases e A
    | .merge d a b =>
      -- The accumulator and the source at their slots' types, or a pool
      -- type; the result the requested type, when every pair of their
      -- clauses merges into it, else a pool type coerced to it.
      let slot (x : Tm) := match x with | .var i => Γ[i]?.toList | _ => []
      return (slot a ++ pool).findCheck? fun R => do
        let ea ← recur Γ a R
        (slot b ++ pool).findCheck? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findCheck? fun N =>
            if ObjectMerge.MergeOk G d R S N then
              coerce G images aliases (.node ⟨Γ,t,N⟩ .merge [ea,eb]) A
            else none
    | .makeKey k a =>
      -- The key and the initializer at their slots' types, or a pool type;
      -- the result the requested type, when each clause of the key's type
      -- gives one of its clauses, else a pool type coerced to it.
      let slot (x : Tm) := match x with | .var i => Γ[i]?.toList | _ => []
      -- The type the requested result holds its one key at.
      let held := (expand G A).filterMap fun c => match c with
        | .refs [(_, T)] [] [] [] [] _ => some T
        | .dict [] [] [] [(_, T)] [] [] [] _ => some T
        | _ => none
      return (slot k ++ pool).findCheck? fun K => do
        let ek ← recur Γ k K
        (slot a ++ held.eraseDups ++ pool).findCheck? fun B => do
          let ea ← recur Γ a B
          (A :: pool).findCheck? fun N =>
            if ComputedKey.KeyedOk G K B N then
              coerce G images aliases (.node ⟨Γ,t,N⟩ .makeKey [ek,ea]) A
            else none
    | .throw a =>
      -- A throw has every type; its operand, at a type of its own.
      let types := (match a with | .var i => Γ[i]?.toList | _ => []) ++ pool
      return types.findCheck? fun B => do
        if !(decide (SourceValues G B)) then none else do
        let ea ← recur Γ a B
        some (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .throw [ea])
    | .ite (.test tag (.var i)) u e =>
      let some B := Γ[i]? | return none
      -- `length` through a view of the slot's object (`lenView`).
      if decide (t = lengthRead i) then
        if let [c] := expand G B then
          if let some (_, vs) := namedMembers c then
            if let some L := vs.lookup lengthKey then
              if PositiveRules.numIn G L then
                return coerce G images aliases (.node ⟨Γ,t,L⟩ (.lenView i) []) A
      if decide (Answers G B tag true) then
        return (recur Γ u A).map fun p => .node ⟨Γ,t,A⟩ .ifTrue [p]
      if decide (Answers G B tag false) then
        return (recur Γ e A).map fun p => .node ⟨Γ,t,A⟩ .ifFalse [p]
      -- Split only an explicit union. A singleton whose graph clause itself
      -- mixes shapes is not made smaller by repeating this rule; its answer
      -- is unknown, the test is a Boolean, and both arms are typed.
      if B.length ≤ 1 then
        return (A :: pool).findCheck? fun C => do
          if !decide ((.boolLit true) ∈ expand G C ∧ (.boolLit false) ∈ expand G C) then none else do
          let pc := ProgramCertificates.Evidence.node ⟨Γ,.test tag (.var i),C⟩ .test
            [.node ⟨Γ,.var i,B⟩ .var []]
          let pt ← recur Γ u A
          let pe ← recur Γ e A
          pure (.node ⟨Γ,t,A⟩ .ifBool [pc,pt,pe])
      return do
        let ps ← B.mapM fun a => recur (Γ.set i [a]) t A
        pure (.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    | .ite c t e =>
      let known := pool.findCheck? fun C => do
        let [.boolLit q] := expand G C | none
        let pc ← recur Γ c C
        let pb ← recur Γ (if q then t else e) A
        pure (.node ⟨Γ,.ite c t e,A⟩ (.ifKnown q) [pc,pb])
      let refined : CheckResult ι (ProgramCertificates.Evidence ι) := do
        let .var i := c | none
        let C ← Γ[i]?
        if !decide (Answers G C .isBool true) then none else do
          let T ← pool.find? fun T => decide (expand G T = [.boolLit true])
          let F ← pool.find? fun F => decide (expand G F = [.boolLit false])
          let pt ← recur (Γ.set i T) t A
          let pe ← recur (Γ.set i F) e A
          pure (.node ⟨Γ,.ite c t e,A⟩ (.ifBoolVar T F) [pt,pe])
      return known.orElse fun _ => refined.orElse fun _ => pool.findCheck? fun C => do
        if !decide (Answers G C .isBool true) then none else do
          let pc ← recur Γ c C
          let pt ← recur Γ t A
          let pe ← recur Γ e A
          pure (.node ⟨Γ,.ite c t e,A⟩ .ifBool [pc,pt,pe])
    | _ => return none

/-- Gather graph labels, every operand of their clauses and supplied union
types. Hints may add intermediate types; they cannot change claims or bypass
evidence checking. -/
@[nospecialize] def vocabulary [DecidableEq ι] [Instantiates ι] (G : NormalGraph ι) (labels : List ι)
    (claims : List (PointClaim ι)) (hints : List (Ty ι)) : List (Ty ι) :=
  ([] :: (labels.map fun i => [i]) ++ hints ++
    claims.flatMap (fun c => c.type :: c.context) ++
    labels.flatMap (fun i => (G i).flatMap Clause.operands)).eraseDups

inductive Failure (ι : Type) where
  | claimCount
  | expression (label : Nat)
  | edge (source : Nat) (destination : Nat) (edgeIndex : Nat)
  | rejected
  | exhaustedExpression (label : Nat) (stop : Exhaustion ι)
  | exhaustedEdge (source destination edgeIndex : Nat) (stop : Exhaustion ι)
  deriving DecidableEq, Repr

/-- Ordinary and observed edges share slot selection and coverage search. The
observation comes from graph dispatch, never from supplied point annotations. -/
@[nospecialize] def edgeUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (target : Target)
    (observed : Option (Nat × BranchRefinement.Observation) := none)
    (fields : List (Nat × PropKey) := []) (optionals : List (Nat × PropKey) := []) :
    CheckResult ι (EdgeEvidence ι) := do
  let c ← claims[target.label]?
  if let some (tested, o) := observed then
    if Γ[tested]?.isNone then failure
    -- An observation the tested type rules out: the edge is never taken.
    if (Γ[tested]?).any (BranchRefinement.impossible G · o) then
      return List.replicate c.context.length {}
  if let some slots := target.mapping then
    if slots.length != c.context.length then failure
  (List.range c.context.length).mapM fun i => do
    let A ← Γ[slot target.mapping i]?
    let B ← c.context[i]?
    match observed with
    | some (tested, o) =>
      if slot target.mapping i == tested then
        match o with
        | .boolean q =>
          if BranchRefinement.booleanMember G B q then pure {} else failure
        | .tag t q =>
          if BranchRefinement.tagMember G B t q then pure {}
          else (subtypeUsing G images (BranchRefinement.tagSlice G A t q) B).orElse fun _ =>
            -- A passed `in` test: the key is present from then on.
            if BranchRefinement.presentKey t q (BranchRefinement.promotes G (BranchRefinement.tagSlice G A t q) B)
            then some {}
            -- A passed `Array.isArray`: a record's member is a built-in array.
            else if t == .isArray && q && BranchRefinement.arraySlice G A B then some {}
            -- A type parameter's value: its meet with what the test admits.
            else if BranchRefinement.meetSlice G A B t q then some {}
            else none
      else (subtypeUsing G images A B).orElse (fun _ => match o with
        -- An object the tested value was read from keeps the labels whose
        -- field admits the observation.
        | .tag t q => (fields ++ optionals).findCheck? fun (k, f) =>
            if k == slot target.mapping i then subtypeUsing G images (BranchRefinement.fieldSlice G A f t q) B
            else none
        | .boolean _ => none) |>.orElse fun _ =>
        -- One read through an optional key, where the observation rules out
        -- the `undefined` an absent key reads: the key is present.
        if BranchRefinement.excludesUndef o && optionals.any (fun (k, f) =>
            k == slot target.mapping i && BranchRefinement.promotes G A B f)
        then some {} else none
    | none => subtypeUsing G images A B


/-- Select effect evidence without changing the requested sequent. A precise
read/value rule may succeed when ordinary derivation search cannot. -/
@[nospecialize] def expressionEffectUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel : Nat) (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (suggestions : List (Sequent ι)) (known : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (aliases : List (ι × ι) := [])
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    CheckResult ι (Evidence ι × HeapExpressionRules.StepEvidence ι × HeapKnowledge.Knowledge) := Id.run do
  -- A node's derivation is first sought among its own types: its claim and
  -- its context's, which are its operands' claims. The pool is consulted
  -- only where those leave a choice open.
  let own := (j.type :: j.context).eraseDups
  let ordinary := (CheckResult.fromOption (known.find? fun e => claim e == j)).orElse fun _ =>
    (expressionWithUsing G images own suggestions aliases fuel j.context j.term j.type).orElse fun _ =>
      expressionWithUsing G images pool suggestions aliases fuel j.context j.term j.type
  let mut incomplete := ordinary.exhaustion
  let mut choices : List (HeapExpressionRules.StepEvidence ι) := []
  match j.term with
  | .var i =>
    if let some R := HeapExpressionRules.valuesAt G j.context k i then
      choices := [.knownValue i R]
  | .readAt fld (.var i) =>
    choices := (k.cells.filter fun f => f.slot == i && f.field == fld).map
      fun f => .observedRead i f.contents
    -- Read at the fixed contract once, then try each justified exclusion.
    if let some Ref := j.context[i]? then
      let tags := [Tag.isUndef, .isNul, .isNullish].filter fun tag =>
        k.cells.any (fun f => f.slot == i && f.field == fld && f.contents.all (·.excludes tag))
      if HeapExpressionRules.fieldOperand (expand G Ref) fld && !tags.isEmpty then
        if let [.refs fs _ _ _ _ _] := expand G Ref then
          if let some C := fs.lookup fld then
            let searched := expressionWithUsing G images (C :: own) suggestions aliases fuel j.context j.term C
            incomplete := incomplete <|> searched.exhaustion
            if let some e := searched.value then
              for tag in tags do
                let compared := subtypeUsing G images (BranchRefinement.tagSlice G C tag false) j.type
                incomplete := incomplete <|> compared.exhaustion
                if let some p := compared.value then choices := choices ++ [.slicedRead tag i e p]
  | _ => pure ()
  if let some e := ordinary.value then
    match j.term with
    | .readAt fld (.var i) =>
      if let some Ref := j.context[i]? then
        if HeapExpressionRules.fieldOperand (expand G Ref) fld ||
            HeapExpressionRules.optionalOperand (expand G Ref) fld then
          choices := choices ++ [.typedRead i e]
    | .makeAt .. | .merge .. | .makeKey .. | .arrLit .. =>
      choices := choices ++ [.allocated e]
    | .writeAt _ (.var i) (.var v) =>
      choices := choices ++ [.written i v (HeapExpressionRules.valuesAt G j.context k v) e]
    | _ => pure ()
    choices := choices ++ [.created e,.pure e,.reading e,.ordinary e]
  for effect in choices do
    let checked := checker.run j k effect codes
    incomplete := incomplete <|> checked.exhaustion
    if let some out := checked.value then
      -- Effect evidence validates this header itself; an ordinary derivation
      -- is not required for the precise read/value alternatives.
      return some (ordinary.value.getD (.node j .var []),effect,out)
  return ⟨none, incomplete⟩

/-- All predecessor edges come from executable continuations. -/
def successors : Continuation → List Target
  | .ret => []
  | .bind t | .effect t => [t]
  | .branch y n | .branchBind y n | .tagBind _ y n => [y,n]

@[nospecialize] def edgeKnowledge (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge) (cont : Continuation) (index : Nat) :
    HeapKnowledge.Knowledge :=
  match cont with
  | .effect _ | .branch _ _ => HeapKnowledge.dropResult k
  | .branchBind _ _ => HeapKnowledge.observeTyped G Γ k 0 (.boolean (index == 0))
  | .tagBind t _ _ => HeapKnowledge.observeTyped G Γ k 0 (.tag t (index == 0))
  | _ => k

@[nospecialize] private def produceNode [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel l : Nat) (node : Node) (claims : List (PointClaim ι))
    (k : HeapKnowledge.Knowledge) (suggestions : List (Sequent ι)) (known : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (aliases : List (ι × ι) := [])
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    Except (Failure ι) (NodeEvidence ι) := do
  let some c := claims[l]? | throw .claimCount
  let searched := expressionEffectUsing G images pool fuel ⟨c.context,node.expression,c.type⟩ k suggestions known codes
    aliases checker
  let some (e,effect,out) := searched.value | throw (match searched.exhaustion with
    | some stop => .exhaustedExpression l stop
    | none => .expression l)
  let target := fun Γ t index =>
    let searched := edgeUsing G images claims Γ t
    match searched.value with
    | some p => Except.ok p
    | none => Except.error (match searched.exhaustion with
      | some stop => Failure.exhaustedEdge l t.label index stop
      | none => Failure.edge l t.label index)
  let branchTarget := fun Γ o t index =>
    let searched := edgeUsing G images claims Γ t (some (0, o)) (readFields out 0) (optionalFields out 0)
    match searched.value with
    | some p => Except.ok p
    | none => Except.error (match searched.exhaustion with
      | some stop => Failure.exhaustedEdge l t.label index stop
      | none => Failure.edge l t.label index)
  let ps ← (match node.continuation with
    | .ret => pure []
    | .bind t => (target (c.type :: c.context) t 0).map (fun p => [p])
    | .effect t => (target c.context t 0).map (fun p => [p])
    | .branch y n => (target c.context y 0).bind (fun py =>
        (target c.context n 1).map (fun pn => [py,pn]))
    | .branchBind y n => (branchTarget (c.type :: c.context) (.boolean true) y 0).bind (fun py =>
        (branchTarget (c.type :: c.context) (.boolean false) n 1).map (fun pn => [py,pn]))
    | .tagBind t y n => (branchTarget (c.type :: c.context) (.tag t true) y 0).bind (fun py =>
        (branchTarget (c.type :: c.context) (.tag t false) n 1).map (fun pn => [py,pn])) : Except (Failure ι) (List (EdgeEvidence ι)))
  -- A handler receives the thrown value at a type admitting every value: the
  -- type its target states for the slot it lands in, else one from the pool.
  let hd ← (match node.handler with
    | none => pure none
    | some t =>
      let landing := ((claims[t.label]?).toList.flatMap fun tc =>
        (List.range tc.context.length).filterMap fun i =>
          if PointClaims.slot t.mapping i == 0 then tc.context[i]? else none)
      let searched := (landing ++ pool).findCheck? fun T =>
        if ControlFlow.admitsAll G T then (edgeUsing G images claims (T :: c.context) t).map (T, ·) else none
      match searched.value with
      | some x => pure (some x)
      | none => throw (match searched.exhaustion with
        | some stop => .exhaustedEdge l t.label (successors node.continuation).length stop
        | none => .edge l t.label (successors node.continuation).length)
    : Except (Failure ι) (Option (Ty ι × EdgeEvidence ι)))
  return {expression := e, edges := ps, knowledge := k, effect := some effect, output := out, handler := hd}

/-- Propagate established postconditions along single-predecessor paths. Entry
starts empty; source cuts use exactly their supplied requirements, even when
empty. Other merge points use supplied requirements. A node is checked once
when its unique predecessor is available; this is dependency scheduling, not invariant iteration.
Every edge is still checked by the independent consumer. -/
@[nospecialize] def produceRawUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel : Nat) (P : Program) (claims : List (PointClaim ι))
    (suggestions : List (Sequent ι) := []) (known : List (Evidence ι) := []) (start : Nat := 0)
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codes : CodeEntry ι → Bool := fun _ => false) (aliases : List (ι × ι) := [])
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    Except (Failure ι) (ControlFlow.Certificate ι) := do
  if P.length != claims.length then throw .claimCount
  let incoming := (List.range P.length).map fun target =>
    P.zipIdx.flatMap fun (node,l) =>
      (successors node.continuation).zipIdx.filterMap fun (t,index) =>
        if t.label == target then some (l,index,t) else none
  let mut table : List (Option (NodeEvidence ι)) := List.replicate P.length none
  -- A merge waits for its predecessors while some pass still makes progress;
  -- once none does, the merges still waiting (a cycle through no cut) take
  -- their stated requirements alone, as every merge did before.
  let mut force := false
  for _ in List.range (2 * P.length + 2) do
    let mut progress := false
    for l in List.range P.length do
      if ((table[l]?).getD none).isSome then continue
      let some node := P[l]? | throw .claimCount
      let some c := claims[l]? | throw .claimCount
      let required := (requirements.lookup l).getD ⟨[],[],[]⟩
      let mut k := required
      if l != start && !cuts.contains l then
        match incoming[l]? with
        | some [(pred,index,target)] =>
          let some previous := (table[pred]?).getD none | continue
          let some source := P[pred]? | throw .claimCount
          k := HeapKnowledge.project (edgeKnowledge G ((claim previous.expression).type :: (claim previous.expression).context) previous.output source.continuation index)
            target.mapping c.context.length
        | some preds =>
          -- A merge that is not a cut states no requirement of its own; it
          -- keeps what every predecessor establishes, once all are available.
          -- Cycles pass through cuts, so waiting here cannot deadlock.
          let mut projections : List HeapKnowledge.Knowledge := []
          let mut ready := true
          for (pred,index,target) in preds do
            match (table[pred]?).getD none, P[pred]? with
            | some previous, some source =>
              projections := projections ++ [HeapKnowledge.project
                (edgeKnowledge G ((claim previous.expression).type :: (claim previous.expression).context) previous.output source.continuation index) target.mapping c.context.length]
            | _, _ => ready := false
          if !ready && !force then continue
          if ready then k := HeapKnowledge.meet projections
        | none => pure ()
      k := ⟨(k.cells ++ required.cells).eraseDups,(k.values ++ required.values).eraseDups,
        (k.links ++ required.links).eraseDups⟩
      let evidence ← produceNode G images pool fuel l node claims k suggestions known codes aliases checker
      table := table.set l (some evidence)
      progress := true
    if !progress then
      if force then break else force := true
    else force := false
  table.mapM fun c => match c with
    | some e => pure e
    | none => throw .rejected

/-- Recover a located failed edge from the completed candidate. This includes
heap entailment; it is not limited to ordinary subtype proof construction. -/
@[nospecialize] private def failedEdge (G : NormalGraph ι) (P : Program)
    (C : ControlFlow.Certificate ι) : Option (Failure ι) := Id.run do
  for (node,l) in P.zipIdx do
    let some c := C[l]? | return some .claimCount
    for (target,index) in (successors node.continuation).zipIdx do
      let facts := edgeKnowledge G ((claim c.expression).type :: (claim c.expression).context) c.output node.continuation index
      let some destination := C[target.label]? | return some .claimCount
      if !HeapKnowledge.check facts destination.knowledge target.mapping then
        return some (.edge l target.label index)
  return none

@[nospecialize] def produceUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (labels : List ι)
    (fuel : Nat) (R : Ty ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (hints : List (Ty ι) := []) (inputs : List (Ty ι) := [])
    (suggestions : List (Sequent ι) := []) (known : List (ProgramCertificates.Evidence ι) := [])
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (aliases : List (ι × ι) := []) :
    Except (Failure ι) (ControlFlow.Certificate ι) :=
  match produceRawUsing G images (vocabulary G labels claims (inputs ++ hints)) fuel P claims suggestions known start requirements cuts codes
      aliases checker with
  | .error e => .error e
  | .ok C =>
    let checked := acceptResult G images R P claims C start inputs codes checker
    if checked.accepted then .ok C
    else match checked.exhaustion with
      | some stop => .error (.exhaustedExpression (stop.nodeLabel.getD start) stop)
      | none => .error ((failedEdge G P C).getD .rejected)

#print axioms comparisonUsing_sound
#print axioms accepted_from_inputs
end Verification.CertificateProducer
