import Verification.Programs.ControlFlow
import Std.Data.HashMap

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
@[nospecialize] def acceptResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : ControlFlow.Goal ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : CheckResult ι Unit :=
  (CheckResult.ofBool (decide (C.map signature = claims))).bind fun _ =>
  checkEntryResult (checker := checker) G images R P C start inputs codes

@[nospecialize] def acceptUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : ControlFlow.Goal ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι) := []) (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) : Bool :=
  (acceptResult (checker := checker) G images R P claims C start inputs codes).accepted

theorem acceptUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (R : ControlFlow.Goal ι) (P : Program)
    (claims : List (PointClaim ι)) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (Ty ι)) (codes : CodeEntry ι → Bool)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    acceptUsing (checker := checker) G images R P claims C start inputs codes = (
  decide (C.map signature = claims) && checkEntryUsing (checker := checker) G images R P C start inputs codes
  ) := by
  simp only [acceptUsing, acceptResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, checkEntryUsing]

theorem accepted_from_inputs [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {checker : HeapExpressionRules.Checker G images} {R : Ty ι} {P claims C start inputs}
    {codes : CodeEntry ι → Bool} (hc : acceptUsing (checker := checker) G images (.plain R) P claims C start inputs codes = true) (n W h ρ)
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
      -- proved equal. The label's image is proposed as the target less the
      -- other labels' images, and, where the instance shares those labels
      -- (a result `undefined | T` at `T = undefined | number`), as the whole
      -- target: each operand's alternatives, the patches their products.
      let respell (P Q : List ι) : List (InstTable ι) :=
        match tyImg table κ₀ P with
        | some img =>
          if PositiveRules.sameLabels img Q then [[]] else
          let open_ := if P.length == 1 then P
            else P.filter fun l => !((entryImg table κ₀ l).getD []).all (· ∈ Q)
          match open_ with
          | [l] =>
            let others := (P.filter (· != l)).flatMap fun m => (entryImg table κ₀ m).getD []
            let rest := Q.filter (!others.contains ·)
            if rest == Q then [[(l, κ₀, Q)]] else [[(l, κ₀, rest)], [(l, κ₀, Q)]]
          | _ => [[]]
        | none => [[]]
      let product (operands : List (List ι × List ι)) : List (InstTable ι) :=
        operands.foldl (fun patches (P, Q) =>
          patches.flatMap fun patch => (respell P Q).map (patch ++ ·)) [[]]
      let fixedPatch (p q : Arrow (List ι)) : List (InstTable ι) :=
        product <| if receiverUniverse G p.receiver q.receiver then
          (p.result :: p.arguments).zip (q.result :: q.arguments)
        else (p.receiver :: p.result :: p.arguments).zip (q.receiver :: q.result :: q.arguments)
      let restPatch (p q : RestArrow (List ι)) : List (InstTable ι) :=
        product <| if receiverUniverse G p.receiver q.receiver then
          (p.arguments.2 :: p.result :: p.arguments.1).zip (q.arguments.2 :: q.result :: q.arguments.1)
        else (p.receiver :: p.arguments.2 :: p.result :: p.arguments.1).zip
          (q.receiver :: q.arguments.2 :: q.result :: q.arguments.1)
      -- Each target chooses one overload. Images of an unused overload need
      -- not equal that target's operands; the checker validates each choice.
      let patches := L.foldl (fun patches q => patches.flatMap fun patch =>
        s.signatures.flatMap fun p =>
          if p.arguments.length == q.arguments.length && p.effect.covers q.effect then
            (fixedPatch p q).map (patch ++ ·) else []) ([[]] : List (InstTable ι))
      let patches := M.foldl (fun patches q => patches.flatMap fun patch =>
        s.variadic.flatMap fun p =>
          if p.arguments.1.length == q.arguments.1.length && p.effect.covers q.effect then
            (restPatch p q).map (patch ++ ·) else []) patches
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
      | .refs _ _ _ _ ns _ _ | .dict _ _ _ _ _ ns _ _ _ => ns
      | _ => []
    (expand G A).flatMap fun c => match c with
      | .refs a bs vs _ _ _ _ =>
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
@[nospecialize] def subtypeSearch [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) : CheckResult ι (PositiveCertificates.SubtypeChoices ι) :=
  CheckResult.fromComparison images.budget.rounds A B (comparisonUsing G images A B)

/-! ### Search with answered requests

The subtype requests one search context answered, by source and target. A
context is one graph, one image check and the label type's class
dictionaries: the caller that holds them creates the answers and passes them
only to searches in that context, so a stored answer is `subtypeSearch`'s
for the same arguments. A search step returns its result and the answers it
grew; a failed step keeps the answers its attempts found. -/

/-- Answered subtype requests, each `subtypeSearch`'s whole result, an
exhaustion included. -/
abbrev Answered (ι : Type) [BEq ι] [Hashable ι] :=
  Std.HashMap (Ty ι × Ty ι) (CheckResult ι (PositiveCertificates.SubtypeChoices ι))

/-- A search step threading the answered requests: a `CheckResult`
computation whose answers persist across its failed alternatives. -/
def SearchM (ι : Type) [BEq ι] [Hashable ι] (α : Type) : Type :=
  Answered ι → CheckResult ι α × Answered ι

namespace SearchM
variable {ι : Type} [BEq ι] [Hashable ι]

@[inline] def lift (r : CheckResult ι α) : SearchM ι α := fun s => (r, s)

/-- As `CheckResult.bind`, the answers threaded. -/
@[nospecialize] def bind (x : SearchM ι α) (f : α → SearchM ι β) : SearchM ι β := fun s =>
  let (r, s) := x s
  match r.value with
  | none => (⟨none, r.exhaustion⟩, s)
  | some a =>
    let (t, s) := f a s
    (if t.value.isSome then t else { t with exhaustion := r.exhaustion <|> t.exhaustion }, s)

instance : Monad (SearchM ι) where
  pure a := lift (pure a)
  bind := bind

/-- As `CheckResult.orElse`, the answers of the failed attempt kept. -/
@[nospecialize] def orElse (x : SearchM ι α) (next : Unit → SearchM ι α) : SearchM ι α := fun s =>
  let (r, s) := x s
  match r.value with
  | some a => (⟨some a, none⟩, s)
  | none =>
    let (t, s) := next () s
    (if t.value.isSome then { t with exhaustion := none }
     else { t with exhaustion := r.exhaustion <|> t.exhaustion }, s)

instance : Alternative (SearchM ι) where
  failure := lift failure
  orElse := orElse

instance : MonadLift Option (SearchM ι) where
  monadLift o := lift (CheckResult.fromOption o)

instance : MonadLift (CheckResult ι) (SearchM ι) where
  monadLift := lift

instance : Coe (CheckResult ι α) (SearchM ι α) := ⟨lift⟩

instance : Coe (Option α) (SearchM ι α) := ⟨fun o => lift (CheckResult.fromOption o)⟩

/-- As `CheckResult.map`. -/
@[nospecialize] def map (f : α → β) (x : SearchM ι α) : SearchM ι β := fun s =>
  let (r, s) := x s
  (r.map f, s)

/-- The whole result as a value, the answers kept: for a caller that reads
its exhaustion. -/
@[nospecialize] def result (x : SearchM ι α) : SearchM ι (CheckResult ι α) := fun s =>
  let (r, s) := x s
  (pure r, s)

/-- `x`'s value where it has one, else `y`, `x`'s exhaustion dropped, as an
`if let some e := x then e else y` over pure results. -/
@[nospecialize] def firstOr (x : SearchM ι α) (y : SearchM ι α) : SearchM ι α := fun s =>
  let (r, s) := x s
  match r.value with
  | some a => (pure a, s)
  | none => y s

/-- A step whose result is read as a value of a state computation. -/
@[inline] def toState (x : SearchM ι α) : StateM (Answered ι) (CheckResult ι α) := fun s => x s

/-- A state computation as a step. -/
@[inline] def ofState (x : StateM (Answered ι) (CheckResult ι α)) : SearchM ι α := fun s => x s

end SearchM

/-- As `List.findCheck?`, the answers threaded through the candidates. -/
@[nospecialize] def _root_.List.findSearch? {ι : Type} [BEq ι] [Hashable ι] (xs : List β)
    (f : β → SearchM ι α) : SearchM ι α :=
  match xs with
  | [] => failure
  | x :: xs => (f x).orElse fun _ => xs.findSearch? f

/-- Subtype search as the producer asks it: an answered request is answered
again from its first answer, `subtypeSearch`'s for the same graph, image
check, source and target. Untrusted: the consumer checks every result. -/
@[nospecialize] def subtypeUsing [DecidableEq ι] [Hashable ι] [Instantiates ι]
    (G : NormalGraph ι) (images : InstanceImageCheck G) (A B : Ty ι) :
    SearchM ι (PositiveCertificates.SubtypeChoices ι) := fun s =>
  match s.get? (A, B) with
  | some r => (r, s)
  | none =>
    let r := subtypeSearch G images A B
    (r, s.insert (A, B) r)

/-- Proofs that the member of key `k` on `O` covers each signature of `F`:
for each fixed one, a member signature of as many parameters, each claimed
parameter within the member's and the member's result within the claimed;
for each variadic one, a member's of as many fixed parameters, likewise, the
claimed rest within the member's too. -/
@[nospecialize] def memberProofsUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (O : Ty ι) (k : PropKey)
    (F : Ty ι) : SearchM ι (List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι) ×
      List (List (PositiveCertificates.SubtypeChoices ι) × PositiveCertificates.SubtypeChoices ι × PositiveCertificates.SubtypeChoices ι) ×
      List (PositiveCertificates.SubtypeChoices ι)) := do
  let m ← ProgramTyping.memberOf G O k
  -- At a quantified signature, the member bound to its host is the scheme.
  if expand G F = [] && m.schemes.contains F then return ([], [], [])
  let [.arrs L S] := expand G F | none
  let calls ← L.mapM fun q => m.calls.findSearch? fun c => do
    if q.arguments.length != c.arguments.length || !(c.effect.drop 0).covers q.effect then none
    let ps ← (q.arguments.zip c.arguments).mapM fun (D, C) => subtypeUsing G images D C
    let pr ← subtypeUsing G images c.result q.result
    pure (ps, pr)
  let rests ← S.mapM fun s => m.rests.findSearch? fun c => do
    if s.arguments.1.length != c.arguments.1.length || !(c.effect.drop 0).covers s.effect then none
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
    SearchM ι (ProgramCertificates.Evidence ι) := do
  if (claim e).type = A then return e
  let p ← (subtypeUsing G images (claim e).type A).orElse fun _ =>
    if aliases.isEmpty then none else
      subtypeUsing G images (ProgramCertificates.renameTy aliases (claim e).type)
        (ProgramCertificates.renameTy aliases A)
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

/-- A subsumption step to `A` by a comparison already made: `p` compares
`e`'s type to `A`, as `coerce` would compare them again. -/
def coerceBy [DecidableEq ι] (p : PositiveCertificates.SubtypeChoices ι) (e : ProgramCertificates.Evidence ι) (A : Ty ι) :
    ProgramCertificates.Evidence ι :=
  if (claim e).type = A then e else .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

instance [DecidableEq ι] (G : NormalGraph ι) (B : Ty ι) (tag : Tag) (q : Bool) :
    Decidable (Answers G B tag q) := by unfold Answers; infer_instance

/-- The arms a chain of tests decided by the context selects: each step a
test of a slot whose type answers it, with the arm taken. The final term is
the first that is no such test. A chain costs one search step, however long:
each of its steps is decided, so nothing is searched. -/
def decidedChain [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) : Tm → List (Tm × Bool) × Tm
  | t@(.ite (.test tag (.var i)) u e) =>
    match Γ[i]? with
    | some B =>
      if decide (Answers G B tag true) then
        let (steps, last) := decidedChain G Γ u
        ((t, true) :: steps, last)
      else if decide (Answers G B tag false) then
        let (steps, last) := decidedChain G Γ e
        ((t, false) :: steps, last)
      else ([], t)
    | none => ([], t)
  | t => ([], t)

/-- Search ordinary typing rules. Every recursive expression request decreases
search fuel, including implicit let typing. Suggestions only prioritize candidate
types; every premise is proved in the actual context, even when the suggestion
came from a different context. No execution budget is inspected. -/
@[nospecialize] def expressionWithUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (suggestions : List (Sequent ι)) (aliases : List (ι × ι)) :
    Nat → List (Ty ι) → Tm → Ty ι → SearchM ι (ProgramCertificates.Evidence ι)
  | 0, _, _, _ => failure
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
      let B := ProgramTyping.members G (← Γ[i]?)
      if B.length ≤ 1 then none else do
        let ps ← B.mapM fun b => recur (Γ.set i [b]) t A
        pure (ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    -- The types an operand may be read at as a string: a slot's own, then
    -- the pool's, each all strings.
    let stringOperands := fun (a : Tm) =>
      ((match a with | .var i => (Γ[i]?).toList | _ => []) ++ pool).filter fun S =>
        decide (Answers G S .isStr true)
    match t with
    | .var i => return (SearchM.lift (CheckResult.fromOption Γ[i]?)).bind fun B => coerce G images aliases (leaf B .var) A
    | .nul | .undef | .tru | .fls =>
      let r := match t with | .nul => Rule.nul | .undef => .undef | .tru => .tru | _ => .fls
      return (A :: pool).findSearch? fun B =>
        let r := if expand G B = [.boolLit true] && t == .tru then Rule.truLit
          else if expand G B = [.boolLit false] && t == .fls then Rule.flsLit else r
        (SearchM.lift (checkTreeResult G images (leaf B r))).bind fun _ => coerce G images aliases (leaf B r) A
    -- A number has one rule: its own singleton. Reaching `number`, or any
    -- union above it, is the coercion's job, exactly as for a boolean literal.
    | .num _ =>
      -- Its own singleton where the claim names one, the family where it does
      -- not: a literal claimed at `number` has no singleton label to coerce
      -- from, exactly as a Boolean claimed at `boolean` has none.
      return (A :: pool).findSearch? fun B =>
        if checkTreeUsing G images (leaf B .numLit) then coerce G images aliases (leaf B .numLit) A
        else if checkTreeUsing G images (leaf B .num) then coerce G images aliases (leaf B .num) A
        else none
    | .str _ =>
      return (A :: pool).findSearch? fun B =>
        if checkTreeUsing G images (leaf B .strLit) then coerce G images aliases (leaf B .strLit) A
        else if checkTreeUsing G images (leaf B .str) then coerce G images aliases (leaf B .str) A
        else none
    | .bigint _ =>
      return (A :: pool).findSearch? fun B =>
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
      return (A :: pool).findSearch? fun F => do
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
      return (own ++ pool).eraseDups.findSearch? fun F => do
        let [.ctors L S _ _ _] := expand G F | none
        let flags := args.map fun a => match a with | .spread _ => true | _ => false
        let candidates : List (CallEffects.MethodArrow (Ty ι) ⊕ CallEffects.MethodRestArrow (Ty ι)) :=
          (if flags.any id then [] else L.map .inl) ++ S.map .inr
        candidates.findSearch? fun c => match c with
        | .inl p => do
          if args.length > p.arguments.length || !p.effect.plain then none else do
          let sub ← subtypeUsing G images p.result A
          let ef ← recur Γ f F
          let eas ← (args.zip p.arguments).mapM fun (a,D) => recur Γ a D
          let eus ← (p.arguments.drop args.length).mapM fun D => recur Γ .undef D
          pure (coerceBy sub (.node ⟨Γ,t,p.result⟩ (.construct p.effect) (ef :: eas ++ eus)) A)
        -- A variadic construct signature: the fixed actuals at its
        -- parameters, then the further parts as a variadic call's.
        | .inr ⟨(), (Ps, P), B, effect⟩ => do
          let k := Ps.length
          if args.length < k || (flags.take k).any id || !effect.plain then none else do
          let sub ← subtypeUsing G images B A
          let ef ← recur Γ f F
          let eas ← (args.zip Ps).mapM fun (a,D) => recur Γ a D
          let parts := args.drop k
          let partFlags := flags.drop k
          let eps ← if partFlags.any id then do
              let E ← restElem G P
              parts.mapM fun a => match a with
                | .spread s => pool.findSearch? fun S =>
                    if decide (SpreadsInto G S E) then recur Γ s S else none
                | a => recur Γ a E
            else do
              let [.pack T []] := expand G P | none
              parts.zipIdx.mapM fun (a, i) => do recur Γ a (← positionTy T i)
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩ (.constructRest k partFlags P) (ef :: eas ++ eps)
          (checkTreeResult G images e).map fun _ => coerceBy sub e A
    -- `.bind`'s forwarding descriptor: a leaf whose checker reads the saved
    -- slots from the context; the claimed type, or a pool type, is its result.
    | .makeAt (.bound (.var _) (.var _) _) [] [] =>
      return (A :: pool).findSearch? fun F =>
        if checkTreeUsing G images (leaf F .bindE) then coerce G images aliases (leaf F .bindE) A
        else if checkTreeUsing G images (leaf F .bindRestE) then coerce G images aliases (leaf F .bindRestE) A
        else none
    -- A member bound to its host: a leaf whose checker reads the object's type
    -- from the context; the claimed type, or a pool type, is its result.
    | .letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var _) []) [] []) =>
      let schemes := match Γ[i]? with
        | some O => ProgramTyping.memberSchemes G O k
        | none => []
      return (A :: schemes ++ pool).findSearch? fun F => do
        let (ps, rs, vs) ← memberProofsUsing G images (← Γ[i]?) k F
        (SearchM.lift (checkTreeResult G images (leaf F (.bindMember ps rs vs)))).bind fun _ =>
          coerce G images aliases (leaf F (.bindMember ps rs vs)) A
    | .letE a b =>
      let exactTypes := suggestions.reverse.filterMap fun j =>
        if j.context == Γ && j.term == a then some j.type else none
      let termTypes := suggestions.reverse.filterMap fun j =>
        if j.term == a then some j.type else none
      let variableType := match a with | .var i => (Γ[i]?).toList | _ => []
      let preferred := variableType ++ exactTypes ++ termTypes
      return (preferred ++ pool).eraseDups.findSearch? (fun B => do
        let ea ← recur Γ a B
        let eb ← recur (B :: Γ) b A
        return ProgramCertificates.Evidence.node ⟨Γ,t,A⟩ .letE [ea,eb])
    | .invoke f recv args =>
      -- A callee read from a slot is tried first at the slot's own type, a
      -- fixed signature of it before its variadic ones (a call of a guard at
      -- its promise signature, beside one taking further arguments), and
      -- those before any variadic one of the pool: coercing it to
      -- each of those first, where its own type is fixed, fails at the cost
      -- of a table over the pool each time. Order only; every premise is
      -- still proved.
      let own := match f with | .var i => (Γ[i]?).toList | _ => []
      -- A variadic callee: the receiver at the signature's receiver, the fixed
      -- actuals at its parameters, then the further parts: with a spread, each
      -- at the element rest's element, or a spread of a pool store type whose
      -- elements are; without one, each at its position in the rest's tuple.
      let variadic := fun (candidates : List (Ty ι)) => candidates.findSearch? fun F => do
        (restSigs G F).findSearch? fun ⟨Rt, (Ps, P), B, effect⟩ => do
          -- Fixed actuals first; a shorter call omits trailing fixed positions,
          -- each proving `undefined`, and writes no further part.
          let k := min args.length Ps.length
          let omitted := Ps.drop k
          let parts := args.drop k
          if !omitted.isEmpty && !parts.isEmpty then none else do
          let sub ← subtypeUsing G images B A
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
              let ea ← ((Γ ++ pool).filter fun C => decide (PackedBy G C q)).findSearch? fun C => recur Γ a C
              let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩
                (.callPacked effect k q P) (ef :: er :: eas ++ [ea])
              return ← (checkTreeResult G images e).map fun _ => coerceBy sub e A
          let eps ← if flags.any id then do
              let E ← restElem G P
              parts.mapM fun a => match a with
                | .spread s => pool.findSearch? fun S =>
                    if decide (SpreadsInto G S E) then recur Γ s S else none
                | a => recur Γ a E
            else do
              let [.pack T []] := expand G P | none
              parts.zipIdx.mapM fun (a, i) => do recur Γ a (← positionTy T i)
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,B⟩
            (.callRest effect k omitted.length flags P) (ef :: er :: eas ++ eus ++ eps)
          (checkTreeResult G images e).map fun _ => coerceBy sub e A
      let direct := fun (candidates : List (Ty ι)) => candidates.findSearch? fun F => do
        let (L,r) ← match expand G F with
          | [.arrs L _] => some (L,Rule.app)
          | [.callable _ _ L _] => some (L,Rule.callCallable)
          | _ => none
        L.findSearch? fun p => do
          -- Require every operand before searching the premises. A signature
          -- with more positions than the call writes is usable when each
          -- remaining contract admits `undefined`, the value bound there.
          if args.length > p.arguments.length then none else do
            let omitted := p.arguments.drop args.length
            let sub ← subtypeUsing G images p.result A
            let ef ← recur Γ f F
            let er ← recur Γ recv p.receiver
            let eas ← (args.zip p.arguments).mapM fun (a,D) => recur Γ a D
            let eus ← omitted.mapM fun D => recur Γ .undef D
            pure (coerceBy sub (.node ⟨Γ,t,p.result⟩ (r p.effect) (ef :: er :: eas ++ eus)) A)
      -- A callee or, for a method dispatched on its object, the receiver.
      return (direct own <|> variadic own <|> variadic pool <|> direct pool).firstOr
        (splitReceiver f <|> splitReceiver recv)
    | .makeAt .absent ns inits =>
      return (A :: pool).findSearch? fun R => do
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
      return (A :: pool).findSearch? fun R => do
        let [.dict _ [] _ ix _ _ _ _ _] := expand G R | none
        ix.findSearch? fun (Kx, E) =>
        [IndexKeys.strings, .numeric, .symbols].findSearch? fun KK => do
          if !KK.within Kx then none else do
          (A :: pool).findSearch? fun K => do
            if expand G K != [keyClause KK] then none else do
            (A :: pool).findSearch? fun U => do
              if expand G U != [.undef] then none else do
              let B := E ++ U
              let sub ← subtypeUsing G images B A
              let ea ← recur Γ a R
              let ek ← recur Γ key K
              pure (coerceBy sub (.node ⟨Γ,t,B⟩ (.indexDict Kx KK E U) [ea, ek]) A)
    | .readAt f a =>
      let direct := pool.findSearch? fun R => do
        -- An invariant field reads at its contract; a view field at its bound;
        -- an optional field, writable or readonly, at its type or `undefined`; a key a
        -- bound does not admit at the prototype's field or view.
        let (B,r) ← (show Option (Ty ι × Rule ι) from match expand G R with
          | [.refs fs [] vs os _ ks _] =>
            (fs.lookup f).map (·,Rule.read) <|>
              ((vs.lookup f).bind fun B => if f == lengthKey && !lengthExcluded G B then none else some (B, Rule.readView)) <|>
              (((os.find? (·.key == f)).map (·.type)).bind fun E => pool.findSome? fun U =>
                if expand G U == [.undef] then some (E ++ U, Rule.readOptional E U) else none) <|>
              (if ks.any (fun K => !K.admits f) then
                ((fs ++ vs).lookup CallArguments.protoField).bind fun P =>
                  match expand G P with
                  | [.refs gs [] ws _ _ _ _] =>
                    ((gs ++ ws.filter (·.1 != lengthKey)).lookup f).map (·, Rule.readProto P)
                  | _ => none
              else none)
          | [.callable fs _ _ _] => (fs.lookup f).map (·,Rule.readCallable)
          | [.ctors _ _ fs _ vs] => (fs.lookup f).map (·,Rule.readCallable) <|> (vs.lookup f).map (·,Rule.readBagView)
          -- A dictionary's named field or view, else its index, which may miss.
          -- The index holds of every present field, an optional one included.
          | [.dict fs [] vs ix _ _ _ _ _] =>
            (fs.lookup f).map (·,Rule.read) <|>
            ((vs.lookup f).bind fun B => if f == lengthKey && !lengthExcluded G B then none else some (B, Rule.readView)) <|>
            (numericFirst ix).findSome? fun (K, B) => if !K.surely f then none else
              pool.findSome? fun U =>
                if expand G U == [.undef] then some (B ++ U, Rule.readDict K B U) else none
          | _ => none )
        let sub ← subtypeUsing G images B A
        let ea ← recur Γ a R
        pure (coerceBy sub (.node ⟨Γ,t,B⟩ r [ea]) A)
      return direct.orElse fun _ => splitReceiver a
    | .writeAt f a b =>
      let direct := pool.findSearch? fun R => do
        let (fs,r) ← match expand G R with
          | [.refs fs [] _ _ _ _] => some (fs,Rule.write)
          | [.callable fs _ _ _] | [.ctors _ _ fs _ _] => some (fs,Rule.writeCallable)
          | _ => none
        let B ← fs.lookup f
        let ea ← recur Γ a R
        let eb ← recur Γ b B
        (A :: pool).findSearch? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ r [ea,eb]
          (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
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
      return operands.findSearch? fun R => do
        let ea ← recur Γ a R
        (operands.filter fun S => (operandsResult G op R S).isSome ||
            decide (EqualityDecided G op R) || decide (EqualityDecided G op S)).findSearch? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findSearch? fun N =>
            let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .arith [ea,eb]
            (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
    -- A literal with spreads: a store type of any length at some element
    -- type, each plain part at it, and for each spread a pool store type
    -- whose elements it admits.
    | .arrLit inits =>
      let flags := inits.map fun a => match a with | .spread _ => true | _ => false
      if flags.any id then
        return (A :: pool).findSearch? fun L => do
          let [.list ⟨[], [], some E, _, _⟩ []] := expand G L | none
          let es ← inits.mapM fun a => match a with
            | .spread src => pool.findSearch? fun S =>
                if decide (SpreadsInto G S E) then recur Γ src S else none
            | a => recur Γ a E
          coerce G images aliases (.node ⟨Γ,t,L⟩ (.arrParts E flags) es) A
      -- Without a spread, the claimed type, or a pool type, names the tuple;
      -- each initializer is typed at its position's contract.
      return (A :: pool).findSearch? fun L => do
        let [.list T []] := expand G L | none
        if inits.length < T.required.length then none else
        if T.rest.isNone && T.required.length + T.optional.length < inits.length then none else do
        let ps ← inits.zipIdx.mapM fun (a, k) => do
          let B ← positionTy T k
          recur Γ a B
        let e := ProgramCertificates.Evidence.node ⟨Γ,t,L⟩ .arrLit ps
        (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
    | .elemAt a i =>
      -- A store read through a union of array objects splits the receiver.
      let direct := pool.findSearch? fun L => do
        let [.list T []] := expand G L | none
        let ea ← recur Γ a L
        pool.findSearch? fun I => do
          let ei ← recur Γ i I
          match expand G I with
          | [.numLit b] => do
            let k ← indexOfBits b
            match T.required[k]? with
            | some B => coerce G images aliases (.node ⟨Γ,t,B⟩ .elem [ea,ei]) A
            | none => do
              let B ← positionTy T k
              (A :: pool).findSearch? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,B ++ U⟩ (.elemOpt U) [ea,ei]
                (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
          | _ =>
            match T with
            | ⟨[], [], some E, _, _⟩ =>
              (A :: pool).findSearch? fun U =>
                let e := ProgramCertificates.Evidence.node ⟨Γ,t,E ++ U⟩ (.elemAny U) [ea,ei]
                (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
            | _ => none
      -- A string's code unit at a numeric key: a string or `undefined`.
      let string := (stringOperands a).findSearch? fun S => do
        let ea ← recur Γ a S
        pool.findSearch? fun I => do
          if !decide (Answers G I .isNum true) then none else do
          let ei ← recur Γ i I
          (A :: pool).findSearch? fun T => do
            if expand G T != [.str] then none else do
            (A :: pool).findSearch? fun U =>
              if expand G U != [.undef] then none else
              coerce G images aliases (.node ⟨Γ,t,T ++ U⟩ (.elemStr T U) [ea,ei]) A
      return direct.orElse fun _ => string.orElse fun _ => do
        let .readAt _ receiver := a | none
        splitReceiver receiver
    | .setElem a i v =>
      return pool.findSearch? fun L => do
        let [.list T []] := expand G L | none
        let ea ← recur Γ a L
        pool.findSearch? fun I => do
          let [.numLit b] := expand G I | none
          let ei ← recur Γ i I
          let k ← indexOfBits b
          let B ← positionTy T k
          let ev ← recur Γ v B
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,L⟩ .setElem [ea,ei,ev]
          (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
    | .lenOf a =>
      let store := pool.findSearch? fun L => do
        let [.list _ []] := expand G L | none
        let ea ← recur Γ a L
        (A :: pool).findSearch? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .len [ea]
          (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
      -- A string's own `length`.
      return store <|> (stringOperands a).findSearch? fun S => do
        let ea ← recur Γ a S
        (A :: pool).findSearch? fun N =>
          let e := ProgramCertificates.Evidence.node ⟨Γ,t,N⟩ .lenStr [ea]
          (SearchM.lift (checkTreeResult G images e)).bind fun _ => coerce G images aliases e A
    | .merge d a b =>
      -- The accumulator and the source at their slots' types, or a pool
      -- type; the result the requested type, when every pair of their
      -- clauses merges into it, else a pool type coerced to it.
      let slot (x : Tm) := match x with | .var i => Γ[i]?.toList | _ => []
      return (slot a ++ pool).findSearch? fun R => do
        let ea ← recur Γ a R
        (slot b ++ pool).findSearch? fun S => do
          let eb ← recur Γ b S
          (A :: pool).findSearch? fun N =>
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
      return (slot k ++ pool).findSearch? fun K => do
        let ek ← recur Γ k K
        (slot a ++ held.eraseDups ++ pool).findSearch? fun B => do
          let ea ← recur Γ a B
          (A :: pool).findSearch? fun N =>
            if ComputedKey.KeyedOk G K B N then
              coerce G images aliases (.node ⟨Γ,t,N⟩ .makeKey [ek,ea]) A
            else none
    | .throw a =>
      -- A throw has every type; its operand, at a type of its own.
      let types := (match a with | .var i => Γ[i]?.toList | _ => []) ++ pool
      return types.findSearch? fun B => do
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
      if decide (Answers G B tag true) || decide (Answers G B tag false) then
        let (steps, last) := decidedChain G Γ t
        return (recur Γ last A).map fun p => steps.foldr (fun (s, q) p =>
          .node ⟨Γ,s,A⟩ (if q then .ifTrue else .ifFalse) [p]) p
      -- Split only an explicit union. A singleton whose graph clause itself
      -- mixes shapes is not made smaller by repeating this rule; its answer
      -- is unknown, the test is a Boolean, and both arms are typed.
      if (ProgramTyping.members G B).length ≤ 1 then
        return (A :: pool).findSearch? fun C => do
          if !decide ((.boolLit true) ∈ expand G C ∧ (.boolLit false) ∈ expand G C) then none else do
          let pc := ProgramCertificates.Evidence.node ⟨Γ,.test tag (.var i),C⟩ .test
            [.node ⟨Γ,.var i,B⟩ .var []]
          let pt ← recur Γ u A
          let pe ← recur Γ e A
          pure (.node ⟨Γ,t,A⟩ .ifBool [pc,pt,pe])
      return do
        let ps ← (ProgramTyping.members G B).mapM fun a => recur (Γ.set i [a]) t A
        pure (.node ⟨Γ,t,A⟩ (.unionVar i) ps)
    | .ite c t e =>
      let known := pool.findSearch? fun C => do
        let [.boolLit q] := expand G C | none
        let pc ← recur Γ c C
        let pb ← recur Γ (if q then t else e) A
        pure (.node ⟨Γ,.ite c t e,A⟩ (.ifKnown q) [pc,pb])
      let refined : SearchM ι (ProgramCertificates.Evidence ι) := do
        let .var i := c | none
        let C ← Γ[i]?
        if !decide (Answers G C .isBool true) then none else do
          let T ← pool.find? fun T => decide (expand G T = [.boolLit true])
          let F ← pool.find? fun F => decide (expand G F = [.boolLit false])
          let pt ← recur (Γ.set i T) t A
          let pe ← recur (Γ.set i F) e A
          pure (.node ⟨Γ,.ite c t e,A⟩ (.ifBoolVar T F) [pt,pe])
      return known.orElse fun _ => refined.orElse fun _ => pool.findSearch? fun C => do
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
  /-- A return whose promised argument has type `actual`, not within the
  promise `promised`. -/
  | promise (label : Nat) (actual promised : Ty ι)
  deriving DecidableEq, Repr

/-- A node's production, threading the answered requests: a failure keeps
the answers its attempts found. -/
abbrev ProduceM (ι : Type) [BEq ι] [Hashable ι] := EStateM (Failure ι) (Answered ι)

/-- A search step's whole result, in production. -/
@[inline] def searchIn [BEq ι] [Hashable ι] (x : SearchM ι α) : ProduceM ι (CheckResult ι α) :=
  fun s => let (r, s) := x s; .ok r s

/-- A state computation over the answers, in production. -/
@[inline] def stateIn [BEq ι] [Hashable ι] (x : StateM (Answered ι) α) : ProduceM ι α :=
  fun s => let (a, s) := x s; .ok a s

/-- Ordinary and observed edges share slot selection and coverage search. The
observation comes from graph dispatch, never from supplied point annotations. -/
@[nospecialize] def edgeUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (claims : List (PointClaim ι)) (Γ : List (Ty ι)) (target : Target)
    (observed : Option (Nat × BranchRefinement.Observation) := none)
    (fields : List (Nat × PropKey) := []) (optionals : List (Nat × PropKey) := [])
    (cells : HeapFacts.Facts := []) :
    SearchM ι (EdgeEvidence ι) := do
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
            -- A tag set: the elements the test leaves.
            else if BranchRefinement.setSlice G A B t q then some {}
            else none
      else ((subtypeUsing G images A B).orElse (fun _ => match o with
        -- An object the tested value was read from keeps the labels whose
        -- field admits the observation.
        | .tag t q => (fields ++ optionals).findSearch? fun (k, f) =>
            if k == slot target.mapping i then subtypeUsing G images (BranchRefinement.fieldSlice G A f t q) B
            else none
        | .boolean _ => none) |>.orElse fun _ =>
        -- One read through an optional key, where the observation rules out
        -- the `undefined` an absent key reads: the key is present.
        if BranchRefinement.excludesUndef o && optionals.any (fun (k, f) =>
            k == slot target.mapping i && BranchRefinement.promotes G A B f)
        then some {} else none) |>.orElse fun _ =>
        -- An object a cell fact is about keeps the labels its field's
        -- observed contents admit.
        cells.findSearch? fun fct =>
          if fct.slot == slot target.mapping i then
            subtypeUsing G images (BranchRefinement.factSlice G A fct.field fct.contents) B
          else none
    | none => subtypeUsing G images A B


/-- Select effect evidence without changing the requested sequent. A precise
read/value rule may succeed when ordinary derivation search cannot. -/
@[nospecialize] def expressionEffectUsing [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel : Nat) (j : Sequent ι) (k : HeapKnowledge.Knowledge)
    (suggestions : List (Sequent ι)) (known : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (aliases : List (ι × ι) := [])
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images) :
    SearchM ι (Evidence ι × HeapExpressionRules.StepEvidence ι × HeapKnowledge.Knowledge) := do
  -- A node's derivation is first sought among its own types: its claim and
  -- its context's, which are its operands' claims. The pool is consulted
  -- only where those leave a choice open.
  let own := (j.type :: j.context).eraseDups
  let ordinary ← (SearchM.orElse (SearchM.lift (CheckResult.fromOption (known.find? fun e => claim e == j))) fun _ =>
    (expressionWithUsing G images own suggestions aliases fuel j.context j.term j.type).orElse fun _ =>
      expressionWithUsing G images pool suggestions aliases fuel j.context j.term j.type).result
  let mut incomplete := ordinary.exhaustion
  let mut choices : List (HeapExpressionRules.StepEvidence ι) := []
  match j.term with
  | .var i =>
    if let some R := HeapExpressionRules.valuesAt G j.context k i then
      choices := [.knownValue i R]
  | .readAt fld (.var i) =>
    choices := (k.cells.filter fun f => f.slot == i && f.field == fld).map
      fun f => .observedRead i f.contents
    -- A read a live read link answers: the linked slot's value, at its type.
    for g in k.links do
      if (HeapLinks.aliases k.links i).contains g.cell && g.field == fld && !g.alias && !g.distinct then
        if let some B := j.context[g.value]? then
          let compared ← (subtypeUsing G images B j.type).result
          incomplete := incomplete <|> compared.exhaustion
          if let some p := compared.value then
            choices := choices ++ [.linkedRead i g.value p]
    -- Read at the fixed contract once, then try each answer the location's
    -- facts give: a nullish exclusion's, and an observed tag's.
    if let some Ref := j.context[i]? then
      let cells := k.cells.filter fun f => f.slot == i && f.field == fld
      let observed := cells.flatMap fun f => f.contents.filterMap fun
        | .tag t q => some (t, q)
        | _ => none
      let answers := (([Tag.isUndef, .isNul, .isNullish].map (·, false)) ++ observed).eraseDups.filter
        fun (t, q) => cells.any fun f => f.contents.all (·.answers t q)
      -- The contract the read is typed at: the record's field, or a
      -- dictionary's index, with `undefined` where the key is absent.
      let contract : Option (Ty ι) := match expand G Ref with
        | [.refs fs _ vs _ _ _ _] => if HeapExpressionRules.fieldOperand (expand G Ref) fld then fs.lookup fld <|> vs.lookup fld else none
        | [.dict _ _ _ ds _ _ _ cs _] =>
          if HeapExpressionRules.optionalOperand (expand G Ref) fld then
            -- The graph's `undefined` row, among the labels the search knows.
            let undef := (j.type :: own ++ pool).findSome? fun T => T.find? fun l =>
              G.plain l && match G l with | [.undef] => true | _ => false
            match ((ds ++ cs).find? (HeapExpressionRules.stringIndex · fld)), undef with
            | some d, some u => some (u :: d.2).eraseDups
            | _, _ => none
          else none
        | _ => none
      if !answers.isEmpty then
          if let some C := contract then
            -- A dictionary's read finds `undefined` where the key is absent:
            -- its row is searched beside the contract.
            let undefs := C.filterMap fun l => match G l with | [.undef] => some [l] | _ => none
            let searched ← (expressionWithUsing G images (C :: undefs ++ own) suggestions aliases fuel j.context j.term C).result
            incomplete := incomplete <|> searched.exhaustion
            if let some e := searched.value then
              for (tag, q) in answers do
                let compared ← (subtypeUsing G images (BranchRefinement.tagSlice G C tag q) j.type).result
                incomplete := incomplete <|> compared.exhaustion
                match compared.value with
                | some p => choices := choices ++ [.slicedRead tag q i e p]
                | none =>
                  if tag == .isArray && q && BranchRefinement.arraySlice G C j.type then
                    choices := choices ++ [.slicedRead tag q i e {}]
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
    let checked := checker.select j k effect codes
    incomplete := incomplete <|> checked.exhaustion
    if let some out := checked.value then
      -- Effect evidence validates this header itself; an ordinary derivation
      -- is not required for the precise read/value alternatives.
      return (ordinary.value.getD (.node j .var []),effect,out)
  SearchM.lift ⟨none, incomplete⟩

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

/-- What a node's expression yields: a call at a promise signature, its
promise; a slot read, the slot's implications; a tag test read as a Boolean,
where it passes, its slot's slice, or, where the slice is the slot's whole
type, a type of the pool the test decides. Untrusted: the checker decides. -/
@[nospecialize] def nodeYields [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (pool : List (Ty ι)) (Γ : List (Ty ι))
    (implies : List (PromiseCalls.Implication ι)) (e : Evidence ι)
    (out k : HeapKnowledge.Knowledge) : StateM (Answered ι) (List (PromiseCalls.Yield ι)) :=
  match PromiseCalls.promiseOf G e with
  | some (effect, a, T) =>
    if out == HeapExpressionRules.ordinaryOutput k ||
        out == HeapExpressionRules.withStable G Γ k (HeapExpressionRules.ordinaryOutput k) then
      pure [{ conditional := match effect.promise with | some (.guards _) => true | _ => false, target := a, type := T }]
    else pure []
  | none =>
    match (claim e).term with
    | .var i => pure (implies.filterMap fun x =>
        if x.test == i then some { conditional := true, target := x.target, type := x.type } else none)
    | .ite (.test tag (.var i)) .tru .fls => do
      let ys ← tested i tag true
      let zs ← throughFields i tag true
      let ns ← memberYields [tag] i [false]
      pure (fewestLast (ys ++ zs) ++ ns)
    | .ite (.test tag (.var i)) .fls .tru => do
      let ys ← tested i tag false
      let zs ← throughFields i tag false
      pure (fewestLast (ys ++ zs))
    | t => match PromiseCalls.memberParts t with
      | some (ts, i) => if PromiseCalls.isMemberOn ts i t then memberYields ts i [true, false] else pure []
      | none => pure []
where
  /-- A membership test's yields (`PromiseCalls.memberYield`): for each
  answer, the tested slot's type and the objects' a current read link says
  its value was read from, as the answer leaves them, where it leaves less;
  each yield's type is its slice, which the empty choices relate to itself
  without a search. -/
  memberYields (ts : List Tag) (i : Nat) (answers : List Bool) : StateM (Answered ι) (List (PromiseCalls.Yield ι)) := do
    let slot ← answers.filterMapM fun q => match Γ[i]? with
      | none => pure none
      | some A =>
        let sliced := PromiseCalls.memberSlice (BranchRefinement.tagSlice G) A ts q
        if sliced == A then pure none else
        pure (some { conditional := q, onFalse := !q, target := i, type := sliced, evidence := some {} })
    let fields ← (answers.flatMap fun q => k.links.map (q, ·)).filterMapM fun (q, g) =>
      if g.distinct || g.alias || g.optional || g.value != i then pure none else
        match Γ[g.cell]? with
        | none => pure none
        | some A =>
          let sliced := PromiseCalls.memberSlice (fun B t q => BranchRefinement.fieldSlice G B g.field t q) A ts q
          if sliced == A then pure none else
          pure (some { conditional := q, onFalse := !q, target := g.cell, type := sliced, evidence := some {} })
    pure (fewestLast (slot ++ fields))
  /-- The edge sets each slot an alias link relates to every yield of its
  class, in order: a slice of fewer labels last, the one the edge keeps. -/
  fewestLast (ys : List (PromiseCalls.Yield ι)) : List (PromiseCalls.Yield ι) :=
    ys.mergeSort fun a b => a.type.length ≥ b.type.length
  /-- The objects a current read link says the tested slot's value was read
  from: each at the arms whose field answers the test so. -/
  throughFields (i : Nat) (tag : Tag) (q : Bool) : StateM (Answered ι) (List (PromiseCalls.Yield ι)) :=
    k.links.filterMapM fun g =>
      if g.distinct || g.alias || g.optional || g.value != i then pure none else
        match Γ[g.cell]? with
        | none => pure none
        | some A =>
          let sliced := BranchRefinement.fieldSlice G A g.field tag q
          if sliced == A then pure none else do
          let r ← (subtypeUsing G images sliced sliced).toState
          pure (r.value.map fun p => { conditional := true, target := g.cell, type := sliced, evidence := some p })
  tested (i : Nat) (tag : Tag) (q : Bool) : StateM (Answered ι) (List (PromiseCalls.Yield ι)) :=
    match Γ[i]? with
    | some A =>
      let sliced := BranchRefinement.tagSlice G A tag q
      let decided := (pool.filter fun B => !B.isEmpty && BranchRefinement.tagMember G B tag q).foldl
        (fun best B => match best with
          | some b => if B.length < b.length then some B else best
          | none => some B) none
      -- A passed `Array.isArray` also drops the labels of no array or of
      -- indexed dictionaries (`arraySlice`).
      let arrays := sliced.filter fun a => !(G.plain a && G.builtins.isSome &&
        (G a).all fun c => tagClause .isArray c == some false || BranchRefinement.indexedDict c)
      if tag == .isArray && q && arrays != sliced && BranchRefinement.arraySlice G A arrays then
        pure [{ conditional := true, target := i, type := arrays, evidence := some {} }]
      else
      -- A tag set the test splits: a claimed type holding the elements it
      -- leaves.
      let decided := decided <|> (pool.filter fun B => !B.isEmpty &&
        BranchRefinement.setSlice G A B tag q).foldl (fun best B => match best with
          | some b => if B.length < b.length then some B else best
          | none => some B) none
      match (if sliced != A then none else decided) with
      | some B => pure [{ conditional := true, target := i, type := B, evidence := some {} }]
      | none => do
        let r ← (subtypeUsing G images sliced sliced).toState
        pure (match r.value with
          | some p => [{ conditional := true, target := i, type := sliced, evidence := some p }]
          | none => [])
    | none => pure []

/-- An edge's implications in the target's slots: each the source states, at
every pair of target slots the mapping reads it from. -/
def projectImplications (xs : List (PromiseCalls.Implication ι)) (m : PointClaims.Mapping) (width : Nat) :
    List (PromiseCalls.Implication ι) :=
  (List.range width).flatMap fun t => (List.range width).filterMap fun a =>
    (xs.find? fun x => x.test == PointClaims.slot m t && x.target == PointClaims.slot m a).map
      fun x => ⟨t, a, x.type⟩

/-- What every predecessor of a merge establishes, in the merge's slots: an
implication one of them states, at the union of the types each states or
justifies by its own type of the target slot; dropped where one justifies it
neither way nor by never holding `true` in the tested slot. -/
def meetImplications [DecidableEq ι] (G : NormalGraph ι)
    (edges : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (width : Nat) : List (PromiseCalls.Implication ι) :=
  let projected := edges.map fun (Γ, xs, m) => (Γ, m, projectImplications xs m width)
  let candidates := (projected.flatMap fun (_, _, xs) => xs.map fun x => (x.test, x.target)).eraseDups
  candidates.filterMap fun (t, a) => do
    let types ← projected.mapM fun (Γ, m, xs) =>
      match xs.find? (fun x => x.test == t && x.target == a) with
      | some x => some x.type
      | none => match Γ[PointClaims.slot m a]? with
        | some A => some A
        | none => if (Γ[PointClaims.slot m t]?).any (BranchRefinement.impossible G · (.boolean true))
          then some [] else none
    return ⟨t, a, types.flatten.eraseDups⟩

/-- A node's evidence at its expression's derivation and the yields chosen
for it: its edges, its handler and, at a return under a promise goal, the
promise's evidence. -/
@[nospecialize] private def produceNodeAt [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (pool : List (Ty ι)) (l : Nat) (node : Node) (claims : List (PointClaim ι))
    (k : HeapKnowledge.Knowledge) (c : PointClaim ι) (e : Evidence ι) (effect : HeapExpressionRules.StepEvidence ι)
    (out : HeapKnowledge.Knowledge) (implies : List (PromiseCalls.Implication ι)) (arguments : List Nat)
    (goal : ControlFlow.Goal ι) (ys : List (PromiseCalls.Yield ι)) : ProduceM ι (NodeEvidence ι) := do
  let unconditional := PromiseCalls.yieldFacts ys false
  let conditional := PromiseCalls.yieldFacts ys true
  let refine := fun Γ facts shift => PromiseCalls.refineBy Γ facts shift
  -- An edge's refinement reaches the slots its knowledge's aliases relate.
  let pushedRefine := fun facts => PromiseCalls.refineBy (c.type :: c.context)
    (PromiseCalls.aliasFacts out.links facts 1) 0
  let keptRefine := fun facts => PromiseCalls.refineBy c.context
    (PromiseCalls.aliasFacts (HeapKnowledge.dropResult out).links facts 0) 0
  let target := fun (Γ : List (Ty ι)) (t : Target) (index : Nat) => (do
    let searched ← searchIn (edgeUsing G images claims Γ t)
    match searched.value with
    | some p => pure p
    | none => throw (match searched.exhaustion with
      | some stop => Failure.exhaustedEdge l t.label index stop
      | none => Failure.edge l t.label index) : ProduceM ι (EdgeEvidence ι))
  let branchTarget := fun (Γ : List (Ty ι)) o (t : Target) (index : Nat) => (do
    let searched ← searchIn (edgeUsing G images claims Γ t (some (0, o)) (readFields out 0) (optionalFields out 0)
      (HeapKnowledge.observeTyped G Γ out 0 o).cells)
    match searched.value with
    | some p => pure p
    | none => throw (match searched.exhaustion with
      | some stop => Failure.exhaustedEdge l t.label index stop
      | none => Failure.edge l t.label index) : ProduceM ι (EdgeEvidence ι))
  let ps ← (match node.continuation with
    | .ret => pure []
    | .bind t => (target (pushedRefine unconditional) t 0).map (fun p => [p])
    | .effect t => (target (keptRefine unconditional) t 0).map (fun p => [p])
    | .branch y n => (target (keptRefine conditional) y 0).bind (fun py =>
        (target (keptRefine unconditional) n 1).map (fun pn => [py,pn]))
    | .branchBind y n => (branchTarget (pushedRefine conditional) (.boolean true) y 0).bind (fun py =>
        (branchTarget (pushedRefine (PromiseCalls.yieldFacts ys false true)) (.boolean false) n 1).map (fun pn => [py,pn]))
    | .tagBind t y n => (branchTarget (pushedRefine
        (PromiseCalls.yieldFacts ys (ControlFlow.truthyBoolean G t c.type))) (.tag t true) y 0).bind (fun py =>
        (branchTarget (pushedRefine unconditional) (.tag t false) n 1).map (fun pn => [py,pn])) : ProduceM ι (List (EdgeEvidence ι)))
  -- A handler receives the thrown value at a type admitting every value: the
  -- type its target states for the slot it lands in, else one from the pool.
  let hd ← (match node.handler with
    | none => pure none
    | some t => do
      let landing := ((claims[t.label]?).toList.flatMap fun tc =>
        (List.range tc.context.length).filterMap fun i =>
          if PointClaims.slot t.mapping i == 0 then tc.context[i]? else none)
      let searched ← searchIn ((landing ++ pool).findSearch? fun T =>
        if ControlFlow.admitsAll G T then (edgeUsing G images claims (T :: c.context) t).map (T, ·) else none)
      match searched.value with
      | some x => pure (some x)
      | none => throw (match searched.exhaustion with
        | some stop => .exhaustedEdge l t.label (successors node.continuation).length stop
        | none => .edge l t.label (successors node.continuation).length)
    : ProduceM ι (Option (Ty ι × EdgeEvidence ι)))
  -- A return under a promise goal: evidence that the argument, as the yields
  -- leave it, is within the promise.
  let within := fun (facts : List (Nat × Ty ι)) (T : Ty ι) =>
    (arguments.findSomeM? fun p => match (refine c.context facts 0)[p]? with
      | some B => do
        let r ← searchIn (subtypeUsing G images B T)
        pure (r.value.map (p, ·))
      | none => pure none : ProduceM ι (Option (Nat × PositiveCertificates.SubtypeChoices ι)))
  let promise ← match node.continuation, goal with
    | .ret, .guards T _ => if BranchRefinement.impossible G c.type (.boolean true) then pure none else within conditional T
    | .ret, .asserts T _ => within unconditional T
    | _, _ => pure none
  let evidence : NodeEvidence ι := {expression := e, edges := ps, knowledge := k, effect := some effect, output := out, handler := hd}
  return { evidence with implies := implies, yields := ys, arguments := arguments, promise := promise }


@[nospecialize] private def produceNode [DecidableEq ι] [Hashable ι] [Instantiates ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι))
    (fuel l : Nat) (node : Node) (claims : List (PointClaim ι))
    (k : HeapKnowledge.Knowledge) (suggestions : List (Sequent ι)) (known : List (Evidence ι))
    (codes : CodeEntry ι → Bool := fun _ => false) (aliases : List (ι × ι) := [])
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (implies : List (PromiseCalls.Implication ι) := []) (arguments : List Nat := [])
    (goal : ControlFlow.Goal ι := .plain []) :
    ProduceM ι (NodeEvidence ι) := do
  let some c := claims[l]? | throw .claimCount
  let searched ← searchIn (expressionEffectUsing G images pool fuel ⟨c.context,node.expression,c.type⟩ k suggestions
    known codes aliases checker)
  let some (e,effect,out) := searched.value | throw (match searched.exhaustion with
    | some stop => .exhaustedExpression l stop
    | none => .expression l)
  let found ← stateIn (nodeYields G images pool c.context implies e out k)
  -- Yields that leave a target's claim unmet are not taken.
  tryCatch (produceNodeAt G images pool l node claims k c e effect out implies arguments goal found) fun err =>
    if found.isEmpty then throw err
    else produceNodeAt G images pool l node claims k c e effect out implies arguments goal []

/-- The implications a source node carries on its edge of `cont` numbered
`index`, and the context, refined by its yields, they are checked in. -/
def edgeImplicationsOf [DecidableEq ι] (previous : NodeEvidence ι) (cont : Continuation) : List (PromiseCalls.Implication ι) :=
  PromiseCalls.aliasImplications (edgeFactsOf previous cont).links (match cont with
    | .effect _ | .branch _ _ => previous.implies
    | _ => PromiseCalls.edgeImplications previous.implies previous.yields true)
where
  /-- The knowledge an edge's implications and argument slots are carried by,
  as the checker reads it (`ControlFlow.carries`). -/
  edgeFactsOf (previous : NodeEvidence ι) : Continuation → HeapKnowledge.Knowledge
    | .effect _ | .branch _ _ => HeapKnowledge.dropResult previous.output
    | _ => previous.output

/-- The slots of a node's edge holding the promised argument, in the source's
slots, its knowledge's aliases included. -/
def edgeArgumentsOf [DecidableEq ι] (previous : NodeEvidence ι) (node : Node) : List Nat :=
  PromiseCalls.aliasSources (edgeImplicationsOf.edgeFactsOf previous node.continuation).links
    (match node.continuation with
     | .effect _ | .branch _ _ => previous.arguments
     | _ => ControlFlow.pushedSources previous.arguments (ControlFlow.aliasedRead previous.arguments node.expression))

/-- An edge's argument slots in the target's: each slot whose mapping reads
one holding it. -/
def projectArguments (sources : List Nat) (m : PointClaims.Mapping) (width : Nat) : List Nat :=
  (List.range width).filter fun i => sources.contains (PointClaims.slot m i)

def edgeContextOf [DecidableEq ι] (G : NormalGraph ι) (previous : NodeEvidence ι) (cont : Continuation) (index : Nat) :
    List (Ty ι) :=
  let Γ := (claim previous.expression).context
  let A := (claim previous.expression).type
  let facts := fun answered => PromiseCalls.yieldFacts previous.yields answered
  let pushed := fun fs => PromiseCalls.refineBy (A :: Γ) (PromiseCalls.aliasFacts previous.output.links fs 1) 0
  let kept := fun fs => PromiseCalls.refineBy Γ
    (PromiseCalls.aliasFacts (HeapKnowledge.dropResult previous.output).links fs 0) 0
  match cont with
  | .bind _ => pushed (facts false)
  | .tagBind t _ _ => pushed (facts (index == 0 && ControlFlow.truthyBoolean G t A))
  | .effect _ => kept (facts false)
  | .branch _ _ => kept (facts (index == 0))
  | .branchBind _ _ => pushed (PromiseCalls.yieldFacts previous.yields (index == 0) (index != 0))
  | .ret => Γ

/-- The slots holding the promised argument at each node: the goal's slot at
the entry, carried along every edge, a handler's included, to each slot whose
mapping reads one holding it, those every predecessor carries. Untrusted: the
checker follows each edge again. -/
@[nospecialize] def argumentSlots (P : Program) (claims : List (PointClaim ι)) (start : Nat)
    (slot : Option Nat) : List (List Nat) := Id.run do
  -- `none`: not reached yet. Arrays: nodes are visited by label.
  let widths := (claims.map (·.context.length)).toArray
  let mut table : Array (Option (List Nat)) := Array.replicate P.length none
  table := table.set! start (some slot.toList)
  for _ in List.range (2 * P.length + 2) do
    let mut changed := false
    for (node, l) in P.zipIdx do
      let some here := table.getD l none | continue
      let edges := (successors node.continuation).zipIdx.map (fun (t, _) =>
          (t, match node.continuation with | .effect _ | .branch _ _ => false | _ => true)) ++
        node.handler.toList.map (fun t => (t, true))
      for (t, pushed) in edges do
        let sources := if pushed then ControlFlow.pushedSources here (ControlFlow.aliasedRead here node.expression)
          else here
        let width := widths.getD t.label 0
        let carried := match t.mapping with
          | none => (List.range width).filter sources.contains
          | some slots => ((List.range width).zip (slots ++ List.replicate (width - slots.length) 0)).filterMap
              fun (i, s) => if sources.contains s then some i else none
        let current := table.getD t.label none
        let merged := match current with
          | none => some carried
          | some old => some (old.filter carried.contains)
        if merged != current then
          table := table.set! t.label merged
          changed := true
    if !changed then break
  return table.toList.map fun x => x.getD []

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
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (goal : ControlFlow.Goal ι := .plain []) :
    ProduceM ι (ControlFlow.Certificate ι) := do
  if P.length != claims.length then throw .claimCount
  -- Arrays: every pass visits nodes and their predecessors by label.
  let arguments := (argumentSlots P claims start goal.slot).toArray
  let nodes := P.toArray
  let claimed := claims.toArray
  let handlerTargets := P.filterMap fun node => node.handler.map (·.label)
  let incoming : Array (List (Nat × Nat × Target)) := P.zipIdx.foldl (fun acc (node,l) =>
      (successors node.continuation).zipIdx.foldl (fun acc (t,index) =>
        if t.label < acc.size then acc.modify t.label (· ++ [(l,index,t)]) else acc) acc)
    (Array.replicate P.length [])
  let mut table : Array (Option (NodeEvidence ι)) := Array.replicate P.length none
  -- A merge waits for its predecessors while some pass still makes progress;
  -- once none does, the merges still waiting (a cycle through no cut) take
  -- their stated requirements alone, as every merge did before.
  let mut force := false
  for _ in List.range (2 * P.length + 2) do
    let mut progress := false
    for l in List.range P.length do
      if (table.getD l none).isSome then continue
      let some node := nodes[l]? | throw .claimCount
      let some c := claimed[l]? | throw .claimCount
      let required := (requirements.lookup l).getD ⟨[],[],[]⟩
      let mut k := required
      let mut implies : List (PromiseCalls.Implication ι) := []
      -- At the entry and at cuts, the argument slots every edge carries.
      let mut held := arguments.getD l []
      if l != start && !cuts.contains l then
        match incoming[l]? with
        | some [(pred,index,target)] =>
          let some previous := table.getD pred none | continue
          let some source := nodes[pred]? | throw .claimCount
          k := HeapKnowledge.project (edgeKnowledge G ((claim previous.expression).type :: (claim previous.expression).context) previous.output source.continuation index)
            target.mapping c.context.length
          implies := projectImplications (edgeImplicationsOf previous source.continuation) target.mapping
            c.context.length
          held := projectArguments (edgeArgumentsOf previous source) target.mapping c.context.length
        | some preds =>
          -- A merge that is not a cut states no requirement of its own; it
          -- keeps what every predecessor establishes, once all are available.
          -- Cycles pass through cuts, so waiting here cannot deadlock.
          let mut projections : List HeapKnowledge.Knowledge := []
          let mut carried : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping) := []
          let mut holding : List (List Nat) := []
          let mut ready := true
          for (pred,index,target) in preds do
            match table.getD pred none, nodes[pred]? with
            | some previous, some source =>
              projections := projections ++ [HeapKnowledge.project
                (edgeKnowledge G ((claim previous.expression).type :: (claim previous.expression).context) previous.output source.continuation index) target.mapping c.context.length]
              carried := carried ++ [(edgeContextOf G previous source.continuation index,
                edgeImplicationsOf previous source.continuation, target.mapping)]
              holding := holding ++ [projectArguments (edgeArgumentsOf previous source) target.mapping
                c.context.length]
            | _, _ => ready := false
          if !ready && !force then continue
          if ready then
            k := HeapKnowledge.meet projections
            implies := meetImplications G carried c.context.length
            held := match holding with
              | first :: rest => first.filter fun p => rest.all (·.contains p)
              | [] => []
        | none => pure ()
      k := ⟨(k.cells ++ required.cells).eraseDups,(k.values ++ required.values).eraseDups,
        HeapLinks.dedup (k.links ++ required.links)⟩
      -- A handler target is entered by throws too, which carry no
      -- implication, and the argument slots the throwing nodes carry.
      if handlerTargets.contains l then
        implies := []
        held := held.filter (arguments.getD l []).contains
      let evidence ← produceNode G images pool fuel l node claims k suggestions known codes aliases checker
        implies held goal
      table := table.set! l (some evidence)
      progress := true
    if !progress then
      if force then break else force := true
    else force := false
  table.toList.mapM fun c => match c with
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
    (fuel : Nat) (R : ControlFlow.Goal ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (hints : List (Ty ι) := []) (inputs : List (Ty ι) := [])
    (suggestions : List (Sequent ι) := []) (known : List (ProgramCertificates.Evidence ι) := [])
    (requirements : List (Nat × HeapKnowledge.Knowledge) := []) (cuts : List Nat := [])
    (codes : CodeEntry ι → Bool := fun _ => false)
    (checker : HeapExpressionRules.Checker G images := HeapExpressionRules.Checker.ordinary G images)
    (aliases : List (ι × ι) := []) (answers : Answered ι := {}) :
    Except (Failure ι) (ControlFlow.Certificate ι) × Answered ι :=
  let promised := match R with
    | .guards T _ | .asserts T _ => [T]
    | .plain _ => []
  match (produceRawUsing G images (vocabulary G labels claims (inputs ++ hints ++ promised)) fuel P claims suggestions known start
      requirements cuts codes aliases checker R).run answers with
  | .error e answers => (.error e, answers)
  | .ok C answers => Prod.mk (
    let checked := acceptResult G images R P claims C start inputs codes checker
    if checked.accepted then .ok C
    else match checked.exhaustion with
      | some stop => .error (.exhaustedExpression (stop.nodeLabel.getD start) stop)
      | none => .error ((failedEdge G P C).getD (Id.run do
          -- The first node whose own check fails: its expression, its yields,
          -- its return, or one of its edges.
          for (node, l) in P.zipIdx do
            if let some c := C[l]? then
              if !checkNodeUsing (checker := checker) G images R P C node c codes then
                return (unkept l node c).getD (.expression l)
          return .rejected))) answers
where
  /-- A return of a promise goal whose answer is right but whose promised
  argument is not within the promise: the argument's type as the return
  knows it. -/
  unkept (l : Nat) (node : Node) (c : NodeEvidence ι) : Option (Failure ι) := do
    let .ret := node.continuation | none
    let (T, answered, answer) ← match R with
      | .guards T _ => some (T, true, BranchRefinement.onlyBoolean G (ControlFlow.result c))
      | .asserts T _ => some (T, false, PromiseCalls.onlyUndef G (ControlFlow.result c))
      | .plain _ => none
    guard answer
    let p ← c.arguments.head?
    let A ← (PromiseCalls.refineBy (ControlFlow.entry c) (PromiseCalls.yieldFacts c.yields answered) 0)[p]?
    pure (.promise l A T)

end Verification.CertificateProducer
