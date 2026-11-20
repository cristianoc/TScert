import Verification.Source.Claims.FragmentFront
import Verification.Programs.TolerantFramesGuaranteeTarget
import Verification.Paper.TolerantFrames.ReadOnlyClaim
import Verification.Semantics.SafeRet

/-! # The single pass's unit theorem: definitions

What an accepted unit of mode 8 (`FilePlans.passGroup`) means, stated
without certificates (`RequestSafe`, `PassUnitSafe`), and the interface the
graph-level proof of `SinglePass.run` supplies (`RunSound`). The statements
and the theorems built on them are presented in
docs/SINGLE-PASS-THEOREM.md. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore
open PositiveCertificates (InstanceImageCheck)
open HeapExpressionRules (Checker)
open CertificateProducer (Answered)

/-! ## The run-level statements

The graph machine's reachability, what an accepted call of the pass
guarantees and the two run-level statements (`RunSound`,
`RunKeepsSummaries`) are the graph proof's own definitions
(`Verification.TolerantFrames.Target`). -/

export Verification.TolerantFrames.Target (ReachesIn EntryHolds GraphGuarantee CheckerScope RunCall
  RunCall.result RunCall.Accepts regionOf RunSound RunKeepsSummaries)


/-! ## Certificate-independent safety of a request and of a unit -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- The request a code request of `r` is checked as. -/
abbrev codeRequest (r : SourceRequest σ ι) (q : CodeRequest ι) : Request σ ι := q.asRequest r.toRequest

/-- The hints of `r`'s code request at `ci`, as the pass reads them. -/
def codeHintsAt (r : SourceRequest σ ι) (ci : Nat) : RequestJson.CodeHints := (r.codeHints[ci]?).getD {}

/-- Safety at every admitted assignment, from every entry. -/
def SafeClause (r : SourceRequest σ ι) : Prop :=
  ∀ η, r.Admits η → ∀ n W h ρ,
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices ρ n W h →
    RootsOk W ρ →
    SafeGraph (excOf (reassign (RequestJson.graph r.toRequest) η)) r.program
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument ρ)) n W h (.at r.start ρ)

/-- Within the claimed footprint, and returning fresh where promised, when the
declaration claims either. -/
def FootprintClause (r : SourceRequest σ ι) : Prop :=
  r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
    ∀ η n W h (L : List Tm) (d : Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h → RootsOk W (envOf L d) →
      (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
        (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
        (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
        (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d r.comp)

/-- Meeting the stated postcondition where the declaration states one. -/
def EnsuresClause (r : SourceRequest σ ι) : Prop :=
  r.ensures ≠ [] → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    HeapObservations.SafePost (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt r.ensures ⟨envOf L d, h⟩ h' (push v (envOf L d))) n W h (gotoOf r.program r.start L d r.comp)

/-- Within the stated regional bound where the declaration states regions. -/
def RegionalClause (r : SourceRequest σ ι) : Prop :=
  ∀ Φ regions, r.regional = some (Φ, regions) → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => r.stated.any (·.onThrow) = true →
        Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      n W h (gotoOf r.program r.start L d r.comp)

/-- Each stated assertion of the graph true at every state reached at its
label within the budget, at every admitted assignment. -/
def AssertionsClause (r : SourceRequest σ ι) : Prop :=
  ∀ η, r.Admits η → ∀ n W h ρ,
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices ρ n W h →
    RootsOk W ρ →
    ∀ l k, (l, k) ∈ r.assertions → ∀ j h' ρ', j < n → ReachesIn r.program j h (.at r.start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ⟨ρ, h⟩ ρ' h'

/-- Each stated assertion of each code's graph true at every state reached
at its label within the budget, from every frame meeting its signature. -/
def CodeAssertionsClause (r : SourceRequest σ ι) : Prop :=
  ∀ ci q, r.codes[ci]? = some q → ∀ η n W h ρ,
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) (codeRequest r q).inputs {}
      (codeRequest r q).entryIndices ρ n W h →
    RootsOk W ρ →
    ∀ l k, (l, k) ∈ (codeHintsAt r ci).requirements → ∀ j h' ρ', j < n →
      ReachesIn (codeRequest r q).program j h (.at (codeRequest r q).start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ⟨ρ, h⟩ ρ' h'

/-- **A request is safe** (`RequestsSafe`'s semantic conjuncts, no
certificate): at every admitted assignment its graph is safe from every
entry meeting its inputs, separation and index facts (`EntryHolds`: its
contracts, an admissible kinded world and a heap that world types) whose
bindings have valid references (`RootsOk`); it meets its claimed
footprint, fresh result, postcondition and regional bound; each stated
assertion of its graph and of each of its codes holds at every state reached
at its label within the budget. -/
def RequestSafe (r : SourceRequest σ ι) : Prop :=
  SafeClause r ∧ FootprintClause r ∧ EnsuresClause r ∧ RegionalClause r ∧ AssertionsClause r ∧
    CodeAssertionsClause r
end

/-! ## Safety of a request under a client obligation

A unit verified through the read-only frame rule is accepted for the
executions in which code outside its component keeps the client obligation
`Θ` of a client frame (`ReadOnly.ClientFrame`, the note's Assumption
"Clients"). Each clause below is a clause of `RequestSafe` read at each call
of the request's code (`gotoOf` at the call's arguments `L` and receiver
`d`, from outside code) the claim is about (`Call`: the frame's
well-formed entries, and its entry premises, `Entry`, code provenance and
the call discipline among them, which every step keeps) and from each
history the frame lets the call start from, along the executions whose every step keeps the obligation
(`SafeUnder`): progress at every state as in `RequestSafe`, nothing claimed
after a step of outside code that breaks it. -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]
open Verification.TolerantFrames.ReadOnly (ClientFrame)

/-- Safety along the executions keeping the frame's obligation, from the
history `g`, with `J` at every state reached. -/
abbrev SafeFramed (fr : ClientFrame (Ty ι)) (J : Heap → Tm → Prop) (Ξ T : Fam) (Q : HeapObservations.WPost)
    (R : HeapObservations.WExc) (n : Nat) (W : WorldT n) (g : Verification.TolerantFrames.ReadOnly.Ghost (fr.F.at fr.C)) (h : Heap) (t : Tm) : Prop :=
  HeapObservations.SafeUnder fr.Keeps fr.next J Ξ T Q R n W g h t

/-- Safety at every admitted assignment, from every call. -/
def FramedSafeClause (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  ∀ η, r.Admits η → ∀ n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    fr.Call n W h (gotoOf r.program r.start L d r.comp) →
    ∀ g, fr.start n W h (gotoOf r.program r.start L d r.comp) g →
    SafeFramed fr (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) n W g h (gotoOf r.program r.start L d r.comp)

/-- Within the claimed footprint, and returning fresh where promised. -/
def FramedFootprintClause (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
    ∀ η n W h (L : List Tm) (d : Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h → RootsOk W (envOf L d) →
      (∀ v ∈ L, isVal v = true) → isVal d = true →
      fr.Call n W h (gotoOf r.program r.start L d r.comp) →
      ∀ g, fr.start n W h (gotoOf r.program r.start L d r.comp) g →
      SafeFramed fr (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
        (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
        (HeapObservations.WPost.lift fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
        (HeapObservations.WExc.lift fun h' => r.onThrow = true → r.footprint.Holds h h') n W g h
        (gotoOf r.program r.start L d r.comp)

/-- Meeting the stated postcondition. -/
def FramedEnsuresClause (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  r.ensures ≠ [] → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    fr.Call n W h (gotoOf r.program r.start L d r.comp) →
    ∀ g, fr.start n W h (gotoOf r.program r.start L d r.comp) g →
    SafeFramed fr (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (HeapObservations.WPost.lift fun h' v => GraphCode.EnsuresAt r.ensures ⟨envOf L d, h⟩ h' (push v (envOf L d)))
      (fun _ _ _ => True) n W g h (gotoOf r.program r.start L d r.comp)

/-- Within the stated regional bound. -/
def FramedRegionalClause (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  ∀ Φ regions, r.regional = some (Φ, regions) → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    fr.Call n W h (gotoOf r.program r.start L d r.comp) →
    ∀ g, fr.start n W h (gotoOf r.program r.start L d r.comp) g →
    SafeFramed fr (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (HeapObservations.WPost.lift fun h' _ => Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      (HeapObservations.WExc.lift fun h' => r.stated.any (·.onThrow) = true →
        Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      n W g h (gotoOf r.program r.start L d r.comp)

/-- **A stated assertion at a state**: the state runs the code `P` at the
label `l` with the frame `envOf L' d'`, and `k` holds there, read from the
entry environment `ρ` and heap `h`. -/
def AssertedAt (P : Program) (assertions : List (Nat × HeapKnowledge.Knowledge)) (ρ : Env) (h : Heap)
    (h' : Heap) (t' : Tm) : Prop :=
  ∀ l k, (l, k) ∈ assertions → ∀ (L' : List Tm) (d' : Tm) (c' : ComponentTag),
    t' = gotoOf P l L' d' c' → HeapKnowledge.Holds k ⟨ρ, h⟩ (envOf L' d') h'

/-- Each stated assertion of the graph true at every state reached at its
label within the budget. -/
def FramedAssertionsClause (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  ∀ η, r.Admits η → ∀ n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    fr.Call n W h (gotoOf r.program r.start L d r.comp) →
    ∀ g, fr.start n W h (gotoOf r.program r.start L d r.comp) g →
    SafeFramed fr (AssertedAt r.program r.assertions (envOf L d) h) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) n W g h (gotoOf r.program r.start L d r.comp)

/-- Each stated assertion of each code's graph true at every state reached
at its label within the budget, from every call meeting its signature, the
code's frames tagged `comp`, whatever the code's results and throws. -/
def FramedCodeAssertionsClause (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  ∀ ci q, r.codes[ci]? = some q → ∀ η n W h (L : List Tm) (d : Tm) (comp : ComponentTag),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) (codeRequest r q).inputs {}
      (codeRequest r q).entryIndices (envOf L d) n W h →
    RootsOk W (envOf L d) →
    fr.Call n W h (gotoOf (codeRequest r q).program (codeRequest r q).start L d comp) →
    ∀ g, fr.start n W h (gotoOf (codeRequest r q).program (codeRequest r q).start L d comp) g →
    SafeFramed fr (AssertedAt (codeRequest r q).program (codeHintsAt r ci).requirements (envOf L d) h)
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ => True) n W g h
      (gotoOf (codeRequest r q).program (codeRequest r q).start L d comp)

/-- **A request is safe under a client frame**: each clause of
`RequestSafe`, at each call, along the executions in which code outside the
frame's component keeps its client obligation. -/
def FramedRequestSafe (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) : Prop :=
  FramedSafeClause r fr ∧ FramedFootprintClause r fr ∧ FramedEnsuresClause r fr ∧ FramedRegionalClause r fr ∧
    FramedAssertionsClause r fr ∧ FramedCodeAssertionsClause r fr

/-! ### The main graph at framed returns

The draft's route to the five main-graph clauses of `FramedRequestSafe`
("The theorems"): the graph theorem at framed returns (`RunSoundFramed`)
gives each clause as safety at framed returns (`SafeRet`) of the term that
runs the request's graph, from every entry meeting its contracts, for the
framed nodes `F` and the returns `Ret`, `RetE` the check reads at them; the
returns at reached executions (`ret_reached`) give an invariant on which
every step keeping the frame's obligation meets those returns. -/

/-- **The main graph's clauses at framed returns** (`RunSoundFramed`'s
conclusion for the request): safety, the footprint, the postcondition, the
regional bound and the assertions, each as `SafeRet` of the term that runs
the request's graph from its entry, no evaluation pending. -/
def FramedReturnsGuarantee (r : SourceRequest σ ι) (F : Nat → Bool) (Ret RetE : Nat → Env → Heap → Heap → Prop) :
    Prop :=
  (∀ η, r.Admits η → ∀ n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    HeapObservations.SafeRet (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) F Ret RetE n W none h (gotoOf r.program r.start L d r.comp)) ∧
  (r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
    ∀ η n W h (L : List Tm) (d : Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h → RootsOk W (envOf L d) →
      (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafeRet (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
        (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
        (HeapObservations.WPost.lift fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
        (HeapObservations.WExc.lift fun h' => r.onThrow = true → r.footprint.Holds h h') F Ret RetE n W none h
        (gotoOf r.program r.start L d r.comp)) ∧
  (r.ensures ≠ [] → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    HeapObservations.SafeRet (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (HeapObservations.WPost.lift fun h' v => GraphCode.EnsuresAt r.ensures ⟨envOf L d, h⟩ h' (push v (envOf L d)))
      (fun _ _ _ => True) F Ret RetE n W none h (gotoOf r.program r.start L d r.comp)) ∧
  (∀ Φ regions, r.regional = some (Φ, regions) → ∀ η n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    HeapObservations.SafeRet (fun _ _ => True) (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (HeapObservations.WPost.lift fun h' _ => Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      (HeapObservations.WExc.lift fun h' => r.stated.any (·.onThrow) = true →
        Footprints.ArgumentSpineRegionsWithin Φ regions (envOf L d) h h')
      F Ret RetE n W none h (gotoOf r.program r.start L d r.comp)) ∧
  (∀ η, r.Admits η → ∀ n W h (L : List Tm) (d : Tm),
    EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
      (envOf L d) n W h → RootsOk W (envOf L d) →
    HeapObservations.SafeRet (AssertedAt r.program r.assertions (envOf L d) h)
      (excOf (reassign (RequestJson.graph r.toRequest) η))
      (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
      (fun _ _ _ _ => True) (fun _ _ _ => True) F Ret RetE n W none h (gotoOf r.program r.start L d r.comp))

/-- **The returns at reached executions, at their worlds**: an invariant
of the frame's history, the pending framed evaluation, the world and the
state, holding at every call of the request the frame's claim is about,
on which every step keeping the frame's obligation at the state's world,
to a world `U` the step's safety admits and a heap it types, meets the
returns `Ret`, `RetE` at the framed nodes `F`, and leaves a state meeting
it at `U` where the term after the step is valid at `U`. -/
def FramedReturnsReachedW (r : SourceRequest σ ι) (fr : ClientFrame (Ty ι)) (F : Nat → Bool)
    (Ret RetE : Nat → Env → Heap → Heap → Prop) : Prop :=
  ∃ I : Verification.TolerantFrames.ReadOnly.Ghost (fr.F.at fr.C) → Option (Nat × Heap) → (k : Nat) → WorldT k → Heap → Tm → Prop,
    (∀ η n W h (L : List Tm) (d : Tm),
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h → RootsOk W (envOf L d) →
      fr.Call n W h (gotoOf r.program r.start L d r.comp) →
      ∀ g, fr.start n W h (gotoOf r.program r.start L d r.comp) g →
        I g none n W h (gotoOf r.program r.start L d r.comp)) ∧
    (∀ g p (k : Nat) (W : WorldT (k + 1)) h t (U : WorldT k) h' t', I g p (k + 1) W h t → Step h t h' t' →
      WExt (trunc k (Nat.le_succ k) W) U → WorldAdm U → HeapOk k U h' → fr.Keeps g (k + 1) W h t h' t' →
      HeapObservations.RetAt Ret RetE p h' t t' ∧ (RefsOk U t' → I (fr.next g h t h' t') (HeapObservations.framedPend F p h t t') k U h' t'))

end

/-! ## A unit's members -/

/-- **A member is safe**: its plan crosses the exhaustive certification
boundary (`FunctionPlan.certify`), and the request of the certified plan is
safe: a graph plan's for every execution (`RequestSafe`), a framed plan's
under its frame's client obligation (`FramedRequestSafe`). -/
def MemberSafe (f : FilePlans) (i : Nat) : Prop :=
  ∃ p c, f.plans[i]? = some (.ok p) ∧ p.certify = .ok c ∧
    match c with
    | .graph _ _ r => RequestSafe r
    | .framed _ _ r spec => FramedRequestSafe r (spec.frame r)

/-- **A unit is safe**: every member of its group is. -/
def PassUnitSafe (f : FilePlans) (i : Nat) : Prop :=
  ∀ j ∈ f.fr.group i, MemberSafe f j

end Verification.SourceClaimJson.PassUnit
