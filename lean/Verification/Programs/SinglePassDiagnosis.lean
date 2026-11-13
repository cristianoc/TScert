import Verification.Programs.SinglePass

/-! # The walk that names every lacking loop-head fact

The single pass stops at the first edge into a loop head that lacks one of
the head's given facts (`headExit`). Where those facts are proposals, each
lacking one costs a whole walk to find. The diagnosing walk is the same
walk (`visitEntry`, `visitStep`, `exitStep`) with one difference: an edge
into a head refused for lacking facts that `droppable` admits leaves them
out of the head's given state (`WalkEnv.given`), one refused for an
implication the head states leaves the head's implications out (with
`implied`), and the exit is taken again over the weaker state; the walk
goes on from there. Its result is what was left out, by head: facts, or
(`none`) the head's implications. The walk decides nothing: its verdict is
read by no check, and a member's verdict stays the pass's (`run`) at the
candidates the facts left out give. -/
namespace Verification.SinglePass
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open HeapKnowledge (Knowledge IndexAtom)

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- The head and the text of a refusal of an edge into a statement entry for
lacking facts (`headExit`'s wording). -/
def lacksIn (why : String) : Option (Nat × String) :=
  match why.splitOn "into statement entry " with
  | _ :: rest :: _ => match rest.splitOn ": lacks " with
    | t :: x :: _ => t.toNat?.map (·, x)
    | _ => none
  | _ => none

/-- The head of a refusal of an edge into a statement entry for an
implication it states (`headExit`'s wording). -/
def implicationIn (why : String) : Option Nat :=
  match why.splitOn "into statement entry " with
  | _ :: rest :: _ => match rest.splitOn ": an implication" with
    | t :: _ :: _ => t.toNat?
    | _ => none
  | _ => none

/-- The facts of `held` a lacks refusal's text names: each written as
`reprStr` writes it, inside the `reprStr` of a list of strings. -/
def namedIn (text : String) (held : List IndexAtom) : List IndexAtom :=
  held.filter fun a =>
    let s := reprStr (reprStr a)
    (text.splitOn ((s.drop 1).toString.dropEnd 1).toString).length > 1

/-- The head's given state without the facts `drop`. -/
def weakenedAt {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (drop : List IndexAtom) : WalkEnv ι G images :=
  match env.given[l]? with
  | some (some req) => { env with given := env.given.set! l (some { req with indices := req.indices.filter (!drop.contains ·) }) }
  | _ => env

/-- One exit (`exitStep`), an edge into a head lacking facts `droppable`
admits taken again with them left out of the head's state, or refused for
an implication the head states taken again without the head's
implications (with `implied`), at most `k` times: the walk's environment, the facts left out by head, and the exits'
record; or where it stopped. -/
def exitDiagnosed (G : NormalGraph ι) (images : InstanceImageCheck G) (droppable : Nat → List IndexAtom) (implied : Bool) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) (ysAll : List (PromiseCalls.Yield ι)) (outAll : Thunk Knowledge)
    (exi : Exit × Nat) :
    Nat → WalkEnv ι G images × List (Nat × Option (List IndexAtom)) × ExitsDone ι G →
      Except (WalkStop ι G) (WalkEnv ι G images × List (Nat × Option (List IndexAtom)) × ExitsDone ι G)
  | k, (env, dropped, acc) =>
    match exitStep G images env l en sd ysAll outAll acc exi with
    | .ok acc' => .ok (env, dropped, acc')
    | .error stop => match k, stop.outcome with
      | k + 1, .refused why => match lacksIn why with
        | some (t, text) =>
          let left := (dropped.filter (·.1 == t)).flatMap fun x => x.2.getD []
          let open_ := (droppable t).filter (!left.contains ·)
          match namedIn text open_ with
          | [] => .error stop
          | named => exitDiagnosed G images droppable implied l en sd ysAll outAll exi k
              (weakenedAt env t named, dropped ++ [(t, some named)], acc)
        | none => match implicationIn why with
          | some t =>
            if !implied || ((env.givenImplies[t]?).getD []).isEmpty then .error stop else
            exitDiagnosed G images droppable implied l en sd ysAll outAll exi k
              ({ env with givenImplies := env.givenImplies.set! t [] }, dropped ++ [(t, none)], acc)
          | none => .error stop
      | _, _ => .error stop

/-- A node's exits (`visitExits`), each diagnosed (`exitDiagnosed`). -/
def exitsDiagnosed (G : NormalGraph ι) (images : InstanceImageCheck G) (droppable : Nat → List IndexAtom) (implied : Bool)
    (env : WalkEnv ι G images) (dropped : List (Nat × Option (List IndexAtom))) (σ : WalkState ι G)
    (l : Nat) (en : Entered ι) (sd : StepDone ι G) :
    Except (WalkStop ι G) (WalkEnv ι G images × List (Nat × Option (List IndexAtom)) × ExitsDone ι G) :=
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  let (yields, answers) := exitsYields G images env l en sd
  let ysAll := yieldsAtSlots en.entry.names (yields.getD [])
  let outAll : Thunk Knowledge := Thunk.mk fun _ => outAllOf G c sd.st.stepOut
  let regional : Except String (Option (RegionalDone ι)) := match env.regional with
    | none => .ok none
    | some rg => (regionalAt G images env l en sd rg answers σ.regionIn).map some
  match regional with
  | .error why => .error (WalkStop.mk (.refused why) sd.counts answers sd.trace)
  | .ok regional =>
    let regionIn := match regional with
      | some r => r.regionIn
      | none => σ.regionIn
    let acc0 : ExitsDone ι G :=
      { incoming := σ.walk.incoming, incomingImpl := σ.walk.incomingImpl, incomingEdges := σ.walk.incomingEdges,
        edges := σ.walk.edges, answers, counts := sd.counts, trace := sd.trace, indeg := σ.indeg, regionIn,
        incomingFrom := σ.incomingFrom, queue := σ.queue, unsat := σ.unsat, yields, regional }
    (Exit.ofNode node).zipIdx.foldlM (fun s exi =>
      exitDiagnosed G images droppable implied l en sd ysAll outAll exi (((droppable exi.1.target.label).length) + 2) s)
      (env, dropped, acc0)

/-- One node's visit (`visitBody`, `visit`), its exits diagnosed. -/
def visitDiagnosed (G : NormalGraph ι) (images : InstanceImageCheck G) (droppable : Nat → List IndexAtom) (implied : Bool)
    (env : WalkEnv ι G images) (dropped : List (Nat × Option (List IndexAtom))) (σ : WalkState ι G) (l : Nat) :
    Except (WalkStop ι G) (WalkEnv ι G images × List (Nat × Option (List IndexAtom)) × WalkState ι G) :=
  match visitEntry G images env σ l with
  | .error stop => .error stop
  | .ok en => match visitStep G images env σ l en with
    | .error stop => .error stop
    | .ok sd => match exitsDiagnosed G images droppable implied env dropped σ l en sd with
      | .error stop => .error stop
      | .ok (env, dropped, ex) =>
        .ok (env, dropped,
          { walk := { labels := σ.walk.labels.set! l (LabelWalk.ofVisit σ.fresh en sd (ex.regional.map (·.state))),
                      incoming := ex.incoming, incomingImpl := ex.incomingImpl, incomingEdges := ex.incomingEdges,
                      edges := ex.edges, visited := σ.walk.visited + 1 },
            answers := keepSummaries σ.answers ex.answers, counts := ex.counts, trace := ex.trace, indeg := ex.indeg,
            fresh := sd.fresh, regionIn := ex.regionIn, incomingFrom := ex.incomingFrom, queue := ex.queue,
            unsat := ex.unsat, lastStamp := en.lastStamp, lastKind := sd.lastKind })

/-- The walk on fuel (`drive`), each visit diagnosed: the facts left out by
head, up to where it ends or stops. -/
def driveDiagnosed (G : NormalGraph ι) (images : InstanceImageCheck G) (droppable : Nat → List IndexAtom) (implied : Bool) :
    Nat → WalkEnv ι G images → List (Nat × Option (List IndexAtom)) → WalkState ι G → List (Nat × Option (List IndexAtom))
  | 0, _, dropped, _ => dropped
  | fuel + 1, env, dropped, σ => match σ.queue with
    | [] => dropped
    | l :: rest => match visitDiagnosed G images droppable implied env dropped { σ with queue := rest } l with
      | .ok (env, dropped, σ') => driveDiagnosed G images droppable implied fuel env dropped σ'
      | .error _ => dropped

/-- **The diagnosing walk over one graph** (`runWalk`'s arguments): the
setup, then the visits each diagnosed (`driveDiagnosed`); the given facts
`droppable` admits that some edge into their head lacks, by head, each left
out where found. -/
def lackingFacts (G : NormalGraph ι) (images : InstanceImageCheck G) (droppable : Nat → List IndexAtom) (implied : Bool)
    (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List IndexAtom)) (entryIndices : List IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (bound : Option (Footprints.Closed × Bool × Bool))
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (ensures : List HeapKnowledge.IndexFact) (givenInputs : Array (List (Nat × Nat)))
    (entrySeparation : HeapSeparation.Separation) (regional : Option Regional) : List (Nat × Option (List IndexAtom)) :=
  match setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices
      suggestions known codes aliases passChecker answers #[] 1000000000 bound givenImplies givenArgs ensures
      givenInputs entrySeparation none false false regional with
  | .error _ => []
  | .ok (env, σ0) => driveDiagnosed G images droppable implied (env.n + 1) env [] σ0

end
end Verification.SinglePass
