import Verification.Programs.TolerantFramesDriverRecords
import Verification.Programs.TolerantFramesStoreOpsEdge

/-! # Tolerant frames: a visit's record from its parts

A visit that returns ran its entry, its step and its exits, and returns
the state `visitBody` builds from them, the read-summary table kept
(`visit_ok`, `visitResult`): the record changes at the visited label only,
counts it, keeps its size and, at a label below the size, marks it visited
(`visitResult_labels`, `visitResult_visits`, `visitResult_size`); so
`VisitsRecord` reduces to the rest of `VisitFacts` (`VisitRest`,
`VisitsRest`, `visitsRecord_of`). A state an exit carries into its
target (`edgeTransfer` over `edgeStoreOf`) has the target's width, a
well-formed store and is below the counter where the mapping reads the
source's slots and gives the target's width, the stores are well-formed
and below the counter, and so are the names (`pushOk_of_exit`). -/

namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Visit
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- The state a visit returns from its parts (`visitBody`): the exits'
arrays and threaded values, the label's record written once, the visited
count one more, the step's fresh counter and the read-summary table kept
(`visit`). -/
def visitResult (σ : SinglePass.WalkState ι G) (l : Nat) (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G)
    (ex : SinglePass.ExitsDone ι G) : SinglePass.WalkState ι G :=
  { walk := { labels := σ.walk.labels.set! l (SinglePass.LabelWalk.ofVisit σ.fresh en sd ex.region), incoming := ex.incoming,
              incomingImpl := ex.incomingImpl, incomingEdges := ex.incomingEdges, edges := ex.edges,
              visited := σ.walk.visited + 1 },
    answers := SinglePass.keepSummaries σ.answers ex.answers, counts := ex.counts, trace := ex.trace,
    indeg := ex.indeg, fresh := sd.fresh, regionIn := ex.regionIn, incomingFrom := ex.incomingFrom,
    queue := ex.queue, unsat := ex.unsat, lastStamp := en.lastStamp, lastKind := sd.lastKind }

theorem visit_ok {env : SinglePass.WalkEnv ι G I} {σ σ'' : SinglePass.WalkState ι G} {l : Nat}
    (h : SinglePass.visit G I env σ l = .ok σ'') :
    ∃ en sd ex, SinglePass.visitEntry G I env σ l = .ok en ∧ SinglePass.visitStep G I env σ l en = .ok sd ∧
      SinglePass.visitExits G I env σ l en sd = .ok ex ∧
      σ'' = visitResult σ l en sd ex := by
  unfold SinglePass.visit at h
  split at h
  · rename_i σb hb
    cases h
    unfold SinglePass.visitBody at hb
    split at hb
    · cases hb
    · rename_i en he
      split at hb
      · cases hb
      · rename_i sd hs
        split at hb
        · cases hb
        · rename_i ex hx
          cases hb
          exact ⟨en, sd, ex, he, hs, hx, rfl⟩
  · cases h

theorem visitResult_labels (σ : SinglePass.WalkState ι G) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (ex : SinglePass.ExitsDone ι G) {t : Nat} (ht : t ≠ l) :
    (visitResult σ l en sd ex).walk.labels[t]? = σ.walk.labels[t]? := by
  simp only [visitResult]
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm ht)]

theorem visitResult_size (σ : SinglePass.WalkState ι G) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (ex : SinglePass.ExitsDone ι G) :
    (visitResult σ l en sd ex).walk.labels.size = σ.walk.labels.size := by
  simp only [visitResult, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem visitResult_visits (σ : SinglePass.WalkState ι G) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (ex : SinglePass.ExitsDone ι G) (hl : l < σ.walk.labels.size) :
    visB (visitResult σ l en sd ex).walk l = true := by
  simp only [visB, visitResult, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hl]
  rfl

/-- **What a visit gives beyond its record's write** (`VisitFacts` but
`labels`, `visits`, `count` and `size`). -/
structure VisitRest (c : Target.RunCall G I) (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G)
    (l : Nat) (σ' : SinglePass.WalkState ι G) : Prop where
  exits : ∀ t ∈ exitsOf env l, t < env.n
  frame : ∀ t, t ∉ exitsOf env l → σ'.walk.incoming[t]? = σ.walk.incoming[t]? ∧
    σ'.walk.incomingImpl[t]? = σ.walk.incomingImpl[t]? ∧ σ'.walk.incomingEdges[t]? = σ.walk.incomingEdges[t]?
  pushes : ∀ t, ∃ ns nis, incS σ'.walk t = ns ++ incS σ.walk t ∧ incI σ'.walk t = nis ++ incI σ.walk t ∧
    ns.length = nis.length ∧ ∀ s ∈ ns, PushOk c t s σ'.fresh
  edges : ∃ new, σ'.walk.edges.toList = σ.walk.edges.toList ++ new ∧ ∀ e ∈ new, e.target.label ∈ exitsOf env l
  fresh : σ.fresh ≤ σ'.fresh
  degs : ∀ t < env.n, envHead env t = false → deg σ' t = deg σ t - (exitsOf env l).count t
  queue : ∃ new, σ'.queue = new ++ σ.queue ∧ (∀ t ∈ new, t ∈ exitsOf env l ∧ envHead env t = false ∧ deg σ' t = 0) ∧
    ((∀ t < env.n, envHead env t = false → (exitsOf env l).count t ≤ deg σ t) → new.Nodup)
  settles : (envHead env l = false → l ∉ exitsOf env l) → SettledCore c (envHead env) env.deadArr.toList σ' l
  mergeFresh : envHead env l = false → 2 ≤ (incS σ.walk l).length → passFresh σ'.walk l = σ.fresh
  inSizes : σ.walk.incoming.size = σ.walk.incomingImpl.size → σ'.walk.incoming.size = σ'.walk.incomingImpl.size
  impBelow : IncomingBelow σ.walk σ.fresh → IncomingBelow σ'.walk σ'.fresh
  extendsWalk : WalkExtends σ.walk σ'.walk

variable (ι) in
/-- **(Named hypothesis) Every visit gives `VisitRest`**, under
`VisitsRecord`'s premises. -/
def VisitsRest : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ0 (σ σ' : SinglePass.WalkState ι G)
    (l : Nat) (rest : List Nat), RunCall.setup c = .ok (env, σ0) → EnvFacts c env → RecInv c env σ →
    σ.queue = l :: rest → SinglePass.visit G I env { σ with queue := rest } l = .ok σ' →
    VisitRest c env { σ with queue := rest } l σ'

/-- **(`visitsRecord_of`) Every visit gives `VisitFacts`** where it gives
the rest (`VisitsRest`): the record's write at the visited label, below the
record's size by the invariant (`visit_ok`, `visitResult_labels`,
`visitResult_visits`, `visitResult_size`). -/
theorem visitsRecord_of (hr : VisitsRest ι) : VisitsRecord ι := by
  intro G I c env σ0 σ σ'' l rest hs hE hI hq hv
  have hR := hr G I c env σ0 σ σ'' l rest hs hE hI hq hv
  obtain ⟨en, sd, ex, -, -, -, rfl⟩ := visit_ok hv
  have hln : l < env.n := (hI.queue l (by rw [hq]; exact List.mem_cons_self ..)).1
  exact { exits := hR.exits,
          labels := fun t ht => visitResult_labels _ _ _ _ _ ht,
          visits := visitResult_visits _ _ _ _ _ (hI.size ▸ hln),
          count := rfl,
          size := visitResult_size _ _ _ _ _,
          frame := hR.frame, pushes := hR.pushes, edges := hR.edges, fresh := hR.fresh, degs := hR.degs,
          queue := hR.queue, settles := hR.settles, mergeFresh := hR.mergeFresh,
          inSizes := hR.inSizes, impBelow := hR.impBelow, extendsWalk := hR.extendsWalk }

/-- **A state an exit carries in meets `PushOk`** (`edgeTransfer_width`,
`edgeTransfer_wf`, `edgeStoreOf_wf`, `edgeTransfer_below`,
`edgeStoreOf_below`): the mapping giving the target's width over the
source's names (`mapNames_length`), the entry's and the step's stores
well-formed and below a positive counter `next`, the source's names, the
pushed names, the entry's fresh names and the result below it. -/
theorem pushOk_of_exit {c : Target.RunCall G I} {tl : Nat} {m : PointClaims.Mapping}
    {names pushedNames : List Nat} {pushed isHandler outFresh : Bool} {entry : SinglePass.State}
    {store : SinglePass.Store} {result width next : Nat} {Γ : List (ProgramTyping.Ty ι)}
    {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {implies : List (PromiseCalls.Implication ι)}
    (hw : match m with
      | none => names.length = (passCtx c tl).length
      | some slots => slots.length = (passCtx c tl).length ∧ ∀ j ∈ slots, j < names.length)
    (we : StoreWF entry.store) (ws : StoreWF store) (he : FactsBelow entry.store next) (hs : FactsBelow store next)
    (hpos : 0 < next) (hn : ∀ x ∈ names, x < next) (hp : ∀ x ∈ pushedNames, x < next)
    (hf : ∀ x ∈ entry.fresh, x < next) (hr : result < next) :
    PushOk c tl (SinglePass.edgeTransfer names m pushed isHandler outFresh entry result
      (SinglePass.edgeStoreOf G Γ entry.store store names pushedNames width pushed isHandler observed promote)
      implies).1 next :=
  ⟨edgeTransfer_width implies hw,
    edgeTransfer_wf (edgeStoreOf_wf we ws names pushedNames width pushed isHandler observed promote) implies,
    edgeTransfer_below hpos hn (edgeStoreOf_below we he hs hn hp width pushed isHandler observed promote) hf hr⟩

end Visit
end Verification.TolerantFrames
