import Verification.Programs.TolerantFramesDriverExitGrowth
import Verification.Programs.TolerantFramesExitVacuity

/-! # Tolerant frames: the rest of a visit's facts from its parts

A visit that returns ran its entry, step and exits (`VisitParts`). Its
exits' fold (`visitExits_fold`, `ExitsFold`) gives the frame, the states
that came in, the edges, the in-degrees, the queue and the arrays' sizes
of `VisitRest`, where every exit's target has a claim (`EnvFacts.claimed`)
and the pushed states meet `PushOk` (`ExitsPushOk`); the entry gives the
merge's counter where a node other than a head has no given state
(`EnvFacts.given`, `visitEntry_merge`); the step's fresh counter is not
below the visit's (`stepFresh`). With the visited label settled
(`VisitsSettle`), every visit gives `VisitRest` (`visitsRest_of`). -/

namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section VisitRest
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

omit [Labels ι] in
/-- A node's exits' targets are its successors (`nodeSucc`). -/
theorem exitLabels_ofNode (nodes : Array Node) (l : Nat) :
    (SinglePass.Exit.ofNode nodes[l]!).map (·.target.label) = SinglePass.nodeSucc nodes l := by
  unfold SinglePass.Exit.ofNode SinglePass.nodeSucc
  cases nodes[l]!.continuation <;> cases nodes[l]!.handler <;> simp [SinglePass.Exit.target, successors]

theorem envHead_eq (env : SinglePass.WalkEnv ι G I) (t : Nat) : envHead env t = env.isHead[t]! := by
  unfold envHead
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rfl

/-- **A node's entry that returns** (`visitEntry`): its merge, fresh
counter, state and implications those of `entryStart`, the state with a
written assertion's facts (`withStated`). -/
theorem visitEntry_merge {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} (h : SinglePass.visitEntry G I env σ l = .ok en) :
    en.merge = (SinglePass.entryStart G env σ l).merge ∧ en.fresh = (SinglePass.entryStart G env σ l).fresh ∧
      en.entry = SinglePass.withStated env l (SinglePass.entryStart G env σ l).base ∧
      en.implies = (SinglePass.entryStart G env σ l).implies := by
  unfold SinglePass.visitEntry at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩) | cases h

/-- **A node's checked step that returns** (`stepRun`): `checkedStep`
accepted at the node's claim from the entry state, the fresh counter and
the answers given. -/
theorem stepRun_ok {env : SinglePass.WalkEnv ι G I} {l : Nat} {entry : SinglePass.State} {fresh : Nat}
    {answers : Answered G} {counts : SinglePass.Counts} {trace : SinglePass.Trace} {ms : List Nat}
    {st : SinglePass.Stepped ι} {stats : SinglePass.StepStats} {a : Answered G}
    (h : SinglePass.stepRun G I env l entry fresh answers counts trace = .ok (ms, st, stats, a)) :
    SinglePass.checkedStep G I env.pool env.fuel env.suggestions env.index env.codes env.aliases env.passChecker
      env.undefTy l env.nodes[l]! env.claimed[l]! entry ms fresh answers = (.ok st, stats, a) := by
  unfold SinglePass.stepRun at h
  extract_lets node c at h
  split at h
  · cases h
  split at h
  · cases h
  extract_lets at h
  split at h
  rename_i stepped stats' a' heq
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hms, rfl, rfl, rfl⟩ := h
    subst hms
    exact heq
  · cases h

/-- **A node's step that returns** (`visitStep`): its checked step
(`stepRun`) from the entry's state and counter and the visit's answers,
the step's answers those it started from, its fresh counter the step's,
one more at a node with a handler. -/
theorem visitStep_ok {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} (h : SinglePass.visitStep G I env σ l en = .ok sd) :
    (∃ ms stats, SinglePass.stepRun G I env l en.entry en.fresh σ.answers en.counts en.trace =
        .ok (ms, sd.st, stats, sd.steppedAnswers)) ∧
      sd.stepAnswers = σ.answers ∧
      sd.fresh = (if (env.nodes[l]!).handler.isSome then sd.st.fresh + 1 else sd.st.fresh) := by
  unfold SinglePass.visitStep at h
  split at h
  · cases h
  rename_i ms st stats a hrun
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; exact ⟨⟨ms, stats, hrun⟩, rfl, rfl⟩) | cases h

/-- **A checked step's fresh counter is not below the one it started
from** (`checkedStep_ok`, `resultOf_cases`). -/
theorem checkedStep_fresh {pool fuel suggestions index codes aliases pc undefTy l} {node : Node} {c : PointClaim ι}
    {entry : SinglePass.State} {ms : List Nat} {fresh : Nat} {answers : Answered G} {st : SinglePass.Stepped ι}
    {stats : SinglePass.StepStats} {ans : Answered G}
    (h : SinglePass.checkedStep G I pool fuel suggestions index codes aliases pc undefTy l node c entry ms fresh
      answers = (.ok st, stats, ans)) : fresh ≤ st.fresh := by
  rcases checkedStep_ok h with ⟨_, -, -, -, hfr, -⟩ | ⟨-, _, _, _, -, -, ⟨_, _, -, -, -, hfresh, -⟩, -⟩
  · omega
  · rw [hfresh]
    rcases resultOf_cases node.expression entry.names fresh with ⟨_, -, -, hf⟩ | ⟨-, hf⟩ <;> omega

/-- **A node's entry's fresh counter is not below the walk's**: a head's
given state takes fresh names past it, a merge's counter grows where the
states that came in have the node's width, well-formed stores and are
below the walk's counter (`mergeState_wf`). -/
theorem entryStart_fresh {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    (hpreds : ∀ q ∈ σ.walk.incoming[l]!, q.names.length = (env.claimed[l]!).context.length ∧ StoreWF q.store ∧
      StateBelow q σ.fresh) :
    σ.fresh ≤ (SinglePass.entryStart G env σ l).fresh := by
  unfold SinglePass.entryStart
  generalize σ.walk.incoming[l]! = inc at hpreds ⊢
  split
  · dsimp only
    unfold SinglePass.headEntry
    dsimp only
    split <;> omega
  · split
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact (mergeState_wf (G := G) (edgesIn := σ.walk.incomingEdges[l]!) (List.cons_ne_nil _ _) (fun q hq => (hpreds q hq).1) (fun q hq => (hpreds q hq).2.1)
        (fun q hq => (hpreds q hq).2.2)).2.1

/-- **A visit's parts that returned**: the call's setup, the invariant at
the state the visit starts from (its queue `l :: rest`), the entry, the
step and the exits. -/
structure VisitParts (c : Target.RunCall G I) (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G)
    (l : Nat) (rest : List Nat) (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G)
    (ex : SinglePass.ExitsDone ι G) : Prop where
  setup : ∃ σ0, RunCall.setup c = .ok (env, σ0)
  facts : EnvFacts c env
  inv : RecInv c env σ
  queue : σ.queue = l :: rest
  entry : SinglePass.visitEntry G I env { σ with queue := rest } l = .ok en
  step : SinglePass.visitStep G I env { σ with queue := rest } l en = .ok sd
  exits : SinglePass.visitExits G I env { σ with queue := rest } l en sd = .ok ex

variable (ι) in
/-- **(Named hypothesis) Each state an exit pushes meets `PushOk`** at its
target and the step's fresh counter (by `pushOk_of_exit` from the step's
stores and names below its counter and the mapping's width). -/
def ExitsPushOk : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ l rest en sd ex,
    VisitParts c env σ l rest en sd ex → ∀ e ∈ SinglePass.Exit.ofNode env.nodes[l]!, ∀ imp,
      PushOk c e.target.label (exitPushed env l en sd e imp) sd.fresh

/-- **(`stepFresh`) The step's fresh counter is not below the visit's**:
the entry's is not (`entryStart_fresh`, the states that came in meeting
`PushOk` by the invariant), the checked step's is not below the entry's
(`checkedStep_fresh`), and a handler takes one more. -/
theorem stepFresh {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G}
    {l : Nat} {rest : List Nat} {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G}
    {ex : SinglePass.ExitsDone ι G} (hP : VisitParts c env σ l rest en sd ex) : σ.fresh ≤ sd.fresh := by
  obtain ⟨-, hen, -, -⟩ := visitEntry_merge hP.entry
  obtain ⟨⟨ms, stats, hrun⟩, -, hsf⟩ := visitStep_ok hP.step
  have hck := checkedStep_fresh (stepRun_ok hrun)
  have hln : l < env.n := (hP.inv.queue l (by rw [hP.queue]; exact List.mem_cons_self ..)).1
  have hctx : (env.claimed[l]!).context = passCtx c l := by
    unfold passCtx
    rw [hP.facts.claims, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    have hl : l < c.claims.toArray.size := by rw [← hP.facts.claims, hP.facts.claimed]; exact hln
    rw [Array.getElem?_eq_getElem hl, List.getElem?_eq_getElem (by simpa using hl)]
    simp
  have hes := entryStart_fresh (env := env) (σ := { σ with queue := rest }) (l := l) fun q hq => by
    have hp := hP.inv.push l q (by
      unfold incS
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at hq
      exact hq)
    exact ⟨hctx ▸ hp.1, hp.2.1, hp.2.2⟩
  have : σ.fresh ≤ en.fresh := hen ▸ hes
  rw [hsf]
  split <;> omega

variable (ι) in
/-- **(Named hypothesis) The visited label is settled** in the state the
visit returns, where it is no exit of its own other than a head. -/
def VisitsSettle : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ l rest en sd ex,
    VisitParts c env σ l rest en sd ex → (envHead env l = false → l ∉ exitsOf env l) →
      SettledCore c (envHead env) env.deadArr.toList (visitResult { σ with queue := rest } l en sd ex) l

/-- **(`visitsRest_of`) Every visit gives `VisitRest`** where the pushed
states meet `PushOk` and the visited label is settled: the rest is the exits' fold (`visitExits_fold`) and the
entry's merge (`visitEntry_merge`), with the incoming implication bound
provided by `hi` (`visitsImplications`). -/
theorem visitsRest_of (hp : ExitsPushOk ι) (hs : VisitsSettle ι)
    (hi : ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ l rest en sd ex,
      VisitParts c env σ l rest en sd ex →
      IncomingBelow (visitResult { σ with queue := rest } l en sd ex).walk sd.fresh) : VisitsRest ι := by
  intro G I c env σ0 σ σ'' l rest hsetup hE hI hq hv
  obtain ⟨en, sd, ex, he, hst, hx, rfl⟩ := visit_ok hv
  have hP : VisitParts c env σ l rest en sd ex := ⟨⟨σ0, hsetup⟩, hE, hI, hq, he, hst, hx⟩
  obtain ⟨acc0, a1, a2, a3, a4, a5, a6, hF⟩ := visitExits_fold hx
  have hL : (SinglePass.Exit.ofNode env.nodes[l]!).map (·.target.label) = exitsOf env l := exitLabels_ofNode _ _
  have hexits : ∀ t ∈ exitsOf env l, t < env.n := fun t ht => hE.claimed ▸ hF.claimed t (hL ▸ ht)
  have hln : l < σ.walk.labels.size := hI.size ▸ (hI.queue l (by rw [hq]; exact List.mem_cons_self ..)).1
  refine { exits := hexits, frame := ?_, pushes := ?_, edges := ?_, fresh := show σ.fresh ≤ sd.fresh from stepFresh hP,
           degs := ?_, queue := ?_, settles := hs G I c env σ l rest en sd ex hP, mergeFresh := ?_, inSizes := ?_,
           impBelow := fun _ => hi G I c env σ l rest en sd ex hP,
           extendsWalk := visitExits_extends hx hI.inSizes,
           vacuity := fun hc => visitExits_cachedVacuity hx hc,
           allocation := ⟨(visitExits_arraySizes hx).1, (visitExits_arraySizes hx).2.2⟩,
           incomingGrowth := fun t => by
             have hG := hF.incomingGrowth t
             rw [a1, hL] at hG
             exact hG }
  · intro t ht
    have := hF.frame t (hL ▸ ht)
    rw [a1, a2, a3] at this
    exact this
  · intro t
    obtain ⟨ns, nis, g1, g2, g3, g4⟩ := hF.pushes t
    refine ⟨ns, nis, ?_, ?_, g3 (by rw [a1, a2]; exact hI.inSizes), fun s hs => ?_⟩
    · unfold incS; rw [← a1]; exact g1
    · unfold incI; rw [← a2]; exact g2
    · obtain ⟨e, hemem, het, imp, rfl⟩ := g4 s hs
      have := hp G I c env σ l rest en sd ex hP e hemem imp
      rw [het] at this
      exact this
  · obtain ⟨new, n1, n2⟩ := hF.edges
    exact ⟨new, by rw [← a4]; exact n1, fun e he => hL ▸ n2 e he⟩
  · intro t _ hg
    have := hF.degs t (by rw [← envHead_eq]; exact hg)
    rw [a5, hL] at this
    exact this
  · obtain ⟨new, q1, q2, q3⟩ := hF.queue
    refine ⟨new, by rw [← a6]; exact q1, fun t ht => ?_, fun hc => q3 fun y hy => ?_⟩
    · obtain ⟨m1, m2, m3⟩ := q2 t ht
      exact ⟨hL ▸ m1, by rw [envHead_eq]; exact m2, m3⟩
    · rw [hL, a5]
      by_cases hyn : y < env.n
      · exact hc y hyn (by rw [envHead_eq]; exact hy)
      · have : (exitsOf env l).count y = 0 :=
          List.count_eq_zero.mpr fun hm => hyn (hexits y hm)
        rw [this]; exact Nat.zero_le _
  · intro hg h2
    obtain ⟨hm, -, -, -⟩ := visitEntry_merge he
    have hgiven := hE.given l (by rw [← envHead_eq]; exact hg)
    obtain ⟨a, b, rs, hab⟩ : ∃ a b rs, σ.walk.incoming[l]! = a :: b :: rs := by
      unfold incS at h2
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      match hh : (σ.walk.incoming[l]?).getD [], h2 with
      | a :: b :: rs, _ => exact ⟨a, b, rs, rfl⟩
    have hmerge : en.merge = some ((env.claimed[l]!).context, σ.fresh) := by
      rw [hm]
      unfold SinglePass.entryStart
      simp only [hgiven]
      exact (by rw [show ({ σ with queue := rest } : SinglePass.WalkState ι G).walk.incoming[l]! = a :: b :: rs from hab])
    unfold passFresh
    simp only [visitResult, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hln]
    simp [SinglePass.LabelWalk.ofVisit, hmerge]
  · intro _
    rw [show (visitResult { σ with queue := rest } l en sd ex).walk.incoming = ex.incoming from rfl,
      show (visitResult { σ with queue := rest } l en sd ex).walk.incomingImpl = ex.incomingImpl from rfl,
      hF.sizes.1, hF.sizes.2, a1, a2]
    exact hI.inSizes

end VisitRest
end Verification.TolerantFrames
