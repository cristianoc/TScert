import Verification.Programs.TolerantFramesDriverExits

/-! # Tolerant frames: the rest of a visit's facts from its parts

A visit that returns ran its entry, step and exits (`VisitParts`). Its
exits' fold (`visitExits_fold`, `ExitsFold`) gives the frame, the states
that came in, the edges, the in-degrees, the queue and the arrays' sizes
of `VisitRest`, where every exit's target has a claim (`EnvFacts.claimed`)
and the pushed states meet `PushOk` (`ExitsPushOk`); the entry gives the
merge's counter where a node other than a head has no given state
(`EnvFacts.given`, `visitEntry_merge`). With the step's fresh counter not
below the visit's (`StepFresh`) and the visited label settled
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

variable (ι) in
/-- **(Named hypothesis) The step's fresh counter is not below the
visit's.** -/
def StepFresh : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ l rest en sd ex,
    VisitParts c env σ l rest en sd ex → σ.fresh ≤ sd.fresh

variable (ι) in
/-- **(Named hypothesis) The visited label is settled** in the state the
visit returns, where it is no exit of its own other than a head. -/
def VisitsSettle : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ l rest en sd ex,
    VisitParts c env σ l rest en sd ex → (envHead env l = false → l ∉ exitsOf env l) →
      SettledCore c (envHead env) env.deadArr.toList (visitResult { σ with queue := rest } l en sd ex) l

/-- **(`visitsRest_of`) Every visit gives `VisitRest`** where the pushed
states meet `PushOk`, the step's counter does not go down and the visited
label is settled: the rest is the exits' fold (`visitExits_fold`) and the
entry's merge (`visitEntry_merge`). -/
theorem visitsRest_of (hp : ExitsPushOk ι) (hf : StepFresh ι) (hs : VisitsSettle ι) : VisitsRest ι := by
  intro G I c env σ0 σ σ'' l rest hsetup hE hI hq hv
  obtain ⟨en, sd, ex, he, hst, hx, rfl⟩ := visit_ok hv
  have hP : VisitParts c env σ l rest en sd ex := ⟨⟨σ0, hsetup⟩, hE, hI, hq, he, hst, hx⟩
  obtain ⟨acc0, a1, a2, a3, a4, a5, a6, hF⟩ := visitExits_fold hx
  have hL : (SinglePass.Exit.ofNode env.nodes[l]!).map (·.target.label) = exitsOf env l := exitLabels_ofNode _ _
  have hexits : ∀ t ∈ exitsOf env l, t < env.n := fun t ht => hE.claimed ▸ hF.claimed t (hL ▸ ht)
  have hln : l < σ.walk.labels.size := hI.size ▸ (hI.queue l (by rw [hq]; exact List.mem_cons_self ..)).1
  refine { exits := hexits, frame := ?_, pushes := ?_, edges := ?_, fresh := hf G I c env σ l rest en sd ex hP,
           degs := ?_, queue := ?_, settles := hs G I c env σ l rest en sd ex hP, mergeFresh := ?_, inSizes := ?_ }
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
