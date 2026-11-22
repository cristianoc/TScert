import Verification.Source.Claims.CallbackPrivateOrigins
import Verification.Source.Claims.CallbackPrivateOperands

namespace Verification.SourceClaimJson.CallbackInferencePlan
open PointClaims CallbackOrigins ControlFlow CertificateProducer GraphCode TolerantFrames TolerantFrames.Reach Footprints

def PrivateSlots (site field : Nat) (slots : Slots) (ρ : Env) : Prop :=
  (∀ i < slots.size, isVal (ρ i) = true) ∧ ∀ i, excludes site slots i = true → ¬Leaves allC (ρ i) field

private theorem excludes_bound {site slots i} (ok : excludes site slots i = true) : i < slots.size := by
  unfold excludes at ok
  cases h : slots[i]? with
  | none => simp [h] at ok
  | some v => exact (Array.getElem?_eq_some_iff.mp h).1

theorem cleanAtTerm {site field slots ρ h t}
    (clean : cleanReads site slots t = true) (vars : PrivateSlots site field slots ρ)
    (source : ObjectCoherence.sourceTerm t = true) (old : field < h.length) (heap : hiddenInHeap h field) :
    ¬ReachesFrom allC h (vals allC Realm.empty true false (instantiate 0 ρ t)) field := by
  unfold cleanReads at clean
  cases hx : SinglePass.mentioned 0 t with
  | none => simp [hx] at clean
  | some ids =>
    simp only [hx,Option.any_some,List.all_eq_true] at clean
    exact mentioned_hidden hx source old heap (fun i hi => ⟨vars.2 i (clean i hi),vars.1 i (excludes_bound (clean i hi))⟩)

private theorem readCompleted {h h' key receiver t v} (run : ValRun h (.readAt key receiver) h' t)
    (value : isVal receiver = true) (raises : Raises t v) : False := by
  generalize expr : Tm.readAt key receiver = u at run
  induction run generalizing receiver with
  | refl => cases expr; cases raises with | readC hr => exact Bool.noConfusion (value.symm.trans (raises_not_val hr))
  | step hh hs more ih =>
    subst_vars
    cases hs with
    | readC hs => exact value_no_step value hs
    | readProto _ _ lookup => exact ih (hh _ _ lookup) raises rfl
    | readField _ lookup =>

      cases more with
      | refl => exact Bool.noConfusion ((hh _ _ lookup).symm.trans (raises_not_val raises))
      | step _ step _ => exact value_no_step (hh _ _ lookup) step
    | readMissing _ _ =>

      cases more with
      | refl => cases raises
      | step _ step _ => exact value_no_step (by rfl) step

private def ExitPrivacy (site label field : Nat) (slots : Slots) (expr t : Tm) (after : Heap) :=
  (isVal t = true → hiddenInHeap after field ∧
    (resultClean site label slots expr = true → ¬Leaves allC t field)) ∧
  (∀ v, Raises t v → hiddenInHeap after field ∧ ¬Leaves allC v field)

private theorem termPrivacy {site label field slots ρ h h' expr t}
    (uses : privateUse site slots expr = true) (vars : PrivateSlots site field slots ρ)
    (source : ObjectCoherence.sourceTerm expr = true) (old : field < h.length) (heap : hiddenInHeap h field)
    (run : ValRun h (instantiate 0 ρ expr) h' t) : ExitPrivacy site label field slots expr t h' := by
  unfold privateUse at uses
  split at uses
  next i =>
    simp only [decide_eq_true_eq] at uses
    simp only [instantiate,Nat.not_lt_zero,↓reduceIte,Nat.sub_zero] at run
    cases run with
    | refl => exact ⟨fun _ => ⟨heap,vars.2 i⟩,fun v hr => Bool.noConfusion ((vars.1 i uses).symm.trans (raises_not_val hr))⟩
    | step _ hs _ => exact (value_no_step (vars.1 i uses) hs).elim
  next key i =>
    simp only [decide_eq_true_eq] at uses
    simp only [instantiate,Nat.not_lt_zero,↓reduceIte,Nat.sub_zero] at run
    refine ⟨fun val => ?_,fun _ hr => (readCompleted run (vars.1 i uses) hr).elim⟩
    obtain ⟨rfl,clean⟩ := readSlot_hidden run (vars.1 i uses) heap val
    exact ⟨heap,fun _ => clean⟩
  next key i rhs =>
    simp only [Bool.and_eq_true,decide_eq_true_eq] at uses
    simp only [ObjectCoherence.sourceTerm,Bool.true_and] at source
    simp only [instantiate,Nat.not_lt_zero,↓reduceIte,Nat.sub_zero] at run
    have exit := writeSlot_hidden run (vars.1 i uses.1) old heap (cleanAtTerm uses.2 vars source old heap)
    exact ⟨fun val => ⟨exit.1,fun _ => exit.2.1 val⟩,fun v hr => ⟨exit.1,exit.2.2 v hr⟩⟩
  next =>
    obtain ⟨keep,never⟩ := call_cannot_publish run old heap (cleanAtTerm uses vars source old heap)
    exact ⟨fun _ => ⟨keep,fun _ => valClean never⟩,fun v hr => ⟨keep,throwClean never hr⟩⟩

def PrivateAt (P : Program) (table : Table) (site field label : Nat) (ρ : Env) (h : Heap) :=
  privateReady P.toArray table label = true ∧ field < h.length ∧ hiddenInHeap h field ∧
    PrivateSlots site field (table.at label) ρ

def PrivateInv (P : Program) (table : Table) (site field : Nat) (h : Heap) : State → Prop
  | .at label ρ => PrivateAt P table site field label ρ h
  | .eval t ρ k x => ∃ (label : Nat) (node : Node) (before : Heap),
      P[label]? = some node ∧ node.continuation = k ∧ node.handler = x ∧
      PrivateAt P table site field label ρ before ∧ ValRun before (instantiate 0 ρ node.expression) h t
  | .done _ | .raised _ => True

theorem checkSiteAt {P : Program} {site table label node} (ok : checkPrivateSite P.toArray table site = true)
    (hn : P[label]? = some node) (active : privateReady P.toArray table label = true) :
    let slots := table.at label
    let clean := excludes site slots
    let valid := fun i => decide (i < slots.size)
    privateUse site slots node.expression = true ∧
      (successors node.continuation).all (cleanEdge P.toArray site table (afterSlot valid (pushes node.continuation) true)
        (afterSlot clean (pushes node.continuation) (resultClean site label slots node.expression))) = true ∧
      node.handler.toList.all (cleanEdge P.toArray site table (afterSlot valid true true) (afterSlot clean true true)) = true := by
  have inside := (List.getElem?_eq_some_iff.mp hn).1
  have found := List.all_eq_true.mp ok label (List.mem_range.mpr (by simpa using inside))
  simp only [privateReady,List.size_toArray,Nat.not_le_of_gt inside,decide_false,Bool.false_or] at active
  obtain ⟨row,hr⟩ := Option.isSome_iff_exists.mp active
  have actual : table.at label = row := by
    unfold Table.at
    cases hl : table[label]? with
    | none => simp [hl] at hr
    | some v => simp only [hl,Option.join_some] at hr; simp [Array.getD_eq_getD_getElem?,hl,hr]
  simp only [hr,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,List.getElem?_toArray,
    hn,Option.getD_some,Bool.and_eq_true] at found
  rw [actual]
  exact ⟨found.1.1,found.1.2,found.2⟩

theorem mappedPrivate {P : Program} {site field table slots ρ v pushed clean target}
    (checked : cleanEdge P.toArray site table (afterSlot (fun i => decide (i < slots.size)) pushed true)
      (afterSlot (excludes site slots) pushed clean) target = true)
    (vars : PrivateSlots site field slots ρ) (value : isVal v = true)
    (result : clean = true → ¬Leaves allC v field) :
    privateReady P.toArray table target.label = true ∧
    PrivateSlots site field (table.at target.label) (mapEnv target.mapping (if pushed then push v ρ else ρ)) := by
  obtain ⟨ready,edges⟩ := Bool.and_eq_true_iff.mp checked
  have access (i : Nat) (hi : i < (table.at target.label).size) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp edges i (List.mem_range.mpr hi))
  refine ⟨ready,?_,?_⟩
  · intro i hi
    have valid := (access i hi).1
    unfold mapEnv
    cases pushed
    · exact vars.1 _ (by simpa [afterSlot] using valid)
    · cases hj : PointClaims.slot target.mapping i with
      | zero => simpa [push,hj] using value
      | succ j => exact vars.1 _ (by simpa [afterSlot,hj] using valid)
  · intro i excluded
    have keep := (access i (excludes_bound excluded)).2
    simp only [excluded,Bool.not_true,Bool.false_or] at keep
    unfold mapEnv
    cases pushed
    · exact vars.2 _ (by simpa [afterSlot] using keep)
    · cases hj : PointClaims.slot target.mapping i with
      | zero => exact result (by simpa [afterSlot,hj] using keep)
      | succ j => exact vars.2 _ (by simpa [afterSlot,hj] using keep)

private theorem normalPrivate {P : Program} {table site field h t ρ k x edge}
    (checked : checkPrivateSite P.toArray table site = true)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (inv : PrivateInv P table site field h (.eval t ρ k x)) (val : isVal t = true)
    (chosen : edge ∈ successors k) : PrivateAt P table site field edge.label
      (mapEnv edge.mapping (if pushes k then push t ρ else ρ)) h := by
  obtain ⟨label,node,before,hn,rfl,rfl,⟨ready,old,heap,vars⟩,run⟩ := inv
  have checks := checkSiteAt checked hn ready
  have exit := (termPrivacy (label := label) checks.1 vars (List.all_eq_true.mp source _ (List.mem_of_getElem? hn)) old heap run).1 val
  obtain ⟨next,vars'⟩ := mappedPrivate (List.all_eq_true.mp checks.2.1 edge chosen) vars val exit.2
  exact ⟨next,Nat.lt_of_lt_of_le old run.length_le,exit.1,vars'⟩

private theorem valRunSnoc {h t h' t' h'' t''} (r : ValRun h t h' t')
    (values : ∀ (i : Nat) v, h'[i]? = some v → isVal v = true) (step : Step h' t' h'' t'') :
    ValRun h t h'' t'' := by
  induction r with
  | refl => exact .step values step .refl
  | step hh hs _ ih => exact .step hh hs (ih values step)

theorem privateStep {P : Program} {table site field h st h' st'} (checked : checkPrivateSite P.toArray table site = true)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (values : ∀ (i : Nat) v, h[i]? = some v → isVal v = true)
    (inv : PrivateInv P table site field h st) (tr : Transition P h st h' st') :
    PrivateInv P table site field h' st' := by
  cases tr with
  | enter hn => exact ⟨_,_,_,hn,rfl,rfl,inv,.refl⟩
  | expr hs =>
    obtain ⟨l,n,b,hn,hk,hx,vars,run⟩ := inv
    exact ⟨l,n,b,hn,hk,hx,vars,valRunSnoc run values hs⟩
  | handle raised =>
    obtain ⟨l,n,b,hn,hk,hx,⟨ready,old,heap,vars⟩,run⟩ := inv
    have checks := checkSiteAt checked hn ready
    have edges := checks.2.2
    rw [hx] at edges
    have exit := (termPrivacy (label := l) checks.1 vars (List.all_eq_true.mp source _ (List.mem_of_getElem? hn)) old heap run).2 _ raised
    obtain ⟨next,vars'⟩ := mappedPrivate (List.all_eq_true.mp edges _ (List.mem_singleton_self _)) vars (raises_val raised) (fun _ => exit.2)
    exact ⟨next,Nat.lt_of_lt_of_le old run.length_le,exit.1,vars'⟩
  | ret | raise => trivial
  | bind hv | effect hv => exact normalPrivate checked source inv hv (by simp [successors])
  | yes | no | yesBind | noBind => all_goals exact normalPrivate checked source inv rfl (by simp [successors])
  | tagBind hv => apply normalPrivate checked source inv hv; simp only [successors,List.mem_cons]; split <;> simp

/-- A checked private-origin table maintains nonpublication through the
concrete suffix after birth, including caught exceptions and loop edges.
Heap values are needed only at prefixes strictly shorter than this run. -/
theorem private_reached {P : Program} {table site field start ρ h l body h' k}
    (checked : checkPrivateSite P.toArray table site = true)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (run : Execution P k h (.at start ρ) h' (.at l body)) (initial : PrivateAt P table site field start ρ h)
    (values : ∀ j hj st, j < k → Execution P j h (.at start ρ) hj st →
      ∀ (i : Nat) v, hj[i]? = some v → isVal v = true) : PrivateAt P table site field l body h' := by
  have keep {k h st h' st'} (r : Execution P k h st h' st') (inv : PrivateInv P table site field h st)
      (hv : ∀ j hj s, j < k → Execution P j h st hj s → ∀ (i : Nat) v, hj[i]? = some v → isVal v = true) :
      PrivateInv P table site field h' st' := by
    induction r with
    | refl => exact inv
    | next tr _ ih =>
      exact ih (privateStep checked source (hv 0 _ _ (by omega) .refl) inv tr)
        (fun j hj s bound pre => hv (j+1) hj s (by omega) (.next tr pre))
  exact keep run initial values

/-- The actual call expression, including its instantiated captures,
receiver, and arguments, cannot reach a tracked private field. -/
theorem private_reached_invoke {P : Program} {table site field start ρ h l body h' k}
    (checked : checkPrivateSite P.toArray table site = true)
    (source : P.all (fun n => ObjectCoherence.sourceTerm n.expression) = true)
    (run : Execution P k h (.at start ρ) h' (.at l body)) (initial : PrivateAt P table site field start ρ h)
    (values : ∀ j hj st, j < k → Execution P j h (.at start ρ) hj st →
      ∀ (i : Nat) v, hj[i]? = some v → isVal v = true)
    {node fn receiver args} (atNode : P[l]? = some node) (invoke : node.expression = .invoke fn receiver args) :
    ¬ReachesFrom allC h' (vals allC Realm.empty true false (instantiate 0 body node.expression)) field := by
  obtain ⟨ready,old,heap,vars⟩ := private_reached checked source run initial values
  have reads := (checkSiteAt checked atNode ready).1
  rw [invoke] at reads
  exact cleanAtTerm (by simpa only [invoke,privateUse] using reads) vars
    (List.all_eq_true.mp source _ (List.mem_of_getElem? atNode)) old heap

end Verification.SourceClaimJson.CallbackInferencePlan
