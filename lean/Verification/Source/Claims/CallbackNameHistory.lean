import Verification.Source.Claims.CallbackAllocationSpines

namespace Verification.SourceClaimJson.CallbackOrigins
open PointClaims ControlFlow CertificateProducer HeapObservations GraphCode

/-- The first completed allocation at a named site, retaining the exact
environment in which its literal captures were instantiated. -/
structure Birth where
  label : Nat
  allocation : Env
  value : Val
  before : Heap
  after : Heap
  node : Node
  steps : Nat

abbrev History := Nat → Option Birth

def denotes (history : History) (entry : Env) (inputs : Nat) : Origin → Val → Prop
  | .input i, v => i < inputs ∧ entry i = v
  | .allocated p, v => ∃ b, history p = some b ∧ b.value = v
  | _, _ => False

def slotsHold (history : History) (entry : Env) (inputs : Nat) (slots : Slots) (ρ : Env) : Prop :=
  ∀ i o, namedAt slots i = some o → denotes history entry inputs o (ρ i) ∧ isVal (ρ i) = true

def grows (old new : History) : Prop := ∀ p b, old p = some b → new p = some b

private theorem denotes_mono {old new entry inputs o v} (growth : grows old new)
    (holds : denotes old entry inputs o v) : denotes new entry inputs o v := by
  cases o with
  | allocated p => obtain ⟨b,atP,h⟩ := holds; exact ⟨b,growth _ _ atP,h⟩
  | input | read | other => exact holds

private theorem slots_mono {old new entry inputs slots ρ} (growth : grows old new)
    (holds : slotsHold old entry inputs slots ρ) : slotsHold new entry inputs slots ρ := by
  intro i o ho
  obtain ⟨h,hv⟩ := holds i o ho
  exact ⟨denotes_mono growth h,hv⟩

def Birth.Valid (P : Program) (b : Birth) : Prop :=
  P[b.label]? = some b.node ∧ allocates b.node.expression = true ∧
  Steps b.steps b.before (instantiate 0 b.allocation b.node.expression) b.after b.value ∧ isVal b.value = true

/-- Every recorded allocation still has the operand names it saw on entry. -/
def historyHolds (P : Program) (table : Table) (entry : Env) (inputs : Nat) (history : History) : Prop :=
  ∀ p b, history p = some b → b.label = p ∧ b.Valid P ∧
    slotsHold history entry inputs (table.at p) b.allocation

private def Past (P : Program) (history : History) (h : Heap) (s : State) : Prop :=
  ∀ p b, history p = some b → ∃ k, Execution P (k+1) b.before (.at p b.allocation) h s

private theorem snoc {P k h s h' s' h'' s''} (r : Execution P k h s h' s') (t : Transition P h' s' h'' s'') :
    Execution P (k+1) h s h'' s'' := by
  induction r with
  | refl => exact .next t .refl
  | next tr _ ih => exact .next tr (ih t)

private theorem past_snoc {P history h s h' s'} (past : Past P history h s) (t : Transition P h s h' s') :
    Past P history h' s' := by
  intro p b hb
  obtain ⟨k,path⟩ := past p b hb
  exact ⟨k+1,snoc path t⟩

private theorem steps_snoc {j h e h' e' h'' e''} (r : Steps j h e h' e') (t : Step h' e' h'' e'') :
    Steps (j+1) h e h'' e'' := by
  induction r with
  | refl => exact .next t .refl
  | next tr _ ih => exact .next tr (ih t)

private theorem eval_run {P l node before ρ j h t} (hn : P[l]? = some node)
    (steps : Steps j before (instantiate 0 ρ node.expression) h t) :
    Execution P (j+1) before (.at l ρ) h (.eval t ρ node.continuation node.handler) := by
  have lift {j h a h' b} (run : Steps j h a h' b) :
      Execution P j h (.eval a ρ node.continuation node.handler) h' (.eval b ρ node.continuation node.handler) := by
    induction run with
    | refl => exact .refl
    | next step _ ih => exact .next (.expr step) ih
  exact .next (.enter hn) (lift steps)

private theorem namedAt_bound {sl : Slots} {i o} (hn : namedAt sl i = some o) : i < sl.size := by
  apply Classical.byContradiction
  intro bad
  have outside := Nat.le_of_not_gt bad
  simp [namedAt,Array.getElem?_eq_none_iff.mpr outside] at hn

private def ready (P : Program) (table : Table) (l : Nat) := (table[l]?.join).isSome || P.length ≤ l

/-- Distinct allocation records occupy ordered intervals of the growing heap. -/
structure Chronology (history : History) (initial current : Nat) : Prop where
  growth : initial ≤ current
  interval : ∀ p b, history p = some b → initial ≤ b.before.length ∧ b.after.length ≤ current
  disjoint : ∀ p q a b, p ≠ q → history p = some a → history q = some b →
    a.after.length ≤ b.before.length ∨ b.after.length ≤ a.before.length

private theorem Chronology.extendTime {history initial lo hi} (time : Chronology history initial lo)
    (le : lo ≤ hi) : Chronology history initial hi :=
  ⟨Nat.le_trans time.growth le,fun p b hb => ⟨(time.interval p b hb).1,Nat.le_trans (time.interval p b hb).2 le⟩,
    time.disjoint⟩

private theorem stepGrowth {j h t h' t'} (r : Steps j h t h' t') : h.length ≤ h'.length := by
  induction r with
  | refl => exact Nat.le_refl _
  | next st _ ih => exact Nat.le_trans (Footprints.step_length_le st) ih

private theorem recordTime {old new initial before after l} (time : Chronology old initial before)
    (le : before ≤ after) (casesOf : ∀ p b, new p = some b → old p = some b ∨
      (p = l ∧ b.before.length = before ∧ b.after.length = after)) : Chronology new initial after := by
  refine ⟨Nat.le_trans time.growth le,?_,?_⟩
  · intro p b hb
    rcases casesOf p b hb with oldB | ⟨_,lo,hi⟩
    · exact (time.extendTime le).interval _ _ oldB
    · exact ⟨lo ▸ time.growth,Nat.le_of_eq hi⟩
  · intro p q a b ne ha hb
    rcases casesOf p a ha with oldA | ⟨rfl,loA,hiA⟩ <;> rcases casesOf q b hb with oldB | ⟨rfl,loB,hiB⟩
    · exact time.disjoint _ _ _ _ ne oldA oldB
    · exact .inl (loB ▸ (time.interval _ _ oldA).2)
    · exact .inr (loA ▸ (time.interval _ _ oldB).2)
    · exact (ne rfl).elim

def atHistory (P : Program) (table : Table) (entry : Env) (inputs mark : Nat) (l : Nat) (ρ : Env) (h : Heap) : Prop :=
  ∃ history, historyHolds P table entry inputs history ∧ Chronology history mark h.length ∧ Past P history h (.at l ρ) ∧
    ready P table l = true ∧ slotsHold history entry inputs (table.at l) ρ

private def NameInv (P : Program) (table : Table) (entry : Env) (inputs mark : Nat) (h : Heap) : State → Prop
  | .at l ρ => atHistory P table entry inputs mark l ρ h
  | .eval t ρ k x => ∃ (l : Nat) (node : Node) (history : History) (before : Heap) (j : Nat),
    P[l]? = some node ∧ node.continuation = k ∧ node.handler = x ∧
    Steps j before (instantiate 0 ρ node.expression) h t ∧ historyHolds P table entry inputs history ∧
    Chronology history mark before.length ∧ Past P history before (.at l ρ) ∧ Past P history h (.eval t ρ k x) ∧
    ready P table l = true ∧ slotsHold history entry inputs (table.at l) ρ
  | .done _ | .raised _ => True

/-- One successful node expression may add a fresh binding to the history.
A previously bound allocation name would give a positive return to that site. -/
private theorem recordResult {P table entry inputs l node history before j h v ρ}
    (hn : P[l]? = some node) (steps : Steps j before (instantiate 0 ρ node.expression) h v)
    (hv : isVal v = true) (valid : historyHolds P table entry inputs history)
    (past : Past P history before (.at l ρ)) (slots : slotsHold history entry inputs (table.at l) ρ) :
    ∃ next, grows history next ∧ historyHolds P table entry inputs next ∧
      (∀ o, namedResult (namedSites P.toArray) (table.at l) l node.expression = some o → denotes next entry inputs o v) ∧
      ∀ p b, next p = some b → history p = some b ∨
        (p = l ∧ b.before = before ∧ b.after = h ∧ b.allocation = ρ) := by
  by_cases copy : ∃ i, node.expression = .var i
  · obtain ⟨i,he⟩ := copy
    refine ⟨history,fun _ _ hx => hx,valid,?_,fun _ _ hx => .inl hx⟩
    intro o ho
    obtain ⟨hi,vi⟩ := slots i o (by simpa only [he,namedResult] using ho)
    rw [he] at steps
    have eq := PromiseCalls.steps_value vi (by simpa [instantiate] using steps)
    rw [eq]
    exact hi
  · have action : namedResult (namedSites P.toArray) (table.at l) l node.expression =
        (if (namedSites P.toArray).getD l false && allocates node.expression then some (.allocated l) else none) := by
      cases he : node.expression <;> first | rfl | exact (copy ⟨_,he⟩).elim
    by_cases named : (namedSites P.toArray).getD l false && allocates node.expression
    · have both := Bool.and_eq_true_iff.mp named
      have free : history l = none := by
        cases hb : history l with
        | none => rfl
        | some b =>
          obtain ⟨n,cycle⟩ := past _ _ hb
          exact (namedSite_no_return both.1 cycle).elim
      let birth : Birth := ⟨l,ρ,v,before,h,node,j⟩
      let next : History := fun p => if p = l then some birth else history p
      have grow : grows history next := by
        intro p b atP
        by_cases same : p = l
        · subst p; simp [free] at atP
        · simpa [next,same] using atP
      refine ⟨next,grow,?_,?_,?_⟩
      · intro p b atP
        by_cases same : p = l
        · subst p
          simp [next] at atP
          subst b
          exact ⟨rfl,⟨hn,both.2,steps,hv⟩,slots_mono grow slots⟩
        · have old := valid p b (by simpa [next,same] using atP)
          exact ⟨old.1,old.2.1,slots_mono grow old.2.2⟩
      · intro o ho
        simp only [action,ite_eq_left named,Option.some.injEq] at ho
        subst o
        exact ⟨birth,by simp [next],rfl⟩
      · intro p b atP
        by_cases same : p = l
        · subst p
          simp [next] at atP
          subst b
          exact .inr ⟨rfl,rfl,rfl,rfl⟩
        · exact .inl (by simpa [next,same] using atP)
    · refine ⟨history,fun _ _ hx => hx,valid,?_,fun _ _ hx => .inl hx⟩
      intro o ho
      simp only [action,ite_eq_right named,reduceCtorEq] at ho

private theorem atNodeChecks {P : Program} {start inputs table l node}
    (check : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (hn : P[l]? = some node) (active : ready P table l = true) :
    let slots := table.at l
    let normal := sourceName slots (pushes node.continuation) (namedResult (namedSites P.toArray) slots l node.expression)
    let edge := fun src (t : Target) => ready P table t.label && checkNameEdge table src t
    (successors node.continuation).all (edge normal) = true ∧
      node.handler.toList.all (edge (sourceName slots true none)) = true := by
  have inside := (List.getElem?_eq_some_iff.mp hn).1
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp check).2 l
    (List.mem_range.mpr (by simpa using inside))
  unfold ready at active
  simp only [Nat.not_le_of_gt inside,decide_false,Bool.or_false] at active
  obtain ⟨slots,hs⟩ := Option.isSome_iff_exists.mp active
  have atSlots : table.at l = slots := by
    unfold Table.at
    cases hx : table[l]? with
    | none => simp [hx] at hs
    | some row => simp only [hx, Option.join_some] at hs; simp [Array.getD_eq_getD_getElem?,hx,hs]
  simp only [hs,List.size_toArray,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,List.getElem?_toArray,
    hn,Option.getD_some,Bool.and_eq_true] at h
  simpa only [ready,atSlots] using h

private theorem mapNames {table src target history entry inputs} {ρ : Env}
    (check : checkNameEdge table src target = true)
    (holds : ∀ i o, src i = some o → denotes history entry inputs o (ρ i) ∧ isVal (ρ i) = true) :
    slotsHold history entry inputs (table.at target.label) (mapEnv target.mapping ρ) := by
  intro i o ho
  have edge := List.all_eq_true.mp check i (List.mem_range.mpr (namedAt_bound ho))
  rw [ho] at edge
  exact holds _ o (by simpa using edge)

private theorem pushedNames {history entry inputs slots ρ value v}
    (hs : slotsHold history entry inputs slots ρ)
    (val : ∀ o, value = some o → denotes history entry inputs o v ∧ isVal v = true) (pushed : Bool) :
    ∀ i o, sourceName slots pushed value i = some o →
      denotes history entry inputs o ((if pushed then push v ρ else ρ) i) ∧
        isVal ((if pushed then push v ρ else ρ) i) = true := by
  cases pushed
  · exact hs
  · intro i
    cases i with
    | zero => exact val
    | succ j => exact hs j

private theorem normalNames {P : Program} {table entry inputs start h t ρ k x target}
    (check : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (inv : NameInv P table entry inputs mark h (.eval t ρ k x)) (hv : isVal t = true)
    (edge : target ∈ successors k)
    (tr : Transition P h (.eval t ρ k x) h (.at target.label (mapEnv target.mapping (if pushes k then push t ρ else ρ)))) :
    atHistory P table entry inputs mark target.label (mapEnv target.mapping (if pushes k then push t ρ else ρ)) h := by
  obtain ⟨l,node,history,before,j,hn,rfl,rfl,steps,valid,time,past0,past,active,slots⟩ := inv
  obtain ⟨next,growth,valid',result,keep⟩ := recordResult hn steps hv valid past0 slots
  have edgeOK := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (atNodeChecks check hn active).1 target edge)
  refine ⟨next,valid',recordTime time (stepGrowth steps) (fun p b hb => (keep p b hb).imp_right fun e => ⟨e.1,congrArg List.length e.2.1,congrArg List.length e.2.2.1⟩),?_,edgeOK.1,mapNames edgeOK.2 (pushedNames (slots_mono growth slots)
    (fun o ho => ⟨result o ho,hv⟩) _)⟩
  intro p b hb
  rcases keep p b hb with old | ⟨rfl,hb,_,hρ⟩
  · exact past_snoc past tr p b old
  · rw [hb,hρ]
    exact ⟨j+1,snoc (eval_run hn steps) tr⟩

private theorem nameStep {P : Program} {start inputs table entry h st h' st'}
    (check : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (inv : NameInv P table entry inputs mark h st) (tr : Transition P h st h' st') :
    NameInv P table entry inputs mark h' st' := by
  cases tr with
  | enter hn =>
    obtain ⟨hi,valid,time,past,active,slots⟩ := inv
    exact ⟨_,_,hi,_,0,hn,rfl,rfl,.refl,valid,time,past,past_snoc past (.enter hn),active,slots⟩
  | expr step =>
    obtain ⟨l,node,hi,before,j,hn,hk,hx,steps,valid,time,past0,past,active,slots⟩ := inv
    exact ⟨l,node,hi,before,j+1,hn,hk,hx,steps_snoc steps step,valid,time,past0,past_snoc past (.expr step),active,slots⟩
  | handle raised =>
    obtain ⟨l,node,hi,before,j,hn,hk,hx,steps,valid,time,past0,past,active,slots⟩ := inv
    have edge := (atNodeChecks check hn active).2
    rw [hx] at edge
    have ok := Bool.and_eq_true_iff.mp (List.all_eq_true.mp edge _ (List.mem_singleton_self _))
    exact ⟨hi,valid,time.extendTime (stepGrowth steps),past_snoc past (.handle raised),ok.1,mapNames ok.2 (pushedNames slots (by simp) true)⟩
  | ret | raise => trivial
  | bind hv => exact normalNames check inv hv (by simp [successors]) (.bind hv)
  | effect hv => exact normalNames check inv hv (by simp [successors]) (.effect hv)
  | yes | no | yesBind | noBind =>
    all_goals apply normalNames check inv rfl (by simp [successors])
    all_goals constructor
  | tagBind hv =>
    apply normalNames check inv hv _ (.tagBind hv)
    simp only [successors,List.mem_cons]
    split <;> simp

theorem checkedNames_reached {P : Program} {table entry inputs start h₀ h l ρ k}
    (check : checkNames P.toArray (namedSites P.toArray) start inputs table = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (run : Execution P k h₀ (.at start entry) h (.at l ρ)) :
    atHistory P table entry inputs h₀.length l ρ h := by
  have keep {j h st h' st'} (r : Execution P j h st h' st') :
      NameInv P table entry inputs h₀.length h st → NameInv P table entry inputs h₀.length h' st' := by
    induction r with
    | refl => exact id
    | next tr _ ih => exact fun inv => ih (nameStep check inv tr)
  have init := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp check).1
  apply keep run
  refine ⟨fun _ => none,by intro _ _ hh; contradiction,⟨Nat.le_refl _,by intros; contradiction,by intros; contradiction⟩,by intro _ _ hh; contradiction,init.1,?_⟩
  intro i o ho
  have hx := List.all_eq_true.mp init.2 i (List.mem_range.mpr (namedAt_bound ho))
  rw [ho] at hx
  simp only [Option.all_some,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hx
  obtain ⟨bound,rfl⟩ := hx
  exact ⟨⟨bound,rfl⟩,values i bound⟩

end Verification.SourceClaimJson.CallbackOrigins

namespace Verification.SourceClaimJson.CallbackOrigins
open ControlFlow HeapObservations

/-- Interpret all caller inputs and all allocated named objects from one
history. Unallocated names carry no operand equality obligation. -/
def historyEnv (entry : Env) (inputs : Nat) (history : History) : Env := fun j =>
  if j < inputs then entry j else ((history (j-inputs)).map (·.value)).getD .undef

theorem allocatedFrame {P table entry inputs history l b} (valid : historyHolds P table entry inputs history)
    (found : history l = some b) :
    b.label = l ∧ b.Valid P ∧ slotsHold history entry inputs (table.at l) b.allocation := valid l b found

/-- A completed literal allocation retains the exact code and its instantiated
captures, including when field initializers require intermediate steps. -/
theorem literalBirth {P b} (valid : Birth.Valid P b)
    {arity exprs conts start caps kind rest comp fields args}
    (literal : b.node.expression = .makeAt (.graph arity exprs conts start caps kind rest comp) fields args) :
    ∃ fs oid, b.value = .objAt fs (.graph arity exprs conts start
      (instantiateArgs 0 b.allocation caps) kind rest comp) oid := by
  obtain ⟨_,_,run,value⟩ := valid
  rw [literal] at run
  simp only [instantiate] at run
  generalize he : CallCode.graph arity exprs conts start (instantiateArgs 0 b.allocation caps) kind rest comp = code at run ⊢
  have preserve {j h u h' v} (r : Steps j h u h' v) :
      (∃ ns as, u = .makeAt code ns as) ∨ (∃ fs oid, u = .objAt fs code oid) →
      (∃ ns as, v = .makeAt code ns as) ∨ (∃ fs oid, v = .objAt fs code oid) := by
    induction r with
    | refl => exact id
    | next tr _ ih =>
      intro pending
      apply ih
      rcases pending with ⟨ns,as,rfl⟩ | ⟨fs,oid,rfl⟩
      · cases tr with
        | makeArg => exact .inl ⟨_,_,rfl⟩
        | makeFields => exact .inr ⟨_,_,rfl⟩
      · exact (value_no_step (by cases code <;> rfl) tr).elim
  rcases preserve run (.inl ⟨_,_,rfl⟩) with ⟨ns,as,eq⟩ | result
  · rw [eq] at value
    contradiction
  · exact result

end Verification.SourceClaimJson.CallbackOrigins

namespace Verification.SourceClaimJson.CallbackOrigins
open Footprints

theorem inputSpinesBelow {n : Nat} {W : WorldT n} {h : Heap} {entry : Env}
    (roots : RootsOk W entry) (heap : HeapOk n W h) {i l}
    (spine : spineOf (entry i) = some l) : l < h.length := by
  have role := slotRole_of_refs (roots i) spine
  cases hr : roleAt W l with
  | none => rw [hr] at role; contradiction
  | some r =>
    have := roleAt_lt hr
    have len : h.length = (entries W).length := by simpa using heap.1.1
    omega

theorem historyNamesApart {P table entry inputs history mark current}
    (valid : historyHolds P table entry inputs history) (time : Chronology history mark current)
    (inputsBelow : ∀ i < inputs, ∀ l, spineOf (entry i) = some l → l < mark)
    {a b l} (different : a ≠ b) (oneNew : inputs ≤ a ∨ inputs ≤ b)
    (ha : spineOf (historyEnv entry inputs history a) = some l)
    (hb : spineOf (historyEnv entry inputs history b) = some l) : False := by
  have birthAt {j} (new : inputs ≤ j) (hj : spineOf (historyEnv entry inputs history j) = some l) :
      ∃ birth, history (j-inputs) = some birth ∧ birth.before.length ≤ l ∧ l < birth.after.length := by
    cases binding : history (j-inputs) with
    | none => simp [historyEnv, Nat.not_lt.mpr new, binding,spineOf,fieldsOf] at hj
    | some birth =>
      have spine : spineOf birth.value = some l := by simpa [historyEnv,Nat.not_lt.mpr new,binding] using hj
      obtain ⟨_,al,steps,value⟩ := (valid _ _ binding).2.1
      exact ⟨birth,rfl,allocationSpine_range al steps value spine⟩
  by_cases oldA : a < inputs <;> by_cases oldB : b < inputs
  · omega
  · have upper := inputsBelow a oldA l (by simpa [historyEnv,oldA] using ha)
    obtain ⟨birth,bind,low,_⟩ := birthAt (Nat.le_of_not_gt oldB) hb
    have := (time.interval _ _ bind).1
    omega
  · have upper := inputsBelow b oldB l (by simpa [historyEnv,oldB] using hb)
    obtain ⟨birth,bind,low,_⟩ := birthAt (Nat.le_of_not_gt oldA) ha
    have := (time.interval _ _ bind).1
    omega
  · obtain ⟨one,h1,lo,hi⟩ := birthAt (Nat.le_of_not_gt oldA) ha
    obtain ⟨two,h2,lo',hi'⟩ := birthAt (Nat.le_of_not_gt oldB) hb
    have order := time.disjoint _ _ _ _ (by omega) h1 h2
    omega

end Verification.SourceClaimJson.CallbackOrigins
