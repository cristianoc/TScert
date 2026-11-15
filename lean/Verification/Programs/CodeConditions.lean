import Verification.Programs.TypingBasics
import Verification.Semantics.ExceptionalPosts

/-! # What a code's body must establish

A code (a function body checked as graph code, `CodeEntry`) is given the
specification its signature states on both exits (the note *Tolerant
frames*, §6, rule Call read from the callee: the body's exits entail the
signature's). One computation decides what its run must establish
(`codeObligations`): its arity within its arguments, its signature's scope
at its arity (`Effect.belowRow`) and no precondition beyond its promise, every
postcondition the signature exports on either exit among those the body's
run establishes (`codeEstablished`, a consequence by membership), and the
closed bound of each exit the run is checked within (`CodeObligations.bound`).

A closed bound entails the requested frame: the frame of an exit is its
closed bound and the receiver entries its scope admits. An exit whose bound
is `⊤` asks nothing of the run, so with both exits at `⊤` and no fresh
result the run is given no bound; a pure body establishes the empty bound
on both exits by itself. Every consumer (the check of a unit's code
requests, the proposals, the diagnosis) reads these two projections,
`codeConditions` and `codeBound`; a module row's code is checked by the
same membership with its stated facts (`rowConditions`).

Membership is consequence (`Exits.exitPost_of_established`): a run within
each exit's class bound that establishes the fresh result and the facts
meets each exit at every admissible state it reaches, so a run meeting the
obligations is safe at the signature's exits (`exportsEstablished_sound`,
`codeObligations_sound`). -/
namespace Verification.ProgramTyping
open Verification CallEffects Parity

section
variable {ι : Type}

/-- **What a code's run must establish**: the closed bound of each exit,
and whether its normal result is fresh. -/
structure CodeObligations where
  bound : Option (Exits Footprints.Closed)
  freshResult : Bool
  deriving DecidableEq

/-- **The postconditions a code's run establishes**: the fresh result where
its bound states one, and the index facts `facts` a run is checked to return
with (a module row's stated postcondition). -/
def codeEstablished (fresh : Bool) (facts : List HeapKnowledge.IndexFact) : List FormulaSchema :=
  (if fresh then [.operation (.freshStore 0)] else []) ++ facts.map fun F => .operation (.fact .after 0 F)

/-- **What a run establishes holds at its exit** (proved): a fresh result
where it is checked for one, and each of `facts` at the call's positions. -/
theorem codeEstablished_holds {fresh : Bool} {facts : List HeapKnowledge.IndexFact} {ι : CallInstantiation}
    {arena : AssertionArena} {r : Tm} {args : List Tm} {v : Tm} {m : Nat} {s s' : TolerantFrames.IndexedHeap}
    (hf : fresh = true → Footprints.FreshAt s.h.length v)
    (he : ∀ F ∈ facts, F.HoldsAt ⟨callEnv r args, s.h⟩ (ensuresEnv v r args) s'.h) :
    ∀ F ∈ codeEstablished fresh facts, Parity.Holds arena (callState r args v m s s') (instantiateFormula ι F) := by
  intro F hF
  simp only [codeEstablished, List.mem_append, List.mem_map] at hF
  rcases hF with hF | ⟨G, hG, rfl⟩
  · cases hfr : fresh <;> rw [hfr] at hF
    · cases hF
    · rw [List.mem_singleton.mp hF]; exact hf hfr
  · exact he G hG

/-- **Membership in what a run establishes is consequence** (proved): an
exit of a schema whose every postcondition is among those a run establishes
(`codeEstablished`) holds at an admissible transition within the class bound
of its frame (`Footprint.classBound_sound`) at which the run established
them. -/
theorem Exits.exitPost_of_established {x : Exits ExitSchema} {c : Completion} {fresh : Bool}
    {facts : List HeapKnowledge.IndexFact} {r : Tm} {args : List Tm} {v : Tm} {s s' : TolerantFrames.IndexedHeap}
    (hadm : TolerantFrames.Admissible s s') (hb : (x.get c).frame.classBound.Holds s.h s'.h)
    (hm : (x.get c).ensures.all (· ∈ codeEstablished fresh facts) = true)
    (hf : fresh = true → Footprints.FreshAt s.h.length v)
    (he : ∀ F ∈ facts, F.HoldsAt ⟨callEnv r args, s.h⟩ (ensuresEnv v r args) s'.h) :
    x.exitPost c r args s s' v := by
  have hm' : ∀ F ∈ (x.get c).ensures, F ∈ codeEstablished fresh facts := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hm
  have hframe : Footprints.Post (x.get c).frame (callEnv r args) s.h s'.h := Footprints.Footprint.classBound_sound hb
  cases c <;>
  · refine ⟨⟨hadm, hframe⟩, ?_⟩
    simp only [Exits.atArity, Exits.map, Exits.get, ExitSchema.instantiate, List.mem_map]
    rintro _ ⟨F, hF, rfl⟩
    exact codeEstablished_holds hf he F (hm' F hF)

/-- **The closed bounds of a signature's two exits**: the class bound of
each exit's frame (`Footprint.classBound`), within which a run meets the
frame. -/
def exitBounds (e : Effect) : Exits Footprints.Closed :=
  e.schema.map fun q => q.frame.classBound

/-- **Whether a run establishes every postcondition a signature exports**,
given the facts `facts` it is checked to return with: each postcondition of
the normal exit among `codeEstablished` at its fresh result and `facts`,
none on the exceptional exit. -/
def exportsEstablished (e : Effect) (facts : List HeapKnowledge.IndexFact) : Bool :=
  e.schema.normal.ensures.all (· ∈ codeEstablished e.fresh facts) &&
    e.schema.exceptional.ensures.all (· ∈ codeEstablished false [])

/-- **A run that establishes what a signature exports meets the signature on
both exits** (proved): where every postcondition of each exit is among those
the run establishes (`exportsEstablished`), a run from a well-formed entry
returning within the normal exit's bound with its fresh result and the facts
`facts`, and throwing within the exceptional exit's bound, is safe at the
signature's exits (`Exits.exitPost_of_established` at every admissible state
it reaches, `SafePostExcV.weaken_reached`). -/
theorem exportsEstablished_sound {e : Effect} {facts : List HeapKnowledge.IndexFact}
    (hx : exportsEstablished e facts = true) {Ξ T : Fam} {r : Tm} {args : List Tm} {j : Nat} {U : WorldT j}
    {heap : Heap} {t : Tm} (hu : WorldAdm U) (hh : HeapOk j U heap)
    (hs : HeapObservations.SafePostExc Ξ T
      (fun h' v => (exitBounds e).normal.Holds heap h' ∧ (e.fresh = true → Footprints.FreshAt heap.length v) ∧
        ∀ F ∈ facts, F.HoldsAt ⟨callEnv r args, heap⟩ (ensuresEnv v r args) h')
      (fun h' => (exitBounds e).exceptional.Holds heap h') j U heap t) :
    HeapObservations.SafePostExcV Ξ T (e.schema.exitPostW .normal r args U heap)
      (e.schema.exitPostW .exceptional r args U heap) j U heap t := by
  simp only [exportsEstablished, Bool.and_eq_true] at hx
  obtain ⟨hn, hexc⟩ := hx
  refine SafePostExcV.weaken_reached hu hh ?_ ?_ (HeapObservations.SafePostExcV.iff_lift.mpr hs) <;>
    rintro s s' v rfl hW rfl hadm hp <;> cases eq_of_heq hW <;> rw [Exits.exitPostW_iff]
  · exact Exits.exitPost_of_established hadm hp.1 hn hp.2.1 hp.2.2
  · exact Exits.exitPost_of_established (fresh := false) (facts := []) hadm hp hexc (by simp) (by simp)

/-- **Whether a signature's frames read the heap at each location alone**
(`Region.atLocation`), on both exits. -/
def framesAtLocation (e : Effect) : Bool :=
  e.schema.normal.frame.all (·.1.atLocation) && e.schema.exceptional.frame.all (·.1.atLocation)

/-- **A signature whose run establishes what it exports, its frames reading
the heap at each location alone, carries its exits across an allocation
before the call** (proved, `Exits.allocStable_of`): each postcondition it
exports with no facts is a fresh result. -/
theorem allocStable_of_established {e : Effect} (hx : exportsEstablished e [] = true)
    (hf : framesAtLocation e = true) : e.schema.AllocStable := by
  simp only [exportsEstablished, framesAtLocation, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hx hf
  refine Exits.allocStable_of (fun c => ?_) (fun c F hF => ?_)
  · cases c
    · exact List.all_eq_true.mpr hf.1
    · exact List.all_eq_true.mpr hf.2
  · have hm : F ∈ codeEstablished e.fresh [] ∨ F ∈ codeEstablished false [] := by
      cases c
      · exact .inl (hx.1 F hF)
      · exact .inr (hx.2 F hF)
    rcases hm with hm | hm <;>
      simp only [codeEstablished, List.map_nil, List.append_nil] at hm <;>
      split at hm <;> simp_all

/-- **The closed bounds a code's run is checked within**: none where both
exits are `⊤` and the result is not fresh, or where a pure body states no
fresh result; both exits' bounds otherwise. -/
def runBounds (c : CodeEntry ι) : Option (Exits Footprints.Closed) :=
  if ((exitBounds c.row.effect).normal == .top && (exitBounds c.row.effect).exceptional == .top &&
      !c.row.effect.fresh) || (!c.row.effect.fresh && c.exprs.all Purity.pureTerm)
  then none else some (exitBounds c.row.effect)

/-- **The bound the run is given** (`RunBound`): both exits' closed bounds
and whether the result is fresh. -/
def codeRunBound (c : CodeEntry ι) : Option RunBound :=
  (runBounds c).map fun b => (b, c.row.effect.fresh)

/-- **The obligations of a code's run**: its arity within its arguments, its
signature's scope at its arity (`Effect.belowRow`), no precondition beyond
its promise, every postcondition its signature exports on either exit
established by its run (`exportsEstablished`), and its frames reading the
heap at each location alone (`framesAtLocation`, so that a body run after
allocating its rest meets them from the invocation's entry); then its run's
bounds and fresh result. -/
def codeObligations (c : CodeEntry ι) : Option CodeObligations :=
  if decide (c.arity ≤ c.row.arguments.length) && c.row.effect.belowRow c.arity && c.row.effect.requires.isNone &&
      exportsEstablished c.row.effect [] && framesAtLocation c.row.effect then
    some ⟨runBounds c, c.row.effect.fresh⟩
  else none

/-- A code's conditions: it has obligations. -/
def codeConditions (c : CodeEntry ι) : Bool := (codeObligations c).isSome

/-- The bound a code's run is given, from its obligations. -/
def codeBound (c : CodeEntry ι) : Option RunBound :=
  (codeObligations c).bind fun o => o.bound.map fun b => (b, o.freshResult)

theorem codeBound_eq {c : CodeEntry ι} (h : codeConditions c = true) : codeBound c = codeRunBound c := by
  unfold codeConditions at h
  unfold codeBound codeRunBound
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
  have ho' := ho
  unfold codeObligations at ho'
  split at ho'
  · cases ho'; rw [ho]; rfl
  · cases ho'

/-- **What the conditions give**: the arity, the scope, no precondition,
every exported postcondition established by the run, and the frames read at
each location alone. -/
theorem codeConditions_spec {c : CodeEntry ι} (h : codeConditions c = true) :
    c.arity ≤ c.row.arguments.length ∧ c.row.effect.belowRow c.arity = true ∧ c.row.effect.requires = none ∧
      exportsEstablished c.row.effect [] = true ∧ framesAtLocation c.row.effect = true := by
  unfold codeConditions at h
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
  unfold codeObligations at ho
  split at ho
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hc
    exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
  · cases ho

/-- **A code's obligations give its signature on both exits** (proved): a
run of a code with obligations `o` (`codeObligations`) from a well-formed
entry, returning within its normal exit's bound with a fresh result where
`o` asks one and throwing within its exceptional exit's bound, is safe at
the signature's exits (`exportsEstablished_sound`, no facts). -/
theorem codeObligations_sound {c : CodeEntry ι} {o : CodeObligations} (hc : codeObligations c = some o)
    {Ξ T : Fam} {r : Tm} {args : List Tm} {j : Nat} {U : WorldT j} {heap : Heap} {t : Tm}
    (hu : WorldAdm U) (hh : HeapOk j U heap)
    (hs : HeapObservations.SafePostExc Ξ T
      (fun h' v => (exitBounds c.row.effect).normal.Holds heap h' ∧
        (o.freshResult = true → Footprints.FreshAt heap.length v))
      (fun h' => (exitBounds c.row.effect).exceptional.Holds heap h') j U heap t) :
    HeapObservations.SafePostExcV Ξ T (c.row.effect.schema.exitPostW .normal r args U heap)
      (c.row.effect.schema.exitPostW .exceptional r args U heap) j U heap t := by
  have hc' := hc
  unfold codeObligations at hc'
  split at hc'
  · rename_i hx
    cases hc'
    simp only [Bool.and_eq_true] at hx
    exact exportsEstablished_sound (facts := []) hx.1.2 hu hh
      (HeapObservations.SafePostExc.weaken (fun _ _ hq => ⟨hq.1, hq.2, by simp⟩) (fun _ hq => hq) hs)
  · cases hc'

/-- **The conditions of a module row's code**: its arity within its
arguments, its signature's scope at its arity with its postcondition
(`Effect.belowRow`), no precondition beyond its promise, and every
postcondition its signature exports established by a run returning with the
signature's own facts (`exportsEstablished`). -/
def rowConditions (c : CodeEntry ι) : Bool :=
  decide (c.arity ≤ c.row.arguments.length) && c.row.effect.belowRow c.arity && c.row.effect.requires.isNone &&
    exportsEstablished c.row.effect c.row.effect.ensures

end

/-- **A run keeps the heap at least as long as a bound it starts above**,
on a normal return and on a throw. -/
theorem SafePostExc.grow {Ξ T : Fam} {Q : HeapObservations.Post} {R : Heap → Prop} {b : Nat} :
    ∀ {n W h t}, b ≤ h.length → HeapObservations.SafePostExc Ξ T Q R n W h t →
      HeapObservations.SafePostExc Ξ T (fun h' v => Q h' v ∧ b ≤ h'.length) (fun h' => R h' ∧ b ≤ h'.length)
        n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t hb hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨hth, hR⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hT, hQ, hb⟩)
    · exact .inl (.inr ⟨hth, hR, hb⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih (Nat.le_trans hb (Footprints.step_length_le step)) hs⟩

end Verification.ProgramTyping
