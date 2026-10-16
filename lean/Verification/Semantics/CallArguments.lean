import Verification.Semantics.Bindings

/-! Call preparation keeps a callee and an ordered argument list separate from
invocation. It reuses the term machine for operand effects and connects prepared
list preparation and dispatch to native call reduction. Source calling conventions
remain integration work. -/
namespace Verification.CallArguments

/-- Only the leftmost non-value argument can step. Completed values are retained
in their original positions, including code objects with live heap captures. -/
inductive ArgStep : Heap → List Tm → Heap → List Tm → Prop where
  | head : Step h a h' a' → ArgStep h (a::args) h' (a'::args)
  | tail : isVal v = true → ArgStep h args h' args' →
      ArgStep h (v::args) h' (v::args')

def Values (args : List Tm) : Prop := ∀ a ∈ args, isVal a = true

/-- The leftmost non-value argument throws: the list's evaluation throws. -/
inductive ArgRaises : List Tm → Tm → Prop where
  | head : Raises a v → ArgRaises (a::args) v
  | tail : isVal w = true → ArgRaises args v → ArgRaises (w::args) v

/-- A throwing argument sits at a position with only values before it. -/
theorem ArgRaises.position {args : List Tm} {v : Tm} (h : ArgRaises args v) :
    ∃ (i : Nat) (a : Tm), args[i]? = some a ∧ (∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true) ∧
      Raises a v := by
  induction h with
  | @head a v rest hr => exact ⟨0, a, rfl, fun j hj => by omega, hr⟩
  | @tail w rest v hw _ ih =>
    obtain ⟨i, a, hg, hb, hr⟩ := ih
    refine ⟨i + 1, a, by simpa using hg, ?_, hr⟩
    intro j hj u hu
    cases j with
    | zero => simp at hu; exact hu ▸ hw
    | succ j => exact hb j (by omega) u (by simpa using hu)

theorem ArgRaises.invoke {f r : Tm} {args : List Tm} {v : Tm} (hf : isVal f = true)
    (hr : isVal r = true) (h : ArgRaises args v) : Raises (.invoke f r args) v := by
  obtain ⟨i, a, hg, hb, ha⟩ := h.position
  exact .callArg hf hr hg hb ha

theorem ArgRaises.construct {f : Tm} {args : List Tm} {v : Tm} (hf : isVal f = true)
    (h : ArgRaises args v) : Raises (.construct f args) v := by
  obtain ⟨i, a, hg, hb, ha⟩ := h.position
  exact .constructArg hf hg hb ha

theorem ArgRaises.make {c : CallCode} {ns : List PropKey} {args : List Tm} {v : Tm}
    (h : ArgRaises args v) : Raises (.makeAt c ns args) v := by
  obtain ⟨i, a, hg, hb, ha⟩ := h.position
  exact .makeArg hg hb ha

theorem ArgRaises.arrLit {args : List Tm} {v : Tm} (h : ArgRaises args v) :
    Raises (.arrLit args) v := by
  obtain ⟨i, a, hg, hb, ha⟩ := h.position
  exact .arrArg hg hb ha

theorem ArgRaises.append {args : List Tm} {v : Tm} (rest : List Tm) (h : ArgRaises args v) :
    ArgRaises (args ++ rest) v := by
  induction h with
  | head hr => exact .head hr
  | tail hw _ ih => exact .tail hw ih

/-- An already evaluated prefix cannot be reordered or evaluated again. -/
theorem keep_prefix (hv : Values vs) (s : ArgStep h args h' args') :
    ArgStep h (vs ++ args) h' (vs ++ args') := by
  induction vs with
  | nil => exact s
  | cons v vs ih =>
    exact .tail (hv v (by simp)) (ih (fun a ha => hv a (by simp [ha])))

/-- Argument preparation selects exactly one position after a completed
prefix. This is the indexed form used by native call reduction. -/
theorem focus_iff : ArgStep h args h' args' ↔
    ∃ i a a', args[i]? = some a ∧
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) ∧
      Step h a h' a' ∧ args' = args.set i a' := by
  constructor
  · intro hs
    induction hs with
    | head hs => exact ⟨0, _, _, rfl, (by intro j hj; omega), hs, rfl⟩
    | @tail v h args h' args' hv hs ih =>
      obtain ⟨i, a, a', hg, hb, ha, he⟩ := ih
      refine ⟨i + 1, a, a', hg, ?_, ha, ?_⟩
      · intro j hj x hx
        cases j with
        | zero => cases hx; exact hv
        | succ j => exact hb j (by omega) x hx
      · exact congrArg (v :: ·) he
  · rintro ⟨i, a, a', hg, hb, hs, rfl⟩
    induction i generalizing args with
    | zero =>
      cases args with
      | nil => simp at hg
      | cons v args => cases hg; exact .head hs
    | succ i ih =>
      cases args with
      | nil => simp at hg
      | cons v args =>
        exact .tail (hb 0 (by omega) v rfl)
          (ih hg (fun j hj x hx => hb (j + 1) (by omega) x hx))

/-- A call in preparation: the callee, the receiver and the actuals. -/
structure Frame where
  callee : Tm
  recv : Tm
  args : List Tm
  deriving DecidableEq, Repr

/-- Preparation never invokes the callee. No receiver effect happens before the
callee is a value, no argument effect before the receiver is one, and
invocation must wait until every argument is a value. -/
inductive Prepare : Heap → Frame → Heap → Frame → Prop where
  | callee : Step h f h' f' → Prepare h ⟨f,r,args⟩ h' ⟨f',r,args⟩
  | recv : isVal f = true → Step h r h' r' → Prepare h ⟨f,r,args⟩ h' ⟨f,r',args⟩
  | args : isVal f = true → isVal r = true → ArgStep h args h' args' →
      Prepare h ⟨f,r,args⟩ h' ⟨f,r,args'⟩
  /-- A spread whose store is ready, after a completed prefix, becomes the
  store's elements; the heap is only read. -/
  | splice {pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} :
      isVal f = true → isVal r = true → args = pre ++ .spread (.arr ls) :: post → Values pre →
      readElems h ls = some vs → Prepare h ⟨f,r,args⟩ h ⟨f,r,pre ++ vs ++ post⟩

/-- Exact-arity calls preserve the declared argument order without padding. -/
theorem parameters_exact (args : List Tm) : parameters args.length args = args := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [parameters, ih]

/-- Trailing `undefined` actuals are exactly what padding already supplies, so a
call that omits them dispatches the same body term as the call that writes them
out. An omitted parameter is therefore not a second binding rule. -/
theorem parameters_pad (n : Nat) (args pad : List Tm) (hp : ∀ a ∈ pad, a = .undef) :
    parameters n (args ++ pad) = parameters n args := by
  induction n generalizing args pad with
  | zero => rfl
  | succ n ih =>
    cases args with
    | nil =>
      cases pad with
      | nil => rfl
      | cons a pad =>
        cases hp a (by simp)
        simp only [List.nil_append, parameters]
        exact congrArg _ (ih [] pad fun v hv => hp v (by simp [hv]))
    | cons a args =>
      simp only [List.cons_append, parameters]
      exact congrArg _ (ih args pad hp)


/-- Binding reads only the first `n` actuals: later ones were evaluated for
their effects and are discarded. -/
theorem parameters_take : ∀ (n : Nat) (args : List Tm), parameters n (args.take n) = parameters n args
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: args => by simp [parameters, parameters_take n args]

theorem parameters_property {P : Tm → Prop} (hu : P .undef)
    (ha : ∀ a ∈ args, P a) : ∀ a ∈ parameters n args, P a := by
  induction n generalizing args with
  | zero => simp [parameters]
  | succ n ih =>
    cases args with
    | nil =>
      intro a hm
      simp only [parameters, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hu
      · exact ih (by simp) a hm
    | cons v args =>
      intro a hm
      simp only [parameters, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ha a (by simp)
      · exact ih (fun a h => ha a (by simp [h])) a hm


/-- Initializers of an allocation reduce exactly as actual arguments do. -/
theorem Step.makeArgs {c : CallCode} {ns : List PropKey} {h h' : Heap} {args args' : List Tm}
    (hs : ArgStep h args h' args') : Step h (.makeAt c ns args) h' (.makeAt c ns args') := by
  obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
  exact .makeArg hg hb hstep

/-- The actuals of `new` reduce exactly as a call's do, once the constructor
is a value. -/
theorem Step.constructArgs {h h' : Heap} {f : Tm} {args args' : List Tm} (hf : isVal f = true)
    (hs : ArgStep h args h' args') : Step h (.construct f args) h' (.construct f args') := by
  obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
  exact .constructArg hf hg hb hstep

/-- A store's initializers reduce exactly as actual arguments do. -/
theorem Step.arrArgs {h h' : Heap} {args args' : List Tm}
    (hs : ArgStep h args h' args') : Step h (.arrLit args) h' (.arrLit args') := by
  obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
  exact .arrArg hg hb hstep

/-- Dispatch a fully evaluated frame to the code on its saved callee. The
descriptor supplies the parameter count; the receiver and all actuals,
including extras, must be values before normalization. Invocation itself
performs no heap effect. -/
inductive Invoke : Frame → Tm → Prop where
  /-- A forwarding descriptor yields the target's call: the saved receiver in
  place of this one, the saved prefix before these actuals. -/
  | bound : isVal r = true → Values args →
      Invoke ⟨.objAt fs (.bound target r₀ pre) oid, r, args⟩ (.invoke target r₀ (pre ++ args))
  /-- Graph code starts its run at its entry, the receiver, the parameters and
  the captures in its environment, after collecting its rest (`graphEntry`),
  where its kind binds the receiver (`Invoke.binds`). -/
  | graph : isVal r = true → Values args → kind.binds r = true →
      Invoke ⟨.objAt fs (.graph arity E K start caps kind rest) oid, r, args⟩
        (graphEntry arity E K start caps rest r args)

/-- What `new` runs for construct code without a rest, for each ready
argument list: the code's body or graph run, with `undefined` for the
receiver. Other code has none: `new` on call code, and on code collecting a
rest, is not a class value here. -/
def construction : CallCode → Option (List Tm → Tm)
  | .graph arity E K start caps .construct false =>
      some fun args => graphEntry arity E K start caps false .undef args
  | _ => none

/-- Construction reads the parameters it binds: omitted trailing positions
padded with `undefined` construct the same. -/
theorem construction_pad {c : CallCode} {enter : List Tm → Tm} (h : construction c = some enter)
    (args pad : List Tm) (hp : ∀ a ∈ pad, a = .undef) : enter (args ++ pad) = enter args := by
  unfold construction at h
  split at h <;> cases h
  simp only [graphEntry, parameters_pad _ _ _ hp]

/-- A ready construction is one step of the machine. -/
theorem construction_step {fs : List (PropKey × Nat)} {c : CallCode} {enter : List Tm → Tm}
    (h : construction c = some enter) {args : List Tm} (hv : Values args) (heap : Heap) :
    Step heap (.construct (.objAt fs c oid) args) heap (enter args) := by
  unfold construction at h
  split at h <;> cases h
  exact .constructGraph hv

theorem invoke_deterministic (hi : Invoke frame body) (hi' : Invoke frame body') :
    body = body' := by
  cases hi <;> cases hi' <;> rfl

/-- Prepared list dispatch is a step of the maintained term machine. -/
theorem Invoke.step (hi : Invoke frame body) (h : Heap) :
    Step h (.invoke frame.callee frame.recv frame.args) h body := by
  cases hi with
  | bound hr hv => exact .callBound hr hv
  | graph hr hv hk => exact .callGraph hr hv hk

/-- Preparation and native operand reduction are the same transition. -/
theorem Prepare.step (hp : Prepare h frame h' frame') :
    Step h (.invoke frame.callee frame.recv frame.args) h'
      (.invoke frame'.callee frame'.recv frame'.args) := by
  cases hp with
  | callee hs => exact .callL hs
  | recv hv hs => exact .callRecv hv hs
  | args hv hr hs =>
    obtain ⟨i, a, a', hg, hb, hstep, rfl⟩ := focus_iff.mp hs
    exact .callArg hv hr hg hb hstep
  | splice hv hr he hp hre => exact .callSpread hv hr he hp hre

/-- Every native call step is preparation or dispatch, and both reconstruct
that same machine step. This includes all argument counts. -/
theorem call_step_iff : Step h (.invoke f r args) h' result ↔
    (∃ frame, Prepare h ⟨f, r, args⟩ h' frame ∧
      result = .invoke frame.callee frame.recv frame.args) ∨
    (h' = h ∧ Invoke ⟨f, r, args⟩ result) := by
  constructor
  · intro hs
    cases hs with
    | callL hs => exact Or.inl ⟨_, .callee hs, rfl⟩
    | callRecv hv hs => exact Or.inl ⟨_, .recv hv hs, rfl⟩
    | callArg hv hr hg hb hs =>
      exact Or.inl ⟨_, .args hv hr (focus_iff.mpr ⟨_, _, _, hg, hb, hs, rfl⟩), rfl⟩
    | callBound hr hv => exact Or.inr ⟨rfl, .bound hr hv⟩
    | callGraph hr hv hk => exact Or.inr ⟨rfl, .graph hr hv hk⟩
    | callSpread hv hr he hp hre => exact Or.inl ⟨_, .splice hv hr he hp hre, rfl⟩
  · rintro (⟨frame, hp, rfl⟩ | ⟨rfl, hi⟩)
    · exact hp.step
    · exact hi.step _

#print axioms invoke_deterministic
#print axioms focus_iff
#print axioms Prepare.step
#print axioms call_step_iff
#print axioms Invoke.step
end Verification.CallArguments
