import Verification.Semantics.SafeUnder

/-! # Safety at framed returns

The draft "Accepting a unit through the read-only frame" (`docs/drafts/framed-acceptance.md`,
"The graph at framed returns"). A run of graph code (`goto` and `frame`
terms over one code's node lists) whose framed nodes `F` are trusted to
return within `Ret` (normal exit) and `RetE` (throw): at each evaluation of
a node `l` with `F l`, from the step entering it (`goto … l …` to `frame …`
at the heap `h₀`) to the step leaving it at the heap `h'`, the node's
environment `ρ` meets `Ret l ρ h₀ h'` where the node's term is a value and
`RetE l ρ h₀ h'` where it throws.

- `SafeRet J Ξ T Q R F Ret RetE`: `SafePostExcW Ξ T Q R` with `J` at every
  state, the run followed past a step leaving a framed node only where the
  return meets `Ret` or `RetE`. The pending evaluation (the framed node and
  the heap it was entered at) is threaded along (`framedPend`).
- `SafeRet.underW` (proved): where an invariant of the obligation's ghost,
  the pending evaluation, the world and the state gives the returns at
  every step keeping the obligation at the state's world (`RetAt`),
  `SafeRet` gives `SafeUnder`.
- `SafeRet.of_safe` (proved): ordinary safety with `J` along the run is
  `SafeRet` at every framed set; `SafeRet.erase` (proved): with no framed
  node, `SafeRet` is ordinary safety. -/
namespace Verification.HeapObservations
open Verification

/-- Whether a term is a frame of graph code. -/
def isFrame : Tm → Bool
  | .frame .. => true
  | _ => false

/-- **The pending framed evaluation after a step** from `t` at the heap `h`
to `t'`: a step entering a framed node `l` (`goto` to `frame`) records `l`
and `h`; a step within a frame keeps the record; any other step clears it. -/
def framedPend (F : Nat → Bool) (p : Option (Nat × Heap)) (h : Heap) (t t' : Tm) : Option (Nat × Heap) :=
  match t with
  | .goto _ _ l _ _ _ => if isFrame t' && F l then some (l, h) else none
  | .frame .. => if isFrame t' then p else none
  | _ => none

/-- **A step meets the framed returns**: a step leaving the frame of a
pending framed node `l` entered at `h₀`, at the heap `h'`, meets `Ret` at
the node's environment where the node's term is a value and `RetE` where it
is not (a throw); every other step meets them. -/
def RetAt (Ret RetE : Nat → Env → Heap → Heap → Prop) (p : Option (Nat × Heap)) (h' : Heap) (t t' : Tm) : Prop :=
  match p, t with
  | some (l, h₀), .frame _ _ u L d _ _ _ =>
    isFrame t' = true ∨ (isVal u = true ∧ Ret l (envOf L d) h₀ h') ∨ (isVal u = false ∧ RetE l (envOf L d) h₀ h')
  | _, _ => True

/-- **Safety at framed returns**: at every budget the running term's
references are valid; at positive budget `J` holds of the state, and it is
a value of `T` meeting `Q`, a throw of `Ξ` meeting `R`, or it steps to a
state, with an admissible world and a heap it types, from which the run is
again safe where the step meets the framed returns (`RetAt`), the pending
evaluation after it `framedPend`'s. -/
def SafeRet (J : Heap → Tm → Prop) (Ξ T : Fam) (Q : WPost) (R : WExc) (F : Nat → Bool)
    (Ret RetE : Nat → Env → Heap → Heap → Prop) :
    (n : Nat) → WorldT n → Option (Nat × Heap) → Heap → Tm → Prop
  | 0, W, _, _, t => RefsOk W t
  | n + 1, W, p, h, t => RefsOk W t ∧ J h t ∧
      (((isVal t = true ∧ T (n + 1) W t ∧ Q (n + 1) W h t) ∨ (Thrown Ξ (n + 1) W t ∧ R (n + 1) W h)) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧ HeapOk n U h' ∧
          (RetAt Ret RetE p h' t t' → SafeRet J Ξ T Q R F Ret RetE n U (framedPend F p h t t') h' t')))

section
variable {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : WPost} {R : WExc} {F : Nat → Bool}
  {Ret RetE : Nat → Env → Heap → Heap → Prop}

/-- The running term of a state safe at framed returns has valid
references (proved). -/
theorem SafeRet.refs : ∀ {n : Nat} {W : WorldT n} {p : Option (Nat × Heap)} {h : Heap} {t : Tm},
    SafeRet J Ξ T Q R F Ret RetE n W p h t → RefsOk W t
  | 0, _, _, _, _, hs => hs
  | _ + 1, _, _, _, _, hs => hs.1

/-- **Safety at framed returns along the executions keeping an obligation**
(proved; the draft, `framed_requestSafe`'s induction): where an invariant
`I` of the obligation's ghost, the pending framed evaluation, the world and
the state holds, and every step keeping the obligation from a state meeting
it, to a world and heap the derivation admits, meets the framed returns and
leaves a state meeting it where its term is valid there, `SafeRet` gives
`SafeUnder`: at each step keeping the obligation the return premise holds,
and after a step breaking it nothing is claimed. -/
theorem SafeRet.underW {γ : Type} {K : γ → (k : Nat) → WorldT k → Heap → Tm → Heap → Tm → Prop}
    {next : γ → Heap → Tm → Heap → Tm → γ}
    {I : γ → Option (Nat × Heap) → (k : Nat) → WorldT k → Heap → Tm → Prop}
    (hinv : ∀ g p (k : Nat) (W : WorldT (k + 1)) h t (U : WorldT k) h' t', I g p (k + 1) W h t → Step h t h' t' →
      WExt (trunc k (Nat.le_succ k) W) U → WorldAdm U → HeapOk k U h' → K g (k + 1) W h t h' t' →
      RetAt Ret RetE p h' t t' ∧ (RefsOk U t' → I (next g h t h' t') (framedPend F p h t t') k U h' t')) :
    ∀ {n : Nat} {W : WorldT n} {g : γ} {p : Option (Nat × Heap)} {h : Heap} {t : Tm}, I g p n W h t →
      SafeRet J Ξ T Q R F Ret RetE n W p h t → SafeUnder K next J Ξ T Q R n W g h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W g p h t hi hs
    obtain ⟨hrf, hJ, hs⟩ := hs
    refine ⟨hrf, hJ, ?_⟩
    rcases hs with hv | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact .inl hv
    · refine .inr ⟨U, h', t', hx, hu, st, hh, fun hK => ?_⟩
      obtain ⟨hret, hi'⟩ := hinv g p n W h t U h' t' hi st hx hu hh hK
      have hs' := hs hret
      exact ih (hi' (SafeRet.refs hs')) hs'

/-- **Ordinary safety is safety at every set of framed returns** (proved):
`SafePostExcW` with `J` at every state reached within the budget gives
`SafeRet` at every framed set, return relations and pending evaluation. -/
theorem SafeRet.of_safe :
    ∀ {n : Nat} {W : WorldT n} {p : Option (Nat × Heap)} {h : Heap} {t : Tm},
      (∀ {j : Nat} {h' : Heap} {t' : Tm}, j < n → Steps j h t h' t' → J h' t') →
      SafePostExcW Ξ T Q R n W h t → SafeRet J Ξ T Q R F Ret RetE n W p h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W p h t hJ hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, hJ (Nat.succ_pos n) .refl, ?_⟩
    rcases hs with hv | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact .inl hv
    · exact .inr ⟨U, h', t', hx, hu, st, hh, fun _ =>
        ih (fun hj hr => hJ (by omega) (.next st hr)) hs⟩

/-- With no framed node, no evaluation is pending after any step. -/
theorem framedPend_none (hF : ∀ l, F l = false) (h : Heap) (t t' : Tm) : framedPend F none h t t' = none := by
  unfold framedPend
  split
  · simp [hF]
  · split <;> rfl
  · rfl

/-- **With no framed node, safety at framed returns is ordinary safety**
(proved; the draft, `runSound_of_framed`): no evaluation is ever pending, so
every step meets the returns. -/
theorem SafeRet.erase (hF : ∀ l, F l = false) :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t : Tm},
      SafeRet J Ξ T Q R F Ret RetE n W none h t → SafePostExcW Ξ T Q R n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t hs
    obtain ⟨hrf, -, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with hv | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact .inl hv
    · have hs' := hs (by simp [RetAt])
      rw [framedPend_none hF] at hs'
      exact .inr ⟨U, h', t', hx, hu, st, hh, ih hs'⟩

end
end Verification.HeapObservations
