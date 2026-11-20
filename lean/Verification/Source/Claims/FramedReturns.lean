import Verification.Source.Claims.PassUnitFramed
import Verification.Source.Claims.PassUnitSafe
import Verification.Paper.TolerantFrames.ReadOnlyTransfer
import Verification.Paper.TolerantFrames.ReadOnlyMemberCert
import Verification.Source.Claims.FramedRealize
import Verification.Source.Claims.FramedNodeChecks

/-! # The returns at reached executions, at their worlds

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The returns, at reached
executions"). The frame's executions are executions of actual steps
(`FrameCore.KStep`): each configuration has an admissible world typing
its heap, and the client obligation is read at that world, as the kinds
the protocol reads are the world's (`St.part`, `kindAt`). The returns at
reached executions are an invariant of the frame's history, the pending
framed evaluation, the world and the state, holding at every call the
claim is about, on which every step keeping the obligation at the state's
world, to a world and heap the step's safety gives, meets the returns
(`FramedReturnsReachedW`, `PassUnit.lean`).

- `ret_reachedW` (proved): `FramedReturnsReachedW` at the returns
  `framedRet S`, from the transfer at each framed node of the request's
  main graph (`FramedNodeTransfer`): along every execution of the frame
  from a reached state entering a framed node `l` to a state whose node's
  term is a value, every support of `S l` is supported from the entry's
  heap to that state's. The invariant is the frame's reached
  configuration at the world, the term the request's graph code at the
  top (`TopRuns`), and the pending evaluation the execution from the
  entry of its node (`PendFrom`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow HeapObservations

/-! ## The request's graph code at the top of the term -/

/-- **Slots of values**: every slot and the default a value. -/
def SlotVals (L : List Tm) (d : Tm) : Prop := (∀ v ∈ L, isVal v = true) ∧ isVal d = true

/-- A slot map keeps slots of values (proved, `envMap_mem`). -/
theorem SlotVals.map {L : List Tm} {d : Tm} (hv : SlotVals L d) (m : Option (List Nat)) :
    SlotVals (envMap m L d).1 (envMap m L d).2 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases envMap_mem (.inl hx) with h | rfl
    · exact hv.1 x h
    · exact hv.2
  · rcases envMap_mem (m := m) (L := L) (d := d) (.inr rfl) with h | h
    · exact hv.1 _ h
    · rw [h]; exact hv.2

/-- A value bound in front keeps slots of values (proved). -/
theorem SlotVals.cons {L : List Tm} {d v : Tm} (hL : SlotVals L d) (hv : isVal v = true) : SlotVals (v :: L) d :=
  ⟨fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact hL.1 x hx, hL.2⟩

section
variable {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag}

/-- **The term runs the graph code `Pe`, `Pk` at its top**, tagged `c₀`:
a `goto` or a `frame` over those node lists with slots of values, or a
term that takes no step (the run has left the code: a value, a throw of a
value). -/
def TopRuns (Pe : List Tm) (Pk : List (Continuation × Option Target)) (c₀ : ComponentTag) (t : Tm) : Prop :=
  (∃ l L d, t = .goto Pe Pk l L d c₀ ∧ SlotVals L d) ∨
    (∃ u L d k x, t = .frame Pe Pk u L d k x c₀ ∧ SlotVals L d) ∨ ∀ h h' t', ¬ Step h t h' t'

/-- **Every step keeps the graph code at the top** (proved, by the step
rules of `goto` and `frame`, each slot map keeping slots of values,
`SlotVals.map`; a value and a throw of a value take no step). -/
theorem TopRuns.step {h h' : Heap} {t t' : Tm} (ht : TopRuns Pe Pk c₀ t) (hs : Step h t h' t') :
    TopRuns Pe Pk c₀ t' := by
  rcases ht with ⟨l, L, d, rfl, hL⟩ | ⟨u, L, d, k, x, rfl, hL⟩ | hn
  · cases hs with
    | gotoEnter => exact .inr (.inl ⟨_, _, _, _, _, rfl, hL⟩)
  · cases hs with
    | frameC => exact .inr (.inl ⟨_, _, _, _, _, rfl, hL⟩)
    | frameRet hv => exact .inr (.inr fun _ _ _ s => value_no_step hv s)
    | frameBind hv => exact .inl ⟨_, _, _, rfl, (hL.cons hv).map _⟩
    | frameEffect => exact .inl ⟨_, _, _, rfl, hL.map _⟩
    | frameYes => exact .inl ⟨_, _, _, rfl, hL.map _⟩
    | frameNo => exact .inl ⟨_, _, _, rfl, hL.map _⟩
    | frameYesBind => exact .inl ⟨_, _, _, rfl, (hL.cons rfl).map _⟩
    | frameNoBind => exact .inl ⟨_, _, _, rfl, (hL.cons rfl).map _⟩
    | frameTag hv => exact .inl ⟨_, _, _, rfl, (hL.cons hv).map _⟩
    | frameHandle hr => exact .inl ⟨_, _, _, rfl, (hL.cons (raises_val hr)).map _⟩
    | frameRaise hr => exact .inr (.inr fun _ _ _ s => by
        cases s with | throwC s => exact value_no_step (raises_val hr) s)
  · exact absurd hs (hn _ _ _)

end

/-- **A step of a frame whose term is a value keeps the heap** (proved):
every rule leaving a frame keeps it, and a value takes no step. -/
theorem frame_val_heap {h h' : Heap} {E : List Tm} {K : List (Continuation × Option Target)} {u : Tm}
    {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} {comp : ComponentTag} {t' : Tm}
    (hu : isVal u = true) (hs : Step h (.frame E K u L d k x comp) h' t') : h' = h := by
  cases hs with
  | frameC s => exact absurd s (value_no_step hu)
  | _ => rfl

/-- **A frame that steps to a frame steps its term** (proved): every other
rule leaving a frame reaches a `goto`, a value or a throw. -/
theorem frame_to_frame {h h' : Heap} {E : List Tm} {K : List (Continuation × Option Target)} {u : Tm}
    {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} {comp : ComponentTag} {t' : Tm}
    (hs : Step h (.frame E K u L d k x comp) h' t') (hf : isFrame t' = true) :
    ∃ u', Step h u h' u' ∧ t' = .frame E K u' L d k x comp := by
  cases hs with
  | frameC s => exact ⟨_, s, rfl⟩
  | frameRet hv =>
    have : ∀ w, isFrame w = true → isVal w = false := fun w => by cases w <;> simp [isFrame, isVal]
    rw [this _ hf] at hv; cases hv
  | frameRaise => simp [isFrame] at hf
  | _ => simp [isFrame] at hf

/-! ## The returns at reached executions -/

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **A state of the run of a frame of the code `Pe`, `Pk`** with slots
`L`, default `d`, continuation `k`, handler `x` and tag `comp`: the frame
at the top, its running term not returned. -/
def FrameRuns (Pe : List Tm) (Pk : List (Continuation × Option Target)) (L : List Tm) (d : Tm) (k : Continuation)
    (x : Option Target) (comp : ComponentTag) (s : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  ∃ u, s.1.t = .frame Pe Pk u L d k x comp ∧ ¬ Returned u

/-- **The evaluation of node `l` of the code `Pe`, `Pk` from a reached
state** to the state `a`: a reached state `b₀` at the heap `h₀` entering
the node (its frame, tagged `c₀`, running the node's expression
instantiated at slots of values), then steps keeping the obligation along which the frame's term has
not returned, ending at the same frame at `a`. -/
def PendFrom (Pe : List Tm) (Pk : List (Continuation × Option Target)) (c₀ : ComponentTag) (l : Nat)
    (h₀ : Heap) (a : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  ∃ (b₀ : Conf × Ghost (fr.F.at fr.C)) (m : Nat) (e : Tm) (L : List Tm) (d : Tm) (k : Continuation)
    (x : Option Target),
    fr.Reached b₀ ∧ b₀.1.s.h = h₀ ∧ Pe[l]? = some e ∧ Pk[l]? = some (k, x) ∧ SlotVals L d ∧
      b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ ∧
      Ex fr.KStep (fr.FrameRuns Pe Pk L d k x c₀) m b₀ a ∧ ∃ u, a.1.t = .frame Pe Pk u L d k x c₀

/-- **The transfer at the framed nodes of a graph code** (the premise
`ret_reachedW` reads; to be proved from `framed_transfer`): along every
execution of the frame keeping the obligation from a reached state
entering a framed node `l` of the code `Pe`, `Pk` (its frame tagged
`c₀`, its slots values), its frame's term not
returned, to a state at which the node's term is a value, every support
of `S l` is supported at the frame's environment from the entry's heap to
that state's. -/
def FramedNodeTransfer (Pe : List Tm) (Pk : List (Continuation × Option Target)) (c₀ : ComponentTag)
    (F : Nat → Bool) (S : Nat → List Footprints.Footprint) : Prop :=
  ∀ (l : Nat) (b₀ a : Conf × Ghost (fr.F.at fr.C)) (m : Nat) (e : Tm) (L : List Tm) (d : Tm) (k : Continuation)
    (x : Option Target) (v : Tm),
    F l = true → fr.Reached b₀ → Pe[l]? = some e → Pk[l]? = some (k, x) → SlotVals L d →
    b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
    Ex fr.KStep (fr.FrameRuns Pe Pk L d k x c₀) m b₀ a → a.1.t = .frame Pe Pk v L d k x c₀ →
    isVal v = true → ∀ T ∈ S l, Footprints.Supported T (envOf L d) b₀.1.s.h a.1.s.h

/-- **The invariant of the returns at reached executions**: at a positive
budget, a configuration at the world, heap and term, reached by the frame
with the history `g`, whose term runs the code `Pe`, `Pk` at its top, and
whose pending framed evaluation, where one is recorded, is the evaluation
of its node from a reached state (`PendFrom`). -/
def RetInv (Pe : List Tm) (Pk : List (Continuation × Option Target)) (c₀ : ComponentTag) (F : Nat → Bool)
    (g : Ghost (fr.F.at fr.C)) (p : Option (Nat × Heap)) (k : Nat) (W : WorldT k) (h : Heap) (t : Tm) : Prop :=
  k = 0 ∨ ∃ y : Conf, y.s.n = k ∧ HEq y.s.W W ∧ y.s.h = h ∧ y.t = t ∧ fr.Reached (y, g) ∧ TopRuns Pe Pk c₀ t ∧
    ∀ l h₀, p = some (l, h₀) → F l = true ∧ fr.PendFrom Pe Pk c₀ l h₀ (y, g)

variable {fr}

/-- A world reached from a world equal to one it is reached from
(proved). -/
theorem reach_heq {n m : Nat} {W' : WorldT n} {W : WorldT (m + 1)} {U : WorldT m} (hn : n = m + 1) (hW : HEq W' W)
    (hx : WExt (trunc m (Nat.le_succ m) W) U) : WorldReach W' U := by
  subst hn; cases hW; exact ⟨_, hx⟩

/-- The obligation at a step, read at an equal world (proved). -/
theorem keeps_heq {g : Ghost (fr.F.at fr.C)} {n m : Nat} {W' : WorldT n} {W : WorldT m} {h h' : Heap} {t t' : Tm}
    (hn : n = m) (hW : HEq W' W) (hK : fr.Keeps g m W h t h' t') : fr.Keeps g n W' h t h' t' := by
  subst hn; cases hW; exact hK

/-- **The invariant at a step** (proved): from a state meeting `RetInv`, a
step keeping the obligation at its world meets the returns `framedRet S`
(`FramedNodeTransfer` at a step leaving a framed node whose term is a
value, the leaving step keeping the heap, `frame_val_heap`; nothing at a
throw) and, at a world the step's safety admits and a heap it types, with
its term valid there, leaves a state meeting it: the step is a step of
the frame (`KStep`, its world reached by `WExt`), the graph code stays at
the top (`TopRuns.step`), an entering step of a framed node starts its
evaluation, and a step of the frame's term extends it
(`frame_to_frame`). -/
theorem retInv_step {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag}
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint} (htr : fr.FramedNodeTransfer Pe Pk c₀ F S)
    {g : Ghost (fr.F.at fr.C)} {p : Option (Nat × Heap)} {k : Nat} {W : WorldT (k + 1)} {h : Heap} {t : Tm}
    {U : WorldT k} {h' : Heap} {t' : Tm} (hi : fr.RetInv Pe Pk c₀ F g p (k + 1) W h t) (hs : Step h t h' t')
    (hx : WExt (trunc k (Nat.le_succ k) W) U) (hu : WorldAdm U) (hh : HeapOk k U h')
    (hK : fr.Keeps g (k + 1) W h t h' t') :
    RetAt (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁) (fun _ _ _ _ => True) p h' t t' ∧
      (RefsOk U t' → fr.RetInv Pe Pk c₀ F (fr.next g h t h' t') (framedPend F p h t t') k U h' t') := by
  rcases hi with h0 | ⟨y, hn, hW, hyh, hyt, hre, htop, hpend⟩
  · cases h0
  subst hyh hyt
  refine ⟨?_, fun hrefs => ?_⟩
  · -- The returns at the step.
    cases p with
    | none => simp [RetAt]
    | some p =>
      obtain ⟨l, h₀⟩ := p
      obtain ⟨hFl, b₀, m, e, L, d, kk, xx, hb₀, hbh, he, hk, hL, hbt, hex, u, hyu⟩ := hpend l h₀ rfl
      rw [hyu]
      simp only [RetAt]
      by_cases hv : isVal u = true
      · by_cases hf : isFrame t' = true
        · exact .inl hf
        · refine .inr (.inl ⟨hv, fun T hT => ?_⟩)
          rw [hyu] at hs
          have hh' := frame_val_heap hv hs
          rw [hh', ← hbh]
          exact htr l b₀ (y, g) m e L d kk xx u hFl hb₀ he hk hL hbt hex hyu hv T hT
      · exact .inr (.inr ⟨by simpa using hv, trivial⟩)
  · -- The invariant after the step.
    cases k with
    | zero => exact .inl rfl
    | succ k =>
    let z : Conf := ⟨⟨k + 1, U, h', Nat.succ_pos k, hu, hh⟩, t', hrefs⟩
    have hks : fr.KStep (y, g) (z, fr.next g y.s.h y.t h' t') :=
      ⟨⟨hs, reach_heq hn hW hx⟩, rfl, keeps_heq hn hW hK⟩
    refine .inr ⟨z, rfl, HEq.rfl, rfl, rfl, Reached.step hre hks, htop.step hs, fun l h₀ hp => ?_⟩
    rcases htop with ⟨l', L, d, hyt, hL⟩ | ⟨u, L, d, kk, xx, hyt, hL⟩ | hns
    · -- An entering step: the evaluation of node `l'` starts.
      rw [hyt] at hp hs
      simp only [framedPend] at hp
      split at hp
      · rename_i hc
        cases hp
        refine ⟨by simp at hc; exact hc.2, ?_⟩
        cases hs with
        | gotoEnter he hk =>
          refine ⟨_, 0, _, L, d, _, _, Reached.step hre hks, rfl, he, hk, hL, rfl,
            .refl _, _, rfl⟩
      · cases hp
    · -- A step of a frame: inside the frame, the evaluation goes on.
      rw [hyt] at hp hs
      simp only [framedPend] at hp
      split at hp
      · rename_i hf
        obtain ⟨hFl, b₀, m, e, L₀, d₀, k₀, x₀, hb₀, hbh, he, hk, hL₀, hbt, hex, u₀, hyu⟩ := hpend l h₀ hp
        rw [hyt] at hyu
        cases hyu
        obtain ⟨u', hs', ht'⟩ := frame_to_frame hs hf
        have hnr : ¬ Returned u := by
          rintro (hv | ⟨w, hw⟩)
          · exact value_no_step hv hs'
          · exact raises_no_step hw hs'
        refine ⟨hFl, b₀, m + 1, e, L, d, kk, xx, hb₀, hbh, he, hk, hL₀, hbt,
          hex.snoc ⟨u, by rw [hyt], hnr⟩ hks, u', ht'⟩
      · cases hp
    · exact absurd hs (hns _ _ _)

/-! ## The obligation reads the world -/

/-- **The client obligation at a step reads the world** (proved, a
counter-model): the same transition of the same heap, at the same
history, keeps a protocol at one world and breaks it at another, since a
location's part reads its kind at the world (`kindAt`): a location the
history protects (an exposed one), of kind `field` at the first world and
of no kind at the second, changes from `0` to `1`, within `any` at a field
and outside `keep` elsewhere. So a step clause quantifying the obligation
at a world unrelated to the execution's configuration admits steps that
break it at the configuration's world, along which the transfer's bound
on `R_C` (`Run.bound`, read at `St.part`) is not established;
`FramedReturnsReachedW` reads the obligation at the world of the state. -/
theorem rowAt_reads_world :
    ∃ (P : Package) (Θ : Protocol P) (g : Ghost P) (h h' : Heap) (W₁ W₂ : WorldT 1),
      RowAt Θ W₁ g h h' ∧ ¬ RowAt Θ W₂ g h h' := by
  let P : Package := ⟨Unit, fun _ => .exposed, fun _ => false⟩
  let Θ : Protocol P := fun p => if p.kind = some .field then .any else .keep
  let g : Ghost P := ⟨fun _ => some (), fun _ => none, fun _ => True, [], fun _ => False⟩
  let W₁ : WorldT 1 := ofEntries [(.field "f", fun _ _ _ _ => True)]
  let W₂ : WorldT 1 := ofEntries []
  refine ⟨P, Θ, g, [.num 0], [.num 1], W₁, W₂, fun l v _ hv => ⟨.num 1, ?_, ?_⟩, fun hrow => ?_⟩
  · cases l with
    | zero => rfl
    | succ l => simp at hv
  · cases l with
    | zero => simp [Θ, W₁, kindAt, roleAt, roles, Role.kind, Footprints.Change.Holds]
    | succ l => simp at hv
  · have hp : RowProtects g 0 := .inl ⟨rfl, trivial⟩
    obtain ⟨v', hv', hc⟩ := hrow 0 (.num 0) hp rfl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv'
    subst hv'
    simp [Θ, W₂, kindAt, roleAt, roles, Footprints.Change.Holds] at hc

/-! ## The transfer at a framed node -/

/-- An operand read from slots of values is a value at the node's entry
(proved). -/
theorem atomB_inst {e : Tm} (he : atomB e = true) {L : List Tm} {d : Tm} (hv : SlotVals L d) :
    isVal (instantiate 0 (envOf L d) e) = true := by
  cases e <;> simp [atomB] at he <;> simp [instantiate, isVal]
  rename_i i
  simp only [envOf]
  rcases getD_mem_or L i d with h | h
  · rw [List.getD_eq_getElem?_getD] at h ⊢; exact hv.1 _ h
  · rw [h]; exact hv.2

/-- **The entry of a node calling operands read from slots of values is a
call of values** (proved). -/
theorem atomCall_inst {e : Tm} (he : atomCallB e = true) {L : List Tm} {d : Tm} (hv : SlotVals L d) :
    ∃ f r args, instantiate 0 (envOf L d) e = .invoke f r args ∧ isVal f = true ∧ isVal r = true ∧
      ∀ a ∈ args, isVal a = true := by
  cases e with
  | invoke f r args =>
    simp only [atomCallB, Bool.and_eq_true, List.all_eq_true] at he
    obtain ⟨⟨hf, hr⟩, ha⟩ := he
    refine ⟨_, _, _, rfl, atomB_inst hf hv, atomB_inst hr hv, fun a hm => ?_⟩
    simp only [instantiateArgs_eq_map, List.mem_map] at hm
    obtain ⟨a', ha', rfl⟩ := hm
    exact atomB_inst (ha a' ha') hv
  | _ => simp [atomCallB] at he

/-- **The transfer at the framed nodes, from the framed transfer** (proved;
the draft, "The transfer at a call", at the claim's top frame): where each
framed node of the code calls operands read from its slots
(`atomCallB`), a reached state entering it is a call state of the top
frame (`CallState`, `atomCall_inst`), and its evaluation to a value is the
call's segment to its resumption (`Inside`, `Resumes`), so
`framed_transfer` gives each support of `S l` supported: with trace
certificates at `Ψj` (`Θ ⊑ Ψj ⊑ Ψc l`), the segment's own steps within
`Ψc l` (`SegWithin`, by `segWithin_of_run`), the callee's effect `Φ l`
bounding the heap along the call's segment (the callback's arrow, part of
`Θ_C`), and the rule's premise at the call state (`Framed`, by
`framed_at_innermost_keys` and `framed_of_cover` from the pass's check of
the node's kept supports). -/
theorem nodeTransfer_of_transfer {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag}
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint} (hc : fr.ChkSound) (hi : fr.StartInv)
    (hcomp : fr.F.ofC fr.C c₀ = true) (hatom : ∀ l e, F l = true → Pe[l]? = some e → atomCallB e = true)
    {Ψj : Protocol (fr.F.at fr.C)} {G : (St (fr.F.at fr.C) → Prop) → Prop} (certs : fr.TraceCerts Ψj G)
    (hΘ : ∀ p, (fr.Θ p).le (Ψj p) = true) {Ψc : Nat → Protocol (fr.F.at fr.C)}
    (hW : ∀ l p, (Ψj p).le (Ψc l p) = true) {Φ : Nat → Footprints.Footprint}
    (hown : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      fr.SegWithin (Ψc l) Pe Pk L d k x c₀ b₀)
    (hfr : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      ∀ T ∈ S l, Framed (Φ l) (Ψc l) T (envOf L d) (lift fr.F fr.C none b₀.1 b₀.2))
    (hΦ : ∀ l (b₀ a : Conf × Ghost (fr.F.at fr.C)) m e L d k x v, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      Ex fr.KStep (fun s => Inside fr.F fr.C Pe Pk L d k x c₀ s.1.t) m b₀ a →
      a.1.t = .frame Pe Pk v L d k x c₀ → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    fr.FramedNodeTransfer Pe Pk c₀ F S := by
  intro l b₀ a m e L d k x v hFl hb he hk hL hbt hex hat hv T hT
  obtain ⟨f, r, args, hinst, hf, hr, ha⟩ := atomCall_inst (hatom l e hFl he) hL
  have hcall : CallState fr.F fr.C Pe Pk L d k x c₀ b₀.1.t :=
    ⟨f, r, args, ⟨by rw [hbt, hinst], hcomp⟩, hf, hr, ha⟩
  have hex' : Ex fr.KStep (fun s => Inside fr.F fr.C Pe Pk L d k x c₀ s.1.t) m b₀ a :=
    hex.mono fun s ⟨u, hu, hnr⟩ => ⟨u, ⟨hu, hcomp⟩, hnr⟩
  have hres : Resumes fr.F fr.C Pe Pk L d k x c₀ a.1.t := ⟨v, ⟨hat, hcomp⟩, .inl hv⟩
  exact framed_transfer hc hi certs hΘ (hW l) hb hcall hex' hres (hown l b₀ e L d k x hFl hb he hk hL hbt)
    (hΦ l b₀ a m e L d k x v hFl hb he hk hL hbt hex' hat hv) (hfr l b₀ e L d k x hFl hb he hk hL hbt T hT)

/-- **The own steps at each framed node, from the call's run** (proved, by
`segWithin_of_run` at each node's set `T l`): where every reached state
fits the flow, meets the residual invariant and layout provenance from the
frame's starts, the flow's tokens are sites and its codes lowered, each
framed node's set passes the closure check, its probe protocol is within
`Ψc l`, and the sets of the call's values at a reached state entering the
node are within `T l`, each meeting layout provenance (`hroots`), every
reached state entering a framed node meets `SegWithin (Ψc l)`, the premise
`nodeTransfer_of_transfer` reads. -/
theorem own_of_run [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    {S₀ T : Nat → Sites (fr.F.at fr.C)} {Ψc : Nat → Protocol (fr.F.at fr.C)}
    {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag} {F : Nat → Bool}
    (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow) (hE : fr.EntryFits Fl.flow)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ Fl lay) a.1.t = true ∧ HeapLay (layQ Fl lay) a.1.s.h)
    (hT : ∀ l, F l = true → capClosedB Fl (tokenCaps Fl lay) (S₀ l) (T l) = true) (htok : tokensSomeB Fl = true)
    (hlow : codesLoweredB Fl = true) (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds Fl) (T l) p).le (Ψc l p) = true)
    (hcomp : fr.F.ofC fr.C c₀ = true) (hatom : ∀ l e, F l = true → Pe[l]? = some e → atomCallB e = true)
    (hroots : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      ∀ v ∈ vals allC true (instantiate 0 (envOf L d) e), ∃ S', VJ Fl.flow b₀.2 b₀.1.s.h.length S' v ∧
        Sub S' (T l) ∧ layP (layQ Fl lay) v = true) :
    ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      fr.SegWithin (Ψc l) Pe Pk L d k x c₀ b₀ := by
  intro l b₀ e L d k x hFl hb he hk hL hbt
  obtain ⟨f, r, args, hinst, hf, hr, ha⟩ := atomCall_inst (hatom l e hFl he) hL
  have hcall : CallState fr.F fr.C Pe Pk L d k x c₀ b₀.1.t :=
    ⟨f, r, args, ⟨by rw [hbt, hinst], hcomp⟩, hf, hr, ha⟩
  refine segWithin_of_run hFa hS hE hwk hly (hT l hFl) htok hlow (hle l hFl) hb hcall fun f' r' args' ht v hv => ?_
  rw [hbt, hinst] at ht
  cases ht
  rw [← hinst] at hv
  exact hroots l b₀ e L d k x hFl hb he hk hL hbt v hv

/-- **An operand read from slots of values meets its slot's set** (proved):
at slots each of whose values meets its slot's set, an operand read from a
slot meets that slot's set, and a constant every set; each meets layout
provenance where the term instantiated does. -/
theorem atom_vj {P : Package} {Fl : Flow P} {g : Ghost P} {n : Nat} {env : Nat → Sites P} {L : List Tm} {d : Tm}
    {q : Code → ComponentTag → Layout → Bool} {a : Tm} (ha : atomB a = true)
    (henv : ∀ i, VJ Fl g n (env i) (envOf L d i)) (hl : layP q (instantiate 0 (envOf L d) a) = true) :
    ∃ S', VJ Fl g n S' (instantiate 0 (envOf L d) a) ∧ (∀ j, a = .var j → S' = env j) ∧
      ((∀ j, a ≠ .var j) → S' = []) ∧ layP q (instantiate 0 (envOf L d) a) = true := by
  cases a <;> simp [atomB] at ha
  case var j => exact ⟨env j, by simpa [instantiate] using henv j, fun _ h => by cases h; rfl,
    fun h => absurd rfl (h j), hl⟩
  all_goals exact ⟨[], VJ.prim (by simp [instantiate, primVal]), fun _ h => (by cases h), fun _ => rfl, hl⟩

/-- **The own steps at each framed node, from the frame's fit** (proved,
`segWithin_of_deep` at each node's set `T l`): `own_of_run` with its root
premise discharged. A reached state entering a framed node fits the flow
(`fitsAt_reached`), so its frame of `C`'s code runs a node `l'` of its code
with `l`'s continuation and handler, at a context `c`, each slot value
meeting the slot's set at `l'` (`Fits.frameC`); each operand of the node's
call read from a slot meets that set, a constant every set (`atom_vj`), and
where `T l` holds the operand slots' sets at every such node and context,
each value of the call's term meets `T l` in depth (`deepIn_of_checks`,
`DeepIn.held`). -/
theorem own_of_fit [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)] {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    {S₀ T : Nat → Sites (fr.F.at fr.C)} {Ψc : Nat → Protocol (fr.F.at fr.C)}
    {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag} {F : Nat → Bool}
    (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow) (hE : fr.EntryFits Fl.flow)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ Fl lay) a.1.t = true ∧ HeapLay (layQ Fl lay) a.1.s.h)
    (hT : ∀ l, F l = true → capClosedB Fl (tokenCaps Fl lay) (S₀ l) (T l) = true) (htok : tokensSomeB Fl = true)
    (hlow : codesLoweredB Fl = true) (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds Fl) (T l) p).le (Ψc l p) = true)
    (hcomp : fr.F.ofC fr.C c₀ = true) (hatom : ∀ l e, F l = true → Pe[l]? = some e → atomCallB e = true)
    (hslots : ∀ l e k x, F l = true → Pe[l]? = some e → Pk[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (Pe, Pk) c = some π → NodeOf (Pe, Pk) l' k x → ∀ j ∈ atomSlots e, Sub (π.env l' j) (T l)) :
    ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      fr.SegWithin (Ψc l) Pe Pk L d k x c₀ b₀ := by
  intro l b₀ e L d k x hFl hb he hk hL hbt
  obtain ⟨f, r, args, hinst, hf, hr, ha⟩ := atomCall_inst (hatom l e hFl he) hL
  have hcall : CallState fr.F fr.C Pe Pk L d k x c₀ b₀.1.t :=
    ⟨f, r, args, ⟨by rw [hbt, hinst], hcomp⟩, hf, hr, ha⟩
  refine segWithin_of_deep hFa hS hE hwk hly (hT l hFl) htok hlow (hle l hFl) hb hcall fun f' r' args' ht v hv => ?_
  rw [hbt, hinst] at ht
  cases ht
  have hfit := (fitsAt_reached hFa hS hE hb).1
  have hlay := (lay_reached hly hb).1
  rw [hbt] at hfit hlay
  have hae := hatom l e hFl he
  cases hfit with
  | val hv => simp [isVal] at hv
  | frameOut hc' => exact absurd hc' (by simpa [Family.at] using hcomp)
  | frameC c π l' _ hcode hn henv =>
    have hlt : layP (layQ Fl lay) (instantiate 0 (envOf L d) e) = true := by
      simp only [layP, Bool.and_eq_true] at hlay; exact hlay.1.1.2
    cases e with
    | invoke fe re argse =>
      simp only [atomCallB, Bool.and_eq_true, List.all_eq_true] at hae
      obtain ⟨⟨haf, har⟩, haa⟩ := hae
      simp only [instantiate, Tm.invoke.injEq] at hinst
      obtain ⟨rfl, rfl, rfl⟩ := hinst
      simp only [instantiate, layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hlt
      have hsub := hslots l _ k x hFl he hk c π l' hcode hn
      have htop : ∀ o, atomB o = true → (o = fe ∨ o = re ∨ o ∈ argse) →
          layP (layQ Fl lay) (instantiate 0 (envOf L d) o) = true →
          DeepIn b₀.2.site (T l) (instantiate 0 (envOf L d) o) := by
        intro o ho hmem hlo
        obtain ⟨S', hv', hvar, hnv, hl'⟩ := atom_vj (env := π.env l') ho henv hlo
        refine deepIn_of_checks (hT l hFl) htok hlow hv' ?_ hl'
        by_cases hvo : ∃ j, o = .var j
        · obtain ⟨j, rfl⟩ := hvo
          rw [hvar j rfl]
          refine hsub j (List.mem_filterMap.mpr ⟨.var j, ?_, rfl⟩)
          rcases hmem with h | h | h
          · rw [h]; exact List.mem_cons_self
          · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
        · rw [hnv fun j h => hvo ⟨j, h⟩]; exact fun _ h => by cases h
      simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap, instantiateArgs_eq_map, List.mem_map] at hv
      rcases hv with (hv | hv) | ⟨a', ⟨o, ho, rfl⟩, hv⟩
      · exact (htop fe haf (.inl rfl) hlt.1.1).held hf hv
      · exact (htop re har (.inr (.inl rfl)) hlt.1.2).held hr hv
      · refine (htop o (haa o ho) (.inr (.inr ho)) ?_).held (ha _ ?_) hv
        · exact hlt.2 _ (by simp only [instantiateArgs_eq_map, List.mem_map]; exact ⟨o, ho, rfl⟩)
        · simp only [instantiateArgs_eq_map, List.mem_map]; exact ⟨o, ho, rfl⟩
    | _ => simp [atomCallB] at hae

/-- **A frame's slots have valid references where the frame does**
(proved). -/
theorem frame_rootsOk {n : Nat} {W : WorldT n} {E : List Tm} {K : List (Continuation × Option Target)} {t : Tm}
    {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} {comp : ComponentTag}
    (h : RefsOk W (.frame E K t L d k x comp)) : RootsOk W (envOf L d) := by
  intro i r hr
  refine h r ?_
  simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
  rcases getD_mem_or L i d with hm | hm
  · simp only [envOf] at hr; rw [List.getD_eq_getElem?_getD] at hm hr
    exact .inl (.inr ⟨_, hm, hr⟩)
  · simp only [envOf] at hr; rw [hm] at hr; exact .inr hr

/-- **The rule's premise at each framed node, from the frame's check**
(proved, `framed_at_innermost_keys`): at a reached state entering a framed
node `l` whose call's operands are read from slots, the frame is the
term's innermost, so where the pass's check of each support of `S l`
passes at every context of the code and every node with `l`'s
continuation and handler, the separation it reads holds at the state, and
every location's key is `none` (`NoKeys`), each support meets `Framed` at
`Ψc l`, protection read nowhere (milestone 1). -/
theorem framed_of_check {Fl : Flow (fr.F.at fr.C)} {Pe : List Tm} {Pk : List (Continuation × Option Target)}
    {c₀ : ComponentTag} {F : Nat → Bool} {S : Nat → List Footprints.Footprint} {Φ : Nat → Footprints.Footprint}
    {Ψc : Nat → Protocol (fr.F.at fr.C)} {q : Nat → Footprints.SepQuery} {tv : TypeView} {dp : Nat}
    (hFa : Fl.Facts) (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl) (hK : fr.NoKeys)
    (hcomp : fr.F.ofC fr.C c₀ = true) (hatom : ∀ l e, F l = true → Pe[l]? = some e → atomCallB e = true)
    (hcheck : ∀ l e k x, F l = true → Pe[l]? = some e → Pk[l]? = some (k, x) → ∀ c π l',
      Fl.code (Pe, Pk) c = some π → NodeOf (Pe, Pk) l' k x →
      ∀ T ∈ S l, frameCheckAt (q l) (Ψc l) (Φ l) T Fl.H (π.env l') noKeys (fun _ => false) = true)
    (hq : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      (q l).Sound (envOf L d) b₀.1.s.h) :
    ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ → Pe[l]? = some e →
      Pk[l]? = some (k, x) → SlotVals L d → b₀.1.t = .frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀ →
      ∀ T ∈ S l, Framed (Φ l) (Ψc l) T (envOf L d) (lift fr.F fr.C none b₀.1 b₀.2) := by
  intro l b₀ e L d k x hFl hb he hk hL hbt T hT
  obtain ⟨f, r, args, hinst, hf, hr, ha⟩ := atomCall_inst (hatom l e hFl he) hL
  have hinn : innermost b₀.1.t = some (.frame Pe Pk (instantiate 0 (envOf L d) e) L d k x c₀) := by
    have hi : innermost (.invoke f r args) = none := by
      have : ∀ xs : List Tm, (∀ a ∈ xs, isVal a = true) → innermostArgs xs = none := by
        intro xs hxs
        induction xs with
        | nil => rfl
        | cons y ys ih =>
          simp only [innermostArgs, hxs y List.mem_cons_self, Bool.true_eq_false, if_false]
          exact ih fun a ha => hxs a (List.mem_cons_of_mem _ ha)
      simp only [innermost, hf, hr, Bool.true_eq_false, if_false]
      exact this args ha
    rw [hbt]; simp only [innermost, hinst, hi]; rfl
  obtain ⟨-, c, π, l', hcode, hn, hfr⟩ :=
    framed_at_innermost_keys hFa hS hE hK hb hinn (by simpa [Family.at] using hcomp)
  have hρ : RootsOk b₀.1.s.W (envOf L d) := frame_rootsOk (by rw [← hbt]; exact b₀.1.ok)
  exact hfr (tv := tv) (dp := dp) (hcheck l e k x hFl he hk c π l' hcode hn T hT)
    (hq l b₀ e L d k x hFl hb he hk hL hbt) hρ (fun _ _ hp => by cases hp)

end ClientFrame
end Verification.TolerantFrames.ReadOnly

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore
open Verification.TolerantFrames.ReadOnly
open HeapObservations

/-- **The returns at reached executions** (proved; the draft's
`ret_reached`, at the worlds of the frame's executions): where the request's
node expressions are source terms, the calls the frame's claim is about
are at positive budgets of admissible worlds typing their heaps with slots
of values, and the
transfer holds at the framed nodes of the request's main graph
(`FramedNodeTransfer`), the returns `framedRet S` hold at the executions
the frame's claim is about, nothing claimed at a throw. The invariant is
`RetInv` (`retInv_step`); at a call it is the frame's reached call itself,
nothing pending. -/
theorem ret_reachedW {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι} {fr : ClientFrame (Ty ι)}
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hty : ∀ n (W : WorldT n) h t, fr.Call n W h t → 0 < n ∧ WorldAdm W ∧ HeapOk n W h)
    (hvals : ∀ n (W : WorldT n) h (L : List Tm) (d : Tm), fr.Call n W h (gotoOf r.program r.start L d r.comp) →
      SlotVals L d)
    (htr : fr.FramedNodeTransfer (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
      r.comp F S) :
    FramedReturnsReachedW r fr F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) := by
  refine ⟨ClientFrame.RetInv fr (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
      r.comp F,
    fun η n W h L d _ hR hN g hg => ?_, fun g p k W h t U h' t' hi hs hx hu hh hK => ClientFrame.retInv_step htr hi hs hx hu hh hK⟩
  obtain ⟨hpos, hadm, hok⟩ := hty n W h _ hN
  let y : Conf := ⟨⟨n, W, h, hpos, hadm, hok⟩, gotoOf r.program r.start L d r.comp, gotoOf_refsOk hsrc hR⟩
  exact .inr ⟨y, rfl, HEq.rfl, rfl, rfl, ⟨(y, g), 0, hN, hg, .refl _⟩, .inl ⟨_, _, _, rfl, hvals n W h L d hN⟩,
    fun _ _ hp => by cases hp⟩

/-- **The returns at reached executions, from the checks** (proved;
`ret_reachedW` with its transfer premise assembled): `framed_transfer` at
each framed node (`nodeTransfer_of_transfer`), its own steps from the
frame's fit and the binding checks (`own_of_fit`), the rule's premise from
the pass's frame check (`framed_of_check`). What it reads besides the
checks: the spec's premises (`hsrc`, `hty`, `hvals`, `ChkSound`,
`StartInv`, the flow's facts at the frame's starts), the members' trace
certificates at `Ψj` (`cert_of_charges` gives them at `Ψ_C`,
`ret_reachedW_of_charges`), the separation the
frame check reads at each framed node's entry, and the callee's effect
bounding the heap along the call's segment (the callback's arrow, part of
`Θ_C`). -/
theorem ret_reachedW_of_checks {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {fr : ClientFrame (Ty ι)} [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)]
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hty : ∀ n (W : WorldT n) h t, fr.Call n W h t → 0 < n ∧ WorldAdm W ∧ HeapOk n W h)
    (hvals : ∀ n (W : WorldT n) h (L : List Tm) (d : Tm), fr.Call n W h (gotoOf r.program r.start L d r.comp) →
      SlotVals L d)
    (hc : fr.ChkSound) (hi : fr.StartInv)
    {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow) (hE : fr.EntryFits Fl.flow) (hK : fr.NoKeys)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ Fl lay) a.1.t = true ∧ HeapLay (layQ Fl lay) a.1.s.h)
    (htok : tokensSomeB Fl = true) (hlow : codesLoweredB Fl = true)
    (hcomp : fr.F.ofC fr.C r.comp = true)
    (hatom : ∀ l e, F l = true → (r.program.map (·.expression))[l]? = some e → ClientFrame.atomCallB e = true)
    {S₀ T : Nat → Sites (fr.F.at fr.C)} {Ψc : Nat → Protocol (fr.F.at fr.C)}
    (hT : ∀ l, F l = true → capClosedB Fl (tokenCaps Fl lay) (S₀ l) (T l) = true)
    (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds Fl) (T l) p).le (Ψc l p) = true)
    (hslots : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ j ∈ ClientFrame.atomSlots e, Sub (π.env l' j) (T l))
    {Φ : Nat → Footprints.Footprint} {q : Nat → Footprints.SepQuery}
    (hcheck : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ T ∈ S l, frameCheckAt (q l) (Ψc l) (Φ l) T Fl.flow.H (π.env l') noKeys (fun _ => false) = true)
    (hq : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      (q l).Sound (envOf L d) b₀.1.s.h)
    {Ψj : Protocol (fr.F.at fr.C)} {G : (St (fr.F.at fr.C) → Prop) → Prop} (certs : fr.TraceCerts Ψj G)
    (hΘ : ∀ p, (fr.Θ p).le (Ψj p) = true) (hW : ∀ l p, (Ψj p).le (Ψc l p) = true)
    (hΦ : ∀ l (b₀ a : Conf × Ghost (fr.F.at fr.C)) m e L d k x v, F l = true → fr.Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      Ex fr.KStep (fun s => Inside fr.F fr.C (r.program.map (·.expression))
        (r.program.map fun n => (n.continuation, n.handler)) L d k x r.comp s.1.t) m b₀ a →
      a.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) v L d k x
        r.comp → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    FramedReturnsReachedW r fr F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) :=
  ret_reachedW hsrc hty hvals
    (ClientFrame.nodeTransfer_of_transfer hc hi hcomp hatom certs hΘ hW
      (ClientFrame.own_of_fit hFa hS hE hwk hly hT htok hlow hle hcomp hatom hslots)
      (ClientFrame.framed_of_check (tv := fr.view.view) (dp := 0) hFa hS hE hK hcomp hatom hcheck hq) hΦ)

/-- **The returns at reached executions, from the checks and the charges**
(proved; `ret_reachedW_of_checks` at the members' certificates
`cert_of_charges` gives at `Ψ_C`, the component's protocol, with no
invariant to keep): its premises but the certificates, and in their place
the reached-term invariant at the frame's starts (`wfS`, a run of `C` not
yet entered only as a binding's body; `FramedSpec.wfS_start` for a framed
plan's frame), the closure check of the capture sites and `O`, the values
of each run an entering step pushes within that closure (`hroots`), and
`Θ_C ⊑ Ψ_C ⊑ Ψc(l)`. -/
theorem ret_reachedW_of_charges {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {fr : ClientFrame (Ty ι)} [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)]
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hty : ∀ n (W : WorldT n) h t, fr.Call n W h t → 0 < n ∧ WorldAdm W ∧ HeapOk n W h)
    (hvals : ∀ n (W : WorldT n) h (L : List Tm) (d : Tm), fr.Call n W h (gotoOf r.program r.start L d r.comp) →
      SlotVals L d)
    (hc : fr.ChkSound) (hi : fr.StartInv)
    {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow) (hE : fr.EntryFits Fl.flow) (hK : fr.NoKeys)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ Fl lay) a.1.t = true ∧ HeapLay (layQ Fl lay) a.1.s.h)
    (htok : tokensSomeB Fl = true) (hlow : codesLoweredB Fl = true)
    (hcomp : fr.F.ofC fr.C r.comp = true)
    (hatom : ∀ l e, F l = true → (r.program.map (·.expression))[l]? = some e → ClientFrame.atomCallB e = true)
    {S₀ T : Nat → Sites (fr.F.at fr.C)} {Ψc : Nat → Protocol (fr.F.at fr.C)}
    (hT : ∀ l, F l = true → capClosedB Fl (tokenCaps Fl lay) (S₀ l) (T l) = true)
    (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds Fl) (T l) p).le (Ψc l p) = true)
    (hslots : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ j ∈ ClientFrame.atomSlots e, Sub (π.env l' j) (T l))
    {Φ : Nat → Footprints.Footprint} {q : Nat → Footprints.SepQuery}
    (hcheck : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ T ∈ S l, frameCheckAt (q l) (Ψc l) (Φ l) T Fl.flow.H (π.env l') noKeys (fun _ => false) = true)
    (hq : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      (q l).Sound (envOf L d) b₀.1.s.h)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hTm : capClosedB Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)
      (capClose Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)) = true)
    (hroots : ∀ (a a₁ : Conf × Ghost (fr.F.at fr.C)), fr.Reached a → XStep fr.F fr.C none fr.Θ fr.chkConf a a₁ →
      δ fr.F fr.C none a₁ = δ fr.F fr.C none a + 1 → ∀ (K : Tm → Tm) E Kc l L d cc, HeapObservations.EvalCtx K →
      a₁.1.t = K (.goto E Kc l L d cc) → ∀ x ∈ vals allC true (.goto E Kc l L d cc),
        ∃ S', VJ Fl.flow a₁.2 a₁.1.s.h.length S' x ∧
          Sub S' (capClose Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)) ∧ layP (layQ Fl lay) x = true)
    (hΘ : ∀ p, (fr.Θ p).le (componentProtocol Fl lay p) = true)
    (hW : ∀ l p, (componentProtocol Fl lay p).le (Ψc l p) = true)
    (hΦ : ∀ l (b₀ a : Conf × Ghost (fr.F.at fr.C)) m e L d k x v, F l = true → fr.Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      Ex fr.KStep (fun s => Inside fr.F fr.C (r.program.map (·.expression))
        (r.program.map fun n => (n.continuation, n.handler)) L d k x r.comp s.1.t) m b₀ a →
      a.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) v L d k x
        r.comp → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    FramedReturnsReachedW r fr F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) :=
  ret_reachedW_of_checks hsrc hty hvals hc hi hFa hS hE hK hwk hly htok hlow hcomp hatom hT hle hslots hcheck hq
    (fun m => ClientFrame.cert_of_charges hFa hS hE hst hwk hly hTm htok hlow hroots m) hΘ hW hΦ

/-- **The returns at reached executions, from the checks, the charges and
the entries** (proved; `ret_reachedW_of_charges` with its premise `hroots`
discharged, `entry_roots` at `cert_of_deep`): where no code of the flow
collects a rest (`noRestB`, a check of the framed plan) and no run of
`C`'s code waits as a binding's body at the frame's starts
(`FramedSpec.noPend_start` for a framed plan's frame), the values of the
run each entering step pushes are the callee's, receiver's and actuals'
of a call of a closure of `C` from outside code, which meet `O`, and those
its callee holds, so they meet the closure of the capture sites and `O` in
depth. -/
theorem ret_reachedW_of_entries {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {fr : ClientFrame (Ty ι)} [DecidableEq (fr.F.at fr.C).Site] [Hashable (fr.F.at fr.C).Site]
    [LawfulHashable (Option (fr.F.at fr.C).Site)]
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hty : ∀ n (W : WorldT n) h t, fr.Call n W h t → 0 < n ∧ WorldAdm W ∧ HeapOk n W h)
    (hvals : ∀ n (W : WorldT n) h (L : List Tm) (d : Tm), fr.Call n W h (gotoOf r.program r.start L d r.comp) →
      SlotVals L d)
    (hc : fr.ChkSound) (hi : fr.StartInv)
    {Fl : FFlow (fr.F.at fr.C)} {lay : List Layout}
    (hFa : Fl.flow.Facts) (hS : fr.FlowSites Fl.flow) (hE : fr.EntryFits Fl.flow) (hK : fr.NoKeys)
    (hwk : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    (hly : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP (layQ Fl lay) a.1.t = true ∧ HeapLay (layQ Fl lay) a.1.s.h)
    (htok : tokensSomeB Fl = true) (hlow : codesLoweredB Fl = true)
    (hcomp : fr.F.ofC fr.C r.comp = true)
    (hatom : ∀ l e, F l = true → (r.program.map (·.expression))[l]? = some e → ClientFrame.atomCallB e = true)
    {S₀ T : Nat → Sites (fr.F.at fr.C)} {Ψc : Nat → Protocol (fr.F.at fr.C)}
    (hT : ∀ l, F l = true → capClosedB Fl (tokenCaps Fl lay) (S₀ l) (T l) = true)
    (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds Fl) (T l) p).le (Ψc l p) = true)
    (hslots : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ j ∈ ClientFrame.atomSlots e, Sub (π.env l' j) (T l))
    {Φ : Nat → Footprints.Footprint} {q : Nat → Footprints.SepQuery}
    (hcheck : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ T ∈ S l, frameCheckAt (q l) (Ψc l) (Φ l) T Fl.flow.H (π.env l') noKeys (fun _ => false) = true)
    (hq : ∀ l (b₀ : Conf × Ghost (fr.F.at fr.C)) e L d k x, F l = true → fr.Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      (q l).Sound (envOf L d) b₀.1.s.h)
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → wfS a.1.t = true)
    (hTm : capClosedB Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)
      (capClose Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)) = true)
    (hnp : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → NoPend (fr.F.at fr.C) a.1.t)
    (hr : noRestB lay = true)
    (hΘ : ∀ p, (fr.Θ p).le (componentProtocol Fl lay p) = true)
    (hW : ∀ l p, (componentProtocol Fl lay p).le (Ψc l p) = true)
    (hΦ : ∀ l (b₀ a : Conf × Ghost (fr.F.at fr.C)) m e L d k x v, F l = true → fr.Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      Ex fr.KStep (fun s => Inside fr.F fr.C (r.program.map (·.expression))
        (r.program.map fun n => (n.continuation, n.handler)) L d k x r.comp s.1.t) m b₀ a →
      a.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) v L d k x
        r.comp → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    FramedReturnsReachedW r fr F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) :=
  ret_reachedW_of_checks hsrc hty hvals hc hi hFa hS hE hK hwk hly htok hlow hcomp hatom hT hle hslots hcheck hq
    (fun m => ClientFrame.cert_of_deep hFa hS hE hst hwk hly hTm htok hlow
      (ClientFrame.entry_roots hFa hS hE hst hly hnp hTm htok hlow hr) m) hΘ hW hΦ

/-- **The returns at reached executions of a framed plan's frame** (proved,
`ret_reachedW_of_entries` at `spec.frame r` and the spec's flow): its
premises the frame's facts discharge are gone, the reached-term invariants
at the frame's calls (`wfS_start`, `noPend_start`), the flow's sites
(`flowSites`), layout provenance and the residual invariant at the calls
(`lay_start`, `wok_start`) from the initial configurations meeting them;
the rest are the checks a framed plan's pass runs, the invariants of the
frame left to prove (the history's `ChkSound` and `StartInv`, the entry's
fit, keys, typing and slots, the frame check's separation at each framed
node's entry) and the trust of `Θ_C` (the callback's arrow, `hΦ`). -/
theorem ret_reachedW_frame {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι) (r : SourceRequest σ ι)
    [Hashable ((spec.frame r).F.at (spec.frame r).C).Site]
    [LawfulHashable (Option ((spec.frame r).F.at (spec.frame r).C).Site)]
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hty : ∀ n (W : WorldT n) h t, (spec.frame r).Call n W h t → 0 < n ∧ WorldAdm W ∧ HeapOk n W h)
    (hvals : ∀ n (W : WorldT n) h (L : List Tm) (d : Tm),
      (spec.frame r).Call n W h (gotoOf r.program r.start L d r.comp) → SlotVals L d)
    (hc : (spec.frame r).ChkSound) (hi : (spec.frame r).StartInv)
    {Fl : FFlow ((spec.frame r).F.at (spec.frame r).C)} (hFl : Fl.flow = spec.flow) {lay : List Layout}
    (hinitW : ∀ x, spec.Initial x → WOk x.t ∧ HeapW x.s.h)
    (hinitL : ∀ x, spec.Initial x → layP (layQ Fl lay) x.t = true ∧ HeapLay (layQ Fl lay) x.s.h)
    (hFa : Fl.flow.Facts) (hE : (spec.frame r).EntryFits Fl.flow) (hK : (spec.frame r).NoKeys)
    (htok : tokensSomeB Fl = true) (hlow : codesLoweredB Fl = true)
    (hcomp : (spec.frame r).F.ofC (spec.frame r).C r.comp = true)
    (hatom : ∀ l e, F l = true → (r.program.map (·.expression))[l]? = some e → ClientFrame.atomCallB e = true)
    {S₀ T : Nat → Sites ((spec.frame r).F.at (spec.frame r).C)}
    {Ψc : Nat → Protocol ((spec.frame r).F.at (spec.frame r).C)}
    (hT : ∀ l, F l = true → capClosedB Fl (tokenCaps Fl lay) (S₀ l) (T l) = true)
    (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds Fl) (T l) p).le (Ψc l p) = true)
    (hslots : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ j ∈ ClientFrame.atomSlots e, Sub (π.env l' j) (T l))
    {Φ : Nat → Footprints.Footprint} {q : Nat → Footprints.SepQuery}
    (hcheck : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      Fl.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ T ∈ S l, frameCheckAt (q l) (Ψc l) (Φ l) T Fl.flow.H (π.env l') noKeys (fun _ => false) = true)
    (hq : ∀ l (b₀ : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) e L d k x, F l = true →
      (spec.frame r).Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      (q l).Sound (envOf L d) b₀.1.s.h)
    (hTm : capClosedB Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)
      (capClose Fl (tokenCaps Fl lay) (captureSites Fl lay ++ Fl.O)) = true)
    (hr : noRestB lay = true)
    (hΘ : ∀ p, ((spec.frame r).Θ p).le (componentProtocol Fl lay p) = true)
    (hW : ∀ l p, (componentProtocol Fl lay p).le (Ψc l p) = true)
    (hΦ : ∀ l (b₀ a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) m e L d k x v, F l = true →
      (spec.frame r).Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      Ex (spec.frame r).KStep (fun s => Inside (spec.frame r).F (spec.frame r).C (r.program.map (·.expression))
        (r.program.map fun n => (n.continuation, n.handler)) L d k x r.comp s.1.t) m b₀ a →
      a.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) v L d k x
        r.comp → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    FramedReturnsReachedW r (spec.frame r) F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) :=
  ret_reachedW_of_entries (Fl := Fl) hsrc hty hvals hc hi hFa (hFl ▸ spec.flowSites r) hE hK
    (spec.wok_start r hinitW) (spec.lay_start r hinitL) htok hlow hcomp hatom hT hle hslots hcheck hq
    (spec.wfS_start r) hTm (spec.noPend_start r) hr hΘ hW hΦ

/-- **The returns at reached executions of a framed plan, from its
component's checks** (proved, `ret_reachedW_frame` at the plan's flow and
layouts): the calls are typed (`call_typed`); the initial configurations
meet layout provenance and the residual invariant where the
initialization's node expressions and the realm's heap do
(`initial_lay`); no code of the component collects a rest where its
binding checks refuse nothing (`componentBindingRefusal_none`). -/
theorem ret_reachedW_spec {σ ι : Type} [Labels ι] [StoreView σ ι] (spec : FramedSpec ι) (r : SourceRequest σ ι)
    {F : Nat → Bool} {S : Nat → List Footprints.Footprint}
    (hsrc : r.program.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (hvals : ∀ n (W : WorldT n) h (L : List Tm) (d : Tm),
      (spec.frame r).Call n W h (gotoOf r.program r.start L d r.comp) → SlotVals L d)
    (hc : (spec.frame r).ChkSound) (hi : (spec.frame r).StartInv)
    (hcomp₀ : spec.componentRefusal.val = none)
    (hEl : ∀ e ∈ spec.initE, layP (layQ spec.fflow spec.lay) e = true) (hEw : ∀ e ∈ spec.initE, WOk e)
    (hLi : ∀ v ∈ spec.initL, layP (layQ spec.fflow spec.lay) v = true ∧ Plain v ∧ free false v = true)
    (hRl : HeapLay (layQ spec.fflow spec.lay) spec.realm) (hRw : HeapW spec.realm)
    (hFa : spec.fflow.flow.Facts) (hE : (spec.frame r).EntryFits spec.fflow.flow) (hK : (spec.frame r).NoKeys)
    (htok : tokensSomeB spec.fflow = true) (hlow : codesLoweredB spec.fflow = true)
    (hcomp : (spec.frame r).F.ofC (spec.frame r).C r.comp = true)
    (hatom : ∀ l e, F l = true → (r.program.map (·.expression))[l]? = some e → ClientFrame.atomCallB e = true)
    {S₀ T : Nat → Sites ((spec.frame r).F.at (spec.frame r).C)}
    {Ψc : Nat → Protocol ((spec.frame r).F.at (spec.frame r).C)}
    (hT : ∀ l, F l = true → capClosedB spec.fflow (tokenCaps spec.fflow spec.lay) (S₀ l) (T l) = true)
    (hle : ∀ l, F l = true → ∀ p, (probeProtocol (flowKinds spec.fflow) (T l) p).le (Ψc l p) = true)
    (hslots : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      spec.fflow.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ j ∈ ClientFrame.atomSlots e, Sub (π.env l' j) (T l))
    {Φ : Nat → Footprints.Footprint} {q : Nat → Footprints.SepQuery}
    (hcheck : ∀ l e k x, F l = true → (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → ∀ c π l',
      spec.fflow.flow.code (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) c = some π →
      NodeOf (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler)) l' k x →
      ∀ T ∈ S l, frameCheckAt (q l) (Ψc l) (Φ l) T spec.fflow.flow.H (π.env l') noKeys (fun _ => false) = true)
    (hq : ∀ l (b₀ : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) e L d k x, F l = true →
      (spec.frame r).Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      (q l).Sound (envOf L d) b₀.1.s.h)
    (hTm : capClosedB spec.fflow (tokenCaps spec.fflow spec.lay) (captureSites spec.fflow spec.lay ++ spec.fflow.O)
      (capClose spec.fflow (tokenCaps spec.fflow spec.lay) (captureSites spec.fflow spec.lay ++ spec.fflow.O)) = true)
    (hΘ : ∀ p, ((spec.frame r).Θ p).le (componentProtocol spec.fflow spec.lay p) = true)
    (hW : ∀ l p, (componentProtocol spec.fflow spec.lay p).le (Ψc l p) = true)
    (hΦ : ∀ l (b₀ a : Conf × Ghost ((spec.frame r).F.at (spec.frame r).C)) m e L d k x v, F l = true →
      (spec.frame r).Reached b₀ →
      (r.program.map (·.expression))[l]? = some e →
      (r.program.map fun n => (n.continuation, n.handler))[l]? = some (k, x) → SlotVals L d →
      b₀.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler))
        (instantiate 0 (envOf L d) e) L d k x r.comp →
      Ex (spec.frame r).KStep (fun s => Inside (spec.frame r).F (spec.frame r).C (r.program.map (·.expression))
        (r.program.map fun n => (n.continuation, n.handler)) L d k x r.comp s.1.t) m b₀ a →
      a.1.t = .frame (r.program.map (·.expression)) (r.program.map fun n => (n.continuation, n.handler)) v L d k x
        r.comp → isVal v = true → TolerantFrames.Action (Φ l) (envOf L d) b₀.1.s a.1.s) :
    FramedReturnsReachedW r (spec.frame r) F (fun l ρ h₀ h₁ => ∀ T ∈ S l, Footprints.Supported T ρ h₀ h₁)
      (fun _ _ _ _ => True) := by
  have hnone := componentBindingRefusal_none (spec.componentRefusal_none hcomp₀)
  have hinit := spec.initial_lay hEl hEw hLi hRl hRw
  exact ret_reachedW_frame spec r hsrc (spec.call_typed r) hvals hc hi (Fl := spec.fflow) rfl
    (fun x hx => (hinit x hx).2) (fun x hx => (hinit x hx).1) hFa hE hK htok hlow hcomp hatom hT hle hslots
    hcheck hq hTm hnone.2.2.2.2.2.1 hΘ hW hΦ

end Verification.SourceClaimJson.PassUnit
