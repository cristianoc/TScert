import Verification.Paper.TolerantFrames.ReadOnlySegment
import Verification.Paper.TolerantFrames.ReadOnlyTraceCert

/-! # Read-only handles: the transfer at a call

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The transfer at a call"). A call of a
frame of `C`'s code at depth `d`, from its call state to its resumption, is
an execution along which at least `d` calls of `C` are active, ending at
`d`. Its steps at the caller's depth of `C`'s code are checked steps at
`d`; each of its steps of outside code at `d` and each call of `C` it
enters from outside code (a member's call, `decompose_trace`) is a run of
outside code at `d`.

- **The segment as a run** (`seg_run`, by the strong induction of
  `decompose` at the caller's depth): a `RunSeq … d d` whose own steps are
  the steps of `C`'s code at `d`, each meeting what the segment's steps
  give (`q`), its inner runs `Run`s at `d`: single outside steps and the
  member calls of `C` the segment makes (`callRun_trace`).
- **The segment's bound** (`seg_bound`, `RunSeq.within` at `dᵢ = d`): own
  steps within `Ψc` below the heap at the call, runs bounded by `Ψj` with
  `Θ ⊑ Ψj ⊑ Ψc`, bound `R_C` by `Ψc`.
- **The transfer at depth `d`** (`transfer_at`): with the callee's effect
  `Φ` bounding the heap, the segment is an action of `Φ ⊕_C Ψc`
  (`Leads.of_bound`, as `readOnly_rule`), and `Framed` gives `Supported`
  (`supported_of_framed`).
- **At a frame of the claim's term** (`ClientFrame.framed_transfer`): a
  call state of the top frame (`CallState`), the frame's term not yet
  returned along the segment (`Inside`) and resumed at its end
  (`Resumes`), at depth `1` (`depthC_frame`, `depthC_frame_val`); the own
  steps within `Ψc` (`SegWithin`), the member calls read from trace
  certificates (`TraceCerts`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-! ## Executions under a larger step relation -/

/-- **An execution of a step relation is one of a larger** (proved). -/
theorem Ex.map {α : Type} {R R' : α → α → Prop} {q : α → Prop} (hR : ∀ a b, q a → R a b → R' a b) :
    ∀ {n : Nat} {a e : α}, Ex R q n a e → Ex R' q n a e
  | _, _, _, .refl a => .refl a
  | _, _, _, .next ha hab he => .next ha (hR _ _ ha hab) (Ex.map hR he)

/-! ## The action of a bounded transition -/

/-- **A bounded transition is a transition of the rule** (proved, as
`readOnly_rule`): a transition bounding `R_P` by `Ψ`, the heap bounded by
`Φ`, is an action of `Φ ⊕_P Ψ` with the history growing. -/
theorem Leads.of_bound {P : Package} {Ψ : Protocol P} {Φ : Footprint} {ρ : Env} {d : Nat} {st st' : St P}
    (hΦ : TolerantFrames.Action Φ ρ st.s st'.s) (hb : RBound Ψ d st st') : Leads d Φ Ψ ρ st st' := by
  obtain ⟨hk, hg, hb⟩ := hb
  refine ⟨⟨hk, fun l v hv => ?_⟩, hg⟩
  obtain ⟨v', hv', ha⟩ := hΦ.2.2 l v hv
  refine ⟨v', hv', fun hR => ?_, fun _ => ha⟩
  obtain ⟨v'', hv'', hc⟩ := hb l v hR hv
  rw [hv'] at hv''
  cases hv''
  exact hc

variable {F : Family} {C : Nat} {c : ComponentTag} {tv : TypeView}
  {Θ Ψ : Protocol (F.at C)} {G : (St (F.at C) → Prop) → Prop} {chk : Conf → Conf → CheckData (F.at C) tv}

/-! ## The segment as a run -/

section SegRun
variable {R : StepRel (F.at C) tv} {Adm : Conf × Ghost (F.at C) → Prop} {off : Nat}
  (hAdm : ∀ a b, Adm a → XStep F C c Θ chk a b → Adm b)
  (mk : ∀ {d : Nat} {a b : Conf × Ghost (F.at C)}, XStep F C c Θ chk a b →
    PkgStep tv d (lift F C c a.1 a.2) (lift F C c b.1 b.2) → R.Rel d (lift F C c a.1 a.2) (lift F C c b.1 b.2))
  (calls : ∀ {d n : Nat} {a b w : Conf × Ghost (F.at C)}, Adm a → XStep F C c Θ chk a b → δ F C c a = d →
    δ F C c b = d + 1 → δ F C c w = d → Ex (XStep F C c Θ chk) (QCall F C c d) n b w →
    a.2.A.length = δ F C c a + off → ∃ k, Run Θ Ψ G k d (lift F C c a.1 a.2) (lift F C c w.1 w.2))
include hAdm mk calls

/-- **The segment as a run** (proved; the draft's `seg_run`, by the strong
induction of `decompose` at the caller's depth): an execution from a state
with `d > 0` calls of `C` active to one with `d`, whose every state a step
leaves meets `Q`, a condition giving at least `d` calls active, from a
state an execution under `Q` from `a₀` reaches, is a run at `d` whose own
steps are its steps of `C`'s code at `d` and whose inner runs are runs of
outside code at `d`: a step of outside code keeping the calls is an outside
step (`outsideStep_of_step`), an entry with the execution up to the first
state with `d` calls active again is a run of outside code at `d` (`calls`,
a member call: `callRun_trace` over trace certificates), and a step of `C`'s code at
`d` is a checked step at `d` (`pkgStep_of`), not an exit, as the next state
has `d` calls active, meeting `q` where the segment's steps give it. -/
theorem seg_run {d : Nat} (hd0 : 0 < d) {Q : Conf × Ghost (F.at C) → Prop}
    (hQ : ∀ x, Q x → d ≤ δ F C c x) {a₀ : Conf × Ghost (F.at C)} {q : St (F.at C) → St (F.at C) → Prop}
    (hq : ∀ m x y, Ex (XStep F C c Θ chk) Q m a₀ x → Q x → XStep F C c Θ chk x y → δ F C c x = d →
      ¬ Outside F C c x.1 → δ F C c y = d → q (lift F C c x.1 x.2) (lift F C c y.1 y.2)) :
    ∀ (n : Nat) (a e : Conf × Ghost (F.at C)) (m : Nat), Ex (XStep F C c Θ chk) Q m a₀ a →
      Ex (XStep F C c Θ chk) Q n a e → Adm a → δ F C c a = d → δ F C c e = d →
      a.2.A.length = δ F C c a + off →
      RunSeq R (fun st st' => ∃ k, Run Θ Ψ G k d st st') d d q (lift F C c a.1 a.2) (lift F C c e.1 e.2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro a e m hpre hex hAa hda hde hl
  cases hex with
  | refl => exact .nil _
  | next hqa hx hrest =>
    rename_i n' b
    have hb : Adm b := hAdm _ _ hAa hx
    have hlb := XStep.len hx hl
    have hpre' : Ex (XStep F C c Θ chk) Q (m + 1) a₀ b := hpre.snoc hqa hx
    have hdb : d ≤ δ F C c b := by
      cases hrest with
      | refl => omega
      | next hqb _ _ => exact hQ _ hqb
    have hlen : d ≤ (lift F C c a.1 a.2).g.A.length := by simp only [lift]; simp only [δ] at hl hda; omega
    obtain ⟨hs, hdisc, hg, hh⟩ := hx
    by_cases ho : Outside F C c a.1
    · have h1 := hdisc.1 ho
      by_cases heq : depthC F C c b.1.t = depthC F C c a.1.t
      · -- A step of outside code at `d`: an inner run of one outside step.
        have hk' := kind_outside ho heq
        have hA : a.2.A ≠ [] := by
          intro h; rw [h] at hl; simp only [δ, List.length_nil] at hl hda; omega
        have hbg : b.2 = a.2.alloc a.1.s.h.length (fun _ => none) (chk a.1 b.1).key := by
          rw [hg]; simp only [Ghost.next, Ghost.stepAt, stepKind_conf, hk']; exact outsideNext_of_ne hA
        have hrow := hyp_row hk' hh
        rw [← hg, hbg] at hrow
        have hos := outsideStep_of_step hs ho hrow
        rw [← hbg] at hos
        exact .inner hlen ⟨0, Run.outside' hos (Run.nil' _)⟩
          (ih n' (by omega) b e (m + 1) hpre' hrest hb (by simp only [δ] at hda ⊢; omega) hde hlb)
      · -- An entry: the member's call up to the first state at `d`, an inner run.
        have hdb1 : δ F C c b = d + 1 := by simp only [δ] at hda ⊢; omega
        obtain ⟨w, n₁, n₂, h₁, hw, h₂, hn⟩ := hrest.first (p := fun x => δ F C c x ≤ d) (by omega)
        have hdw : δ F C c w = d := by
          cases h₂ with
          | refl => exact hde
          | next hqw _ _ => have := hQ _ hqw; have : δ F C c w ≤ d := hw; omega
        have hcq : Ex (XStep F C c Θ chk) (QCall F C c d) n₁ b w := h₁.mono fun x hx => by
          simp only [QCall]; have := hx.2; omega
        have hpw : Ex (XStep F C c Θ chk) Q (m + 1 + n₁) a₀ w := hpre'.trans (h₁.mono fun _ hx => hx.1)
        have hAw : Adm w := h₁.carry (r := Adm) (fun x y _ hxy hx' => hAdm x y hx' hxy) hb
        have hlw : w.2.A.length = δ F C c w + off :=
          h₁.carry (r := fun x => x.2.A.length = δ F C c x + off) (fun _ _ _ hs' h => hs'.len h) hlb
        exact .inner hlen (calls hAa ⟨hs, hdisc, hg, hh⟩ hda hdb1 hdw hcq hl)
          (ih n₂ (by omega) w e _ hpw h₂ hAw hdw hde hlw)
    · -- A step of `C`'s code at `d`: a checked step at `d`.
      have h2 := hdisc.2 ho
      have hdb' : δ F C c b = d := by simp only [δ] at hda hdb ⊢; omega
      have hne : kind F C c a.1 b.1 ≠ .outside := kind_ne_outside fun h => ho h.1
      have hpk := pkgStep_of (d := d) hs hne (hyp_props hne hh) (by simp only [δ] at hl hda; omega)
        (fun hx' => by
          have := (kind_spec (F := F) (C := C) (c := c) a.1 b.1).2.2.1 hx'
          simp only [δ] at hda hdb'; omega)
      rw [← hg] at hpk
      exact .step (mk ⟨hs, hdisc, hg, hh⟩ hpk) (hq m a b hpre hqa ⟨hs, hdisc, hg, hh⟩ hda ho hdb')
        (ih n' (by omega) b e (m + 1) hpre' hrest hb hdb' hde hlb)

/-- **The segment's bound** (proved, `seg_run` and `RunSeq.within` at
`dᵢ = d`): where every step of `C`'s code at `d` of the segment from `a₀`
is within `Ψc` below the heap at `a₀`, and `Θ ⊑ Ψ ⊑ Ψc`, the segment
bounds `R_C` at `a₀` by `Ψc` and keeps the invariants: its runs of outside
code at `d` by `Run.bound`, lifted to `Ψc`. -/
theorem seg_bound {Ψc : Protocol (F.at C)} (hΘ : ∀ p, (Θ p).le (Ψ p) = true)
    (hW : ∀ p, (Ψ p).le (Ψc p) = true) {d : Nat} {Q : Conf × Ghost (F.at C) → Prop}
    (hQ : ∀ x, Q x → d ≤ δ F C c x) {n : Nat} {a e : Conf × Ghost (F.at C)}
    (hq : ∀ m x y, Ex (XStep F C c Θ chk) Q m a x → Q x → XStep F C c Θ chk x y → δ F C c x = d →
      ¬ Outside F C c x.1 → δ F C c y = d →
      StepWithin Ψc a.1.s.h.length (lift F C c x.1 x.2) (lift F C c y.1 y.2))
    (hex : Ex (XStep F C c Θ chk) Q n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2)) :
    RBound Ψc d (lift F C c a.1 a.2) (lift F C c e.1 e.2) ∧ Ok d (lift F C c e.1 e.2) := by
  have hr := seg_run hAdm mk calls hok.pos hQ hq n a e 0 (.refl a) hex hAa hda hde hl
  obtain ⟨hb, ok'⟩ := RunSeq.within (.inl rfl) (fun t t' ⟨k, hk⟩ ho =>
    let h := Run.bound hΘ k d t t' hk ho
    ⟨h.1.mono hW, h.2⟩) hr hok
  exact ⟨hb.all, ok'⟩

/-- **The transfer at depth `d`** (proved): the segment of `seg_bound`, the
heap bounded by the callee's effect `Φ`, the support `S` meeting the rule's
premise at `Ψc` at the call state (`Framed`), is supported from the call's
heap to the resumption's (`Leads.of_bound`, `supported_of_framed`). -/
theorem transfer_at {Ψc : Protocol (F.at C)} (hΘ : ∀ p, (Θ p).le (Ψ p) = true)
    (hW : ∀ p, (Ψ p).le (Ψc p) = true) {d : Nat} {Q : Conf × Ghost (F.at C) → Prop}
    (hQ : ∀ x, Q x → d ≤ δ F C c x) {n : Nat} {a e : Conf × Ghost (F.at C)}
    (hq : ∀ m x y, Ex (XStep F C c Θ chk) Q m a x → Q x → XStep F C c Θ chk x y → δ F C c x = d →
      ¬ Outside F C c x.1 → δ F C c y = d →
      StepWithin Ψc a.1.s.h.length (lift F C c x.1 x.2) (lift F C c y.1 y.2))
    (hex : Ex (XStep F C c Θ chk) Q n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2)) {Φ S : Footprint} {ρ : Env}
    (hΦ : TolerantFrames.Action Φ ρ a.1.s e.1.s) (hfr : Framed Φ Ψc S ρ (lift F C c a.1 a.2)) :
    Supported S ρ a.1.s.h e.1.s.h :=
  supported_of_framed hfr
    (Leads.of_bound (st := lift F C c a.1 a.2) (st' := lift F C c e.1 e.2) hΦ
      (seg_bound hAdm mk calls hΘ hW hQ hq hex hAa hda hde hl hok).1).1

end SegRun

/-! ## At a frame of the claim's term -/

/-- **A frame's term that has returned**: a value, or a throw. -/
def Returned (u : Tm) : Prop := isVal u = true ∨ ∃ w, Raises u w

/-- **A frame of `C`'s code at the top of a term**, with code `E, K`,
slots `L`, default `d`, continuation `k`, handler `x` and tag `comp`, its
running term `u`. -/
def TopFrame (F : Family) (C : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (L : List Tm) (d : Tm) (k : ControlFlow.Continuation) (x : Option ControlFlow.Target) (comp : ComponentTag)
    (t u : Tm) : Prop :=
  t = .frame E K u L d k x comp ∧ F.ofC C comp = true

/-- **A call state of the top frame** (the draft, Definitions): the frame of
`C`'s code at the top of the term, its running term a call whose callee,
receiver and arguments are values. -/
def CallState (F : Family) (C : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (L : List Tm) (d : Tm) (k : ControlFlow.Continuation) (x : Option ControlFlow.Target) (comp : ComponentTag)
    (t : Tm) : Prop :=
  ∃ f r args, TopFrame F C E K L d k x comp t (.invoke f r args) ∧ isVal f = true ∧ isVal r = true ∧
    ∀ a ∈ args, isVal a = true

/-- **A state inside the call** (the draft, the call's segment): the same
frame at the top, its running term not yet returned. -/
def Inside (F : Family) (C : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (L : List Tm) (d : Tm) (k : ControlFlow.Continuation) (x : Option ControlFlow.Target) (comp : ComponentTag)
    (t : Tm) : Prop :=
  ∃ u, TopFrame F C E K L d k x comp t u ∧ ¬ Returned u

/-- **The resumption** (the draft, the call's segment): the same frame at
the top, its running term returned, a value (a normal return) or a throw
(an exceptional one). -/
def Resumes (F : Family) (C : Nat) (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target))
    (L : List Tm) (d : Tm) (k : ControlFlow.Continuation) (x : Option ControlFlow.Target) (comp : ComponentTag)
    (t : Tm) : Prop :=
  ∃ u, TopFrame F C E K L d k x comp t u ∧ Returned u

/-- **A frame of `C`'s code alone above the top segment holds one call of
`C`** (proved, `path_frame`). -/
theorem depthC_frame_val {F : Family} {C : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {u : Tm} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (hc : F.ofC C comp = true) (hu : path comp u = [(comp, u)]) :
    depthC F C none (.frame E K u L d k x comp) = 1 := by
  have hn : F.ofC C none = false := by simp [Family.ofC, Family.Runs]
  simp [depthC, path_frame hu, blocks, hc, hn]

/-- A call state holds one call of `C` (proved). -/
theorem CallState.depth {F : Family} {C : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} {t : Tm}
    (h : CallState F C E K L d k x comp t) : depthC F C none t = 1 := by
  obtain ⟨f, r, args, ⟨rfl, hc⟩, hf, hr, ha⟩ := h
  refine depthC_frame_val hc ?_
  simp only [path, hf, hr, Bool.true_eq_false, if_false]
  exact pathArgs_vals _ ha

/-- A resumption holds one call of `C` (proved). -/
theorem Resumes.depth {F : Family} {C : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} {t : Tm}
    (h : Resumes F C E K L d k x comp t) : depthC F C none t = 1 := by
  obtain ⟨u, ⟨rfl, hc⟩, hu | ⟨w, hw⟩⟩ := h
  · exact depthC_frame_val hc (path_val hu)
  · exact depthC_frame_val hc (raises_path hw _)

/-- A state inside the call holds at least one call of `C` (proved,
`depthC_frame`). -/
theorem Inside.depth {F : Family} {C : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} {t : Tm}
    (h : Inside F C E K L d k x comp t) : 1 ≤ depthC F C none t := by
  obtain ⟨u, ⟨rfl, hc⟩, -⟩ := h
  exact depthC_frame hc

/-- **A step of a frame whose term has not returned is a step of its term**
(proved; the draft's `frameC_shape`): the frame's code, slots, default,
continuation, handler and tag are kept, so the frame's environment is the
same at every state of the segment. -/
theorem frameC_shape {h h' : Heap} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {u t' : Tm} {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target}
    {comp : ComponentTag} (hs : Step h (.frame E K u L d k x comp) h' t') (hu : ¬ Returned u) :
    ∃ u', Step h u h' u' ∧ t' = .frame E K u' L d k x comp := by
  cases hs with
  | frameC hs' => exact ⟨_, hs', rfl⟩
  | frameRet hv => exact absurd (.inl hv) hu
  | frameBind hv => exact absurd (.inl hv) hu
  | frameEffect hv => exact absurd (.inl hv) hu
  | frameYes => exact absurd (.inl rfl) hu
  | frameNo => exact absurd (.inl rfl) hu
  | frameYesBind => exact absurd (.inl rfl) hu
  | frameNoBind => exact absurd (.inl rfl) hu
  | frameTag hv => exact absurd (.inl hv) hu
  | frameHandle hr => exact absurd (.inr ⟨_, hr⟩) hu
  | frameRaise hr => exact absurd (.inr ⟨_, hr⟩) hu

/-- **The segment runs the frame's term** (proved, `frameC_shape` at each
step): along an execution of steps keeping the obligation whose every state
a step leaves is inside the call, from the frame with the running term
`u₀`, the frame's term runs: the state reached is the same frame around a
term `u₀` reaches by the calculus's steps. -/
theorem FrameCore.inside_run {τ : Type} {core : FrameCore τ} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} :
    ∀ {m : Nat} {a y : Conf × Ghost (core.F.at core.C)} {u₀ : Tm},
      Ex core.KStep (fun s => Inside core.F core.C E K L d k x comp s.1.t) m a y →
      a.1.t = .frame E K u₀ L d k x comp →
      ∃ u, HeapObservations.Steps m a.1.s.h u₀ y.1.s.h u ∧ y.1.t = .frame E K u L d k x comp
  | _, _, _, _, .refl _, ha => ⟨_, .refl, ha⟩
  | _, a, _, u₀, .next hin hab hrest, ha => by
    obtain ⟨u, ⟨hu, -⟩, hnr⟩ := hin
    rw [ha] at hu
    cases hu
    have hs := hab.1.step
    rw [ha] at hs
    obtain ⟨u', hs', ht'⟩ := frameC_shape hs hnr
    obtain ⟨w, hw, hy⟩ := FrameCore.inside_run hrest ht'
    exact ⟨w, .next hs' hw, hy⟩

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **The own steps of a segment within `Ψc`** (the draft's `SegWithin`):
every step of `C`'s code at the call's depth, from a state of the segment
from `a` (the top frame `E, K, L, d, k, x, comp` not yet returned), is
within `Ψc` below the heap at `a`. -/
def SegWithin (Ψc : Protocol (fr.F.at fr.C)) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (L : List Tm) (d : Tm)
    (k : ControlFlow.Continuation) (x : Option ControlFlow.Target) (comp : ComponentTag)
    (a : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  ∀ m y z, Ex fr.KStep (fun s => Inside fr.F fr.C E K L d k x comp s.1.t) m a y →
    Inside fr.F fr.C E K L d k x comp y.1.t → fr.KStep y z → δ fr.F fr.C none y = δ fr.F fr.C none a →
    ¬ Outside fr.F fr.C none y.1 →
    StepWithin Ψc a.1.s.h.length (lift fr.F fr.C none y.1 y.2) (lift fr.F fr.C none z.1 z.2)

/-- **The trace certificates a frame's members carry**: for each code a
call of `C` enters, a certificate over the traces of the calls of it made
from the states the claim's executions reach. -/
def TraceCerts (Ψ : Protocol (fr.F.at fr.C)) (G : (St (fr.F.at fr.C) → Prop) → Prop) : Prop :=
  ∀ m : Option Code, TraceCert fr.F fr.C none fr.Θ fr.chkConf fr.Reached Ψ G m

variable {fr}

/-- **Framed transfer** (proved; the draft, "The transfer at a call"): from
a reached call state of the claim's top frame, along its segment keeping
`Θ_C` (the frame not yet returned) to its resumption, with certificates at
`Ψj` (`Θ_C ⊑ Ψj ⊑ Ψc`) over the traces of the calls of `C` the claim's
executions make,
the segment's own steps within `Ψc`, the heap bounded by the callee's
effect `Φ` at the frame's environment, and a support `S` meeting the
rule's premise at `Ψc` at the call state, `S` is supported from the call's
heap to the resumption's. By `transfer_at` at depth `1`
(`CallState.depth`, `Inside.depth`, `Resumes.depth`), the executions
being the paper's (`ex_xstep`) and the call state `Ok` (`reached_ok`). -/
theorem framed_transfer (hc : fr.ChkSound) (hi : fr.StartInv) {Ψj Ψc : Protocol (fr.F.at fr.C)}
    {G : (St (fr.F.at fr.C) → Prop) → Prop} (certs : fr.TraceCerts Ψj G) (hΘ : ∀ p, (fr.Θ p).le (Ψj p) = true)
    (hW : ∀ p, (Ψj p).le (Ψc p) = true) {a e : Conf × Ghost (fr.F.at fr.C)} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} {n : Nat}
    (ha : fr.Reached a) (hcall : CallState fr.F fr.C E K L d k x comp a.1.t)
    (hex : Ex fr.KStep (fun s => Inside fr.F fr.C E K L d k x comp s.1.t) n a e)
    (hres : Resumes fr.F fr.C E K L d k x comp e.1.t) (hown : fr.SegWithin Ψc E K L d k x comp a)
    {Φ S : Footprint} {ρ : Env} (hΦ : TolerantFrames.Action Φ ρ a.1.s e.1.s)
    (hfr : Framed Φ Ψc S ρ (lift fr.F fr.C none a.1 a.2)) :
    Footprints.Supported S ρ a.1.s.h e.1.s.h := by
  have hda : δ fr.F fr.C none a = 1 := hcall.depth
  have hde : δ fr.F fr.C none e = 1 := hres.depth
  have hx := ex_xstep hc ha hex
  have hok := reached_ok hc hi ha
  have hok1 : Ok 1 (lift fr.F fr.C none a.1 a.2) := by have := hok.2.2 (by omega); rwa [hda] at this
  refine transfer_at (fun a b h hx => Reached.xstep h hx) (fun hx p => XStep.checked hx p)
    (fun hAa hx hda hdb hdw hcq hl => ⟨_, callRun_trace (fun a b h hx => Reached.xstep h hx) certs
      (fun hx p => XStep.checked hx p) 0 hAa hx hda hdb hdw hcq hl⟩) hΘ hW
    (Q := fun s => Inside fr.F fr.C E K L d k x comp s.1.t) (fun s hs => hs.depth)
    (fun m y z hpre hy hyz hdy ho _ => hown m y z
      (Ex.map (fun _ _ _ h => kstep_of_xstep h) hpre) hy (kstep_of_xstep hyz) (by rw [hdy, hda]) ho)
    hx ha hda hde (by simpa using hok.1) hok1 hΦ hfr

end ClientFrame
end Verification.TolerantFrames.ReadOnly
