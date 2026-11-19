import Verification.Paper.TolerantFrames.ReadOnlyCert
import Verification.Paper.TolerantFrames.ReadOnlyBridge

/-! # Read-only handles: certificates over a call's trace

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Certificates"). A member's
certificate states, of each actual call of a code from a reached state, the
bound and the guarantees over the call's trace: its entering step and
every own step after it (`TraceCert`), each read at the call's entry.

- **The call's entry and its own steps** (`Entering`, `OwnAfter`): the
  entering step from a state meeting `Adm`, into the code `m`, one call
  deeper; a step of `C`'s code one call deeper than the entry, from a state
  the call's execution reaches while it is active.
- **The member a trace's steps give** (`traceMember`): its call is a run
  whose own steps are within `Ψ` below its entry's heap and keep each
  invariant of `G` (`ownQ`), its inner runs one call deeper; its bound is
  `MemberRun.within`, its invariants kept step by step
  (`RunSeq.keeps`).
- **The decomposition over traces** (`decompose_trace`, `decompose`
  restated): an actual execution inside a call of `C` is a run of outside
  code whose member calls are calls of `traceMember`, each own step's
  property read from the certificate of the code its call entered at the
  call's entry, the entering step prepended. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-! ## Runs whose own steps keep an invariant -/

variable {P : Package}

/-- **A run's own steps meeting a smaller property** (proved). -/
theorem RunSeq.mono {tv : TypeView} {R : StepRel P tv} {Inner : St P → St P → Prop} {d dᵢ : Nat}
    {q q' : St P → St P → Prop} (hq : ∀ t t', q t t' → q' t t') {st st' : St P}
    (hr : RunSeq R Inner d dᵢ q st st') : RunSeq R Inner d dᵢ q' st st' := by
  induction hr with
  | nil st => exact .nil st
  | step hp hs _ ih => exact .step hp (hq _ _ hs) ih
  | inner hl hin _ ih => exact .inner hl hin ih

/-- **A member's run keeps an invariant** (proved, by induction on the
run): its own steps keep it, its inner runs one call deeper keep it. -/
theorem RunSeq.keeps {tv : TypeView} {R : StepRel P tv} {Ψ : Protocol P} {Inner : St P → St P → Prop}
    {d : Nat} {q : St P → St P → Prop} {I : St P → Prop}
    (hI : ∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t')
    (hIk : ∀ t t', Inner t t' → Ok (d + 1) t → I t → I t')
    (hstep : ∀ t t', q t t' → I t → I t') {st st' : St P}
    (hr : MemberRun.Own R Inner d q st st') (hok : Ok d st) (hi : I st) : I st' := by
  induction hr with
  | nil st => exact hi
  | step hp hs _ ih => exact ih (pkg_step_ok (R.pkg hp) hok).1 (hstep _ _ hs hi)
  | inner hl hin _ ih =>
    have ok₁ := (hI _ _ hin (hok.deeper hl)).2
    exact ih (ok₁.shallower hok.pos) (hIk _ _ hin (hok.deeper hl) hi)

/-- **What a member's own step meets**: within `Ψ` below `b`, the heap's
length at the call's entry, and keeping each invariant of `G`. -/
def ownQ (Ψ : Protocol P) (G : (St P → Prop) → Prop) (b : Nat) (t t' : St P) : Prop :=
  StepWithin Ψ b t t' ∧ ∀ I, G I → I t → I t'

/-- **The member a call's trace gives**: its call is a run whose own steps
meet `ownQ` at its entry's heap, its inner runs one call deeper. Bounded by
`MemberRun.within`, its invariants kept by `RunSeq.keeps` (proved). -/
def traceMember {tv : TypeView} (R : StepRel P tv) (Ψ : Protocol P) (G : (St P → Prop) → Prop) :
    Member P Ψ G where
  Call d Inner st st' := MemberRun.Own R Inner d (ownQ Ψ G st.s.h.length) st st'
  bound _ _ hI _ _ hr hok :=
    let h := MemberRun.within hI (hr.mono fun _ _ h => h.1) hok
    ⟨h.1.all, h.2⟩
  keeps I hG _ _ hI hIk _ _ hr hok hi :=
    RunSeq.keeps hI hIk (fun _ _ h => h.2 I hG) hr hok hi

/-! ## Certificates over a call's trace -/

variable {F : Family} {C : Nat} {c : ComponentTag} {tv : TypeView}

section Trace
variable (F C c) (Θ : Protocol (F.at C)) (chk : Conf → Conf → CheckData (F.at C) tv)

/-- **The entering step of a call of the code `m`** from a state meeting
`Adm`: one call of `C` deeper. -/
def Entering (Adm : Conf × Ghost (F.at C) → Prop) (m : Option Code) (a a₁ : Conf × Ghost (F.at C)) : Prop :=
  Adm a ∧ XStep F C c Θ chk a a₁ ∧ entered c a₁.1.t = m ∧ δ F C c a₁ = δ F C c a + 1

/-- **An own step of a call after its entry**: a step of `C`'s code, one
call deeper than the entry, from a state the call's execution reaches while
the call is active. -/
def OwnAfter (a a₁ y z : Conf × Ghost (F.at C)) : Prop :=
  (∃ n, Ex (XStep F C c Θ chk) (QCall F C c (δ F C c a)) n a₁ y) ∧ XStep F C c Θ chk y z ∧
    δ F C c y = δ F C c a + 1 ∧ ¬ Outside F C c y.1

/-- **A member's certificate over its calls' traces** (the draft,
"Certificates"): of each actual call of the code `m` from a state meeting
`Adm`, its entering step and every own step after it are within `Ψ` below
the heap at the call's entry and keep each invariant of `G`. -/
structure TraceCert (Adm : Conf × Ghost (F.at C) → Prop) (Ψ : Protocol (F.at C))
    (G : (St (F.at C) → Prop) → Prop) (m : Option Code) : Prop where
  enterWithin : ∀ a a₁, Entering F C c Θ chk Adm m a a₁ →
    StepWithin Ψ a.1.s.h.length (lift F C c a.1 a.2) (lift F C c a₁.1 a₁.2)
  own : ∀ a a₁ y z, Entering F C c Θ chk Adm m a a₁ → OwnAfter F C c Θ chk a a₁ y z →
    StepWithin Ψ a.1.s.h.length (lift F C c y.1 y.2) (lift F C c z.1 z.2)
  enterKeeps : ∀ I, G I → ∀ a a₁, Entering F C c Θ chk Adm m a a₁ →
    I (lift F C c a.1 a.2) → I (lift F C c a₁.1 a₁.2)
  tolerant : ∀ I, G I → ∀ a a₁ y z, Entering F C c Θ chk Adm m a a₁ → OwnAfter F C c Θ chk a a₁ y z →
    I (lift F C c y.1 y.2) → I (lift F C c z.1 z.2)

end Trace

variable {Θ Ψ : Protocol (F.at C)} {G : (St (F.at C) → Prop) → Prop} {chk : Conf → Conf → CheckData (F.at C) tv}

section DecomposeTrace
variable {R : StepRel (F.at C) tv} {Adm : Conf × Ghost (F.at C) → Prop}
  (hAdm : ∀ a b, Adm a → XStep F C c Θ chk a b → Adm b)
  (certs : (m : Option Code) → TraceCert F C c Θ chk Adm Ψ G m)
  (mk : ∀ {d : Nat} {a b : Conf × Ghost (F.at C)}, XStep F C c Θ chk a b →
    PkgStep tv d (lift F C c a.1 a.2) (lift F C c b.1 b.2) → R.Rel d (lift F C c a.1 a.2) (lift F C c b.1 b.2))
include hAdm certs mk

/-- **An actual execution is a run of outside code, its member calls read
from their traces** (proved; the draft's `decompose` restated over
`TraceCert`, by the strong induction of `decompose`). An execution inside a
call of `C` at depth `d` (`QRun`), from and to a state with `d` calls
active, is a run within the budget of its length whose member calls are
calls of `traceMember`: an entry, the entering step meeting `ownQ` at its
own heap by the certificate of the code it enters (`enterWithin`,
`enterKeeps`), and the execution up to the first state with `d` calls
active again. Inside such a call entered at `a` (`QCall`), every step of
`C`'s code is a checked step meeting `ownQ` at `a`'s heap (`own`,
`tolerant`), and an execution from a state whose active frame is outside
`C` up to the first state of `C`'s code with `d + 1` calls active is a run
of outside code one call deeper. -/
theorem decompose_trace (off : Nat) : ∀ n : Nat,
    (∀ (d : Nat) (a e : Conf × Ghost (F.at C)), 0 < d → Ex (XStep F C c Θ chk) (QRun F C c d) n a e → Adm a →
      δ F C c a = d → δ F C c e = d → a.2.A.length = δ F C c a + off →
      ∀ k, n ≤ k → Run Θ Ψ G k d (lift F C c a.1 a.2) (lift F C c e.1 e.2)) ∧
    (∀ (d : Nat) (a₀ a₁ a e : Conf × Ghost (F.at C)), Entering F C c Θ chk Adm (entered c a₁.1.t) a₀ a₁ →
      δ F C c a₀ = d → (∃ n₀, Ex (XStep F C c Θ chk) (QCall F C c d) n₀ a₁ a) →
      Ex (XStep F C c Θ chk) (QCall F C c d) n a e → Adm a →
      δ F C c a = d + 1 → δ F C c e = d → a.2.A.length = δ F C c a + off →
      ∀ k, n ≤ k → MemberRun.Own R (Run Θ Ψ G k (d + 1)) d (ownQ Ψ G a₀.1.s.h.length)
        (lift F C c a.1 a.2) (lift F C c e.1 e.2)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hlen : ∀ {q : Conf × Ghost (F.at C) → Prop} {m : Nat} {a b : Conf × Ghost (F.at C)},
      Ex (XStep F C c Θ chk) q m a b → a.2.A.length = δ F C c a + off → b.2.A.length = δ F C c b + off :=
    fun hx hl => hx.carry (r := fun x => x.2.A.length = δ F C c x + off) (fun _ _ _ hs h => hs.len h) hl
  have hcar : ∀ {q : Conf × Ghost (F.at C) → Prop} {m : Nat} {a b : Conf × Ghost (F.at C)},
      Ex (XStep F C c Θ chk) q m a b → Adm a → Adm b :=
    fun hx ha => hx.carry (r := Adm) (fun x y _ hxy hx' => hAdm x y hx' hxy) ha
  refine ⟨fun d a e hd0 hex hAa hda hde hl k hk => ?_,
    fun d a₀ a₁ a e hent hd₀ hpre hex hAa hda hde hl k hk => ?_⟩
  · cases hex with
    | refl => exact Run.nil' _
    | next hq hx hrest =>
      rename_i m b
      obtain ⟨hs, hdisc, hg, hh⟩ := hx
      have ho : Outside F C c a.1 := hq.2 hda
      have h1 := hdisc.1 ho
      by_cases heq : depthC F C c b.1.t = depthC F C c a.1.t
      · -- A step of outside code.
        have hk' := kind_outside ho heq
        have hA : a.2.A ≠ [] := by
          intro h; rw [h] at hl; simp only [δ, List.length_nil] at hl hda; omega
        have hb : b.2 = a.2.alloc a.1.s.h.length (fun _ => none) (chk a.1 b.1).key := by
          rw [hg]; simp only [Ghost.next, Ghost.stepAt, stepKind_conf, hk']; exact outsideNext_of_ne hA
        have hrow := hyp_row hk' hh
        rw [← hg, hb] at hrow
        have hos := outsideStep_of_step hs ho hrow
        rw [← hb] at hos
        exact Run.outside' hos ((ih m (by omega)).1 d b e hd0 hrest (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩)
          (by simp only [δ] at hda ⊢; omega) hde
          (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) k (by omega))
      · -- The entry of a call of `C`: the entering step, then the call's trace.
        have hlt : depthC F C c a.1.t < depthC F C c b.1.t := by omega
        have hk' := kind_enter hlt
        have hne : kind F C c a.1 b.1 ≠ .outside := by rw [hk']; simp
        have hpk := pkgStep_of (d := d) hs hne (hyp_props hne hh) (by simp only [δ] at hl hda; omega)
          (fun h => by rw [hk'] at h; cases h)
        rw [← hg] at hpk
        have hdb : δ F C c b = d + 1 := by simp only [δ] at hda ⊢; omega
        have hent : Entering F C c Θ chk Adm (entered c b.1.t) a b :=
          ⟨hAa, ⟨hs, hdisc, hg, hh⟩, rfl, by rw [hdb, hda]⟩
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨w, n₁, n₂, h₁, hw, h₂, hn⟩ := hrest.first (p := fun x => δ F C c x ≤ d) (by omega)
        have hdw : d ≤ δ F C c w := h₁.carry (r := fun x => d ≤ δ F C c x) (by
          rintro x y ⟨-, hnx⟩ ⟨-, hd', -, -⟩ hx
          simp only [δ] at hnx hx ⊢
          by_cases hox : Outside F C c x.1
          · have := (hd'.1 hox).1; omega
          · have := (hd'.2 hox).2; omega) (by omega)
        have hdw' : δ F C c w = d := by have hw' : δ F C c w ≤ d := hw; omega
        have hcq : Ex (XStep F C c Θ chk) (QCall F C c d) n₁ b w := h₁.mono fun x hx => by
          simp only [QCall]; simp only [QRun] at hx; omega
        have hM := (ih n₁ (by omega)).2 d a b b w hent hda ⟨0, .refl b⟩ hcq
          (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩) hdb hdw' (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) k' (by omega)
        have hcall : (traceMember R Ψ G).Call d (Run Θ Ψ G k' (d + 1)) (lift F C c a.1 a.2) (lift F C c w.1 w.2) :=
          .step (mk ⟨hs, hdisc, hg, hh⟩ hpk)
            ⟨(certs _).enterWithin a b hent, fun I hG => (certs _).enterKeeps I hG a b hent⟩ hM
        exact RunAt.member _ hcall ((ih n₂ (by omega)).1 d w e hd0 h₂ (hcar h₁ (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩))
          hdw' hde (hlen h₁ (XStep.len ⟨hs, hdisc, hg, hh⟩ hl)) (k' + 1) (by omega))
  · by_cases ho : Outside F C c a.1
    · -- A run of outside code one call deeper, up to the first state of `C`'s code with `d + 1` calls.
      let p : Conf × Ghost (F.at C) → Prop := fun x => (δ F C c x ≤ d + 1 ∧ ¬ Outside F C c x.1) ∨ δ F C c x ≤ d
      obtain ⟨v, n₁, n₂, h₁, hv, h₂, hn⟩ := hex.first (p := p) (.inr (by omega))
      have hdv : d + 1 ≤ δ F C c v := h₁.carry (r := fun x => d + 1 ≤ δ F C c x) (by
          rintro x y ⟨-, hnx⟩ ⟨-, hd', -, -⟩ hx
          by_cases hox : Outside F C c x.1
          · have := (hd'.1 hox).1; simp only [δ] at hx ⊢; omega
          · have := (hd'.2 hox).2
            have h3 : ¬ (δ F C c x ≤ d + 1) := fun h => hnx (.inl ⟨h, hox⟩)
            simp only [δ] at hx h3 ⊢; omega) (by omega)
      have hv' : δ F C c v = d + 1 ∧ ¬ Outside F C c v.1 := by
        rcases hv with ⟨h, h'⟩ | h
        · exact ⟨by omega, h'⟩
        · omega
      have hn₁ : n₁ ≠ 0 := by
        rintro rfl
        have := h₁.zero; subst this; exact hv'.2 ho
      have hn₂ : n₂ ≠ 0 := by
        rintro rfl
        have := h₂.zero; subst this; omega
      have hin := (ih n₁ (by omega)).1 (d + 1) a v (by omega) (h₁.mono fun x ⟨hx₁, hx₂⟩ => by
          unfold QRun
          exact ⟨by simp only [QCall] at hx₁; omega,
            fun he => Classical.byContradiction fun hno => hx₂ (.inl ⟨by omega, hno⟩)⟩) hAa hda hv'.1 hl k
          (by omega)
      obtain ⟨n₀, hp₀⟩ := hpre
      have hpv : ∃ n₀, Ex (XStep F C c Θ chk) (QCall F C c d) n₀ a₁ v :=
        ⟨n₀ + n₁, hp₀.trans (h₁.mono fun _ hx => hx.1)⟩
      exact .inner (by simp only [δ] at hl hda; simp only [lift]; omega) hin
        ((ih n₂ (by omega)).2 d a₀ a₁ v e hent hd₀ hpv h₂ (hcar h₁ hAa) hv'.1 hde (hlen h₁ hl) k (by omega))
    · cases hex with
      | refl => omega
      | next hq hx hrest =>
        rename_i m b
        obtain ⟨hs, hdisc, hg, hh⟩ := hx
        have h2 := hdisc.2 ho
        have hne : kind F C c a.1 b.1 ≠ .outside := kind_ne_outside fun h => ho h.1
        have hpk := pkgStep_of (d := d) hs hne (hyp_props hne hh) (by simp only [δ] at hl hda; omega)
          (fun _ => by simp only [δ] at hl hda; omega)
        rw [← hg] at hpk
        obtain ⟨n₀, hp₀⟩ := hpre
        have hown : OwnAfter F C c Θ chk a₀ a₁ a b :=
          ⟨⟨n₀, by rw [hd₀]; exact hp₀⟩, ⟨hs, hdisc, hg, hh⟩, by rw [hd₀]; exact hda, ho⟩
        have hq' : ownQ Ψ G a₀.1.s.h.length (lift F C c a.1 a.2) (lift F C c b.1 b.2) :=
          ⟨(certs _).own a₀ a₁ a b hent hown, fun I hG => (certs _).tolerant I hG a₀ a₁ a b hent hown⟩
        by_cases hbe : depthC F C c b.1.t = d
        · -- The exit of the call.
          obtain ⟨-, rfl⟩ := hrest.stop (by simp only [QCall, δ]; omega)
          exact .step (mk ⟨hs, hdisc, hg, hh⟩ hpk) hq' (.nil _)
        · exact .step (mk ⟨hs, hdisc, hg, hh⟩ hpk) hq'
            ((ih m (by omega)).2 d a₀ a₁ b e hent hd₀ ⟨n₀ + 1, hp₀.snoc hq ⟨hs, hdisc, hg, hh⟩⟩ hrest
              (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩) (by simp only [δ] at hda ⊢; omega) hde
              (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) k (by omega))

/-- **(L2) of an actual execution, its member calls read from their
traces** (proved, `decompose_trace` and `Run.bound`). -/
theorem exec_bound_trace (hΘ : ∀ p, (Θ p).le (Ψ p) = true) (off : Nat) {d n : Nat}
    {a e : Conf × Ghost (F.at C)}
    (hex : Ex (XStep F C c Θ chk) (QRun F C c d) n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2)) :
    RBound Ψ d (lift F C c a.1 a.2) (lift F C c e.1 e.2) ∧ Ok d (lift F C c e.1 e.2) :=
  Run.bound hΘ n d _ _
    ((decompose_trace hAdm certs mk off n).1 d a e hok.pos hex hAa hda hde hl n (Nat.le_refl _)) hok

/-- **A call of `C` from outside code is a run at the caller's depth**
(proved, `decompose_trace`): the entering step from `a`, at depth `d`, and
the execution up to the first state with `d` calls active again, is a
member call of `traceMember`, a run of outside code at `d`. -/
theorem callRun_trace (off : Nat) {d n : Nat} {a b w : Conf × Ghost (F.at C)} (hAa : Adm a)
    (hx : XStep F C c Θ chk a b) (hda : δ F C c a = d) (hdb : δ F C c b = d + 1) (hdw : δ F C c w = d)
    (hcq : Ex (XStep F C c Θ chk) (QCall F C c d) n b w) (hl : a.2.A.length = δ F C c a + off) :
    Run Θ Ψ G (n + 1) d (lift F C c a.1 a.2) (lift F C c w.1 w.2) := by
  have hent : Entering F C c Θ chk Adm (entered c b.1.t) a b := ⟨hAa, hx, rfl, by rw [hdb, hda]⟩
  have hk : kind F C c a.1 b.1 = .enter := kind_enter (by simp only [δ] at hda hdb; omega)
  have hne : kind F C c a.1 b.1 ≠ .outside := by rw [hk]; simp
  obtain ⟨hs, hdisc, hg, hh⟩ := hx
  have hpk := pkgStep_of (d := d) hs hne (hyp_props hne hh) (by simp only [δ] at hl hda; omega)
    (fun h => by rw [hk] at h; cases h)
  rw [← hg] at hpk
  have hM := (decompose_trace hAdm certs mk off n).2 d a b b w hent hda ⟨0, .refl b⟩ hcq
    (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩) hdb hdw (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) n (Nat.le_refl _)
  exact RunAt.member (traceMember R Ψ G)
    (.step (mk ⟨hs, hdisc, hg, hh⟩ hpk) ⟨(certs _).enterWithin a b hent, fun I hG => (certs _).enterKeeps I hG a b hent⟩ hM)
    (RunAt.nil _)

end DecomposeTrace

end Verification.TolerantFrames.ReadOnly
