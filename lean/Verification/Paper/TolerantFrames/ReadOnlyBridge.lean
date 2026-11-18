import Verification.Paper.TolerantFrames.ReadOnlyClaim

/-! # Read-only handles: the framed claim's executions are the paper's

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
framed claim", "The executions of the claim"). The framed claim
(`FramedRequestSafe`) is about the executions from an entry meeting the
frame's premises (`ClientFrame.Entry`) and a history the frame starts from,
each of whose steps keeps the client obligation (`SafeUnder`). This module
shows those executions are the executions the paper's rule is stated over:

- **A step keeping the obligation** (`ClientFrame.KStep`): an actual step,
  the history after it the frame's (`next`), the obligation kept at the
  step's world. Every step `SafeUnder` follows from a state, the obligation
  kept, is one (`safeUnder_kstep`), to a state where `SafeUnder` holds
  again.
- **The states reached** (`ClientFrame.Reached`) from an entry and a start,
  by such steps, meet the entry's premises (`Reached.entry`).
- **What the checks give** (`ClientFrame.ChkSound`, hypothesis, the
  interface of the checks of `C`'s code): at each step of `C`'s code from a
  reached state, the fields of `PkgStep` the step's own code establishes
  (`PkgProps`), at the checks' data `chk`. **What the starts give**
  (`ClientFrame.StartInv`, hypothesis): the invariants of states at an
  entry and one set of the history per call of `C` active.
- **Each such step is an `XStep`** (`kstep_xstep`): the call discipline from
  the entry's premises (`disc_of_wf`), the history by definition
  (`next_conf`), `Row` at a step of outside code from the obligation
  (`keeps_conf`), `PkgProps` at a step of `C`'s code from `ChkSound`.
- **`Ok` at every depth** (`reached_ok`): along an execution from a start,
  every state meets the invariants with one set per call, and is `Ok` at
  its depth inside a call (`Ex.inv`).
- **A call of outside code** (`call_segment`): from a state of outside code
  at depth `d > 0` to the first later state of `C`'s code at depth `d`, an
  execution of `XStep`s whose every state but the last meets `QRun d`. With
  `reached_ok` these are the premises of `exec_bound`, `exec_keeps` and
  `exec_rely` at the call (`call_premises`): the walker's call of its
  callback, and the call of outside code of every unit whose plan reads a
  frame. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

namespace Ex
variable {α : Type} {R : α → α → Prop} {q : α → Prop}

/-- **An invariant carried along an execution holds at every state a step
leaves.** -/
theorem strengthen {r : α → Prop} (hr : ∀ a b, q a → R a b → r a → r b) :
    ∀ {n : Nat} {a e : α}, Ex R q n a e → r a → Ex R (fun x => q x ∧ r x) n a e
  | _, _, _, .refl a, _ => .refl a
  | _, _, _, .next ha hab he, h => .next ⟨ha, h⟩ hab (strengthen hr he (hr _ _ ha hab h))

/-- **Executions compose.** -/
theorem trans : ∀ {n m : Nat} {a b e : α}, Ex R q n a b → Ex R q m b e → Ex R q (n + m) a e
  | _, _, _, _, _, .refl _, h => by simpa using h
  | _, m, _, _, _, .next (n := n) ha hab he, h => by
    have := Ex.next ha hab (trans he h); rwa [show n + 1 + m = n + m + 1 by omega]

/-- A last step. -/
theorem snoc {n : Nat} {a b e : α} (h : Ex R q n a b) (hb : q b) (hbe : R b e) : Ex R q (n + 1) a e :=
  h.trans (.next hb hbe (.refl e))

end Ex

/-- **The history before an entry**: every location is outside storage, no
location is exposed or protected, and each call of `C` active at the term
has one set of the history, empty. -/
noncomputable def bareStart (F : Family) (C : Nat) (t : Tm) : Ghost (F.at C) :=
  ⟨fun _ => none, fun _ => none, fun _ => False, List.replicate (depthC F C none t) (fun _ => False),
    fun _ => False⟩

/-- **The history at an entry** (Appendix A, the start of an execution):
at a call of an entry from a state where `C` holds nothing protected, the
call's set pushed, then each argument `v` crossing in at its parameter's
type `T`. The released and outside locations it reaches read-only join every
set of the history; the exposed ones `E`. -/
noncomputable def entryStart (F : Family) (C : Nat) (tv : TypeView) (h : Heap) (t : Tm)
    (args : List (tv.Ty × Val)) : Ghost (F.at C) :=
  Ghost.crosses tv h (args.map fun a => ⟨.into, a.1, a.2⟩) (bareStart F C t)

/-- Crossings keep the history uniform (proved, `HStep.uniform`). -/
theorem Ghost.crosses_uniform {P : Package} {tv : TypeView} {h : Heap} :
    ∀ (xs : List (Crossing tv)) (g : Ghost P), g.Uniform → (Ghost.crosses tv h xs g).Uniform
  | [], _, hu => hu
  | x :: xs, g, hu => Ghost.crosses_uniform xs _ ((HStep.cross (h := h) g x.dir x.ty x.val).uniform hu)

theorem bareStart_uniform (F : Family) (C : Nat) (t : Tm) : (bareStart F C t).Uniform := by
  intro X hX l
  simp only [bareStart, List.mem_replicate] at hX
  obtain ⟨-, rfl⟩ := hX
  simp only [Ghost.Prot, bareStart, List.mem_replicate, false_iff, not_or, not_exists, not_and]
  exact ⟨fun Y hY => by rw [hY.2]; exact id, id⟩

/-- The entry history keeps every location outside storage. -/
theorem entryStart_site {F : Family} {C : Nat} {tv : TypeView} {h : Heap} {t : Tm} {args : List (tv.Ty × Val)} :
    (entryStart F C tv h t args).site = fun _ => none :=
  (Ghost.crosses_site _ _).1

/-- **The entry history meets the invariants of states** (proved, by
`Inv.of_lent`): crossings keep it uniform, every location of it is outside
storage, and the roots are the term's. -/
theorem entryStart_inv {F : Family} {C : Nat} {tv : TypeView} (x : Conf) (args : List (tv.Ty × Val)) :
    Inv (lift F C none x (entryStart F C tv x.s.h x.t args)) :=
  Inv.of_lent (Ghost.crosses_uniform _ _ (bareStart_uniform F C x.t))
    (fun l => .inr (by simp [lift, Ghost.origin, entryStart_site]))
    (rootsValid_of_term (P := F.at C) (st := lift F C none x _) rfl x.ok)

/-- **The entry history has one set per call of `C` active** (proved). -/
theorem entryStart_len {F : Family} {C : Nat} {tv : TypeView} {h : Heap} {t : Tm} (args : List (tv.Ty × Val)) :
    (entryStart F C tv h t args).A.length = depthC F C none t := by
  simp [entryStart, Ghost.crosses_len, bareStart]

/-- **An argument crossing in is protected at the entry** (proved): a
location an argument reaches read-only at its parameter's type is protected
in the entry history, inside a call of `C`. -/
theorem entryStart_prot {F : Family} {C : Nat} {tv : TypeView} {h : Heap} {t : Tm} {args : List (tv.Ty × Val)}
    (hd : 0 < depthC F C none t) {T : tv.Ty} {v : Val} (ha : (T, v) ∈ args) {l : Nat}
    (hr : ReachRO tv (F.at C).ofC T h v l) : (entryStart F C tv h t args).Prot l := by
  suffices ∀ (xs : List (Crossing tv)) (g : Ghost (F.at C)), 0 < g.A.length → g.site = (fun _ => none) →
      ∀ x ∈ xs, x.dir = .into → ReachRO tv (F.at C).ofC x.ty h x.val l → (Ghost.crosses tv h xs g).Prot l by
    exact this _ _ (by simpa [bareStart] using hd) rfl ⟨.into, T, v⟩
      (List.mem_map.mpr ⟨(T, v), ha, rfl⟩) rfl hr
  intro xs
  induction xs with
  | nil => intro _ _ _ x hx; cases hx
  | cons y ys ih =>
    intro g hl hs x hx hd' hr'
    have hl' : 0 < (g.cross tv y.dir y.ty h y.val).A.length := by simpa [Ghost.cross, Ghost.add] using hl
    rcases List.mem_cons.mp hx with rfl | hx
    · have hp : (g.cross tv x.dir x.ty h x.val).Prot l := by
        obtain ⟨X, hX⟩ := List.exists_mem_of_length_pos hl
        refine .inl ⟨_, List.mem_map.mpr ⟨X, hX, rfl⟩, .inr ⟨hd', hr', .inr ?_⟩⟩
        simp [Ghost.origin, hs]
      clear ih hx hl'
      suffices ∀ (zs : List (Crossing tv)) (g' : Ghost (F.at C)), g'.Prot l → (Ghost.crosses tv h zs g').Prot l from
        this ys _ hp
      intro zs
      induction zs with
      | nil => exact fun _ h => h
      | cons z zs ihz => exact fun g' hp' => ihz _ (Ghost.prot_add hp')
    · exact ih _ hl' (by rw [← hs]; rfl) x hx hd' hr'

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **A step keeping the obligation**: an actual step, the history after it
the frame's, the obligation kept at the step's world. -/
def KStep (a b : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  AStep a.1 b.1 ∧ b.2 = fr.next a.2 a.1.s.h a.1.t b.1.s.h b.1.t ∧
    fr.Keeps a.2 a.1.s.n a.1.s.W a.1.s.h a.1.t b.1.s.h b.1.t

/-- **A state reached** from an entry meeting the premises and a history the
frame starts from, by steps keeping the obligation. -/
def Reached (b : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  ∃ a n, fr.Entry a.1.s.h a.1.t ∧ fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 ∧ Ex fr.KStep (fun _ => True) n a b

/-- **What the checks give** (hypothesis, the interface of the checks (S),
(K) and (O) of `C`'s code): at each step of `C`'s code from a reached
state, the fields of `PkgStep` that read the step's own code. -/
def ChkSound : Prop :=
  ∀ a b, fr.Reached a → fr.KStep a b → kind fr.F fr.C none a.1 b.1 ≠ .outside →
    PkgProps fr.view.view (lift fr.F fr.C none a.1 a.2)
      (lift fr.F fr.C none b.1 (Ghost.next fr.F fr.C none fr.chkConf a.1 b.1 a.2))
      (midOf fr.chkConf a.1 b.1 a.2) (fr.chkConf a.1 b.1).xs

/-- **What the starts give** (hypothesis): at an entry, a history the frame
starts from meets the invariants of states, with one set per call of `C`
active. -/
def StartInv : Prop :=
  ∀ (x : Conf) g, fr.Entry x.s.h x.t → fr.start x.s.n x.s.W x.s.h x.t g →
    Inv (lift fr.F fr.C none x g) ∧ g.A.length = depthC fr.F fr.C none x.t

variable {fr}

/-- **A frame starting from the entry history** (`entryStart`): its starts
are exactly the history after the entry's arguments `args` cross in. -/
def StartsEntry (args : Heap → Tm → List (fr.view.view.Ty × Val)) : Prop :=
  ∀ k W h t g, fr.start k W h t g ↔ g = entryStart fr.F fr.C fr.view.view h t (args h t)

/-- **The entry history gives what the starts give** (proved): the
invariants of states by `entryStart_inv`, one set per call of `C` active by
`entryStart_len`. -/
theorem startInv_of_entry {args : Heap → Tm → List (fr.view.view.Ty × Val)} (hs : fr.StartsEntry args) :
    fr.StartInv := by
  intro x g _ hg
  rw [hs] at hg; subst hg
  exact ⟨entryStart_inv x _, entryStart_len _⟩

/-- **Every state has the entry history** (proved): the starts of a frame
starting from it are total. -/
theorem entryStart_total (F : Family) (C : Nat) (tv : TypeView) (args : Heap → Tm → List (tv.Ty × Val)) :
    ∀ (k : Nat) (_ : WorldT k) (h : Heap) (t : Tm), ∃ g, g = entryStart F C tv h t (args h t) :=
  fun _ _ _ _ => ⟨_, rfl⟩

/-- **A reached state meets the entry's premises** (proved): every step
keeps them (`Entry.step`). -/
theorem Reached.entry {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : fr.Entry b.1.s.h b.1.t := by
  obtain ⟨a, n, he, -, hex⟩ := hb
  exact hex.carry (r := fun x => fr.Entry x.1.s.h x.1.t) (fun _ _ _ hk h => Entry.step fr h hk.1.step) he

/-- **A step from a reached state reaches a state** (proved). -/
theorem Reached.step {a b : Conf × Ghost (fr.F.at fr.C)} (ha : fr.Reached a) (hk : fr.KStep a b) : fr.Reached b := by
  obtain ⟨s, n, he, hs, hex⟩ := ha
  exact ⟨s, n + 1, he, hs, hex.snoc trivial hk⟩

/-- **A step keeping the obligation is a step of the paper's executions**
(proved): `XStep` at the frame's checks, the client obligation giving `Row`
at a step of outside code, `ChkSound` the checks at a step of `C`'s code,
the entry's premises the call discipline. -/
theorem kstep_xstep (hc : fr.ChkSound) {a b : Conf × Ghost (fr.F.at fr.C)} (ha : fr.Reached a)
    (hk : fr.KStep a b) : XStep fr.F fr.C none fr.Θ fr.chkConf a b := by
  obtain ⟨hs, hg, hK⟩ := hk
  have hw := (Reached.entry ha)
  refine XStep.of_wf hs hw.2.1 (hg.trans (fr.next_conf a.2 a.1 b.1)) ?_
  unfold StepHyp
  split
  · rename_i ho
    exact ((fr.keeps_conf a.2 (Ghost.next fr.F fr.C none fr.chkConf a.1 b.1 a.2) a.1 b.1).mp hK) ho
  · rename_i ho
    exact hc a b ha ⟨hs, hg, hK⟩ ho

/-- **The execution from a start is an execution of `XStep`s** (proved). -/
theorem ex_xstep (hc : fr.ChkSound) :
    ∀ {n : Nat} {a e : Conf × Ghost (fr.F.at fr.C)} {q : Conf × Ghost (fr.F.at fr.C) → Prop},
      fr.Reached a → Ex fr.KStep q n a e → Ex (XStep fr.F fr.C none fr.Θ fr.chkConf) q n a e
  | _, _, _, _, _, .refl a => .refl a
  | _, _, _, _, ha, .next hq hk he => .next hq (kstep_xstep hc ha hk) (ex_xstep hc (Reached.step ha hk) he)

/-- **`Ok` at every depth** (proved, `Ex.inv`): a reached state meets the
invariants of states with one set of the history per call of `C` active,
and is `Ok` at its depth inside a call. -/
theorem reached_ok (hc : fr.ChkSound) (hi : fr.StartInv) {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) :
    b.2.A.length = δ fr.F fr.C none b ∧ Inv (lift fr.F fr.C none b.1 b.2) ∧
      (0 < δ fr.F fr.C none b → Ok (δ fr.F fr.C none b) (lift fr.F fr.C none b.1 b.2)) := by
  obtain ⟨a, n, he, hs, hex⟩ := hb
  have ⟨hI, hl⟩ := hi a.1 a.2 he hs
  exact Ex.inv (ex_xstep hc ⟨a, 0, he, hs, .refl a⟩ hex) hl hI

/-- The running term of a state safe under an obligation has valid
references (proved). -/
theorem safeUnder_refs {γ : Type} {K : γ → (k : Nat) → WorldT k → Heap → Tm → Heap → Tm → Prop}
    {nx : γ → Heap → Tm → Heap → Tm → γ} {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : HeapObservations.WPost}
    {R : HeapObservations.WExc} :
    ∀ {n : Nat} {W : WorldT n} {g : γ} {h : Heap} {t : Tm},
      HeapObservations.SafeUnder K nx J Ξ T Q R n W g h t → RefsOk W t
  | 0, _, _, _, _, hs => hs
  | _ + 1, _, _, _, _, hs => hs.1

/-- **A step of the safe execution keeping the obligation** (proved): from a
state safe under the obligation at budget `n + 1 > 1`, the calculus's step
(deterministic) is the one the derivation follows; where the step keeps the
obligation it is a `KStep` to a configuration at which the run is again safe
under it. -/
theorem safeUnder_kstep {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : HeapObservations.WPost}
    {R : HeapObservations.WExc} {x : Conf} {g : Ghost (fr.F.at fr.C)} {n : Nat} (hn : 0 < n) (hx : x.s.n = n + 1)
    (hs : HeapObservations.SafeUnder fr.Keeps fr.next J Ξ T Q R x.s.n x.s.W g x.s.h x.t) {h' : Heap} {t' : Tm}
    (hst : Step x.s.h x.t h' t') (hK : fr.Keeps g x.s.n x.s.W x.s.h x.t h' t') :
    ∃ y : Conf, y.s.h = h' ∧ y.t = t' ∧ y.s.n = n ∧ fr.KStep (x, g) (y, fr.next g x.s.h x.t h' t') ∧
      HeapObservations.SafeUnder fr.Keeps fr.next J Ξ T Q R y.s.n y.s.W (fr.next g x.s.h x.t h' t') y.s.h y.t := by
  obtain ⟨⟨m, W, h, pos, adm, ok⟩, t, ht⟩ := x
  simp only at hx hs hst hK ⊢
  subst hx
  obtain ⟨-, -, (⟨hv, -⟩ | ⟨hr, -⟩) | ⟨U, h₂, t₂, hxt, hu, st₂, hh, hs'⟩⟩ := hs
  · exact (value_no_step hv hst).elim
  · exact (hr.no_step hst).elim
  · obtain ⟨rfl, rfl⟩ := Step_det st₂ hst
    have hsU := hs' hK
    exact ⟨⟨⟨n, U, h₂, hn, hu, hh⟩, t₂, safeUnder_refs hsU⟩, rfl, rfl, rfl,
      ⟨⟨hst, ⟨Nat.le_succ n, hxt⟩⟩, rfl, hK⟩, hsU⟩

/-- **The executions the framed claim is about** (proved): along a path of
the calculus within the budget from a state safe under the obligation,
either every step keeps the obligation, and the path is an execution of
`KStep`s to a configuration at its end, or some step of it breaks the
obligation, after which the claim states nothing. -/
theorem safeUnder_path {J : Heap → Tm → Prop} {Ξ T : Fam} {Q : HeapObservations.WPost}
    {R : HeapObservations.WExc} :
    ∀ {j : Nat} {x : Conf} {g : Ghost (fr.F.at fr.C)} {h' : Heap} {t' : Tm},
      HeapObservations.SafeUnder fr.Keeps fr.next J Ξ T Q R x.s.n x.s.W g x.s.h x.t →
      HeapObservations.Steps j x.s.h x.t h' t' → j + 1 < x.s.n →
      (∃ e, Ex fr.KStep (fun _ => True) j (x, g) e ∧ e.1.s.h = h' ∧ e.1.t = t') ∨
      (∃ b m h₁ t₁, Ex fr.KStep (fun _ => True) m (x, g) b ∧ m < j ∧ Step b.1.s.h b.1.t h₁ t₁ ∧
        ¬ fr.Keeps b.2 b.1.s.n b.1.s.W b.1.s.h b.1.t h₁ t₁)
  | _, x, g, _, _, _, .refl, _ => .inl ⟨(x, g), .refl _, rfl, rfl⟩
  | k + 1, x, g, h', t', hs, .next (h' := h₁) (t' := t₁) st hrest, hj => by
    obtain ⟨m, hm⟩ : ∃ m, x.s.n = m + 1 := ⟨x.s.n - 1, by omega⟩
    by_cases hK : fr.Keeps g x.s.n x.s.W x.s.h x.t h₁ t₁
    · obtain ⟨y, rfl, rfl, hyn, hk, hsy⟩ := safeUnder_kstep (by omega) hm hs st hK
      rcases safeUnder_path hsy hrest (by omega) with ⟨e, hex, he⟩ | ⟨b, m', h₂, t₂, hex, hm', hst, hb⟩
      · exact .inl ⟨e, .next trivial hk hex, he⟩
      · exact .inr ⟨b, m' + 1, h₂, t₂, .next trivial hk hex, by omega, hst, hb⟩
    · exact .inr ⟨(x, g), 0, h₁, t₁, .refl _, by omega, st, hK⟩

/-- **A state of a framed execution from an entry is reached** (proved):
from an entry meeting the premises and a history the frame starts from, a
state at the end of a path every step of which keeps the obligation is a
reached state. -/
theorem reached_of_path {x : Conf} {g : Ghost (fr.F.at fr.C)} (he : fr.Entry x.s.h x.t)
    (hs : fr.start x.s.n x.s.W x.s.h x.t g) {j : Nat} {e : Conf × Ghost (fr.F.at fr.C)}
    (hex : Ex fr.KStep (fun _ => True) j (x, g) e) : fr.Reached e :=
  ⟨(x, g), j, he, hs, hex⟩

/-- **A call of outside code** (proved): along an execution of `XStep`s, from
a state of outside code at depth `d` to the first later state of `C`'s code
at depth `d`, every state but the last has at least `d` calls of `C` active
and runs outside code when it has exactly `d`: the execution meets `QRun d`
(`decompose`'s run of outside code). The call discipline gives it: a step of
outside code never lowers the calls, a step of `C`'s code lowers them by one
at most. -/
theorem call_segment {d : Nat} {q : Conf × Ghost (fr.F.at fr.C) → Prop} :
    ∀ {n : Nat} {a e : Conf × Ghost (fr.F.at fr.C)},
      Ex (XStep fr.F fr.C none fr.Θ fr.chkConf) (fun x => q x ∧ ¬ (δ fr.F fr.C none x = d ∧ ¬ Outside fr.F fr.C none x.1))
        n a e →
      d ≤ δ fr.F fr.C none a → Ex (XStep fr.F fr.C none fr.Θ fr.chkConf) (QRun fr.F fr.C none d) n a e := by
  intro n a e hex hd
  have h := hex.strengthen (r := fun x => d ≤ δ fr.F fr.C none x) (fun x y hq hxy hr => by
      obtain ⟨-, hdisc, -, -⟩ := hxy
      simp only [δ] at hr ⊢
      by_cases ho : Outside fr.F fr.C none x.1
      · exact Nat.le_trans hr (hdisc.1 ho).1
      · have := (hdisc.2 ho).2
        have hne : δ fr.F fr.C none x ≠ d := fun he => hq.2 ⟨he, ho⟩
        simp only [δ] at hne; omega) hd
  exact h.mono fun x ⟨⟨_, hp⟩, hr⟩ => ⟨hr, fun he => Classical.byContradiction fun ho => hp ⟨he, ho⟩⟩

/-- **The premises of the rule at a call of outside code** (proved): from a
reached state of outside code at depth `d > 0`, along steps keeping the
obligation, to the first later state of `C`'s code at depth `d`, the
execution is a run of outside code (`QRun d`) from and to depth `d`, the
history has one set per call active, and the call's first state is `Ok` at
`d`: the premises `hex`, `hda`, `hde`, `hl` and `hok` of `exec_bound`,
`exec_keeps` and `exec_rely` at `off = 0`. -/
theorem call_premises (hc : fr.ChkSound) (hi : fr.StartInv) {d n : Nat} {a e : Conf × Ghost (fr.F.at fr.C)}
    (ha : fr.Reached a) (hd : 0 < d) (hda : δ fr.F fr.C none a = d)
    (hex : Ex fr.KStep (fun x => ¬ (δ fr.F fr.C none x = d ∧ ¬ Outside fr.F fr.C none x.1)) n a e)
    (hde : δ fr.F fr.C none e = d) :
    Ex (XStep fr.F fr.C none fr.Θ fr.chkConf) (QRun fr.F fr.C none d) n a e ∧
      a.2.A.length = δ fr.F fr.C none a + 0 ∧ Ok d (lift fr.F fr.C none a.1 a.2) ∧ δ fr.F fr.C none e = d := by
  have hx := ex_xstep hc ha hex
  have hok := reached_ok hc hi ha
  refine ⟨call_segment (q := fun _ => True) (hx.mono fun _ h => ⟨trivial, h⟩) (by omega), by simpa using hok.1, ?_, hde⟩
  have := hok.2.2 (by omega); rwa [hda] at this

end ClientFrame
end Verification.TolerantFrames.ReadOnly
