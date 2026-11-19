import Verification.Paper.TolerantFrames.ReadOnlyFitsReach

/-! # Read-only handles: the fit of an entry

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites of a term"). Every reached state fits the
flow where every entry does (`ClientFrame.fitsAt_reached`). This module
proves the fit of an entry (`ClientFrame.EntryFits`) from the shape of the
calls the claim is about (proof scope: the lemmas below):

- **A well-formed value at an entry** (`EntryVal`): every value it holds
  in its code (`Within`) is a value, and every closure of `C`'s code
  among them has a proposal whose entry names a signature only at a
  capture holding a closure of it or at its own slot (`FnsOk`, `CapFn`).
- **The shape of an entry** (`EntryShape`): a run of `C`'s code at a node
  whose slots naming a signature hold closures of it (`EnvFn`), every
  value of its environment and of the heap well formed.
- **The values a value holds keep its premises** (`Within.prov`,
  `Within.refsOkN`): code provenance and valid references.
- **A value of an entry meets every set holding outside storage**
  (`VJ.entry`): at the entry history every location is outside storage
  (`entryStart_site`), so its sites are; it is closed (`ClosedAt`),
  references allocated locations (the configuration's valid references),
  and every closure of outside code it holds has lowered code (`Source`).
- **Every entry fits** (`ClientFrame.entryFits`): where the frame starts
  from the entry history (`StartsEntry`) and every call it is about has
  the shape, the call's term fits `O` at a position of outside code and
  its heap meets the flow; with the flow's facts, `ChkSound` follows
  (`chkSound_of_flow`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package}

/-! ## The values a value holds -/

/-- **A value outside code holds meets code provenance** where the term
does (proved). -/
theorem vals_prov {ok : Code → ComponentTag → Bool} {ofC : ComponentTag → Bool} (t : Tm) :
    ∀ o, prov ok t = true → ∀ u ∈ vals ofC o t, prov ok u = true := by
  induction t using Tm.induct
  all_goals intro o hp u hu
  all_goals simp only [vals, valsArgs_eq] at hu
  all_goals (repeat' split at hu)
  all_goals (try simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    false_or, or_false] at hu)
  all_goals (try (subst hu; exact hp))
  all_goals (try (rcases hu with rfl | hu; exact hp))
  all_goals (try (subst hu; simp [prov]))
  all_goals (simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at hp; grind [prov])

/-- **A value a value holds meets code provenance** (proved). -/
theorem Within.prov {ok : Code → ComponentTag → Bool} {v w : Val} (hw : Within P v w)
    (hv : ReadOnly.prov ok v = true) : ReadOnly.prov ok w = true := by
  induction hw with
  | refl => exact hv
  | cap hu _ ih =>
    simp only [ReadOnly.prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at hv
    exact ih (hv.2 _ hu)
  | code hu _ ih =>
    simp only [ReadOnly.prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at hv
    simp only [valsArgs_eq, List.mem_flatMap] at hu
    obtain ⟨e, he, hu⟩ := hu
    exact ih (vals_prov e true (hv.1.2 e he) _ hu)
  | bound hu _ ih =>
    simp only [ReadOnly.prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at hv
    simp only [List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · exact ih hv.1.1
    · exact ih hv.1.2
    · exact ih (hv.2 _ hu)

/-- A term's references are a value's that holds it in its code. -/
theorem refsOkN_of_sub {k : Nat} {W : WorldT k} {v u : Tm} (hv : RefsOkN W v) (hs : ∀ r ∈ refs u, r ∈ refs v) :
    RefsOkN W u :=
  fun r hr hn => hv r (hs r hr) hn

/-- **A value a value holds has valid references** where the value does,
identities aside (proved). -/
theorem Within.refsOkN {k : Nat} {W : WorldT k} {v w : Val} (hw : Within P v w) (hv : RefsOkN W v) :
    RefsOkN W w := by
  induction hw with
  | refl => exact hv
  | cap hu _ ih =>
    refine ih (refsOkN_of_sub hv fun r hr => ?_)
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    exact .inr (.inr ⟨_, hu, hr⟩)
  | code hu _ ih =>
    simp only [valsArgs_eq, List.mem_flatMap] at hu
    obtain ⟨e, he, hu⟩ := hu
    refine ih (vals_refsOkN (refsOkN_of_sub hv fun r hr => ?_) hu)
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    exact .inr (.inl ⟨e, he, hr⟩)
  | bound hu _ ih =>
    refine ih (refsOkN_of_sub hv fun r hr => ?_)
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    simp only [List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · exact .inr (.inl (.inl hr))
    · exact .inr (.inl (.inr hr))
    · exact .inr (.inr ⟨_, hu, hr⟩)

/-! ## Well-formed values and the shape of an entry -/

variable (Fl : Flow P)

/-- **A closure of `C`'s code meets its proposal's entry**: its code has a
proposal whose entry names a signature only at a capture holding a closure
of it or at the closure's own slot (`CapFn`), is open at that entry where
its token lies in `O` (`OpenAt`), and holds outside storage at each
capture's slot and the closures each capture holds (`FnsIn`). -/
def FnsOk (w : Val) : Prop :=
  ∀ fs ar E K s caps k rest comp oid, w = .objAt fs (.graph ar E K s caps k rest comp) oid →
    P.ofC comp = true → ∃ π, Fl.code (E, K) = some π ∧ CapFn π ar E K s caps rest ∧
      (π.tok ∈ Fl.O → OpenAt Fl π ar s rest caps.length) ∧ (∀ i, i < caps.length → none ∈ π.env s (capSlot ar rest i)) ∧
      ∀ i u, caps[i]? = some u → FnsIn Fl (π.env s (capSlot ar rest i)) u

/-- **A well-formed value at an entry**: every value it holds in its code
is a value meeting its proposal's entry signatures. -/
def EntryVal (v : Val) : Prop := ∀ w, Within P v w → isVal w = true ∧ FnsOk Fl w

/-- **The shape of an entry**: a run of `C`'s code at a node whose every
slot holds outside storage and the closures its value holds, and whose
slots naming a signature hold closures of it, its code's returns within
`O`, every value of its environment and of the heap well formed, and the
closures a value of the heap holds of outside storage's contents. -/
def EntryShape (h : Heap) (t : Tm) : Prop :=
  ∃ E K l L d comp π, t = .goto E K l L d comp ∧ P.ofC comp = true ∧ Fl.code (E, K) = some π ∧
    (∀ i, none ∈ π.env l i) ∧ Sub π.ret Fl.O ∧ (∀ i, FnsIn Fl (π.env l i) (envOf L d i)) ∧
    (∀ v ∈ h, FnsIn Fl (Fl.H.contents none) v) ∧
    EnvFn π l L d ∧ (∀ i, EntryVal Fl (envOf L d i)) ∧ ∀ v ∈ h, EntryVal Fl v

variable {Fl}

/-- **A well-formed value at an entry meets every set holding outside
storage** (proved): at a ghost whose every location is outside storage,
a closed value with valid references, meeting code provenance and lowered
source, whose every value is well formed, meets `S` at the heap's
length. -/
theorem VJ.entry {g : Ghost P} {S : Sites P} {v : Val} {s : IndexedHeap}
    (hg : ∀ l, g.site l = none) (hS : none ∈ S) (hF : FnsIn Fl S v) (hv : EntryVal Fl v) (hc : Scoped 0 v)
    (hr : RefsOkN s.W v) (hp : prov (srcOk P.ofC) v = true) : VJ Fl g s.h.length S v where
  val := (hv v (.refl v)).1
  closed := Scoped.closed hc
  below := fun _ hl => Leaves.lt hr hl
  sites := fun l _ => by rw [hg]; exact hS
  fns := hF
  inner := by
    intro w hw
    have hrw := hw.refsOkN hr
    have hpw := hw.prov hp
    refine ⟨(hv w hw).1, ?_, ?_⟩
    · intro fs ar E K st caps k rest comp oid hw' hc'
      obtain ⟨π, hπ, hfn, hop, hcs, hcf⟩ := (hv w hw).2 fs ar E K st caps k rest comp oid hw' hc'
      refine ⟨π, hπ, fun i u hu => ⟨⟨fun l _ => by
        rw [hg]; exact hcs i (List.getElem?_eq_some_iff.mp hu).1, hcf i u hu⟩, ?_⟩, hfn, hop⟩
      have hm : u ∈ caps := List.mem_of_getElem? hu
      have hru : RefsOkN s.W u := refsOkN_of_sub hrw fun r hr' => by
        subst hw'
        simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
        exact .inr (.inr ⟨u, hm, hr'⟩)
      exact fun l hl => Leaves.lt hru hl
    · intro fs ar E K st caps k rest comp oid hw' hc' e he
      subst hw'
      simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true, srcOk, decide_eq_true_eq] at hpw
      exact LoweredSrc.lowered Fl (hpw.1.1 hc' e he)

/-- **The heap of an entry meets the flow** (proved): at a ghost whose
every location is outside storage, whose contents and bindings the flow's
storage of outside storage holds. -/
theorem HeapInv.entry {g : Ghost P} {s : IndexedHeap} (hF : Fl.Facts) (hg : ∀ l, g.site l = none)
    (hfn : ∀ v ∈ s.h, FnsIn Fl (Fl.H.contents none) v)
    (hv : ∀ v ∈ s.h, EntryVal Fl v) (hc : ∀ v ∈ s.h, Scoped 0 v) (hp : HeapProv (srcOk P.ofC) s.h) :
    HeapInv Fl g s.h := by
  intro w u hu
  have hm : u ∈ s.h := List.mem_of_getElem? hu
  have hl : w < s.h.length := (List.getElem?_eq_some_iff.mp hu).1
  have hst := hF.writable none hF.none
  rw [hg]
  refine ⟨VJ.entry hg (hst.1 none hF.none) (hfn u hm) (hv u hm) (hc u hm) (RefsOk.refsOkN (contents_valid hl hu)) (hp u hm),
    fun x _ l _ => by rw [hg]; exact hst.2 none hF.none⟩

/-! ## The closures an entry may hold -/

/-- **The shape of a closure `C`'s code makes**: its signature, and, for
each capture, the signature of the closure of `C`'s code it holds where
one is known (a closure of the module capturing the module's closures of
the functions it calls), `none` otherwise (a closure lowered code creates,
capturing its variables). -/
abbrev Shape := FnSig × List (Option FnSig)

variable (P) in
/-- **A closure of one of the shapes `Sh`** (`OfShape`): a closure of `C`'s code of a
shape's signature, with one capture per entry of the shape, each capture
the shape names a signature for holding a closure of it, each other
capture holding no closure of `C`'s code. -/
inductive OfShape (Sh : List Shape) : Val → Prop where
  | mk {σ : FnSig} {cs : List (Option FnSig)} {fs : List (PropKey × Nat)} {caps : List Tm} {k : Invoke}
      {comp : ComponentTag} {oid : Nat} : (σ, cs) ∈ Sh → caps.length = cs.length → cs.length = σ.ncaps →
      P.ofC comp = true → (∀ (j : Nat) σ', cs[j]? = some (some σ') → ∃ u, caps[j]? = some u ∧ FnIs P σ' u) →
      (∀ (j : Nat) u, cs[j]? = some none → caps[j]? = some u → ∀ x, CodeReach P.ofC u x →
        ∀ fs ar E K s caps k rest comp oid, P.ofC comp = true → x ≠ .objAt fs (.graph ar E K s caps k rest comp) oid) →
      OfShape Sh (.objAt fs (.graph σ.ar σ.code.1 σ.code.2 σ.s caps k σ.rest comp) oid)

variable (P) in
/-- **A well-formed value of an entry** (named premise, well-formed
entries): every value it holds in its code is a value, and every closure
of `C`'s code among them is of one of the shapes `Sh` at which `C`'s code
makes closures. -/
def WfVal (Sh : List Shape) (v : Val) : Prop :=
  ∀ w, Within P v w → isVal w = true ∧
    ∀ fs ar E K s caps k rest comp oid, w = .objAt fs (.graph ar E K s caps k rest comp) oid →
      P.ofC comp = true → OfShape P Sh w

variable (Fl) in
/-- **The proposal meets the shapes** (the checker's condition): the code
of each shape has a proposal whose entry names a signature only at a
capture the shape names it for, or at the closure's own slot, is open at
that entry where its token lies in `O`, holds outside storage at each
capture's slot, and the token of the code of each capture's signature
there. -/
def ShapesOk (Sh : List Shape) : Prop :=
  ∀ σ cs, (σ, cs) ∈ Sh → ∃ π, Fl.code σ.code = some π ∧ (∀ i σ', π.fn σ.s i = some σ' →
    (∃ j, i = capSlot σ.ar σ.rest j ∧ cs[j]? = some (some σ')) ∨
      (i = capSlot σ.ar σ.rest cs.length ∧ σ' = σ)) ∧
    (π.tok ∈ Fl.O → OpenAt Fl π σ.ar σ.s σ.rest cs.length) ∧
    (∀ j, j < cs.length → none ∈ π.env σ.s (capSlot σ.ar σ.rest j)) ∧
    ∀ j σ', cs[j]? = some (some σ') → ∃ π', Fl.code σ'.code = some π' ∧ π'.tok ∈ π.env σ.s (capSlot σ.ar σ.rest j)

/-- **A closure of a shape meets its proposal's entry signatures** (proved):
a capture the shape names holds a closure of it, the closure's own slot
the closure. -/
theorem OfShape.fnsOk {Sh : List Shape} (hS : ShapesOk Fl Sh) {w : Val} (hw : OfShape P Sh w) : FnsOk Fl w := by
  intro fs ar E K s caps k rest comp oid he _
  cases hw with
  | @mk σ cs fs' caps' k' comp' oid' hm hl hn _ hcap hnone =>
    simp only [Tm.objAt.injEq, CallCode.graph.injEq] at he
    obtain ⟨-, ⟨rfl, hE, hK, rfl, rfl, -, rfl, -⟩, -⟩ := he
    obtain ⟨π, hπ, hfn, hop, hcs, htk⟩ := hS σ cs hm
    have hσ : σ.code = (E, K) := by rw [← hE, ← hK]
    refine ⟨π, hσ ▸ hπ, fun i σ' hi => ?_, by rw [hl]; exact hop, fun i hi => hcs i (by rw [← hl]; exact hi),
      fun j u hu => ?_⟩
    rotate_left
    · intro x hx fs₁ ar₁ E₁ K₁ s₁ caps₁ k₁ rest₁ comp₁ oid₁ hx₁ hc₁
      have hj : j < cs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hu).1
      cases hcj : cs[j]? with
      | none => simp at hcj; omega
      | some o =>
        cases o with
        | none => exact absurd hx₁ (hnone j u hcj hu x hx fs₁ ar₁ E₁ K₁ s₁ caps₁ k₁ rest₁ comp₁ oid₁ hc₁)
        | some σ' =>
          obtain ⟨u', hu', hfu⟩ := hcap j σ' hcj
          rw [hu] at hu'; cases hu'
          obtain ⟨fs₂, caps₂, k₂, comp₂, oid₂, rfl, -, hc₂⟩ := hfu
          cases hx with
          | refl =>
            simp only [Tm.objAt.injEq, CallCode.graph.injEq] at hx₁
            obtain ⟨-, ⟨-, hE₁, hK₁, -⟩, -⟩ := hx₁
            obtain ⟨π', hπ', ht'⟩ := htk j σ' hcj
            exact ⟨π', by rw [← hE₁, ← hK₁]; exact hπ', ht'⟩
          | step hm' _ => simp [codeVals, hc₂] at hm'
    rcases hfn i σ' hi with ⟨j, rfl, hj⟩ | ⟨hi', he'⟩
    · exact ⟨j, rfl, .inl (hcap j σ' hj)⟩
    · subst hi' he'
      refine ⟨caps'.length, by rw [hl], .inr ⟨rfl, ?_⟩⟩
      rw [hl, hn, ← hσ]

/-- **A well-formed value is a value of an entry** (proved): every closure
of `C`'s code it holds is of a shape the proposal meets. -/
theorem WfVal.entryVal {Sh : List Shape} (hS : ShapesOk Fl Sh) {v : Val} (hv : WfVal P Sh v) : EntryVal Fl v :=
  fun w hw => ⟨(hv w hw).1, fun fs ar E K s caps k rest comp oid he hc =>
    OfShape.fnsOk hS ((hv w hw).2 fs ar E K s caps k rest comp oid he hc) fs ar E K s caps k rest comp oid he hc⟩

/-- **The shape of an entry from well-formed values** (proved): a run of
`C`'s code at a node every slot of which holds outside storage and the
closures its value holds, of a code returning within `O`, whose proposal
names a signature only at slots `sl` names it for, which hold closures of
it, its environment's and its heap's values well formed at shapes the
proposal meets, the closures a value of the heap holds of outside
storage's contents. -/
theorem entryShape_of {Sh : List Shape} (hS : ShapesOk Fl Sh) {h : Heap} {E : List Tm}
    {K : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm} {comp : ComponentTag}
    {π : CodeFlow P} (hc : P.ofC comp = true) (hcode : Fl.code (E, K) = some π)
    (hnone : ∀ i, none ∈ π.env l i) (hret : Sub π.ret Fl.O) (henvF : ∀ i, FnsIn Fl (π.env l i) (envOf L d i))
    (hheapF : ∀ v ∈ h, FnsIn Fl (Fl.H.contents none) v) {sl : Nat → Option FnSig}
    (hsl : ∀ i σ, π.fn l i = some σ → sl i = some σ) (hfn : ∀ i σ, sl i = some σ → FnIs P σ (envOf L d i))
    (henv : ∀ i, WfVal P Sh (envOf L d i)) (hheap : ∀ v ∈ h, WfVal P Sh v) :
    EntryShape Fl h (.goto E K l L d comp) :=
  ⟨E, K, l, L, d, comp, π, rfl, hc, hcode, hnone, hret, henvF, hheapF, fun i σ hi => hfn i σ (hsl i σ hi),
    fun i => (henv i).entryVal hS, fun v hv => (hheap v hv).entryVal hS⟩

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **Every entry fits the flow** (proved): where the frame starts from the
entry history and every call the claim is about has the shape the flow
reads (`EntryShape`), the call's term fits `O` at a position of outside
code and its heap meets the flow. -/
theorem entryFits {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts) {args : Heap → Tm → List (fr.view.view.Ty × Val)}
    (hst : fr.StartsEntry args) (hsh : ∀ h t, fr.Call h t → EntryShape Fl h t) : fr.EntryFits Fl := by
  intro x g hc hg
  rw [hst] at hg
  have hsite : ∀ l, g.site l = none := by subst hg; simp [entryStart_site]
  obtain ⟨E, K, l, L, d, comp, π, ht, hcomp, hcode, hnone, hret, henvF, hheapF, hfn, henv, hheap⟩ := hsh _ _ hc
  obtain ⟨hpv, -, hsrc, hcl⟩ := hc.1
  refine ⟨?_, HeapInv.entry hF hsite hheapF hheap hcl.2 hsrc.2⟩
  have hok := x.ok
  rw [ht] at hok hcl hsrc ⊢
  refine .gotoC π hcomp hcode (fun i => .inl ?_) hfn hret (fun _ => Sub.refl _)
  have hS : none ∈ π.env l i := hnone i
  -- The environment's value at `i`: an element of `L`, or `d`.
  have hmem : ∀ r ∈ refs (envOf L d i), r ∈ refs (.goto E K l L d comp) := by
    intro r hr
    simp only [envOf, List.getD_eq_getElem?_getD] at hr
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    cases hi : L[i]? with
    | none => rw [hi] at hr; exact .inr hr
    | some u => rw [hi] at hr; exact .inl (.inr ⟨u, List.mem_of_getElem? hi, hr⟩)
  have hsc : Scoped 0 (envOf L d i) := by
    have h1 := hcl.1
    simp only [Scoped, scopedArgs_iff] at h1
    simp only [envOf, List.getD_eq_getElem?_getD]
    cases hi : L[i]? with
    | none => exact h1.2
    | some u => exact h1.1 u (List.mem_of_getElem? hi)
  have hpr : prov (srcOk (fr.F.at fr.C).ofC) (envOf L d i) = true := by
    have h1 := hsrc.1
    simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true] at h1
    simp only [envOf, List.getD_eq_getElem?_getD]
    cases hi : L[i]? with
    | none => exact h1.2
    | some u => exact h1.1.2 u (List.mem_of_getElem? hi)
  exact VJ.entry hsite hS (henvF i) (henv i) hsc (refsOkN_of_sub (RefsOk.refsOkN hok) hmem) hpr

/-- **`ChkSound` from the flow and the shape of the calls** (proved): the
fit of every entry (`entryFits`) gives `SitesSound` (`sitesSound_of_fits`),
and the flow's facts the checks at the actual crossings
(`chkSound_of_sites`). -/
theorem chkSound_of_flow {T : τ} {Fl : Flow (fr.F.at fr.C)} (hF : Fl.Facts) (hS : fr.FlowSites Fl)
    {args : Heap → Tm → List (fr.view.view.Ty × Val)} (hst : fr.StartsEntry args)
    (hsh : ∀ h t, fr.Call h t → EntryShape Fl h t) (hx : fr.ActualCrossings T) (hlend : Lendable Fl.O)
    (hL : LocalHeld Fl.H) (hB : ∀ s, NoLocal (Fl.H.bindings s)) : fr.ChkSound :=
  chkSound_of_sites hx (fun s hs s' h' => hF.closed s hs s' h') hlend hL hB
    (sitesSound_of_fits hF hS (entryFits hF hst hsh))

end ClientFrame
end Verification.TolerantFrames.ReadOnly
