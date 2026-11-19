import Verification.Paper.TolerantFrames.ReadOnlyFitsReach

/-! # Read-only handles: the fit of an entry

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites of a term"). Every reached state fits the
flow where every entry does (`ClientFrame.fitsAt_reached`). This module
proves the fit of an entry (`ClientFrame.EntryFits`) from the shape of the
calls the claim is about (proof scope: the lemmas below):

- **A closure outside code may hold** (`GivenOut`): a closure of `C`'s
  code of a code whose token lies in `O`, open at its entry, whose entry
  names a signature only at a capture holding a closure of it or at its
  own slot (`CapFn`): one `C`'s code gave out, at this entry or an earlier
  one.
- **A well-formed value at an entry** (`EntryVal`): every value it holds
  in its code (`Within`) is a value, and every closure of `C`'s code it
  holds, in a capture or in the code of outside closures and bound
  functions, is one `C`'s code gave out.
- **What outside code may supply** (`Supplied`): a set holding outside
  storage and the token of every code whose token lies in `O`; every slot
  of a member's entry, outside storage's contents and each capture's slot
  of an open code hold it, so a closure an earlier call gave out may come
  back in any value outside code supplies.
- **The shape of an entry** (`EntryShape`): a run of `C`'s code at a node
  whose every slot holds what outside code may supply, whose slots naming
  a signature hold closures of it (`EnvFn`), every value of its
  environment and of the heap well formed.
- **The values a value holds keep its premises** (`Within.prov`,
  `Within.refsOkN`): code provenance and valid references.
- **A value of an entry meets every set holding what outside code may
  supply** (`VJ.entry`): at the entry history every location is outside storage
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

/-- **What a value holds holds** (proved): `Within` is transitive. -/
theorem Within.trans {u v w : Val} (h₁ : Within P u v) (h₂ : Within P v w) : Within P u w := by
  induction h₁ with
  | refl => exact h₂
  | cap hu _ ih => exact .cap hu (ih h₂)
  | code hu _ ih => exact .code hu (ih h₂)
  | bound hu _ ih => exact .bound hu (ih h₂)

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

/-- **A closure outside code may hold**: a closure of `C`'s code of a code
whose token lies in `O`, open at its entry context (`OpenAt`), at every
context of which each capture's slot holds what outside code may supply
and the entry names a signature only at a capture holding a closure of it
or at its own slot (`CapFn`): one `C`'s code gave out. -/
def GivenOut (w : Val) : Prop :=
  ∀ fs ar E K s caps k rest comp oid, w = .objAt fs (.graph ar E K s caps k rest comp) oid →
    P.ofC comp = true → (∃ π, Fl.code (E, K) entryCx = some π ∧ π.tok ∈ Fl.O ∧ OpenAt Fl π ar s rest caps.length) ∧
      ∀ c π, Fl.code (E, K) c = some π → CapFn π ar E K s caps rest ∧
        ∀ i, i < caps.length → Supplied Fl (π.env s (capSlot ar rest i))

/-- **A well-formed value at an entry**: every value it holds in its code
(`Within`) is a value, and every closure of `C`'s code such a value is or
holds in the code of outside closures and bound functions (`CodeReach`) is
one `C`'s code gave out (`GivenOut`). -/
def EntryVal (v : Val) : Prop :=
  ∀ w, Within P v w → isVal w = true ∧ ∀ x, CodeReach P.ofC w x → GivenOut Fl x

/-- **The shape of an entry**: a run of `C`'s code at a node every slot of
which holds what outside code may supply (`Supplied`), whose slots naming
a signature hold closures of it, its code's returns within `O`, every value
of its environment and of the heap well formed. -/
def EntryShape (h : Heap) (t : Tm) : Prop :=
  ∃ E K l L d comp π, t = .goto E K l L d comp ∧ P.ofC comp = true ∧ Fl.code (E, K) entryCx = some π ∧
    (∀ i, Supplied Fl (π.env l i)) ∧ Sub π.ret Fl.O ∧
    EnvFn π l L d ∧ (∀ i, EntryVal Fl (envOf L d i)) ∧ ∀ v ∈ h, EntryVal Fl v

variable {Fl}

/-- **A well-formed value holds the closures it holds at a set holding what
outside code may supply** (proved): each closure of `C`'s code is one
`C`'s code gave out, whose token lies in `O`; the set holds outside
storage, the token of closures of outside code. -/
theorem EntryVal.fnsIn {S : Sites P} {v w : Val} (hv : EntryVal Fl v) (hw : Within P v w) (hS : Supplied Fl S) :
    FnsIn Fl S w := by
  intro x hx fs ar E K s caps k rest comp oid he
  refine ⟨fun hc => ?_, fun _ => hS.1⟩
  obtain ⟨⟨π, hπ, ht, -⟩, -⟩ := (hv w hw).2 x hx fs ar E K s caps k rest comp oid he hc
  exact ⟨π, hπ, hS.2 _ _ hπ ht⟩

/-- **A well-formed value at an entry meets every set holding what outside
code may supply** (proved): at a ghost whose every location is outside
storage, a closed value with valid references, meeting code provenance
and lowered source, whose every value is well formed, meets `S` at the
heap's length. -/
theorem VJ.entry {g : Ghost P} {S : Sites P} {v : Val} {s : IndexedHeap}
    (hg : ∀ l, g.site l = none) (hS : Supplied Fl S) (hv : EntryVal Fl v) (hc : Scoped 0 v)
    (hr : RefsOkN s.W v) (hp : prov (srcOk P.ofC) v = true) : VJ Fl g s.h.length S v where
  val := (hv v (.refl v)).1
  closed := Scoped.closed hc
  below := fun _ hl => Leaves.lt hr hl
  sites := fun l _ => by rw [hg]; exact hS.1
  fns := hv.fnsIn (.refl v) hS
  inner := by
    intro w hw
    have hrw := hw.refsOkN hr
    have hpw := hw.prov hp
    refine ⟨(hv w hw).1, ?_, ?_⟩
    · intro fs ar E K st caps k rest comp oid hw' hc'
      obtain ⟨⟨π, hπ, -, hop⟩, hall⟩ := (hv w hw).2 w (.refl w) fs ar E K st caps k rest comp oid hw' hc'
      refine ⟨⟨π, hπ, fun _ => hop⟩, fun i u hu => ?_, fun c π' h' => ?_⟩
      · have hm : u ∈ caps := List.mem_of_getElem? hu
        have hru : RefsOkN s.W u := refsOkN_of_sub hrw fun r hr' => by
          subst hw'
          simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
          exact .inr (.inr ⟨u, hm, hr'⟩)
        exact fun l hl => Leaves.lt hru hl
      · obtain ⟨hfn, hsup⟩ := hall c π' h'
        refine ⟨fun i u hu => ⟨fun l _ => ?_, ?_⟩, hfn⟩
        · rw [hg]; exact (hsup i (List.getElem?_eq_some_iff.mp hu).1).1
        · subst hw'
          exact hv.fnsIn (hw.trans (.cap (List.mem_of_getElem? hu) (.refl u)))
            (hsup i (List.getElem?_eq_some_iff.mp hu).1)
    · intro fs ar E K st caps k rest comp oid hw' hc' e he
      subst hw'
      simp only [prov, provs_eq, List.all_eq_true, Bool.and_eq_true, srcOk, decide_eq_true_eq] at hpw
      exact LoweredSrc.lowered Fl (hpw.1.1 hc' e he)

/-- **The heap of an entry meets the flow** (proved): at a ghost whose
every location is outside storage, whose contents and bindings the flow's
storage of outside storage holds. -/
theorem HeapInv.entry {g : Ghost P} {s : IndexedHeap} (hF : Fl.Facts) (hg : ∀ l, g.site l = none)
    (hv : ∀ v ∈ s.h, EntryVal Fl v) (hc : ∀ v ∈ s.h, Scoped 0 v) (hp : HeapProv (srcOk P.ofC) s.h) :
    HeapInv Fl g s.h := by
  intro w u hu
  have hm : u ∈ s.h := List.mem_of_getElem? hu
  have hl : w < s.h.length := (List.getElem?_eq_some_iff.mp hu).1
  have hst := hF.writable none hF.none
  -- outside storage's contents hold `O`, so what outside code may supply
  have hS : Supplied Fl (Fl.H.contents none) := ⟨hst.1 none hF.none, fun _ _ _ ht => hst.1 _ ht⟩
  rw [hg]
  refine ⟨VJ.entry hg hS (hv u hm) (hc u hm) (RefsOk.refsOkN (contents_valid hl hu)) (hp u hm),
    fun x _ l _ => by rw [hg]; exact hst.2 none hF.none⟩

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
  obtain ⟨E, K, l, L, d, comp, π, ht, hcomp, hcode, hsup, hret, hfn, henv, hheap⟩ := hsh _ _ hc
  obtain ⟨hpv, -, hsrc, hcl⟩ := hc.1
  refine ⟨?_, HeapInv.entry hF hsite hheap hcl.2 hsrc.2⟩
  have hok := x.ok
  rw [ht] at hok hcl hsrc ⊢
  refine .gotoC entryCx π hcomp hcode (fun i => .inl ?_) hfn hret (fun _ => Sub.refl _)
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
  exact VJ.entry hsite (hsup i) (henv i) hsc (refsOkN_of_sub (RefsOk.refsOkN hok) hmem) hpr

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
