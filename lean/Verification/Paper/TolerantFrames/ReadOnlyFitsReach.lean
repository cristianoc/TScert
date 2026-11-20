import Verification.Paper.TolerantFrames.ReadOnlyFitsStep

/-! # Read-only handles: the sites at every reached state

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites of a term"). Every step keeps a term fitting a set and the heap
meeting the flow (`fits_step`); this module carries that along the
executions of a client frame and reads `ClientFrame.SitesSound` from it
(proof scope: the lemmas below; the fit of an entry is a premise,
`EntryFits`):

- **The sites a ghost reads** (`VJ.congr`, `HeapInv.congr`): a value and a
  heap read the ghost's sites only below the heap's length.
- **The site of a fresh location** (`activeFrame_tag`, `stepSite_outside`):
  the innermost frame `stepSite` reads is the one whose tag the path's
  head names (`activeTag`), so a step of outside code allocates at
  outside storage; the history after a step gives its fresh locations
  outside storage at a step of outside code and the checks' sites
  otherwise (`stepAt_site`).
- **At every reached state** (`FitsAt`, `fitsAt_reached`): where the
  frame's checks give a step's fresh locations `stepSite` (`FlowSites`)
  and every entry fits, the term of every reached state fits `O` at a
  position of outside code and its heap meets the flow.
- **The roots of outside code meet `O`** (`fits_roots`): every value at a
  position of outside code fits a subset of `O` (the rules' premise at
  `o = true`).
- **`SitesSound`** (`ClientFrame.sitesSound_of_fits`): at each step of
  `C`'s code from a reached state, the heap after it meets the heap of
  sites and the roots of outside code meet `O`, at the ghost after its
  allocation. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} {Fl : Flow P}

/-! ## The sites a ghost reads -/

theorem SitesOf.congr_below {g g' : Ghost P} {S : Sites P} {v : Val} {n : Nat}
    (he : ∀ l, l < n → g'.site l = g.site l) (hb : ∀ l, Leaves P.ofC v l → l < n) (h : SitesOf g S v) :
    SitesOf g' S v := by
  intro l hl; rw [he l (hb l hl)]; exact h l hl

theorem CapsOk.congr {g g' : Ghost P} {n : Nat} {w : Val} (he : ∀ l, l < n → g'.site l = g.site l)
    (h : CapsOk Fl g n w) : CapsOk Fl g' n w := by
  intro fs ar E K s caps k rest comp oid hw hc
  obtain ⟨h₀, hbelow, hall⟩ := h fs ar E K s caps k rest comp oid hw hc
  refine ⟨h₀, hbelow, fun c π hπ => ?_⟩
  obtain ⟨hcaps, hfn⟩ := hall c π hπ
  exact ⟨fun i u hu => ⟨(hcaps i u hu).1.congr_below he (hbelow i u hu), (hcaps i u hu).2⟩, hfn⟩

/-- **A value reads the ghost's sites below its bound** (proved). -/
theorem VJ.congr {g g' : Ghost P} {n : Nat} {S : Sites P} {v : Val} (he : ∀ l, l < n → g'.site l = g.site l)
    (h : VJ Fl g n S v) : VJ Fl g' n S v :=
  ⟨h.val, h.closed, h.below, h.sites.congr_below he h.below, h.fns,
    fun w hw => ⟨(h.inner w hw).1, (h.inner w hw).2.1.congr he, (h.inner w hw).2.2.1,
      fun x hx l hl => by
        obtain ⟨hlt, ho⟩ := (h.inner w hw).2.2.2 x hx l hl
        refine ⟨hlt, ?_⟩
        unfold Ghost.origin; rw [he l hlt]; exact ho⟩⟩

/-- **A heap reads the ghost's sites below its length** (proved). -/
theorem HeapInv.congr {g g' : Ghost P} {h : Heap} (he : ∀ l, l < h.length → g'.site l = g.site l)
    (hH : HeapInv Fl g h) : HeapInv Fl g' h := by
  intro w u hw
  have hl : w < h.length := (List.getElem?_eq_some_iff.mp hw).1
  rw [he w hl]
  exact (hH w u hw).congr he

/-! ## The frame a fresh location's site is read at -/

/-- The tag of a frame, `none` outside every frame. -/
def frameTag : Option FrameKey → ComponentTag
  | some ((_, c), _) => c
  | none => none

theorem activeFrame_cong {cur : Option FrameKey} {a : Tm} (A : Tm)
    (hf : activeFrame cur A = activeFrame cur a) (hp : activeTag (frameTag cur) A = activeTag (frameTag cur) a)
    (ih : frameTag (activeFrame cur a).1 = activeTag (frameTag cur) a) :
    frameTag (activeFrame cur A).1 = activeTag (frameTag cur) A := by
  rw [hf, ih, hp]

/-- **The frame of a step that allocates is the path's innermost**
(proved, by induction on the step): `activeFrame` and `path` follow the
same congruences, and a step allocating runs no `goto`. -/
theorem activeFrame_tag {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hlen : h.length < h'.length) :
    ∀ cur : Option FrameKey, frameTag (activeFrame cur t).1 = activeTag (frameTag cur) t := by
  induction hs
  all_goals intro cur
  -- Steps that keep the heap's length allocate nothing.
  all_goals try (exfalso; simp_all; done)
  all_goals try (exfalso; simp at hlen; done)
  case callL hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case callRecv hfv hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hfv]) (by simp [activeTag, path, wrap_head, hn, hfv]) (ih hlen cur)
  case callArg hfv hrv hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong _ (by simp only [activeFrame, hfv, hrv, Bool.true_eq_false, ite_false]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, hfv, hrv, Bool.true_eq_false, ite_false, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case constructL hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case constructArg hfv hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong _ (by simp only [activeFrame, hfv, Bool.true_eq_false, ite_false]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, hfv, Bool.true_eq_false, ite_false, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case letC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case spreadC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case makeArg hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong _ (by simp only [activeFrame]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case readC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case indexC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case indexC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case writeC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case writeC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case testC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case iteC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case arithC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case arithC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case arrArg hai hpre hst ih =>
    have hn := notVal_of_step hst
    refine activeFrame_cong _ (by simp only [activeFrame]; exact activeArgs_at hai hpre hn)
      (by simp only [activeTag, path, pathArgs_at _ hai hpre hn, wrap_head]) (ih hlen cur)
  case elemC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case elemC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case setC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case setC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case setC3 hav hiv hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav, hiv]) (by simp [activeTag, path, wrap_head, hn, hav, hiv]) (ih hlen cur)
  case lenC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case throwC hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case mergeC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case mergeC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case makeKeyC1 hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn]) (by simp [activeTag, path, wrap_head, hn]) (ih hlen cur)
  case makeKeyC2 hav hst ih =>
    have hn := notVal_of_step hst
    exact activeFrame_cong _ (by simp [activeFrame, hn, hav]) (by simp [activeTag, path, wrap_head, hn, hav]) (ih hlen cur)
  case frameC ih =>
    rw [activeTag_frame]
    simp only [activeFrame]
    exact ih hlen _
  case makeFields hvs _ =>
    simp only [activeFrame, path, activeArgs_vals hvs, pathArgs_vals _ hvs, activeTag]; rfl
  case arrAlloc hvs _ =>
    simp only [activeFrame, path, activeArgs_vals hvs, pathArgs_vals _ hvs, activeTag]; rfl
  case arrAllocThrow hvs _ =>
    simp only [activeFrame, path, activeArgs_vals hvs, pathArgs_vals _ hvs, activeTag]; rfl
  case setGrow ls b _ _ v hv _ _ =>
    simp only [activeFrame, path, hv, show isVal (.arr ls) = true from rfl, show isVal (.num b) = true from rfl,
      Bool.true_eq_false, ite_false, activeTag, List.head?_cons, Option.map_some, Option.getD_some]
  case lenStrThrow =>
    simp [activeFrame, path, activeTag, isVal]
  case arithThrow hb =>
    obtain ⟨ha, hb'⟩ := binopThrows_values hb
    simp [activeFrame, path, activeTag, ha, hb']

/-- **A step of outside code allocates outside storage** (proved): where
the path's innermost tag runs no code of `C`, the innermost frame's
allocation sites are outside storage's. -/
theorem stepSite_outside {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hlen : h.length < h'.length)
    {cur : Option FrameKey} (hout : P.ofC (activeTag (frameTag cur) t) = false) :
    stepSite Fl cur t = none := by
  have htag := activeFrame_tag hs hlen cur
  have hal : allocOf Fl (activeFrame cur t).1 = Alloc.outside := by
    rw [← htag] at hout
    cases hfr : (activeFrame cur t).1 with
    | none => rfl
    | some p =>
      obtain ⟨⟨m, c⟩, kx⟩ := p
      rw [hfr] at hout
      simp only [frameTag] at hout
      simp [allocOf, hout]
  unfold stepSite
  split <;> (rename_i heq; rw [heq] at hal; simp [hal, Alloc.outside])

/-! ## The ghost after a step -/

/-- **The sites after a step** (proved): the step's allocation, outside
storage at a step of outside code, the checks' sites otherwise; entries,
crossings and exits change no site. -/
theorem stepAt_site {F : Family} {C : Nat} {c : ComponentTag} {tv : TypeView} {d : CheckData (F.at C) tv}
    {h : Heap} {t : Tm} {h' : Heap} {t' : Tm} {g : Ghost (F.at C)} :
    (Ghost.stepAt F C c d h t h' t' g).site =
      (g.alloc h.length (if stepKind F C c t t' = .outside then fun _ => none else d.site)).site := by
  unfold Ghost.stepAt
  split <;> rename_i hk
  · rw [ite_eq_left hk]; unfold outsideNextAt; split <;> rfl
  · rw [ite_eq_right (by rw [hk]; decide)]; exact (Ghost.crosses_site _ _)
  · rw [ite_eq_right (by rw [hk]; decide)]; exact (Ghost.crosses_site _ _)
  · rw [ite_eq_right (by rw [hk]; decide)]; exact (Ghost.crosses_site _ _)

/-! ## The roots of outside code -/

theorem vals_sites_of_value {g : Ghost P} {n : Nat} {S : Sites P} {v r : Val} (hv : VJ Fl g n S v)
    (hr : r ∈ vals P.ofC true v) : SitesOf g S r :=
  fun l hl => hv.sites l (leaves_of_vals hv.val hr hl)

theorem vals_false_value {v r : Val} (hv : isVal v = true) (hr : r ∈ vals P.ofC false v) : False := by
  cases v with
  | objAt fs cc i => cases cc <;> simp_all [vals]
  | _ => simp_all [isVal, vals]

/-- **A position of a value or a variable holds values meeting the set**
(proved): a value of a set within `O` at a position of outside code. -/
theorem vor_roots {g : Ghost P} {n : Nat} {Γ : Nat → Option (Sites P)} {S : Sites P} {o : Bool} {u : Tm}
    (h : VOr (VJ Fl g n) Γ S u) (ho : o = true → Sub S Fl.O) : ∀ r ∈ vals P.ofC o u, SitesOf g Fl.O r := by
  intro r hr
  rcases h with hv | ⟨j, _, rfl, _, _⟩
  · cases o with
    | false => exact (vals_false_value hv.val hr).elim
    | true => exact (vals_sites_of_value hv hr).mono (ho rfl)
  · simp [vals] at hr

/-- A spine's first locations are its cells (proved). -/
theorem arr_leaves {ls : List (Option Nat)} {l : Nat} (hl : Leaves P.ofC (.arr ls) l) : some l ∈ ls := by
  obtain ⟨x, hx, a, hn⟩ := hl
  cases hx with
  | refl =>
    cases a with
    | cell i =>
      simp only [next, spineEntries] at hn
      cases hi : ls[i]? with
      | none => rw [hi] at hn; cases hn
      | some o =>
        rw [hi] at hn
        cases o with
        | none => cases hn
        | some l' => cases hn; exact List.mem_of_getElem? hi
    | _ => cases hn
  | step hm _ => simp [codeVals] at hm

theorem envOf_default (L : List Tm) (d : Tm) : envOf L d L.length = d := by
  simp [envOf, List.getD_eq_getElem?_getD]

theorem vor_default {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {S : Sites P} {L : List Tm} {d : Tm}
    (henv : ∀ i, VOr V Γ S (envOf L d i)) : VOr V Γ S d := by
  have := henv L.length
  rwa [envOf_default] at this

theorem lowered_roots {g : Ghost P} {E : List Tm} (hE : ∀ e ∈ E, Lowered Fl e) :
    ∀ r ∈ valsArgs P.ofC true E, SitesOf g Fl.O r := by
  intro r hr
  simp only [valsArgs_eq, List.mem_flatMap] at hr
  obtain ⟨e, he, hr⟩ := hr
  obtain ⟨ls, rfl, hls⟩ := lowered_vals e true (hE e he) hr
  intro l hl
  exact absurd (hls _ (arr_leaves hl)) (by simp)

/-- **The roots of a fitting term meet `O`** (proved, by induction on
`Fits`): a value at a position of outside code fits a subset of `O`; a run
of outside code holds lowered code and an environment of `O`. -/
theorem fits_roots {g : Ghost P} {n : Nat} :
    ∀ {Γ a o S t}, Fits Fl (VJ Fl g n) Γ a o S t → ∀ r ∈ vals P.ofC o t, SitesOf g Fl.O r := by
  intro Γ a o S t h
  induction h with
  | val hv h₀ ho => exact vor_roots (Γ := fun _ => none) (.inl h₀) ho
  | var _ _ _ => intro r hr; simp [vals] at hr
  | invoke _ _ _ _ _ _ _ _ ihf ihr iha =>
    intro r hr
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with (hr | hr) | ⟨x, hx, hr⟩
    · exact ihf r hr
    · exact ihr r hr
    · exact iha x hx r hr
  | invokeC σ c π Sa Sr hof hfn _ _ _ hargs _ _ _ _ _ ihr iha =>
    intro r hr
    subst hof
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with (hr | hr) | ⟨x, hx, hr⟩
    · exact (vals_false_value hfn.val hr).elim
    · exact ihr r hr
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      exact iha i x hi r hr
  | construct _ _ _ _ _ _ _ ihf iha =>
    intro r hr
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with hr | ⟨x, hx, hr⟩
    · exact ihf r hr
    · exact iha x hx r hr
  | letE _ _ _ ihx ihb =>
    intro r hr
    simp only [vals, List.mem_append] at hr
    exact hr.elim (ihx r) (ihb r)
  | spread _ _ _ ih => intro r hr; simp only [vals] at hr; exact ih r hr
  | makeAbsent _ _ _ _ _ ih =>
    intro r hr
    simp only [vals, valsArgs_eq, List.mem_flatMap] at hr
    obtain ⟨x, hx, hr⟩ := hr
    exact ih x hx r hr
  | makeView _ _ _ _ hv ho ih =>
    intro r hr
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with hr | ⟨x, hx, hr⟩
    · exact vor_roots (Γ := fun _ => none) (.inl hv) ho r (by simpa only [vals] using hr)
    · exact ih x hx r hr
  | makeBound _ _ _ _ _ hb _ hp ho ih =>
    intro r hr
    have ho' := fun h' => Sub.trans hb (ho h')
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with ((hr | hr) | ⟨x, hx, hr⟩) | ⟨x, hx, hr⟩
    · exact vor_roots (hp _ (List.mem_cons_self ..)) ho' r hr
    · exact vor_roots (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ho' r hr
    · exact vor_roots (hp x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))) ho' r hr
    · exact ih x hx r hr
  | makeGraphC _ _ _ _ _ hc _ _ _ _ _ _ ih =>
    intro r hr
    simp only [vals, hc, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, List.nil_append, valsArgs_eq,
      List.mem_flatMap] at hr
    obtain ⟨x, hx, hr⟩ := hr
    exact ih x hx r hr
  | makeGraphOut _ _ _ _ hc hE _ hb _ hcaps ho _ ih =>
    intro r hr
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with hr | ⟨x, hx, hr⟩
    · split at hr
      · rename_i hcond
        have hot := (Bool.and_eq_true _ _).mp hcond
        rw [List.mem_append] at hr
        rcases hr with hr | hr
        · exact lowered_roots hE r (by simpa [valsArgs_eq] using hr)
        · obtain ⟨x, hx, hr⟩ := List.mem_flatMap.mp hr
          rw [← hot.1] at hr
          exact vor_roots (hcaps x hx) (fun h' => Sub.trans hb (ho h')) r hr
      · simp at hr
    · exact ih x hx r hr
  | readAt _ _ _ _ _ ih => intro r hr; simp only [vals] at hr; exact ih r hr
  | indexAt _ _ _ _ _ _ ihx ihk =>
    intro r hr; simp only [vals, List.mem_append] at hr; exact hr.elim (ihx r) (ihk r)
  | writeAt _ _ _ _ ihx ihy =>
    intro r hr; simp only [vals, List.mem_append] at hr; exact hr.elim (ihx r) (ihy r)
  | test _ _ ih => intro r hr; simp only [vals] at hr; exact ih r hr
  | ite _ _ _ _ ihc ihx ihy =>
    intro r hr; simp only [vals, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact ihc r hr
    · exact ihx r hr
    · exact ihy r hr
  | arith _ _ _ ihx ihy =>
    intro r hr; simp only [vals, List.mem_append] at hr; exact hr.elim (ihx r) (ihy r)
  | arrLit _ _ _ _ _ ih =>
    intro r hr
    simp only [vals, valsArgs_eq, List.mem_flatMap] at hr
    obtain ⟨x, hx, hr⟩ := hr
    exact ih x hx r hr
  | elemAt _ _ _ _ ihx ihi =>
    intro r hr; simp only [vals, List.mem_append] at hr; exact hr.elim (ihx r) (ihi r)
  | setElem _ _ _ _ _ _ _ ihx ihi ihv =>
    intro r hr; simp only [vals, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact ihx r hr
    · exact ihi r hr
    · exact ihv r hr
  | lenOf _ _ ih => intro r hr; simp only [vals] at hr; exact ih r hr
  | throw _ _ ih => intro r hr; simp only [vals] at hr; exact ih r hr
  | merge _ _ _ _ _ _ _ _ ihx ihy =>
    intro r hr; simp only [vals, List.mem_append] at hr; exact hr.elim (ihx r) (ihy r)
  | makeKey _ _ _ _ _ ihk ihx =>
    intro r hr; simp only [vals, List.mem_append] at hr; exact hr.elim (ihk r) (ihx r)
  | gotoC _ _ hc _ _ _ _ _ => intro r hr; simp [vals, hc] at hr
  | gotoOut hc hE henv _ _ =>
    intro r hr
    simp only [vals, hc, Bool.false_eq_true, ite_false, valsArgs_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hr with (hr | ⟨x, hx, hr⟩) | hr
    · exact lowered_roots hE r (by simpa [valsArgs_eq] using hr)
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      have := henv i
      simp only [envOf, List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
      exact vor_roots this (fun _ => Sub.refl _) r hr
    · exact vor_roots (vor_default henv) (fun _ => Sub.refl _) r hr
  | frameC _ _ _ hc _ _ _ _ _ _ _ _ ih =>
    intro r hr
    simp only [vals, hc, ite_true, List.nil_append, Bool.not_true] at hr
    exact ih r hr
  | frameOut hc hE henv _ _ _ ih =>
    intro r hr
    simp only [vals, hc, Bool.false_eq_true, ite_false, Bool.not_false, valsArgs_eq, List.mem_append,
      List.mem_flatMap] at hr
    rcases hr with ((hr | ⟨x, hx, hr⟩) | hr) | hr
    · exact lowered_roots hE r (by simpa [valsArgs_eq] using hr)
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      have := henv i
      simp only [envOf, List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
      exact vor_roots (Γ := fun _ => none) (.inl this) (fun _ => Sub.refl _) r hr
    · exact vor_roots (Γ := fun _ => none) (.inl (vor_default (V := VJ Fl g n) (Γ := fun _ => none)
        (fun i => .inl (henv i))).top) (fun _ => Sub.refl _) r hr
    · exact ih r hr

/-! ## Along the executions of a client frame -/

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- **The checks give a step's fresh locations the flow's sites**: the
sites `stepSite` reads at the step's term. -/
def FlowSites (Fl : Flow (fr.F.at fr.C)) : Prop :=
  ∀ h t h' t', (fr.chk h t h' t').site = fun _ => stepSite Fl none t

/-- **A state fits the flow**: its term fits `O` at a position of outside
code, outside every frame, and its heap meets the flow. -/
def FitsAt (Fl : Flow (fr.F.at fr.C)) (a : Conf × Ghost (fr.F.at fr.C)) : Prop :=
  Fits Fl (VJ Fl a.2 a.1.s.h.length) (fun _ => none) FrameAt.outside true Fl.O a.1.t ∧ HeapInv Fl a.2 a.1.s.h

/-- **Every entry fits the flow** (the premise the fit of an entry
discharges): at a call the claim is about, every history the frame
starts from. -/
def EntryFits (Fl : Flow (fr.F.at fr.C)) : Prop :=
  ∀ (x : Conf) g, fr.Call x.s.n x.s.W x.s.h x.t → fr.start x.s.n x.s.W x.s.h x.t g → fr.FitsAt Fl (x, g)

variable {fr} {Fl : Flow (fr.F.at fr.C)}

/-- **The ghost after a step reads the sites `fits_step` gives** (proved):
below the heap's length, its old sites; a fresh location, outside storage
at a step of outside code, whose innermost frame `stepSite` reads is then
outside code's (`stepSite_outside`), and the checks' sites otherwise. -/
theorem next_site (hS : fr.FlowSites Fl) {a b : Conf × Ghost (fr.F.at fr.C)} (hk : fr.KStep a b) :
    ∀ l, l < b.1.s.h.length →
      b.2.site l = (a.2.alloc a.1.s.h.length (fun _ => stepSite Fl none a.1.t)).site l := by
  obtain ⟨hst, hg, -⟩ := hk
  intro l hl
  rw [hg]
  simp only [FrameCore.next, stepAt_site, Ghost.alloc]
  split
  · rfl
  · rename_i hlt
    split
    · rename_i hk
      have hout : OutsideAt fr.F fr.C none a.1.t := ((kind_spec (F := fr.F) (C := fr.C) (c := none) a.1 b.1).1 hk).1
      have hof : (fr.F.at fr.C).ofC (activeTag (frameTag none) a.1.t) = false := by
        simpa [Family.at, Family.ofC, OutsideAt, frameTag] using hout
      exact (stepSite_outside hst.step (by omega) hof).symm
    · rw [hS]

/-- **Every step keeps a state fitting the flow** (proved, `fits_step`). -/
theorem fitsAt_step (hF : Fl.Facts) (hS : fr.FlowSites Fl) {a b : Conf × Ghost (fr.F.at fr.C)} (hk : fr.KStep a b)
    (ha : fr.FitsAt Fl a) : fr.FitsAt Fl b := by
  obtain ⟨hfit, hH⟩ := fits_step hF hk.1.step (cur := none) ha.1 ha.2
  have he := next_site hS hk
  exact ⟨hfit.mono fun _ _ hv => hv.congr he, hH.congr he⟩

/-- **Every reached state fits the flow** (proved): where every entry fits
it, every step keeps it. -/
theorem fitsAt_reached (hF : Fl.Facts) (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : fr.FitsAt Fl b := by
  obtain ⟨a, n, he, hst, hex⟩ := hb
  exact hex.carry (r := fun x => fr.FitsAt Fl x) (fun _ _ _ hk h => fitsAt_step hF hS hk h) (hE _ _ he hst)

/-- **`SitesSound` from the flow** (proved): at each step from a reached
state, `fits_step` gives the heap after it meeting the flow, so the heap
of sites (`HeapInv.sites`), and its term fitting `O` at a position of
outside code, so the roots of outside code meeting `O` (`fits_roots`), at
the ghost after the step's allocation (`midOf`, the checks' sites
`stepSite`). -/
theorem sitesSound_of_fits (hF : Fl.Facts) (hS : fr.FlowSites Fl) (hE : fr.EntryFits Fl) :
    fr.SitesSound Fl.H Fl.O := by
  intro a b ha hk _
  have hfa := fitsAt_reached hF hS hE ha
  obtain ⟨hfit, hH⟩ := fits_step hF hk.1.step (cur := none) hfa.1 hfa.2
  have hmid : midOf fr.chkConf a.1 b.1 a.2 =
      a.2.alloc a.1.s.h.length (fun _ => stepSite Fl none a.1.t) := by
    simp only [midOf, chkConf]; rw [hS]
  rw [hmid]
  refine ⟨hH.sites, fun r hr => fits_roots hfit r ?_⟩
  have hn : fr.F.ofC fr.C none = false := by simp [Family.ofC, Family.Runs]
  have : rootsOf fr.F fr.C none b.1.t = vals (fr.F.at fr.C).ofC true b.1.t := by simp [rootsOf, hn]; rfl
  rw [← this]; exact hr

end ClientFrame

end Verification.TolerantFrames.ReadOnly
