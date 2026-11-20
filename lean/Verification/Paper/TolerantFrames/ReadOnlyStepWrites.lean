import Verification.Paper.TolerantFrames.ReadOnlyCharges
import Verification.Paper.TolerantFrames.ReadOnlySteps

/-! # Read-only handles: a step's changes are at its writing redex

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Charges", `stepWrites_sound`). The
first part of the lemma, at the level of one step of the calculus: every
old location a step changes is written by the redex the step reduces, the
active term of the innermost frame (`activeFrame`), which is a writing
redex at that location (`WriteRedex`): a field write into an object
holding the location under the written key (`Step.writeField`), or an
element store into a spine whose element at the index is the location
(`Step.setPresent`) (`step_writes_active`). With `step_changes` it locates
the change among the term's references; here it names the redex, the frame
it runs in and the receiver, which the charges of the frame's node
expression bound.

- **The active term fits** (`Fits.active`): the term a fitting term's next
  step reduces fits at some position.
- **The changed location's site** (`write_site`): at a step from a term
  fitting at the value judgment `VJ`, every old location the step changes
  is one step from the active redex's receiver, a value meeting a set
  that holds the location's site. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-- **A writing redex at a location**: a field write whose receiver holds
the location under the written key, or an element store whose spine's
element at the index is the location. -/
def WriteRedex (l : Nat) : Tm → Prop
  | .writeAt k (.objAt fs _ _) _ => fs.lookup k = some l
  | .setElem (.arr ls) (.num b) _ => elemLoc ls b = some l
  | _ => False

/-- **A step changes an old location only at its active writing redex**
(proved, by induction on the step): the active term of the innermost
frame, from any frame `cur` outside the term, is a writing redex at the
location. Each congruence step's active term is its subterm's, and every
other step leaves each old location's value or only appends. -/
theorem step_writes_active {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    ∀ {l : Nat} {v : Val}, h[l]? = some v → h'[l]? ≠ some v → ∀ cur, WriteRedex l (activeFrame cur t).2 := by
  induction hs
  all_goals intro l v hv hne cur
  -- Steps that leave the heap, or only append to it.
  all_goals try first
    | exact (hne hv).elim
    | exact (hne (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
    | exact (hne (by
        rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
  case callL hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case callRecv hfv hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hfv] using ih hv hne cur
  case callArg hfv hrv hai hpre hst ih =>
    have hn := notVal_of_step hst
    simp only [activeFrame, hfv, hrv, Bool.true_eq_false, ite_false]
    rw [activeArgs_at hai hpre hn]; exact ih hv hne cur
  case constructL hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case constructArg hfv hai hpre hst ih =>
    have hn := notVal_of_step hst
    simp only [activeFrame, hfv, Bool.true_eq_false, ite_false]
    rw [activeArgs_at hai hpre hn]; exact ih hv hne cur
  case letC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case spreadC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case makeArg hai hpre hst ih =>
    have hn := notVal_of_step hst
    simp only [activeFrame]
    rw [activeArgs_at hai hpre hn]; exact ih hv hne cur
  case readC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case indexC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case indexC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case writeC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case writeC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case testC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case iteC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case arithC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case arithC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case arrArg hai hpre hst ih =>
    have hn := notVal_of_step hst
    simp only [activeFrame]
    rw [activeArgs_at hai hpre hn]; exact ih hv hne cur
  case elemC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case elemC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case setC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case setC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case setC3 hav hiv hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav, hiv] using ih hv hne cur
  case lenC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case throwC hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case mergeC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case mergeC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case makeKeyC1 hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn] using ih hv hne cur
  case makeKeyC2 hav hst ih =>
    have hn := notVal_of_step hst
    simpa [activeFrame, hn, hav] using ih hv hne cur
  case frameC ih =>
    simp only [activeFrame]
    exact ih hv hne _
  case writeField oid f fs c l' _ w hw hf _ =>
    by_cases he : l = l'
    · subst he
      simp only [activeFrame, show isVal (.objAt fs c oid) = true from rfl, hw, Bool.true_eq_false, ite_false]
      exact hf
    · exact (hne (by rw [List.getElem?_set_ne (Ne.symm he)]; exact hv)).elim
  case setPresent ls b l' _ w hw hl _ =>
    by_cases he : l = l'
    · subst he
      simp only [activeFrame, show isVal (.arr ls) = true from rfl, show isVal (.num b) = true from rfl, hw,
        Bool.true_eq_false, ite_false]
      exact hl
    · exact (hne (by rw [List.getElem?_set_ne (Ne.symm he)]; exact hv)).elim

/-! ## The active redex fits -/

section fits
variable {P : Package} {Fl : Flow P} {V : Sites P → Val → Prop}

/-- The active term of a list is the term itself or that of one of its
elements (proved). -/
theorem activeArgs_self_or {cur : Option FrameKey} {t : Tm} (xs : List Tm) :
    (activeArgs cur t xs).2 = t ∨ ∃ x ∈ xs, activeArgs cur t xs = activeFrame cur x := by
  rcases activeArgs_split (cur := cur) (t := t) xs with ⟨h₁, _⟩ | ⟨x, hx, h₁, _⟩
  · exact .inl (by rw [h₁])
  · exact .inr ⟨x, hx, h₁⟩

/-- **The active term fits, or is the term** (proved, by induction on
`Fits`): the term a fitting term's next step reduces, read from any frame
`cur` outside it, is the term itself or fits at some position. -/
theorem Fits.active_aux :
    ∀ {Γ a o S t}, Fits Fl V Γ a o S t → ∀ cur, (activeFrame cur t).2 = t ∨
      ∃ Γ' a' o' S', Fits Fl V Γ' a' o' S' (activeFrame cur t).2 := by
  intro Γ a o S t h
  induction h with
  | val hv _ _ => intro cur; left; cases ‹Tm› <;> simp_all [activeFrame, isVal]
  | var _ _ _ => intro cur; left; simp [activeFrame]
  | invoke hf hr ha _ _ _ _ _ ihf ihr iha =>
    intro cur
    simp only [activeFrame]
    split
    · exact .inr ((ihf cur).elim (fun he => ⟨_, _, _, _, he ▸ hf⟩) id)
    · split
      · exact .inr ((ihr cur).elim (fun he => ⟨_, _, _, _, he ▸ hr⟩) id)
      · rcases activeArgs_self_or (cur := cur) (t := .invoke _ _ _) _ with he | ⟨x, hx, he⟩
        · exact .inl he
        · rw [he]; exact .inr ((iha x hx cur).elim (fun he' => ⟨_, _, _, _, he' ▸ ha x hx⟩) id)
  | invokeC σ c π Sa Sr _ hfn _ _ hr ha _ _ _ _ _ ihr iha =>
    intro cur
    simp only [activeFrame, hfn.val, Bool.true_eq_false, ite_false]
    split
    · exact .inr ((ihr cur).elim (fun he => ⟨_, _, _, _, he ▸ hr⟩) id)
    · rcases activeArgs_self_or (cur := cur) (t := .invoke _ _ _) _ with he | ⟨x, hx, he⟩
      · exact .inl he
      · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
        rw [he]; exact .inr ((iha i x hi cur).elim (fun he' => ⟨_, _, _, _, he' ▸ ha i x hi⟩) id)
  | construct hf ha _ _ _ _ _ ihf iha =>
    intro cur
    simp only [activeFrame]
    split
    · exact .inr ((ihf cur).elim (fun he => ⟨_, _, _, _, he ▸ hf⟩) id)
    · rcases activeArgs_self_or (cur := cur) (t := .construct _ _) _ with he | ⟨x, hx, he⟩
      · exact .inl he
      · rw [he]; exact .inr ((iha x hx cur).elim (fun he' => ⟨_, _, _, _, he' ▸ ha x hx⟩) id)
  | letE hx _ _ ihx _ =>
    intro cur; simp only [activeFrame]; split
    · exact .inr ((ihx cur).elim (fun he => ⟨_, _, _, _, he ▸ hx⟩) id)
    · exact .inl rfl
  | spread hx _ _ ih | readAt hx _ _ _ _ ih | test hx _ ih | lenOf hx _ ih | throw hx _ ih =>
    intro cur; simp only [activeFrame]; split
    · exact .inr ((ih cur).elim (fun he => ⟨_, _, _, _, he ▸ hx⟩) id)
    · exact .inl rfl
  | ite hc _ _ _ ihc _ _ =>
    intro cur; simp only [activeFrame]; split
    · exact .inr ((ihc cur).elim (fun he => ⟨_, _, _, _, he ▸ hc⟩) id)
    · exact .inl rfl
  | makeAbsent _ _ hx _ _ ih | makeView _ _ hx _ _ _ ih | makeBound _ _ hx _ _ _ _ _ _ ih
  | makeGraphC _ _ _ hx _ _ _ _ _ _ _ _ ih | makeGraphOut _ _ hx _ _ _ _ _ _ _ _ _ ih | arrLit _ _ hx _ _ ih =>
    intro cur
    simp only [activeFrame]
    rcases activeArgs_self_or (cur := cur) (t := _) _ with he | ⟨x, hx', he⟩
    · exact .inl he
    · rw [he]; exact .inr ((ih x hx' cur).elim (fun he' => ⟨_, _, _, _, he' ▸ hx x hx'⟩) id)
  | indexAt hx hk _ _ _ _ ihx ihk | writeAt hx hk _ _ ihx ihk | arith hx hk _ ihx ihk | elemAt hx hk _ _ ihx ihk
  | merge hx hk _ _ _ _ _ _ ihx ihk | makeKey hx _ hk _ _ ihx ihk =>
    intro cur; simp only [activeFrame]; split
    · exact .inr ((ihx cur).elim (fun he => ⟨_, _, _, _, he ▸ hx⟩) id)
    · split
      · exact .inr ((ihk cur).elim (fun he => ⟨_, _, _, _, he ▸ hk⟩) id)
      · exact .inl rfl
  | setElem hx hi hv _ _ _ _ ihx ihi ihv =>
    intro cur; simp only [activeFrame]; split
    · exact .inr ((ihx cur).elim (fun he => ⟨_, _, _, _, he ▸ hx⟩) id)
    · split
      · exact .inr ((ihi cur).elim (fun he => ⟨_, _, _, _, he ▸ hi⟩) id)
      · split
        · exact .inr ((ihv cur).elim (fun he => ⟨_, _, _, _, he ▸ hv⟩) id)
        · exact .inl rfl
  | gotoC _ _ _ _ _ _ _ _ | gotoOut _ _ _ _ _ => intro cur; left; simp [activeFrame]
  | frameC _ _ _ _ _ _ _ _ _ ht _ _ ih =>
    intro cur; simp only [activeFrame]
    exact .inr ((ih _).elim (fun he => ⟨_, _, _, _, he ▸ ht⟩) id)
  | frameOut _ _ _ ht _ _ _ ih =>
    intro cur; simp only [activeFrame]
    exact .inr ((ih _).elim (fun he => ⟨_, _, _, _, he ▸ ht⟩) id)

/-- **The active term of a fitting term fits** (proved, `Fits.active_aux`). -/
theorem Fits.active {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {S : Sites P} {t : Tm}
    (h : Fits Fl V Γ a o S t) (cur : Option FrameKey) :
    ∃ Γ' a' o' S', Fits Fl V Γ' a' o' S' (activeFrame cur t).2 :=
  (h.active_aux cur).elim (fun he => ⟨_, _, _, _, he ▸ h⟩) id

end fits

/-- **A changed location's site is among the receiver's sites** (proved):
at a step from a fitting term at a value judgment `VJ`, every old location
the step changes is written by the active redex (`step_writes_active`),
whose receiver, a value, meets a set holding the location's site: the
location is one step from the receiver (`Leaves`), and the receiver's
sites (`VJ.sites`) hold its site. -/
theorem write_site {P : Package} {Fl : Flow P} {g : Ghost P} {n : Nat} {Γ : Nat → Option (Sites P)}
    {a : FrameAt P} {o : Bool} {S : Sites P} {h h' : Heap} {t t' : Tm}
    (hf : Fits Fl (VJ Fl g n) Γ a o S t) (hs : Step h t h' t') (cur : Option FrameKey)
    {l : Nat} {v : Val} (hv : h[l]? = some v) (hne : h'[l]? ≠ some v) :
    ∃ Sx, g.site l ∈ Sx ∧ ∃ x, VJ Fl g n Sx x ∧ Leaves P.ofC x l ∧
      ((∃ k y, (activeFrame cur t).2 = .writeAt k x y) ∨ ∃ i y, (activeFrame cur t).2 = .setElem x i y) := by
  have hw := step_writes_active hs hv hne cur
  obtain ⟨Γ', a', o', S', hfa⟩ := hf.active cur
  generalize (activeFrame cur t).2 = r at hw hfa ⊢
  match r, hw, hfa with
  | .writeAt k (.objAt fs c oid) y, hw, hfa =>
    cases hfa with
    | val hv _ _ => simp [isVal] at hv
    | writeAt hx _ _ _ =>
      cases hx with
      | val _ hvj _ =>
        have hl : Leaves P.ofC (.objAt fs c oid) l := Leaves.of_next (a := .key k) (by simpa [next, Footprints.fieldsOf, WriteRedex] using hw)
        exact ⟨_, hvj.sites l hl, _, hvj, hl, .inl ⟨k, y, rfl⟩⟩
  | .setElem (.arr ls) (.num b) y, hw, hfa =>
    cases hfa with
    | val hv _ _ => simp [isVal] at hv
    | setElem hx _ _ _ _ _ _ =>
      cases hx with
      | val _ hvj _ =>
        obtain ⟨i, hi⟩ := List.getElem?_of_mem (Kinds.elemLoc_mem (show elemLoc ls b = some l from hw))
        have hl : Leaves P.ofC (.arr ls) l := Leaves.of_next (a := .cell i) (by simp [next, spineEntries, hi])
        exact ⟨_, hvj.sites l hl, _, hvj, hl, .inr ⟨.num b, y, rfl⟩⟩

end Verification.TolerantFrames.ReadOnly
