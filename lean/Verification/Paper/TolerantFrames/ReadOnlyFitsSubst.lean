import Verification.Paper.TolerantFrames.ReadOnlyFits

/-! # Read-only handles: substitution and lowered code in a fitting term

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites of a term"). Three facts of the typing `Fits` (proof scope: the
lemmas below):

- **A term fitting a set fits every larger set** (`Fits.sub`): every rule
  reads its set covariantly.
- **Substitution keeps a term fitting** (`fits_subst`): a value meeting the
  sites `Sx` of the variable `j` replaces it; the variables past `j` move
  down by one (`insertSites`).
- **Lowered code instantiated at an environment of `O` fits `O`**
  (`fits_lowered`): at the allocation sites of outside code, every set is
  `O`. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} {Fl : Flow P}

/-! ## A larger set -/

theorem VOr.sub {V : Sites P → Val → Prop} (hV : Mono V) {Γ : Nat → Option (Sites P)} {S S' : Sites P} {u : Tm}
    (h : VOr V Γ S u) (hS : Sub S S') : VOr V Γ S' u :=
  Or.imp (hV _ _ _ hS) (fun ⟨j, S'', hu, hj, hs⟩ => ⟨j, S'', hu, hj, hs.trans hS⟩) h

theorem Fits.sub_aux {V : Sites P → Val → Prop} (hV : Mono V) :
    ∀ {Γ a S t}, Fits Fl V Γ a S t → ∀ {S'}, Sub S S' → Fits Fl V Γ a S' t := by
  intro Γ a S t h
  induction h with
  | val hv h₀ => intro _ hS; exact .val hv (hV _ _ _ hS h₀)
  | var h₁ h₂ => intro _ hS; exact .var h₁ (h₂.trans hS)
  | invoke hf hr hargs hO ha _ _ _ => intro _ hS; exact .invoke hf hr hargs (hO.trans hS) ha
  | construct hf hargs hO ha _ _ => intro _ hS; exact .construct hf hargs (hO.trans hS) ha
  | letE hx _ _ ihb => intro _ hS; exact .letE hx (ihb hS)
  | spread hx hc _ => intro _ hS; exact .spread hx fun s hs => (hc s hs).trans hS
  | makeAbsent Ss hst hi hs _ => intro _ hS; exact .makeAbsent Ss hst hi (hS _ hs)
  | makeView Ss hst hi hs hv _ => intro _ hS; exact .makeView Ss hst hi (hS _ hs) (hV _ _ _ hS hv)
  | makeBound Ss hst hi hs hp _ =>
    intro _ hS; exact .makeBound Ss hst hi (hS _ hs) fun x hx => (hp x hx).sub hV hS
  | makeGraphC π Ss hst hi hs hc hcode hcaps hE _ =>
    intro _ hS; exact .makeGraphC π Ss hst hi (hS _ hs) hc hcode hcaps hE
  | makeGraphOut Ss hst hi hs hc hE hcaps _ =>
    intro _ hS; exact .makeGraphOut Ss hst hi (hS _ hs) hc hE fun u hu => (hcaps u hu).sub hV hS
  | readAt hx hq hcl hr _ => intro _ hS; exact .readAt hx hq hcl fun s hs => (hr s hs).trans hS
  | indexAt hx hk hq hcl hr _ _ => intro _ hS; exact .indexAt hx hk hq hcl fun s hs => (hr s hs).trans hS
  | writeAt hx hy hst _ _ => intro _ _; exact .writeAt hx hy hst
  | test hx _ => intro _ _; exact .test hx
  | ite hc _ _ _ ihx ihy => intro _ hS; exact .ite hc (ihx hS) (ihy hS)
  | arith hx hy _ _ => intro _ _; exact .arith hx hy
  | arrLit Ss hst hi hs _ => intro _ hS; exact .arrLit Ss hst hi (hS _ hs)
  | elemAt hx hi hc _ _ => intro _ hS; exact .elemAt hx hi fun s hs => (hc s hs).trans hS
  | setElem hx hi hv hst hSx ha _ _ _ => intro _ hS; exact .setElem hx hi hv hst (hSx.trans hS) (hS _ ha)
  | lenOf hx _ => intro _ _; exact .lenOf hx
  | throw hx _ => intro _ _; exact .throw hx
  | merge hx hy hst hs _ _ => intro _ hS; exact .merge hx hy hst (hS _ hs)
  | makeKey hk hst hx hs _ _ => intro _ hS; exact .makeKey hk hst hx (hS _ hs)
  | gotoC π hc hcode henv hO => intro _ hS; exact .gotoC π hc hcode henv (hO.trans hS)
  | gotoOut hc hE henv hO => intro _ hS; exact .gotoOut hc hE henv (hO.trans hS)
  | frameC π l hc hcode hn henv ht hO _ => intro _ hS; exact .frameC π l hc hcode hn henv ht (hO.trans hS)
  | frameOut hc hE henv ht hO _ => intro _ hS; exact .frameOut hc hE henv ht (hO.trans hS)

/-- **A term fitting a set fits every larger set** (proved), at a monotone
value judgment. -/
theorem Fits.sub {V : Sites P → Val → Prop} (hV : Mono V) {Γ a S S' t} (h : Fits Fl V Γ a S t)
    (hS : Sub S S') : Fits Fl V Γ a S' t :=
  Fits.sub_aux hV h hS

/-! ## Substitution -/

/-- The variables' sites with the variable `j` inserted at the sites `Sx`:
the variables at and past `j` move up by one. -/
def insertSites (j : Nat) (Sx : Sites P) (Γ : Nat → Option (Sites P)) : Nat → Option (Sites P) :=
  fun i => if i < j then Γ i else if i = j then some Sx else Γ (i - 1)

theorem consSites_insertSites (S Sx : Sites P) (j : Nat) (Γ : Nat → Option (Sites P)) :
    consSites S (insertSites j Sx Γ) = insertSites (j + 1) Sx (consSites S Γ) := by
  funext i
  cases i with
  | zero => simp [consSites, insertSites]
  | succ k =>
    simp only [consSites, insertSites, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff, Nat.add_sub_cancel]
    by_cases hk : k < j
    · simp [hk]
    · by_cases he : k = j
      · simp [he]
      · simp only [hk, he, if_false]
        cases k with
        | zero => omega
        | succ m => simp

/-- A variable after a substitution: the substituted value at `j`, or a
variable the outer sites bind as before (proved). -/
theorem subst_var_ins {Γ : Nat → Option (Sites P)} {j i : Nat} {Sx S' : Sites P} {v : Tm}
    (h : insertSites j Sx Γ i = some S') :
    (S' = Sx ∧ subst j v (.var i) = v) ∨ ∃ i', Γ i' = some S' ∧ subst j v (.var i) = .var i' := by
  unfold insertSites at h
  simp only [subst]
  by_cases hij : i = j
  · subst hij
    left
    simp only [Nat.lt_irrefl, if_false, if_true, Option.some.injEq] at h
    exact ⟨h.symm, by simp⟩
  · by_cases hlt : i < j
    · right
      refine ⟨i, by simpa [hlt] using h, ?_⟩
      simp [hij, show ¬ j < i by omega]
    · right
      refine ⟨i - 1, by simpa [hlt, hij] using h, ?_⟩
      simp [hij, show j < i by omega]

theorem envOf_map (f : Tm → Tm) (L : List Tm) (d : Tm) (i : Nat) :
    envOf (L.map f) (f d) i = f (envOf L d i) := by
  unfold envOf
  induction L generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp_all

open Classical in
/-- **The sites of a mapped list** (proved): each image takes the sites of
one of its preimages. -/
theorem sites_map {St : Sites P → Prop} {Fi : Sites P → Tm → Prop} (f : Tm → Tm) {Ss : Tm → Sites P}
    {xs : List Tm} (hst : ∀ x ∈ xs, St (Ss x)) (hi : ∀ x ∈ xs, Fi (Ss x) (f x)) :
    ∃ Ss' : Tm → Sites P, (∀ y ∈ xs.map f, St (Ss' y)) ∧ ∀ y ∈ xs.map f, Fi (Ss' y) y := by
  refine ⟨fun y => if h : ∃ x, x ∈ xs ∧ f x = y then Ss (Classical.choose h) else Ss y, ?_, ?_⟩
  · intro y hy
    have h : ∃ x, x ∈ xs ∧ f x = y := List.mem_map.mp hy
    simp only [h, dif_pos]
    exact hst _ (Classical.choose_spec h).1
  · intro y hy
    have h : ∃ x, x ∈ xs ∧ f x = y := List.mem_map.mp hy
    simp only [h, dif_pos]
    have hs := Classical.choose_spec h
    have := hi _ hs.1
    rwa [hs.2] at this

variable {g : Ghost P} {n : Nat}

/-- **Substitution keeps a position** (proved). -/
theorem VOr.subst {j : Nat} {Sx : Sites P} {v : Val} (hv : VJ Fl g n Sx v) {Γ : Nat → Option (Sites P)}
    {S : Sites P} {u : Tm} (h : VOr (VJ Fl g n) (insertSites j Sx Γ) S u) :
    VOr (VJ Fl g n) Γ S (Verification.subst j v u) := by
  rcases h with h | ⟨i, S', rfl, hi, hs⟩
  · left; rw [h.closed j v]; exact h
  · rcases subst_var_ins (v := v) hi with ⟨rfl, he⟩ | ⟨i', hi', he⟩
    · rw [he]; exact .inl (hv.sub hs)
    · rw [he]; exact .inr ⟨i', S', rfl, hi', hs⟩

theorem fits_subst_aux {Sx : Sites P} {v : Val} (hv : VJ Fl g n Sx v) :
    ∀ {Γ' a S t}, Fits Fl (VJ Fl g n) Γ' a S t → ∀ {j Γ}, Γ' = insertSites j Sx Γ →
      Fits Fl (VJ Fl g n) Γ a S (subst j v t) := by
  intro Γ' a S t h
  induction h with
  | val hv' h₀ => intro j _ _; rw [h₀.closed j v]; exact .val hv' h₀
  | var h₁ h₂ =>
    intro j Γ hΓ; subst hΓ
    rcases subst_var_ins (v := v) h₁ with ⟨rfl, he⟩ | ⟨i', hi', he⟩
    · rw [he]; exact .val hv.val (hv.sub h₂)
    · rw [he]; exact .var hi' h₂
  | invoke _ _ _ hO ha ihf ihr iha =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .invoke (ihf rfl) (ihr rfl) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy rfl) hO ha
  | construct _ _ hO ha ihf iha =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .construct (ihf rfl) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy rfl) hO ha
  | letE _ _ ihx ihb =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .letE (ihx rfl) (ihb (j := j + 1) (consSites_insertSites _ _ _ _))
  | spread _ hc ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .spread (ih rfl) hc
  | makeAbsent Ss hst _ hs ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _) (subst j v) hst fun x hx => ih x hx rfl
    exact .makeAbsent Ss' h₁ h₂ hs
  | makeView Ss hst _ hs hv' ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _) (subst j v) hst fun x hx => ih x hx rfl
    exact .makeView Ss' h₁ h₂ hs hv'
  | makeBound Ss hst _ hs hp ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _) (subst j v) hst fun x hx => ih x hx rfl
    refine .makeBound Ss' h₁ h₂ hs fun x hx => ?_
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | rfl | ⟨y, hy, rfl⟩
    · exact (hp _ (by simp)).subst hv
    · exact (hp _ (by simp)).subst hv
    · exact (hp y (by simp [hy])).subst hv
  | makeGraphC π Ss hst _ hs hc hcode hcaps hE ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _) (subst j v) hst fun x hx => ih x hx rfl
    refine .makeGraphC π Ss' h₁ h₂ hs hc hcode (fun i u hu => ?_) hE
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact (hcaps i x hx).subst hv
  | makeGraphOut Ss hst _ hs hc hE hcaps ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _) (subst j v) hst fun x hx => ih x hx rfl
    refine .makeGraphOut Ss' h₁ h₂ hs hc hE fun u hu => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
    exact (hcaps y hy).subst hv
  | readAt _ hq hcl hr ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .readAt (ih rfl) hq hcl hr
  | indexAt _ _ hq hcl hr ihx ihk =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .indexAt (ihx rfl) (ihk rfl) hq hcl hr
  | writeAt _ _ hst ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .writeAt (ihx rfl) (ihy rfl) hst
  | test _ ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .test (ih rfl)
  | ite _ _ _ ihc ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .ite (ihc rfl) (ihx rfl) (ihy rfl)
  | arith _ _ ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .arith (ihx rfl) (ihy rfl)
  | arrLit Ss hst _ hs ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _) (subst j v) hst fun x hx => ih x hx rfl
    exact .arrLit Ss' h₁ h₂ hs
  | elemAt _ _ hc ihx ihi =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .elemAt (ihx rfl) (ihi rfl) hc
  | setElem _ _ _ hst hS ha ihx ihi ihv =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .setElem (ihx rfl) (ihi rfl) (ihv rfl) hst hS ha
  | lenOf _ ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .lenOf (ih rfl)
  | throw _ ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .throw (ih rfl)
  | merge _ _ hst hs ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .merge (ihx rfl) (ihy rfl) hst hs
  | makeKey _ hst _ hs ihk ihx =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .makeKey (ihk rfl) hst (ihx rfl) hs
  | gotoC π hc hcode henv hO =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .gotoC π hc hcode (fun i => by rw [envOf_map]; exact (henv i).subst hv) hO
  | gotoOut hc hE henv hO =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .gotoOut hc hE (fun i => by rw [envOf_map]; exact (henv i).subst hv) hO
  | frameC π l hc hcode hn henv _ hO ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .frameC π l hc hcode hn (fun i => by rw [envOf_map, (henv i).closed j v]; exact henv i) (ih rfl) hO
  | frameOut hc hE henv _ hO ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .frameOut hc hE (fun i => by rw [envOf_map, (henv i).closed j v]; exact henv i) (ih rfl) hO

/-- **Substitution keeps a term fitting** (proved): a value meeting the
sites of the variable `j` replaces it. -/
theorem fits_subst {j : Nat} {Sx : Sites P} {v : Val} (hv : VJ Fl g n Sx v) :
    ∀ {Γ a S t}, Fits Fl (VJ Fl g n) (insertSites j Sx Γ) a S t →
      Fits Fl (VJ Fl g n) Γ a S (subst j v t) :=
  fun h => fits_subst_aux hv h rfl

/-! ## Lowered code at an environment of `O` -/

theorem instantiate_prim {d : Nat} {ρ : Env} {x : Tm} (hp : primVal x = true) : instantiate d ρ x = x := by
  cases x <;> simp [primVal] at hp <;> simp [instantiate]

/-- **A part of a closure's code, instantiated** (proved): a variable below
`d` the sites bind to `O`, a value of the environment, or a primitive. -/
theorem codePart_instantiate {ρ : Env} (hρ : ∀ i, VJ Fl g n Fl.O (ρ i)) {x : Tm} (hx : CodePart x) {d : Nat}
    {Γ : Nat → Option (Sites P)} (hΓ : ∀ i, i < d → Γ i = some Fl.O) {S : Sites P} (hS : Sub Fl.O S) :
    VOr (VJ Fl g n) Γ S (instantiate d ρ x) := by
  rcases hx with ⟨i, rfl⟩ | hp
  · simp only [instantiate]
    split
    · exact .inr ⟨i, Fl.O, rfl, hΓ i ‹_›, hS⟩
    · exact .inl ((hρ _).sub hS)
  · rw [instantiate_prim hp]; exact .inl (VJ.prim hp)

/-- **Lowered code instantiated at an environment of `O` fits `O`**
(proved), at the allocation sites of outside code. -/
theorem fits_lowered (hF : Fl.Facts) (ρ : Env) (hρ : ∀ i, VJ Fl g n Fl.O (ρ i)) :
    ∀ (e : Tm) (d : Nat) (Γ : Nat → Option (Sites P)), Lowered Fl e → (∀ i, i < d → Γ i = some Fl.O) →
      Fits Fl (VJ Fl g n) Γ Alloc.outside Fl.O (instantiate d ρ e) := by
  have hst : Stores Fl none Fl.O := hF.writable none hF.none
  have hc : ∀ s ∈ Fl.O, Sub (Fl.H.contents s) Fl.O := hF.closed
  intro e
  induction e using Tm.induct with
  | var i =>
    intro d Γ _ hΓ
    simp only [instantiate]
    split
    · exact .var (hΓ i ‹_›) (Sub.refl _)
    · exact .val (hρ _).val (hρ _)
  | invoke f r args ihf ihr iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    exact .invoke (ihf d Γ hL.1 hΓ) (ihr d Γ hL.2.1 hΓ) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL.2.2 y hy) hΓ) (Sub.refl _) hF.none
  | construct f args ihf iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    exact .construct (ihf d Γ hL.1 hΓ) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL.2 y hy) hΓ) (Sub.refl _) hF.none
  | letE x b ihx ihb =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    refine .letE (ihx d Γ hL.1 hΓ) (ihb (d + 1) (consSites Fl.O Γ) hL.2 fun i hi => ?_)
    cases i with
    | zero => rfl
    | succ k => exact hΓ k (by omega)
  | nul => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl)
  | undef => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl)
  | tru => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl)
  | fls => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl)
  | num v => intro d Γ _ _; rw [instantiate_prim (x := .num v) rfl]; exact .val rfl (VJ.prim rfl)
  | str v => intro d Γ _ _; rw [instantiate_prim (x := .str v) rfl]; exact .val rfl (VJ.prim rfl)
  | bigint v => intro d Γ _ _; rw [instantiate_prim (x := .bigint v) rfl]; exact .val rfl (VJ.prim rfl)
  | sym v => intro d Γ _ _; rw [instantiate_prim (x := .sym v) rfl]; exact .val rfl (VJ.prim rfl)
  | objAbsent => intro d Γ hL _; simp only [Lowered] at hL
  | objBound => intro d Γ hL _; simp only [Lowered] at hL
  | makeBound t r pre ns args _ _ _ iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    obtain ⟨ht, hr, hpre, hargs⟩ := hL
    simp only [instantiate, instantiateArgs_eq_map]
    refine .makeBound (fun _ => Fl.O) (fun _ _ => hst) (fun x hx => ?_) hF.none (fun x hx => ?_)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hargs y hy) hΓ
    · simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | rfl | ⟨y, hy, rfl⟩
      · exact codePart_instantiate hρ ht hΓ (Sub.refl _)
      · exact codePart_instantiate hρ hr hΓ (Sub.refl _)
      · exact codePart_instantiate hρ (hpre y hy) hΓ (Sub.refl _)
  | alloc ns args iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    refine .makeAbsent (fun _ => Fl.O) (fun _ _ => hst) (fun x hx => ?_) hF.none
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL y hy) hΓ
  | objView => intro d Γ hL _; simp only [Lowered] at hL
  | makeView => intro d Γ hL _; simp only [Lowered] at hL
  | read f x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .readAt (ih d Γ hL hΓ) (Sub.refl _) hc hc
  | index x key ihx ihk =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .indexAt (ihx d Γ hL.1 hΓ) (ihk d Γ hL.2 hΓ) (Sub.refl _) hc hc
  | write f x y ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .writeAt (ihx d Γ hL.1 hΓ) (ihy d Γ hL.2 hΓ) hF.writable
  | test k x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .test (ih d Γ hL hΓ)
  | ite c x y ihc ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .ite (ihc d Γ hL.1 hΓ) (ihx d Γ hL.2.1 hΓ) (ihy d Γ hL.2.2 hΓ)
  | arith op x y ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .arith (ihx d Γ hL.1 hΓ) (ihy d Γ hL.2 hΓ)
  | arr ls =>
    intro d Γ hL _
    simp only [Lowered] at hL
    have he : instantiate d ρ (.arr ls) = .arr ls := by simp [instantiate]
    rw [he]
    exact .val rfl (VJ.arr fun l hl => by have := hL _ hl; simp at this)
  | viewSpine => intro d Γ hL _; simp only [Lowered] at hL
  | arrLit inits iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    refine .arrLit (fun _ => Fl.O) (fun _ _ => hst) (fun x hx => ?_) hF.none
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL y hy) hΓ
  | elemAt x i ihx ihi =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .elemAt (ihx d Γ hL.1 hΓ) (ihi d Γ hL.2 hΓ) hc
  | setElem x i v ihx ihi ihv =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    refine .setElem (ihx d Γ hL.1 hΓ) (ihi d Γ hL.2.1 hΓ) (ihv d Γ hL.2.2 hΓ) (fun s hs => ?_) (Sub.refl _) hF.none
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hst
    · exact hF.writable s hs
  | lenOf x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .lenOf (ih d Γ hL hΓ)
  | spread x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .spread (ih d Γ hL hΓ) hc
  | throw x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .throw (ih d Γ hL hΓ)
  | merge dr x y ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    refine .merge (ihx d Γ hL.1 hΓ) (ihy d Γ hL.2 hΓ) (fun s hs => ?_) hF.none
    have hs' : s ∈ Fl.O := by simpa using hs
    exact ⟨(hc s hs').trans hst.1, (hc s hs').trans hst.2⟩
  | makeKey k x ihk ihx =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .makeKey (ihk d Γ hL.1 hΓ) hst (ihx d Γ hL.2 hΓ) hF.none
  | objGraph => intro d Γ hL _; simp only [Lowered] at hL
  | makeGraph ar E K s caps k r comp ns args _ _ iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    obtain ⟨hπ, hE, hcaps, hargs⟩ := hL
    simp only [instantiate, instantiateArgs_eq_map]
    have hi : ∀ x ∈ args.map (instantiate d ρ), Fits Fl (VJ Fl g n) Γ Alloc.outside ((fun _ => Fl.O) x) x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hargs y hy) hΓ
    cases hcomp : P.ofC comp with
    | true =>
      obtain ⟨π, hcode⟩ := hπ hcomp
      refine .makeGraphC π (fun _ => Fl.O) (fun _ _ => hst) hi hF.none hcomp hcode (fun i u hu => ?_) hE
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      exact codePart_instantiate hρ (hcaps x (List.mem_of_getElem? hx)) hΓ (hF.envO _ π hcode _ _)
    | false =>
      refine .makeGraphOut (fun _ => Fl.O) (fun _ _ => hst) hi hF.none hcomp hE fun u hu => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
      exact codePart_instantiate hρ (hcaps y hy) hΓ (Sub.refl _)
  | goto => intro d Γ hL _; simp only [Lowered] at hL
  | frame => intro d Γ hL _; simp only [Lowered] at hL

end Verification.TolerantFrames.ReadOnly
