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
    ∀ {Γ a o S t}, Fits Fl V Γ a o S t → ∀ {S'}, Sub S S' → (o = true → Sub S' Fl.O) → Fits Fl V Γ a o S' t := by
  intro Γ a o S t h
  induction h with
  | val hv h₀ _ => intro _ hS ho; exact .val hv (hV _ _ _ hS h₀) ho
  | var h₁ h₂ _ => intro _ hS ho; exact .var h₁ (h₂.trans hS) ho
  | invoke hf hr hargs hO ha _ hSf hout _ _ _ => intro _ hS ho; exact .invoke hf hr hargs (hO.trans hS) ha ho hSf hout
  | invokeC σ c π Sa Sr hof hfn hcode hself hr hargs hat hpar hrest hO _ _ _ =>
    intro _ hS ho; exact .invokeC σ c π Sa Sr hof hfn hcode hself hr hargs hat hpar hrest (hO.trans hS) ho
  | construct hf hargs hO ha _ hSf hout _ _ => intro _ hS ho; exact .construct hf hargs (hO.trans hS) ha ho hSf hout
  | letE hx _ _ _ ihb => intro _ hS ho; exact .letE hx (ihb hS ho) ho
  | spread hx hc _ _ => intro _ hS ho; exact .spread hx (fun s hs => (hc s hs).trans hS) ho
  | makeAbsent Ss hst hi hs _ _ => intro _ hS ho; exact .makeAbsent Ss hst hi (hS _ hs) ho
  | makeView Ss hst hi hs hv _ _ => intro _ hS ho; exact .makeView Ss hst hi (hS _ hs) (hV _ _ _ hS hv) ho
  | makeBound Ss hst hi hs Sb hb hnl hp _ _ =>
    intro _ hS ho; exact .makeBound Ss hst hi (hS _ hs) Sb (fun x hx => hS _ (hb x hx)) hnl hp ho
  | makeGraphC π Ss hst hi hs hc hcode hcaps htok hop hE _ _ =>
    intro _ hS ho; exact .makeGraphC π Ss hst hi (hS _ hs) hc hcode hcaps (hS _ htok) hop hE ho
  | makeGraphOut Ss hst hi hs hc hE Sc hb hnl hcaps _ hn _ =>
    intro _ hS ho; exact .makeGraphOut Ss hst hi (hS _ hs) hc hE Sc (fun x hx => hS _ (hb x hx)) hnl hcaps ho (hS _ hn)
  | readAt hx hq hcl hr _ _ => intro _ hS ho; exact .readAt hx hq hcl (fun s hs => (hr s hs).trans hS) ho
  | indexAt hx hk hq hcl hr _ _ _ =>
    intro _ hS ho; exact .indexAt hx hk hq hcl (fun s hs => (hr s hs).trans hS) ho
  | writeAt hx hy hst _ _ _ => intro _ _ ho; exact .writeAt hx hy hst ho
  | test hx _ _ => intro _ _ ho; exact .test hx ho
  | ite hc _ _ _ _ ihx ihy => intro _ hS ho; exact .ite hc (ihx hS ho) (ihy hS ho) ho
  | arith hx hy _ _ _ => intro _ _ ho; exact .arith hx hy ho
  | arrLit Ss hst hi hs _ _ => intro _ hS ho; exact .arrLit Ss hst hi (hS _ hs) ho
  | elemAt hx hi hc _ _ _ => intro _ hS ho; exact .elemAt hx hi (fun s hs => (hc s hs).trans hS) ho
  | setElem hx hi hv hst hSx ha _ _ _ _ => intro _ hS ho; exact .setElem hx hi hv hst (hSx.trans hS) (hS _ ha) ho
  | lenOf hx _ _ => intro _ _ ho; exact .lenOf hx ho
  | throw hx _ _ => intro _ _ ho; exact .throw hx ho
  | merge hx hy hq hcl hst hs hQ _ _ _ => intro _ hS ho; exact .merge hx hy hq hcl hst (hS _ hs) hQ ho
  | makeKey hk hst hx hs _ _ _ => intro _ hS ho; exact .makeKey hk hst hx (hS _ hs) ho
  | gotoC c π hc hcode henv hfn hO _ => intro _ hS ho; exact .gotoC c π hc hcode henv hfn (hO.trans hS) ho
  | gotoOut hc hE henv hO _ => intro _ hS ho; exact .gotoOut hc hE henv (hO.trans hS) ho
  | frameC c π l hc hcode hn henv hfn hvfn ht hO _ _ =>
    intro _ hS ho; exact .frameC c π l hc hcode hn henv hfn hvfn ht (hO.trans hS) ho
  | frameOut hc hE henv ht hO _ _ => intro _ hS ho; exact .frameOut hc hE henv ht (hO.trans hS) ho

/-- **A term fitting a set fits every larger set** (proved), at a monotone
value judgment, within `O` at a position of outside code. -/
theorem Fits.sub {V : Sites P → Val → Prop} (hV : Mono V) {Γ a o S S' t} (h : Fits Fl V Γ a o S t)
    (hS : Sub S S') (ho : o = true → Sub S' Fl.O) : Fits Fl V Γ a o S' t :=
  Fits.sub_aux hV h hS ho

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
      · simp only [hk, he, ite_false]
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
    simp only [Nat.lt_irrefl, ite_false, ite_true, Option.some.injEq] at h
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
    simp only [h, dite_eq_left]
    exact hst _ (Classical.choose_spec h).1
  · intro y hy
    have h : ∃ x, x ∈ xs ∧ f x = y := List.mem_map.mp hy
    simp only [h, dite_eq_left]
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

/-- A variable is no closure. -/
theorem FnIs.not_var {σ : FnSig} {k : Nat} (h : FnIs P σ (.var k)) : False := by
  obtain ⟨_, _, _, _, _, he, _⟩ := h; cases he

/-- **A position naming a signature is a closed value** (proved): a
variable is no closure. -/
theorem VOr.fn_closed {Γ : Nat → Option (Sites P)} {S : Sites P} {u : Tm} {σ : FnSig}
    (h : VOr (VJ Fl g n) Γ S u) (hf : FnIs P σ u) : Verification.Closed u := by
  rcases h with h | ⟨k, _, rfl, _, _⟩
  · exact h.closed
  · exact hf.not_var.elim

/-- **Substitution keeps an atom** (proved): a value fitting a set is
closed; a variable becomes the value or a variable. -/
theorem atom_subst {Γ a o S} {j : Nat} {v : Val} (hv : isVal v = true) {x : Tm}
    (hx : Fits Fl (VJ Fl g n) Γ a o S x) (hat : isVal x = true ∨ ∃ k, x = .var k) :
    isVal (subst j v x) = true ∨ ∃ k, subst j v x = .var k := by
  rcases hat with hx' | ⟨k, rfl⟩
  · rw [(hx.value hx').closed j v]; exact .inl hx'
  · simp only [subst]
    split
    · exact .inl hv
    · split
      · exact .inr ⟨_, rfl⟩
      · exact .inr ⟨_, rfl⟩

theorem fits_subst_aux {Sx : Sites P} {v : Val} (hv : VJ Fl g n Sx v) :
    ∀ {Γ' a o S t}, Fits Fl (VJ Fl g n) Γ' a o S t → ∀ {j Γ}, Γ' = insertSites j Sx Γ →
      Fits Fl (VJ Fl g n) Γ a o S (subst j v t) := by
  intro Γ' a o S t h
  induction h with
  | val hv' h₀ ho => intro j _ _; rw [h₀.closed j v]; exact .val hv' h₀ ho
  | var h₁ h₂ ho =>
    intro j Γ hΓ; subst hΓ
    rcases subst_var_ins (v := v) h₁ with ⟨rfl, he⟩ | ⟨i', hi', he⟩
    · rw [he]; exact .val hv.val (hv.sub h₂) ho
    · rw [he]; exact .var hi' h₂ ho
  | invoke _ _ _ hO ha ho hSf hout ihf ihr iha =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .invoke (ihf rfl) (ihr rfl) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy rfl) hO ha ho hSf hout
  | invokeC σ c π Sa Sr hof hfn hcode hself _ hargs hat hpar hrest hO ho ihr iha =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    rw [hself.closed j v]
    refine .invokeC σ c π Sa Sr hof hfn hcode hself (ihr rfl) (fun i x hx => ?_) (fun x hx => ?_) hpar hrest hO ho
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact iha i y hy rfl
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
      exact atom_subst hv.val (hargs i y hi) (hat y hy)
  | construct _ _ hO ha ho hSf hout ihf iha =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .construct (ihf rfl) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy rfl) hO ha ho hSf hout
  | letE _ _ ho ihx ihb =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .letE (ihx rfl) (ihb (j := j + 1) (consSites_insertSites _ _ _ _)) ho
  | spread _ hc ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .spread (ih rfl) hc ho
  | makeAbsent Ss hst _ hs ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _ _) (subst j v) hst fun x hx => ih x hx rfl
    exact .makeAbsent Ss' h₁ h₂ hs ho
  | makeView Ss hst _ hs hv' ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _ _) (subst j v) hst fun x hx => ih x hx rfl
    exact .makeView Ss' h₁ h₂ hs hv' ho
  | makeBound Ss hst _ hs Sb hb hnl hp ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _ _) (subst j v) hst fun x hx => ih x hx rfl
    refine .makeBound Ss' h₁ h₂ hs Sb hb hnl (fun x hx => ?_) ho
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | rfl | ⟨y, hy, rfl⟩
    · exact (hp _ (by simp)).subst hv
    · exact (hp _ (by simp)).subst hv
    · exact (hp y (by simp [hy])).subst hv
  | makeGraphC π Ss hst _ hs hc hcode hcaps htok hop hE ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _ _) (subst j v) hst fun x hx => ih x hx rfl
    refine .makeGraphC π Ss' h₁ h₂ hs hc hcode (fun c π' h' => ⟨fun i u hu => ?_, fun i σ hi => ?_⟩) htok
      (by rwa [List.length_map]) hE ho
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      exact ((hcaps c π' h').1 i x hx).subst hv
    · obtain ⟨k, hk, hcase⟩ := (hcaps c π' h').2 i σ hi
      refine ⟨k, hk, ?_⟩
      rcases hcase with ⟨u, hu, hfu⟩ | ⟨hk', hσ⟩
      · refine .inl ⟨u, ?_, hfu⟩
        rw [List.getElem?_map, hu, Option.map_some, (((hcaps c π' h').1 k u hu).fn_closed hfu) j v]
      · exact .inr ⟨by rw [hk', List.length_map], by rw [hσ, List.length_map]⟩
  | makeGraphOut Ss hst _ hs hc hE Sc hb hnl hcaps ho hn ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _ _) (subst j v) hst fun x hx => ih x hx rfl
    refine .makeGraphOut Ss' h₁ h₂ hs hc hE Sc hb hnl (fun u hu => ?_) ho hn
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
    exact (hcaps y hy).subst hv
  | readAt _ hq hcl hr ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .readAt (ih rfl) hq hcl hr ho
  | indexAt _ _ hq hcl hr ho ihx ihk =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .indexAt (ihx rfl) (ihk rfl) hq hcl hr ho
  | writeAt _ _ hst ho ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .writeAt (ihx rfl) (ihy rfl) hst ho
  | test _ ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .test (ih rfl) ho
  | ite _ _ _ ho ihc ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .ite (ihc rfl) (ihx rfl) (ihy rfl) ho
  | arith _ _ ho ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .arith (ihx rfl) (ihy rfl) ho
  | arrLit Ss hst _ hs ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) Γ _ _) (subst j v) hst fun x hx => ih x hx rfl
    exact .arrLit Ss' h₁ h₂ hs ho
  | elemAt _ _ hc ho ihx ihi =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .elemAt (ihx rfl) (ihi rfl) hc ho
  | setElem _ _ _ hst hS ha ho ihx ihi ihv =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .setElem (ihx rfl) (ihi rfl) (ihv rfl) hst hS ha ho
  | lenOf _ ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .lenOf (ih rfl) ho
  | throw _ ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .throw (ih rfl) ho
  | merge _ _ hq hcl hst hs hQ ho ihx ihy =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .merge (ihx rfl) (ihy rfl) hq hcl hst hs hQ ho
  | makeKey _ hst _ hs ho ihk ihx =>
    intro j Γ hΓ; subst hΓ
    simp only [subst]
    exact .makeKey (ihk rfl) hst (ihx rfl) hs ho
  | gotoC c π hc hcode henv hfn hO ho =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    refine .gotoC c π hc hcode (fun i => by rw [envOf_map]; exact (henv i).subst hv) (fun i σ hi => ?_) hO ho
    rw [envOf_map, ((henv i).fn_closed (hfn i σ hi)) j v]
    exact hfn i σ hi
  | gotoOut hc hE henv hO ho =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .gotoOut hc hE (fun i => by rw [envOf_map]; exact (henv i).subst hv) hO ho
  | frameC c π l hc hcode hn henv hfn hvfn ht hO ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    refine .frameC c π l hc hcode hn (fun i => by rw [envOf_map, (henv i).closed j v]; exact henv i)
      (fun i σ hi => by rw [envOf_map, (henv i).closed j v]; exact hfn i σ hi) (fun σ hσ => ?_) (ih rfl) hO ho
    have hf := hvfn σ hσ
    rw [(ht.value hf.val).closed j v]; exact hf
  | frameOut hc hE henv _ hO ho ih =>
    intro j Γ hΓ; subst hΓ
    simp only [subst, substArgs_eq_map]
    exact .frameOut hc hE (fun i => by rw [envOf_map, (henv i).closed j v]; exact henv i) (ih rfl) hO ho

/-- **Substitution keeps a term fitting** (proved): a value meeting the
sites of the variable `j` replaces it. -/
theorem fits_subst {j : Nat} {Sx : Sites P} {v : Val} (hv : VJ Fl g n Sx v) :
    ∀ {Γ a o S t}, Fits Fl (VJ Fl g n) (insertSites j Sx Γ) a o S t →
      Fits Fl (VJ Fl g n) Γ a o S (subst j v t) :=
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
theorem fits_lowered (hF : Fl.Facts) (ρ : Env) (hρ : ∀ i, VJ Fl g n Fl.O (ρ i)) {o : Bool} :
    ∀ (e : Tm) (d : Nat) (Γ : Nat → Option (Sites P)), Lowered Fl e → (∀ i, i < d → Γ i = some Fl.O) →
      Fits Fl (VJ Fl g n) Γ FrameAt.outside o Fl.O (instantiate d ρ e) := by
  have hoO : o = true → Sub Fl.O Fl.O := fun _ => Sub.refl _
  have hst : Stores Fl none Fl.O := hF.writable none hF.none
  have hc : ∀ s ∈ Fl.O, Sub (Fl.H.contents s) Fl.O := hF.closed
  intro e
  induction e using Tm.induct with
  | var i =>
    intro d Γ _ hΓ
    simp only [instantiate]
    split
    · exact .var (hΓ i ‹_›) (Sub.refl _) hoO
    · exact .val (hρ _).val (hρ _) hoO
  | invoke f r args ihf ihr iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    exact .invoke (ihf d Γ hL.1 hΓ) (ihr d Γ hL.2.1 hΓ) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL.2.2 y hy) hΓ) (Sub.refl _) hF.none hoO
      (Sub.refl _) (fun _ => rfl)
  | construct f args ihf iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    exact .construct (ihf d Γ hL.1 hΓ) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL.2 y hy) hΓ) (Sub.refl _) hF.none hoO
      (Sub.refl _) (fun _ => rfl)
  | letE x b ihx ihb =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    refine .letE (ihx d Γ hL.1 hΓ) (ihb (d + 1) (consSites Fl.O Γ) hL.2 fun i hi => ?_) hoO
    cases i with
    | zero => rfl
    | succ k => exact hΓ k (by omega)
  | nul => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl) hoO
  | undef => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl) hoO
  | tru => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl) hoO
  | fls => intro d Γ _ _; rw [instantiate_prim rfl]; exact .val rfl (VJ.prim rfl) hoO
  | num v => intro d Γ _ _; rw [instantiate_prim (x := .num v) rfl]; exact .val rfl (VJ.prim rfl) hoO
  | str v => intro d Γ _ _; rw [instantiate_prim (x := .str v) rfl]; exact .val rfl (VJ.prim rfl) hoO
  | bigint v => intro d Γ _ _; rw [instantiate_prim (x := .bigint v) rfl]; exact .val rfl (VJ.prim rfl) hoO
  | sym v => intro d Γ _ _; rw [instantiate_prim (x := .sym v) rfl]; exact .val rfl (VJ.prim rfl) hoO
  | objAbsent => intro d Γ hL _; simp only [Lowered] at hL
  | objBound => intro d Γ hL _; simp only [Lowered] at hL
  | makeBound t r pre ns args _ _ _ iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    obtain ⟨ht, hr, hpre, hargs⟩ := hL
    simp only [instantiate, instantiateArgs_eq_map]
    refine .makeBound (fun _ => Fl.O) (fun _ _ => hst) (fun x hx => ?_) hF.none Fl.O (Sub.refl _) hF.noLocal
      (fun x hx => ?_) hoO
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
    refine .makeAbsent (fun _ => Fl.O) (fun _ _ => hst) (fun x hx => ?_) hF.none hoO
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL y hy) hΓ
  | objView => intro d Γ hL _; simp only [Lowered] at hL
  | makeView => intro d Γ hL _; simp only [Lowered] at hL
  | read f x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .readAt (ih d Γ hL hΓ) (Sub.refl _) hc hc hoO
  | index x key ihx ihk =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .indexAt (ihx d Γ hL.1 hΓ) (ihk d Γ hL.2 hΓ) (Sub.refl _) hc hc hoO
  | write f x y ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .writeAt (ihx d Γ hL.1 hΓ) (ihy d Γ hL.2 hΓ) hF.writable hoO
  | test k x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .test (ih d Γ hL hΓ) hoO
  | ite c x y ihc ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .ite (ihc d Γ hL.1 hΓ) (ihx d Γ hL.2.1 hΓ) (ihy d Γ hL.2.2 hΓ) hoO
  | arith op x y ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .arith (ihx d Γ hL.1 hΓ) (ihy d Γ hL.2 hΓ) hoO
  | arr ls =>
    intro d Γ hL _
    simp only [Lowered] at hL
    have he : instantiate d ρ (.arr ls) = .arr ls := by simp [instantiate]
    rw [he]
    exact .val rfl (VJ.arr fun l hl => by have := hL _ hl; simp at this) hoO
  | viewSpine => intro d Γ hL _; simp only [Lowered] at hL
  | arrLit inits iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    simp only [instantiate, instantiateArgs_eq_map]
    refine .arrLit (fun _ => Fl.O) (fun _ _ => hst) (fun x hx => ?_) hF.none hoO
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hL y hy) hΓ
  | elemAt x i ihx ihi =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .elemAt (ihx d Γ hL.1 hΓ) (ihi d Γ hL.2 hΓ) hc hoO
  | setElem x i v ihx ihi ihv =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    refine .setElem (ihx d Γ hL.1 hΓ) (ihi d Γ hL.2.1 hΓ) (ihv d Γ hL.2.2 hΓ) (fun s hs => ?_) (Sub.refl _) hF.none hoO
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hst
    · exact hF.writable s hs
  | lenOf x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .lenOf (ih d Γ hL hΓ) hoO
  | spread x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .spread (ih d Γ hL hΓ) hc hoO
  | throw x ih =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .throw (ih d Γ hL hΓ) hoO
  | merge dr x y ihx ihy =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    refine .merge (Q := Fl.O) (ihx d Γ hL.1 hΓ) (ihy d Γ hL.2 hΓ) (fun s hs => by simpa using hs) hc
      (fun s hs => (hc s hs).trans hst) hF.none hoO hoO
  | makeKey k x ihk ihx =>
    intro d Γ hL hΓ
    simp only [Lowered] at hL
    simp only [instantiate]
    exact .makeKey (ihk d Γ hL.1 hΓ) hst (ihx d Γ hL.2 hΓ) hF.none hoO
  | objGraph => intro d Γ hL _; simp only [Lowered] at hL
  | makeGraph ar E K s caps k r comp ns args _ _ iha =>
    intro d Γ hL hΓ
    simp only [Lowered, loweredArgs_iff] at hL
    obtain ⟨hπ, hE, hcaps, hargs⟩ := hL
    simp only [instantiate, instantiateArgs_eq_map]
    have hi : ∀ x ∈ args.map (instantiate d ρ), Fits Fl (VJ Fl g n) Γ FrameAt.outside o ((fun _ => Fl.O) x) x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact iha y hy d Γ (hargs y hy) hΓ
    cases hcomp : P.ofC comp with
    | true =>
      obtain ⟨⟨π, hcode, htok, hop⟩, hall⟩ := hπ hcomp
      refine .makeGraphC π (fun _ => Fl.O) (fun _ _ => hst) hi hF.none hcomp hcode (fun c π' h' => ?_)
        htok (fun _ => by rwa [List.length_map]) hE hoO
      obtain ⟨hself, hoc⟩ := hall c π' h'
      have hself' : SelfFn π' ar E K s r (caps.map (instantiate d ρ)).length := by rwa [List.length_map]
      refine ⟨fun i u hu => ?_, hself'.capFn⟩
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      exact codePart_instantiate hρ (hcaps x (List.mem_of_getElem? hx)) hΓ
        (hoc i (List.getElem?_eq_some_iff.mp hx).1)
    | false =>
      refine .makeGraphOut (fun _ => Fl.O) (fun _ _ => hst) hi hF.none hcomp hE Fl.O (Sub.refl _) hF.noLocal
        (fun u hu => ?_) hoO hF.none
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
      exact codePart_instantiate hρ (hcaps y hy) hΓ (Sub.refl _)
  | goto => intro d Γ hL _; simp only [Lowered] at hL
  | frame => intro d Γ hL _; simp only [Lowered] at hL

end Verification.TolerantFrames.ReadOnly
