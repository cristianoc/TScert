import Verification.Paper.TolerantFrames.ReadOnlyFitsSubst

/-! # Read-only handles: every step keeps a term fitting

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites of a term"). Every step of the calculus from a closed term fitting a
set, on a heap meeting the flow, leads to a term fitting the same set and
a heap meeting the flow, at the ghost that gives the step's fresh
locations the innermost frame's site (`fits_step`, by induction on the
step):

- **Congruences** carry the fit of the stepped position; the others are
  kept by allocation (`Fits.alloc`).
- **Reads** give values meeting the contents of a site the read may reach
  (`HeapInv.read`, `spread_vj`, `merge_vals`); **writes and allocations**
  store what the storage may hold (`HeapInv.set_same`, `HeapInv.fresh`).
- **A call** of a callee that may be outside code enters its run with an
  environment of the receiver, the actuals and the closure, all of `O`,
  and the captures (`fits_graphEntry`); a call of a closure of `C`'s code
  of a known signature, with the receiver and the actuals at its entry's
  slots (`fits_graphEntryC`); a bound function forwards its parts
  (`VJ.boundPart`).
- **A `let`** substitutes its value (`fits_subst`); **a run entering a
  node** instantiates it, by the proposal's conditions for `C`'s code
  (`CodeOk`) and as lowered code for outside code (`fits_lowered`); a
  frame's continuation and handler map its environment (`ContOk`,
  `HandlerOk`); a raised value meets `O` (`raises_fits`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} {Fl : Flow P} {g : Ghost P}

theorem insertSites_zero (Sx : Sites P) (Γ : Nat → Option (Sites P)) : insertSites 0 Sx Γ = consSites Sx Γ := by
  funext i; cases i <;> simp [insertSites, consSites]

/-! ### The values a closure holds -/

theorem map_self_mem {f : Tm → Tm} : ∀ {l : List Tm}, l.map f = l → ∀ u ∈ l, f u = u
  | [], _, _, hu => by cases hu
  | x :: xs, h, u, hu => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact map_self_mem h.2 u hu

/-- A value's own first locations are those of a value it holds as itself
(proved). -/
theorem leaves_self_vals {u : Val} (hu : isVal u = true) {l : Nat} (hl : Leaves P.ofC u l) :
    ∃ x ∈ vals P.ofC true u, Leaves P.ofC x l := by
  cases u with
  | objAt fs cc i => exact ⟨_, by rw [vals_objAt]; exact List.mem_cons_self .., hl⟩
  | arr ls => exact ⟨_, by simp [vals], hl⟩
  | viewSpine f cs => exact ⟨_, by simp [vals], hl⟩
  | _ =>
    exfalso
    obtain ⟨x, hx, a, hn⟩ := hl
    cases hx with
    | refl => cases a <;> simp [next, Footprints.fieldsOf, HeapKnowledge.descriptorSpine, spineEntries] at hn
    | step hm _ => simp [codeVals] at hm
    all_goals simp [isVal] at hu

/-- **A part of a value's code holds what the value holds** (proved): an
object among the values the value's code holds. -/
theorem FnsIn.part {S : Sites P} {v u : Val} (h : FnsIn Fl S v)
    (hu : ∀ fs cc i, u = .objAt fs cc i → u ∈ codeVals P.ofC v) : FnsIn Fl S u := by
  intro y hy
  cases u with
  | objAt fs cc i => exact h y (.step (hu fs cc i rfl) hy)
  | _ =>
    intro fs ar E K s caps k rest comp oid he
    cases hy with
    | refl => cases he
    | step hm _ => simp [codeVals] at hm

/-- **A bound function's parts meet its set** (proved). -/
theorem VJ.boundPart {n : Nat} {S : Sites P} {fs : List (PropKey × Nat)} {t r : Tm} {pre : List Tm} {oid : Nat}
    (hv : VJ Fl g n S (.objAt fs (.bound t r pre) oid)) {u : Tm} (hu : u ∈ t :: r :: pre) : VJ Fl g n S u := by
  have hval := (hv.inner u (.bound hu (.refl u))).1
  have hcl : Verification.Closed u := by
    intro k a
    have := hv.closed k a
    simp only [subst, substArgs_eq_map, Tm.objAt.injEq, CallCode.bound.injEq] at this
    rcases List.mem_cons.mp hu with rfl | hu
    · exact this.2.1.1
    rcases List.mem_cons.mp hu with rfl | hu
    · exact this.2.1.2.1
    · exact map_self_mem this.2.1.2.2 u hu
  have hl : ∀ l, Leaves P.ofC u l → Leaves P.ofC (.objAt fs (.bound t r pre) oid) l := by
    intro l hl
    obtain ⟨x, hx, hxl⟩ := leaves_self_vals hval hl
    refine Leaves.code ?_ hxl
    simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap]
    rcases List.mem_cons.mp hu with rfl | hu
    · exact .inl (.inl hx)
    rcases List.mem_cons.mp hu with rfl | hu
    · exact .inl (.inr hx)
    · exact .inr ⟨u, hu, hx⟩
  have hF : FnsIn Fl S u := hv.fns.part fun fs cc i he => by
    subst he
    simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap]
    rcases List.mem_cons.mp hu with he | hu
    · rw [← he, vals_objAt]; exact .inl (.inl (List.mem_cons_self ..))
    rcases List.mem_cons.mp hu with he | hu
    · rw [← he, vals_objAt]; exact .inl (.inr (List.mem_cons_self ..))
    · exact .inr ⟨_, hu, by rw [vals_objAt]; exact List.mem_cons_self ..⟩
  exact ⟨hval, hcl, fun l h => hv.below l (hl l h), fun l h => hv.sites l (hl l h), hF,
    fun w hw => hv.inner w (.bound hu hw)⟩

/-- **A capture of a closure is a closed value within it** (proved). -/
theorem VJ.capInner {n : Nat} {S : Sites P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} (hv : VJ Fl g n S (.objAt fs (.graph ar E K s caps kd rest comp) oid))
    {u : Tm} (hu : u ∈ caps) :
    isVal u = true ∧ Verification.Closed u ∧
      ∀ w, Within P u w → isVal w = true ∧ CapsOk Fl g n w ∧ OutLowered Fl w ∧ CodeNL g n w := by
  refine ⟨(hv.inner u (.cap hu (.refl u))).1, fun k a => ?_, fun w hw => hv.inner w (.cap hu hw)⟩
  have := hv.closed k a
  simp only [subst, substArgs_eq_map, Tm.objAt.injEq, CallCode.graph.injEq] at this
  exact map_self_mem this.2.1.2.2.2.2.1 u hu

/-- **A capture of a closure of outside code meets the closure's set**
(proved): the closure's code holds it. -/
theorem VJ.capOut {n : Nat} {S : Sites P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} (hc : P.ofC comp = false)
    (hv : VJ Fl g n S (.objAt fs (.graph ar E K s caps kd rest comp) oid)) {u : Tm} (hu : u ∈ caps) :
    VJ Fl g n S u := by
  obtain ⟨hval, hcl, hin⟩ := hv.capInner hu
  have hl : ∀ l, Leaves P.ofC u l → Leaves P.ofC (.objAt fs (.graph ar E K s caps kd rest comp) oid) l := by
    intro l hl
    obtain ⟨x, hx, hxl⟩ := leaves_self_vals hval hl
    refine Leaves.code ?_ hxl
    simp only [codeVals, hc, Bool.false_eq_true, ite_false, List.mem_append, valsArgs_eq, List.mem_flatMap]
    exact .inr ⟨u, hu, hx⟩
  have hF : FnsIn Fl S u := hv.fns.part fun fs cc i he => by
    subst he
    simp only [codeVals, hc, Bool.false_eq_true, ite_false, List.mem_append, valsArgs_eq, List.mem_flatMap]
    exact .inr ⟨_, hu, by rw [vals_objAt]; exact List.mem_cons_self ..⟩
  exact ⟨hval, hcl, fun l h => hv.below l (hl l h), fun l h => hv.sites l (hl l h), hF, hin⟩

/-- **A capture of a closure of `C`'s code meets its slot at every context
of the closure's code** (proved). -/
theorem VJ.capC {n : Nat} {S : Sites P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} (hc : P.ofC comp = true)
    (hv : VJ Fl g n S (.objAt fs (.graph ar E K s caps kd rest comp) oid)) {c : Nat} {π : CodeFlow P}
    (hcode : Fl.code (E, K) c = some π) :
    (∀ i u, caps[i]? = some u → VJ Fl g n (π.env s (capSlot ar rest i)) u) ∧ CapFn π ar E K s caps rest := by
  obtain ⟨-, hbelow, hall⟩ := (hv.inner _ (.refl _)).2.1 fs ar E K s caps kd rest comp oid rfl hc
  obtain ⟨hcaps, hfn⟩ := hall c π hcode
  refine ⟨fun i u hu => ?_, hfn⟩
  obtain ⟨hval, hcl, hin⟩ := hv.capInner (List.mem_of_getElem? hu)
  exact ⟨hval, hcl, hbelow i u hu, (hcaps i u hu).1, (hcaps i u hu).2, hin⟩

/-- **The entry context of a closure of `C`'s code** (proved): its code has
one, open at its entry where its token lies in `O`. -/
theorem VJ.entryC {n : Nat} {S : Sites P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} (hc : P.ofC comp = true)
    (hv : VJ Fl g n S (.objAt fs (.graph ar E K s caps kd rest comp) oid)) :
    ∃ π, Fl.code (E, K) entryCx = some π ∧ (π.tok ∈ Fl.O → OpenAt Fl π ar s rest caps.length) :=
  ((hv.inner _ (.refl _)).2.1 fs ar E K s caps kd rest comp oid rfl hc).1

/-- The entries of a run's environment at its entry (proved). -/
theorem envOf_entry {pre caps : List Tm} {self : Tm} (i : Nat) :
    let e := envOf (pre ++ (caps ++ [self])) .nul i
    e ∈ pre ∨ (∃ j, i = pre.length + j ∧ caps[j]? = some e) ∨ e = self ∨ e = .nul := by
  simp only [envOf, List.getD_eq_getElem?_getD]
  by_cases h₁ : i < pre.length
  · left; rw [List.getElem?_append_left h₁]; simp [List.getElem?_eq_getElem h₁]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h₂ : i - pre.length < caps.length
    · right; left
      refine ⟨i - pre.length, by omega, ?_⟩
      rw [List.getElem?_append_left h₂]; simp [List.getElem?_eq_getElem h₂]
    · rw [List.getElem?_append_right (by omega)]
      right; right
      cases h : i - pre.length - caps.length with
      | zero => simp
      | succ m => simp

/-- The entries of a run's environment at its entry, by slot (proved). -/
theorem envOf_entry_at {pre caps : List Tm} {self : Tm} (i : Nat) :
    let e := envOf (pre ++ (caps ++ [self])) .nul i
    (i < pre.length ∧ pre[i]? = some e) ∨ (∃ j, i = pre.length + j ∧ caps[j]? = some e) ∨
      (i = pre.length + caps.length ∧ e = self) ∨ e = .nul := by
  simp only [envOf, List.getD_eq_getElem?_getD]
  by_cases h₁ : i < pre.length
  · left; rw [List.getElem?_append_left h₁]; simp [h₁]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h₂ : i - pre.length < caps.length
    · right; left
      refine ⟨i - pre.length, by omega, ?_⟩
      rw [List.getElem?_append_left h₂]; simp [List.getElem?_eq_getElem h₂]
    · rw [List.getElem?_append_right (by omega)]
      right; right
      cases h : i - pre.length - caps.length with
      | zero => left; simp; omega
      | succ m => right; simp

theorem parameters_length : ∀ (n : Nat) (args : List Tm), (CallArguments.parameters n args).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp [CallArguments.parameters, parameters_length n []]
  | n + 1, _ :: args => by simp [CallArguments.parameters, parameters_length n args]

theorem parameters_mem' {P' : Tm → Prop} (hu : P' .undef) : ∀ {n : Nat} {args : List Tm},
    (∀ a ∈ args, P' a) → ∀ x ∈ CallArguments.parameters n args, P' x
  | 0, _, _, x, hx => by simp [CallArguments.parameters] at hx
  | n + 1, [], h, x, hx => by
    simp only [CallArguments.parameters, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact parameters_mem' hu h x hx
  | n + 1, a :: args, h, x, hx => by
    simp only [CallArguments.parameters, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h _ (List.mem_cons_self ..)
    · exact parameters_mem' hu (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

/-- **A run entered by a call meets its entry's signatures** (proved): only
a capture or the closure itself names one (`CapFn`). -/
theorem envFn_entry {π : CodeFlow P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} {pre : List Tm} (hc : P.ofC comp = true) (hfn : CapFn π ar E K s caps rest)
    (hl : pre.length = (if rest then 1 else 0) + 1 + ar) :
    EnvFn π s (pre ++ (caps ++ [.objAt fs (.graph ar E K s caps kd rest comp) oid])) .nul := by
  intro i σ hi
  obtain ⟨j, rfl, hcase⟩ := hfn i σ hi
  have he : envOf (pre ++ (caps ++ [Tm.objAt fs (.graph ar E K s caps kd rest comp) oid])) .nul (capSlot ar rest j) =
      (caps ++ [Tm.objAt fs (.graph ar E K s caps kd rest comp) oid]).getD j .nul := by
    simp only [envOf, capSlot, ← hl, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rw [he, List.getD_eq_getElem?_getD]
  rcases hcase with ⟨u, hu, hfu⟩ | ⟨rfl, rfl⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1, hu]; exact hfu
  · rw [List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    exact ⟨fs, caps, kd, comp, oid, rfl, rfl, hc⟩

/-- **The environment at a run's entry, slot by slot** (proved): the
slots before the captures as given, then the captures, the closure and
the default. -/
theorem envIn_entry {Γ' : Nat → Option (Sites P)} {τ : Nat → Sites P} {ar : Nat} {rest : Bool}
    {caps : List Tm} {self : Tm} {pre : List Tm} (hl : pre.length = (if rest then 1 else 0) + 1 + ar)
    (hpre : ∀ i x, pre[i]? = some x → VOr (VJ Fl g n) Γ' (τ i) x)
    (hcaps : ∀ i u, caps[i]? = some u → VJ Fl g n (τ (capSlot ar rest i)) u)
    (hself : VJ Fl g n (τ (capSlot ar rest caps.length)) self) :
    ∀ i, VOr (VJ Fl g n) Γ' (τ i) (envOf (pre ++ (caps ++ [self])) .nul i) := by
  intro i
  simp only [envOf, List.getD_eq_getElem?_getD]
  by_cases h₁ : i < pre.length
  · rw [List.getElem?_append_left h₁, List.getElem?_eq_getElem h₁]
    exact hpre i _ (List.getElem?_eq_getElem h₁)
  · obtain ⟨j, rfl⟩ : ∃ j, i = pre.length + j := ⟨i - pre.length, by omega⟩
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have hslot : pre.length + j = capSlot ar rest j := by simp [capSlot, hl]
    by_cases h₂ : j < caps.length
    · rw [List.getElem?_append_left h₂, List.getElem?_eq_getElem h₂]
      rw [hslot]; exact .inl (hcaps j _ (List.getElem?_eq_getElem h₂))
    · rw [List.getElem?_append_right (by omega)]
      by_cases h₃ : j = caps.length
      · subst h₃; rw [hslot]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        exact .inl hself
      · rw [List.getElem?_eq_none (by simp; omega)]
        exact .inl (VJ.prim rfl)

theorem parameters_get : ∀ {n : Nat} {args : List Tm} {i : Nat} {x : Tm},
    (CallArguments.parameters n args)[i]? = some x → i < n ∧ (args[i]? = some x ∨ x = .undef)
  | 0, _, _, _, h => by simp [CallArguments.parameters] at h
  | n + 1, [], 0, x, h => by simp [CallArguments.parameters] at h; exact ⟨by omega, .inr h.symm⟩
  | n + 1, [], i + 1, x, h => by
    simp only [CallArguments.parameters, List.getElem?_cons_succ] at h
    obtain ⟨hi, hx⟩ := parameters_get h
    exact ⟨by omega, .inr (hx.elim (fun h => by simp at h) id)⟩
  | n + 1, a :: args, 0, x, h => by simp [CallArguments.parameters] at h; exact ⟨by omega, .inl (by simp [h])⟩
  | n + 1, a :: args, i + 1, x, h => by
    simp only [CallArguments.parameters, List.getElem?_cons_succ] at h
    obtain ⟨hi, hx⟩ := parameters_get h
    exact ⟨by omega, by simpa using hx⟩

/-- **A run of `C`'s code entered by a call of a known signature fits**
(proved): the receiver and the actuals meet its entry's slots, the
captures and the closure meet theirs (`CapsOk`), and a rest spine is
allocated at the caller's array site, of the spine's slot. -/
theorem fits_graphEntryC {n : Nat} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {S : Sites P}
    {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm} {K : List (Continuation × Option Target)} {s : Nat}
    {caps : List Tm} {kd : Invoke} {rest : Bool} {comp : ComponentTag} {oid : Nat} {recv : Tm} {args : List Tm}
    {c : Nat} {π : CodeFlow P} (hc : P.ofC comp = true) (hcode : Fl.code (E, K) c = some π)
    (hf : VJ Fl g n (π.env s (capSlot ar rest caps.length)) (.objAt fs (.graph ar E K s caps kd rest comp) oid))
    (hr : VJ Fl g n (π.env s (recvSlot rest)) recv) (Sa : Nat → Sites P) (Sr : Sites P)
    (hargs : ∀ i x, args[i]? = some x → VJ Fl g n (Sa i) x)
    (hpar : ∀ i, i < ar → Sub (Sa i) (π.env s (paramSlot rest i)))
    (hrest : rest = true → a.arr ∈ π.env s 0 ∧ Stores Fl a.arr Sr ∧ ∀ i, ar ≤ i → Sub (Sa i) Sr)
    (hS : Sub π.ret S) (hof : o = false) :
    Fits Fl (VJ Fl g n) Γ a o S
      (CallArguments.graphEntry ar E K s caps (.objAt fs (.graph ar E K s caps kd rest comp) oid) rest comp recv args) := by
  obtain ⟨hcaps, hfn⟩ := hf.capC hc hcode
  have hparam : ∀ (Γ' : Nat → Option (Sites P)) i x, (CallArguments.parameters ar args)[i]? = some x →
      VOr (VJ Fl g n) Γ' (π.env s (paramSlot rest i)) x := by
    intro Γ' i x hx
    obtain ⟨hi, hx⟩ := parameters_get hx
    rcases hx with hx | rfl
    · exact .inl ((hargs i x hx).sub (hpar i hi))
    · exact .inl (VJ.prim rfl)
  cases rest with
  | false =>
    have hl : (recv :: CallArguments.parameters ar args).length = (if false then 1 else 0) + 1 + ar := by
      simp [parameters_length]; omega
    refine .gotoC c π hc hcode (envIn_entry hl (fun i x hx => ?_) hcaps hf) (envFn_entry hc hfn hl) hS
      (by simp [hof])
    cases i with
    | zero => simp at hx; subst hx; exact .inl hr
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx
      have := hparam Γ i x hx
      simpa [paramSlot, recvSlot, Nat.add_comm] using this
  | true =>
    obtain ⟨ha, hst, hge⟩ := hrest rfl
    have hl : (.var 0 :: recv :: CallArguments.parameters ar args).length = (if true then 1 else 0) + 1 + ar := by
      simp [parameters_length]; omega
    refine .letE (Sx := π.env s 0) (.arrLit (fun _ => Sr) (fun _ _ => hst) (fun x hx => ?_) ha (by simp [hof]))
      ?_ (by simp [hof])
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      rw [List.getElem?_drop] at hi
      have := hargs _ x hi
      exact .val this.val (this.sub (hge _ (Nat.le_add_right _ _))) (by simp [hof])
    refine .gotoC c π hc hcode (envIn_entry hl (fun i x hx => ?_) hcaps hf) (envFn_entry hc hfn hl) hS (by simp [hof])
    cases i with
    | zero => simp at hx; subst hx; exact .inr ⟨0, _, rfl, rfl, Sub.refl _⟩
    | succ i =>
      cases i with
      | zero => simp at hx; subst hx; exact .inl hr
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have := hparam (consSites (π.env s 0) Γ) i x hx
        simpa [paramSlot, recvSlot, Nat.add_comm, Nat.add_left_comm] using this

/-- **A run entered by a call fits** (proved): its environment holds the
receiver, the actuals and the closure, all of `O`, and the captures, of
the closure's code's entry slots (`C`'s code) or of `O` (outside code);
a rest spine is allocated at the caller's array site, of `O`. -/
theorem fits_graphEntry {n : Nat} (hF : Fl.Facts) {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {S : Sites P}
    {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm} {K : List (Continuation × Option Target)} {s : Nat}
    {caps : List Tm} {kd : Invoke} {rest : Bool} {comp : ComponentTag} {oid : Nat} {recv : Tm} {args : List Tm}
    (hf : VJ Fl g n Fl.O (.objAt fs (.graph ar E K s caps kd rest comp) oid)) (hr : VJ Fl g n Fl.O recv)
    (hargs : ∀ x ∈ args, VJ Fl g n Fl.O x) (ha : a.arr ∈ Fl.O) (hS : Sub Fl.O S) (ho : o = true → Sub S Fl.O)
    (hao : P.ofC comp = false → a.out = true) :
    Fits Fl (VJ Fl g n) Γ a o S
      (CallArguments.graphEntry ar E K s caps (.objAt fs (.graph ar E K s caps kd rest comp) oid) rest comp recv args) := by
  -- every entry before the captures, the closure and the default meet `O`
  have hpre : ∀ x ∈ recv :: CallArguments.parameters ar args, VJ Fl g n Fl.O x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hr
    · exact parameters_mem' (VJ.prim rfl) hargs x hx
  have hlen : (recv :: CallArguments.parameters ar args).length = 1 + ar := by
    simp [parameters_length]; omega
  cases hc : P.ofC comp
  · -- outside code
    have hlow := (hf.inner _ (.refl _)).2.2.1 fs ar E K s caps kd rest comp oid rfl hc
    have hO : ∀ (Γ' : Nat → Option (Sites P)) (pre : List Tm), (∀ x ∈ pre, VOr (VJ Fl g n) Γ' Fl.O x) → ∀ i,
        VOr (VJ Fl g n) Γ' Fl.O (envOf (pre ++ (caps ++ [.objAt fs (.graph ar E K s caps kd rest comp) oid])) .nul i) := by
      intro Γ' pre hp i
      rcases envOf_entry (pre := pre) (caps := caps) (self := .objAt fs (.graph ar E K s caps kd rest comp) oid) i with
        h | ⟨j, -, hj⟩ | h | h
      · exact hp _ h
      · exact .inl (hf.capOut hc (List.mem_of_getElem? hj))
      · rw [h]; exact .inl hf
      · rw [h]; exact .inl (VJ.prim rfl)
    cases rest with
    | false => exact .gotoOut hc hlow (hO _ _ fun x hx => .inl (hpre x hx)) hS ho (hao hc)
    | true =>
      refine .letE (Sx := Fl.O) (.arrLit (fun _ => Fl.O) (fun _ _ => hF.writable _ ha)
        (fun x hx => .val (hargs x (List.mem_of_mem_drop hx)).val (hargs x (List.mem_of_mem_drop hx))
          (fun _ => Sub.refl _)) ha (fun _ => Sub.refl _)) ?_ ho
      refine .gotoOut hc hlow (hO _ _ fun x hx => ?_) hS ho (hao hc)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr ⟨0, Fl.O, rfl, rfl, Sub.refl _⟩
      · exact .inl (hpre x hx)
  · -- `C`'s code
    obtain ⟨π, hπ, hop⟩ := hf.entryC hc
    obtain ⟨hcaps, hfn⟩ := hf.capC hc hπ
    have hop : OpenAt Fl π ar s rest caps.length := by
      obtain ⟨π', hπ', ht⟩ := (hf.fns _ (.refl _) fs ar E K s caps kd rest comp oid rfl).1 hc
      rw [hπ] at hπ'; cases hπ'
      exact hop ht
    have hR : Sub π.ret S := hop.2.2.1.trans hS
    have hC : ∀ (Γ' : Nat → Option (Sites P)) (pre : List Tm), pre.length = (if rest then 1 else 0) + 1 + ar →
        (∀ x ∈ pre, VOr (VJ Fl g n) Γ' Fl.O x) → ∀ i,
        VOr (VJ Fl g n) Γ' (π.env s i)
          (envOf (pre ++ (caps ++ [.objAt fs (.graph ar E K s caps kd rest comp) oid])) .nul i) := by
      intro Γ' pre hl hp i
      rcases envOf_entry_at (pre := pre) (caps := caps) (self := .objAt fs (.graph ar E K s caps kd rest comp) oid) i with
        ⟨hi, h⟩ | ⟨j, hi, hj⟩ | ⟨hi, h⟩ | h
      · have hsub : Sub Fl.O (π.env s i) := hop.1 i (by simp only [capSlot]; omega)
        rcases hp _ (List.mem_of_getElem? h) with h' | ⟨j, S', he, hg, hs⟩
        · exact .inl (h'.sub hsub)
        · exact .inr ⟨j, S', he, hg, hs.trans hsub⟩
      · have := hcaps j _ hj
        subst hi
        rw [hl] at this ⊢
        exact .inl (by simpa only [capSlot] using this)
      · rw [h]
        have hsub : Sub Fl.O (π.env s i) := by
          rw [hi, hl]; simpa only [capSlot, Nat.add_assoc] using hop.2.1
        exact .inl (hf.sub hsub)
      · rw [h]; exact .inl (VJ.prim rfl)
    cases rest with
    | false =>
      exact .gotoC entryCx π hc hπ (hC _ _ (by simp [parameters_length]; omega) fun x hx => .inl (hpre x hx))
        (envFn_entry hc hfn (by simp [parameters_length]; omega)) hR ho
    | true =>
      refine .letE (Sx := Fl.O) (.arrLit (fun _ => Fl.O) (fun _ _ => hF.writable _ ha)
        (fun x hx => .val (hargs x (List.mem_of_mem_drop hx)).val (hargs x (List.mem_of_mem_drop hx))
          (fun _ => Sub.refl _)) ha (fun _ => Sub.refl _)) ?_ ho
      refine .gotoC entryCx π hc hπ (hC _ _ (by simp [parameters_length]; omega) fun x hx => ?_)
        (envFn_entry hc hfn (by simp [parameters_length]; omega)) hR ho
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr ⟨0, Fl.O, rfl, rfl, Sub.refl _⟩
      · exact .inl (hpre x hx)

/-! ### Spreads -/

theorem readElems_mem {h : Heap} : ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs →
    ∀ v ∈ vs, v = .undef ∨ ∃ l, some l ∈ ls ∧ h[l]? = some v
  | [], vs, hr, v, hv => by simp [readElems] at hr; subst hr; cases hv
  | none :: ls, vs, hr, v, hv => by
    simp only [readElems, Option.map_eq_some_iff] at hr
    obtain ⟨ws, hws, rfl⟩ := hr
    rcases List.mem_cons.mp hv with rfl | hv
    · exact .inl rfl
    · rcases readElems_mem hws v hv with h' | ⟨l, hl, hl'⟩
      · exact .inl h'
      · exact .inr ⟨l, List.mem_cons_of_mem _ hl, hl'⟩
  | some m :: ls, vs, hr, v, hv => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨w, hw, ws, hws, rfl⟩ := hr
    rcases List.mem_cons.mp hv with rfl | hv
    · exact .inr ⟨m, List.mem_cons_self .., hw⟩
    · rcases readElems_mem hws v hv with h' | ⟨l, hl, hl'⟩
      · exact .inl h'
      · exact .inr ⟨l, List.mem_cons_of_mem _ hl, hl'⟩

/-- **A spread's elements meet the contents of its cells' sites** (proved). -/
theorem spread_vj {h : Heap} {Sx S : Sites P} {ls : List (Option Nat)} {vs : List Tm} (hH : HeapInv Fl g h)
    (hx : VJ Fl g h.length Sx (.arr ls)) (hc : ∀ s ∈ Sx, Sub (Fl.H.contents s) S)
    (hr : readElems h ls = some vs) : ∀ v ∈ vs, VJ Fl g h.length S v := by
  intro v hv
  rcases readElems_mem hr v hv with rfl | ⟨l, hl, hl'⟩
  · exact VJ.prim rfl
  · have hs := hx.sites l (cells_leaves rfl hl)
    exact (hH l v hl').sub (hc _ hs)

/-! ### A merge's reads -/

theorem lookup_of_mem_nodup {α : Type} : ∀ {l : List (PropKey × α)} {e : PropKey × α},
    (l.map Prod.fst).Nodup → e ∈ l → l.lookup e.1 = some e.2
  | [], _, _, he => by cases he
  | (k, x) :: l, e, hn, he => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp he with rfl | he
    · simp [List.lookup]
    · have hne : e.1 ≠ k := fun h => hn.1 (h ▸ List.mem_map.mpr ⟨e, he, rfl⟩)
      have : (e.1 == k) = false := by simpa using hne
      simp only [List.lookup, this]
      exact lookup_of_mem_nodup hn.2 he

theorem lookup_map_snd {α β : Type} (f : α → β) : ∀ (l : List (PropKey × α)) (k : PropKey),
    (l.map fun p => (p.1, f p.2)).lookup k = (l.lookup k).map f
  | [], _ => rfl
  | (j, x) :: l, k => by
    by_cases h : k = j
    · subst h; simp [List.lookup]
    · have : (k == j) = false := by simpa using h
      simp only [List.map_cons, List.lookup, this]
      exact lookup_map_snd f l k

theorem lookup_filter_key {α : Type} (q : PropKey → Bool) : ∀ (l : List (PropKey × α)) (k : PropKey),
    (l.filter fun p => q p.1).lookup k = if q k then l.lookup k else none
  | [], _ => by simp
  | (j, y) :: l, k => by
    have ih := lookup_filter_key q l k
    by_cases hk : k = j
    · subst hk
      by_cases hq : q k = true
      · simp [hq, List.lookup]
      · simp only [List.filter_cons, hq, Bool.false_eq_true, ite_false]; simpa [hq] using ih
    · have : (k == j) = false := by simpa using hk
      by_cases hq : q j = true
      · simp only [List.filter_cons, hq, ite_true, List.lookup, this]; exact ih
      · simp only [List.filter_cons, hq, Bool.false_eq_true, ite_false, List.lookup, this]; exact ih

theorem lookup_filter_some {α : Type} {q : PropKey → Bool} {l : List (PropKey × α)} {k : PropKey} {x : α}
    (h : (l.filter fun p => q p.1).lookup k = some x) : l.lookup k = some x := by
  rw [lookup_filter_key] at h
  split at h
  · exact h
  · cases h

/-- **A copied value is a primitive or meets the contents of a site of
`Q`** (proved), at a location one step from a value meeting a subset of
`Q`. -/
theorem heapVal_vj {h : Heap} {Su Q : Sites P} {u : Val} {l : Nat} (hH : HeapInv Fl g h)
    (hu : VJ Fl g h.length Su u) (hq : Sub Su Q) (hl : Leaves P.ofC u l) :
    primVal (heapVal h l) = true ∨ ∃ s ∈ Q, VJ Fl g h.length (Fl.H.contents s) (heapVal h l) := by
  unfold heapVal
  split
  · rename_i v hv
    split
    · exact .inr ⟨_, hq _ (hu.sites l hl), hH l v hv⟩
    · exact .inl rfl
  · exact .inl rfl

/-- **The copied fields of an object are at its own fields' locations**
(proved): the first entry of each key, which `lookup` finds. -/
theorem copied_field {h : Heap} {q : PropKey → Bool} {fs : List (PropKey × Nat)} {e : PropKey × Tm}
    (he : ((fs.filter fun p => q p.1).map fun p => (p.1, heapVal h p.2)).lookup e.1 = some e.2) :
    ∃ l, fs.lookup e.1 = some l ∧ e.2 = heapVal h l := by
  rw [lookup_map_snd (heapVal h)] at he
  obtain ⟨l, hl, he⟩ := Option.map_eq_some_iff.mp he
  exact ⟨l, lookup_filter_some hl, he.symm⟩

theorem firstKeys_lookup' {α : Type} {ps : List (PropKey × α)} {e : PropKey × α} (he : e ∈ firstKeys ps) :
    ps.lookup e.1 = some e.2 := by
  rw [← lookup_firstKeys]; exact lookup_of_mem_nodup (firstKeys_nodup ps) he

/-- **A merge's values are primitives or meet the contents of a site of a
closed set holding both operands' sites** (proved). -/
theorem merge_vals {h : Heap} {d : List PropKey} {x y : Tm} {ps : List (PropKey × Tm)} {Sx Sy Q : Sites P}
    (hH : HeapInv Fl g h) (hx : VJ Fl g h.length Sx x) (hy : VJ Fl g h.length Sy y) (hq : Sub (Sx ++ Sy) Q)
    (hcl : ∀ s ∈ Q, Sub (Fl.H.contents s) Q) (hm : mergeParts h d x y = some ps) :
    ∀ p ∈ ps, primVal p.2 = true ∨ ∃ s ∈ Q, VJ Fl g h.length (Fl.H.contents s) p.2 := by
  simp only [mergeParts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
  obtain ⟨pa, hpa, qb, hqb, rfl⟩ := hm
  have hqx : Sub Sx Q := fun s hs => hq s (List.mem_append_left _ hs)
  have hqy : Sub Sy Q := fun s hs => hq s (List.mem_append_right _ hs)
  intro p hp
  rcases mem_mergeData hp with hp | hp
  · -- the accumulator's own fields
    unfold ownAll at hpa
    split at hpa
    · split at hpa
      · cases hpa
      · simp only [Option.some.injEq] at hpa; subst hpa
        obtain ⟨l, hl, he⟩ := copied_field (q := fun j => j != arraySpineKey) (firstKeys_lookup' hp)
        rw [he]
        exact heapVal_vj hH hx hqx (Leaves.of_next (a := .key _) (by simpa [next, Footprints.fieldsOf] using hl))
    · cases hpa
  · -- the source's copied properties
    have hp := (List.mem_filter.mp hp).1
    unfold ownData at hqb
    split at hqb
    · split at hqb
      · cases hqb
      · simp only [Option.some.injEq] at hqb; subst hqb
        rcases lookup_append_some (firstKeys_lookup' hp) with hA | hB
        · obtain ⟨l, hl, he⟩ := copied_field (q := copiedKey) hA
          rw [he]
          exact heapVal_vj hH hy hqy (Leaves.of_next (a := .key _) (by simpa [next, Footprints.fieldsOf] using hl))
        · unfold spineData at hB
          split at hB
          · rename_i l₁ hl₁
            split at hB
            · rename_i ls hls
              simp only [List.mem_filterMap, Option.map_eq_some_iff] at hB
              obtain ⟨⟨o, i⟩, hoi, m, hm, he⟩ := hB
              subst hm
              have hs₁ := hqy _ (hy.sites l₁ (Leaves.of_next (a := .key _) (by simpa [next, Footprints.fieldsOf] using hl₁)))
              have harr := hH l₁ _ hls
              have hcell : some m ∈ ls := by
                have := List.mem_zipIdx hoi
                rw [this.2.2]; exact List.getElem_mem _
              simp only [Prod.mk.injEq] at he
              rw [← he.2]
              exact heapVal_vj hH harr (hcl _ hs₁) (cells_leaves rfl hcell)
            · cases hB
          · cases hB
    all_goals first
      | (cases hqb; done)
      | (simp only [Option.some.injEq] at hqb; subst hqb; simp at hp; done)
      | (simp only [Option.some.injEq] at hqb; subst hqb
         have hp' := mem_firstKeys hp
         simp only [stringData, List.mem_map] at hp'
         obtain ⟨_, _, rfl⟩ := hp'
         exact .inl rfl)

open Classical in
/-- **A merge's allocation fits** (proved): each copied value is a
primitive or meets the contents of a site whose contents the object's
storage may hold. -/
theorem fits_mergeAlloc {n : Nat} {Γ : Nat → Option (Sites P)} {a : FrameAt P} {o : Bool} {S Q : Sites P}
    {ns : List PropKey} {inits : List Tm} (hst : ∀ s ∈ Q, Stores Fl a.obj (Fl.H.contents s)) (hs : a.obj ∈ S)
    (hcl : ∀ s ∈ Q, Sub (Fl.H.contents s) Q) (hQ : o = true → Sub Q Fl.O) (ho : o = true → Sub S Fl.O)
    (hv : ∀ v ∈ inits, primVal v = true ∨ ∃ s ∈ Q, VJ Fl g n (Fl.H.contents s) v) :
    Fits Fl (VJ Fl g n) Γ a o S (.makeAt .absent ns inits) := by
  refine .makeAbsent (fun v => if hv : ∃ s ∈ Q, VJ Fl g n (Fl.H.contents s) v then Fl.H.contents hv.choose else [])
    (fun v _ => ?_) (fun v hv' => ?_) hs ho
  · split
    · rename_i he; exact hst _ he.choose_spec.1
    · exact fun _ h => nomatch h
  · split
    · rename_i he
      exact .val he.choose_spec.2.val he.choose_spec.2
        (fun h => (hcl _ he.choose_spec.1).trans (hQ h))
    · rename_i he
      rcases hv v hv' with hpr | hex
      · exact .val (VJ.prim (Fl := Fl) (g := g) (n := n) (S := []) hpr).val (VJ.prim hpr) (fun _ _ h => nomatch h)
      · exact absurd hex he

/-- **Every step keeps a term fitting and the heap meeting the flow**
(proved, by induction on the step): the fresh locations at the site of
the innermost frame (`stepSite`). A step reduces no term under a binder,
so the terms are closed (`fun _ => none`). -/
theorem fits_step (hF : Fl.Facts) {h t h' t'} (hs : Step h t h' t') :
    ∀ {cur : Option FrameKey} {ou o : Bool} {S : Sites P},
      Fits Fl (VJ Fl g h.length) (fun _ => none) ⟨allocOf Fl cur, ou⟩ o S t → HeapInv Fl g h →
      Fits Fl (VJ Fl (g.alloc h.length (fun _ => stepSite Fl cur t)) h'.length) (fun _ => none) ⟨allocOf Fl cur, ou⟩ o S t' ∧
        HeapInv Fl (g.alloc h.length (fun _ => stepSite Fl cur t)) h' := by
  induction hs with
  | callL hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke hf hr hargs hS ha _ hSf hout =>
      have hn := notVal_of_step hst
      have hl := Footprints.step_length_le hst
      obtain ⟨hf', hH'⟩ := ih hf hH
      simp only [stepSite, activeFrame, hn, ite_true] at hf' hH' ⊢
      exact ⟨.invoke hf' (hr.alloc hl) (fun x hx => (hargs x hx).alloc hl) hS ha ho hSf hout, hH'⟩
    | invokeC _ _ _ _ _ _ hfn => have := hfn.val; rw [notVal_of_step hst] at this; cases this
  | callRecv hfv hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke hf hr hargs hS ha _ hSf hout =>
      have hn := notVal_of_step hst
      have hl := Footprints.step_length_le hst
      obtain ⟨hr', hH'⟩ := ih hr hH
      simp only [stepSite, activeFrame, hn, hfv, ite_true, Bool.true_eq_false, ite_false] at hr' hH' ⊢
      exact ⟨.invoke (hf.alloc hl) hr' (fun x hx => (hargs x hx).alloc hl) hS ha ho hSf hout, hH'⟩
    | invokeC σ c π Sa Sr hof hfn hcode hself hr hargs hat hpar hrest hS =>
      have hn := notVal_of_step hst
      have hl := Footprints.step_length_le hst
      obtain ⟨hr', hH'⟩ := ih hr hH
      simp only [stepSite, activeFrame, hn, hfv, ite_true, Bool.true_eq_false, ite_false] at hr' hH' ⊢
      exact ⟨.invokeC σ c π Sa Sr hof hfn hcode (hself.alloc hl) hr' (fun i x hx => (hargs i x hx).alloc hl) hat hpar
        hrest hS ho, hH'⟩
  | callArg hfv hrv hai hpre hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke hf hr hargs hS ha _ hSf hout =>
      have hn := notVal_of_step hst
      have hl := Footprints.step_length_le hst
      obtain ⟨ha', hH'⟩ := ih (hargs _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, hfv, hrv, Bool.true_eq_false, ite_false, activeArgs_at hai hpre hn] at ha' hH' ⊢
      refine ⟨.invoke (hf.alloc hl) (hr.alloc hl) (fun x hx => ?_) hS ha ho hSf hout, hH'⟩
      rcases mem_set_cases hx with hx | rfl
      · exact (hargs x hx).alloc hl
      · exact ha'
    | invokeC _ _ _ _ _ _ _ _ _ _ _ hat =>
      rcases hat _ (List.mem_of_getElem? hai) with hv | ⟨j, rfl⟩
      · rw [notVal_of_step hst] at hv; cases hv
      · cases hst
  | constructL hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | construct hf hargs hS ha _ hSf hout =>
      obtain ⟨hx', hH'⟩ := ih hf hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.construct hx' (fun x hx => (hargs x hx).alloc hl) hS ha ho hSf hout, hH'⟩
  | constructArg hfv hai hpre hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | construct hf hargs hS ha _ hSf hout =>
      obtain ⟨hx', hH'⟩ := ih (hargs _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, hfv, Bool.true_eq_false, ite_false, activeArgs_at hai hpre hn] at hx' hH' ⊢
      refine ⟨.construct (hf.alloc hl) (fun x hx => ?_) hS ha ho hSf hout, hH'⟩
      rcases mem_set_cases hx with hx | rfl
      · exact (hargs x hx).alloc hl
      · exact hx'
  | letC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | letE hx hb =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.letE hx' (hb.alloc hl) ho, hH'⟩
  | spreadC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | spread hx hc =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.spread hx' hc ho, hH'⟩
  | readC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | readAt hx hq hcl hr =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.readAt hx' hq hcl hr ho, hH'⟩
  | indexC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | indexAt hx hk hq hcl hr =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.indexAt hx' (hk.alloc hl) hq hcl hr ho, hH'⟩
  | indexC2 hav hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | indexAt hx hk hq hcl hr =>
      obtain ⟨hx', hH'⟩ := ih hk hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.indexAt (hx.alloc hl) hx' hq hcl hr ho, hH'⟩
  | writeC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | writeAt hx hy hst' =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.writeAt hx' (hy.alloc hl) hst' ho, hH'⟩
  | writeC2 hav hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | writeAt hx hy hst' =>
      obtain ⟨hx', hH'⟩ := ih hy hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.writeAt (hx.alloc hl) hx' hst' ho, hH'⟩
  | testC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | test hx =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.test hx' ho, hH'⟩
  | iteC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | ite hc hx hy =>
      obtain ⟨hx', hH'⟩ := ih hc hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.ite hx' (hx.alloc hl) (hy.alloc hl) ho, hH'⟩
  | arithC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | arith hx hy =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.arith hx' (hy.alloc hl) ho, hH'⟩
  | arithC2 hav hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | arith hx hy =>
      obtain ⟨hx', hH'⟩ := ih hy hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.arith (hx.alloc hl) hx' ho, hH'⟩
  | elemC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | elemAt hx hi hc =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.elemAt hx' (hi.alloc hl) hc ho, hH'⟩
  | elemC2 hav hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | elemAt hx hi hc =>
      obtain ⟨hx', hH'⟩ := ih hi hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.elemAt (hx.alloc hl) hx' hc ho, hH'⟩
  | setC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | setElem hx hi hv hst' hS ha =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.setElem hx' (hi.alloc hl) (hv.alloc hl) hst' hS ha ho, hH'⟩
  | setC2 hav hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | setElem hx hi hv hst' hS ha =>
      obtain ⟨hx', hH'⟩ := ih hi hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.setElem (hx.alloc hl) hx' (hv.alloc hl) hst' hS ha ho, hH'⟩
  | setC3 hav hiv hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | setElem hx hi hv hst' hS ha =>
      obtain ⟨hx', hH'⟩ := ih hv hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, hiv, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.setElem (hx.alloc hl) (hi.alloc hl) hx' hst' hS ha ho, hH'⟩
  | lenC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | lenOf hx =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.lenOf hx' ho, hH'⟩
  | throwC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | throw hx =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.throw hx' ho, hH'⟩
  | mergeC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | merge hx hy hq hcl hst' hs hQ =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.merge hx' (hy.alloc hl) hq hcl hst' hs hQ ho, hH'⟩
  | mergeC2 hav hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | merge hx hy hq hcl hst' hs hQ =>
      obtain ⟨hx', hH'⟩ := ih hy hH
      simp only [stepSite, activeFrame, hn, ite_true, hav, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.merge (hx.alloc hl) hx' hq hcl hst' hs hQ ho, hH'⟩
  | makeKeyC1 hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | makeKey hk hst' hx hs =>
      obtain ⟨hx', hH'⟩ := ih hk hH
      simp only [stepSite, activeFrame, hn, ite_true] at hx' hH' ⊢
      exact ⟨.makeKey hx' hst' (hx.alloc hl) hs ho, hH'⟩
  | makeKeyC2 hkv hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | makeKey hk hst' hx hs =>
      obtain ⟨hx', hH'⟩ := ih hx hH
      simp only [stepSite, activeFrame, hn, ite_true, hkv, Bool.true_eq_false, ite_false] at hx' hH' ⊢
      exact ⟨.makeKey (hk.alloc hl) hst' hx' hs ho, hH'⟩
  | makeArg hai hpre hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | makeAbsent Ss hst' hi hs =>
      obtain ⟨hx', hH'⟩ := ih (hi _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, activeArgs_at hai hpre hn] at hx' hH' ⊢
      obtain ⟨hst'', hi''⟩ := sites_set hai hst' hi hx' fun _ _ h => h.alloc hl
      exact ⟨.makeAbsent _ hst'' hi'' hs ho, hH'⟩
    | makeView Ss hst' hi hs hv =>
      obtain ⟨hx', hH'⟩ := ih (hi _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, activeArgs_at hai hpre hn] at hx' hH' ⊢
      obtain ⟨hst'', hi''⟩ := sites_set hai hst' hi hx' fun _ _ h => h.alloc hl
      exact ⟨.makeView _ hst'' hi'' hs (hv.alloc hl) ho, hH'⟩
    | makeBound Ss hst' hi hs Sb hb hnl hp =>
      obtain ⟨hx', hH'⟩ := ih (hi _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, activeArgs_at hai hpre hn] at hx' hH' ⊢
      obtain ⟨hst'', hi''⟩ := sites_set hai hst' hi hx' fun _ _ h => h.alloc hl
      exact ⟨.makeBound _ hst'' hi'' hs Sb hb hnl (fun x hx => (hp x hx).alloc hl) ho, hH'⟩
    | makeGraphC π Ss hst' hi hs hc hcode hcaps htok hop hE =>
      obtain ⟨hx', hH'⟩ := ih (hi _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, activeArgs_at hai hpre hn] at hx' hH' ⊢
      obtain ⟨hst'', hi''⟩ := sites_set hai hst' hi hx' fun _ _ h => h.alloc hl
      exact ⟨.makeGraphC π _ hst'' hi'' hs hc hcode
        (fun c π' h' => ⟨fun i u hu => ((hcaps c π' h').1 i u hu).alloc hl, (hcaps c π' h').2⟩) htok hop hE ho, hH'⟩
    | makeGraphOut Ss hst' hi hs hc hE Sc hb hnl hcaps _ hnone =>
      obtain ⟨hx', hH'⟩ := ih (hi _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, activeArgs_at hai hpre hn] at hx' hH' ⊢
      obtain ⟨hst'', hi''⟩ := sites_set hai hst' hi hx' fun _ _ h => h.alloc hl
      exact ⟨.makeGraphOut _ hst'' hi'' hs hc hE Sc hb hnl (fun u hu => (hcaps u hu).alloc hl) ho hnone, hH'⟩
  | arrArg hai hpre hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hn := notVal_of_step hst
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | arrLit Ss hst' hi hs =>
      obtain ⟨hx', hH'⟩ := ih (hi _ (List.mem_of_getElem? hai)) hH
      simp only [stepSite, activeFrame, activeArgs_at hai hpre hn] at hx' hH' ⊢
      obtain ⟨hst'', hi''⟩ := sites_set hai hst' hi hx' fun _ _ h => h.alloc hl
      exact ⟨.arrLit _ hst'' hi'' hs ho, hH'⟩
  | frameC hst ih =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    have hl := Footprints.step_length_le hst
    cases hfit with
    | val hv => simp [isVal] at hv
    | frameC c π l hc hcode hnode henv hfn hvfn ht hS =>
      rw [show π.at l (_, _) = ⟨π.alloc (_, _), π.out l⟩ from rfl, ← allocOf_C hF.agree hc hcode] at ht
      obtain ⟨ht', hH'⟩ := ih ht hH
      rw [allocOf_C hF.agree hc hcode] at ht'
      simp only [stepSite, activeFrame] at ht' hH' ⊢
      exact ⟨.frameC c π l hc hcode hnode (fun i => (henv i).alloc hl) hfn (fun σ hσ => (hvfn σ hσ).step hst) ht' hS ho,
        hH'⟩
    | frameOut hc hE henv ht hS _ hao =>
      rw [show (FrameAt.outside : FrameAt P) = ⟨Alloc.outside, true⟩ from rfl,
        ← allocOf_out (Fl := Fl) (m := (_, _)) (kx := (_, _)) hc] at ht
      obtain ⟨ht', hH'⟩ := ih ht hH
      rw [allocOf_out hc] at ht'
      simp only [stepSite, activeFrame] at ht' hH' ⊢
      exact ⟨.frameOut hc hE (fun i => (henv i).alloc hl) ht' hS ho hao, hH'⟩
  | testV hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    exact ⟨.val (by split <;> rfl) (VJ.prim (by split <;> rfl)) ho, hH.same⟩
  | iteT =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | ite _ hx _ => exact ⟨hx.alloc (Nat.le_refl _), hH.same⟩
  | iteF =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | ite _ _ hy => exact ⟨hy.alloc (Nat.le_refl _), hH.same⟩
  | arithV hb =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    obtain ⟨-, -, hr⟩ := binop_result hb
    rcases hr with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨.val rfl (VJ.prim rfl) ho, hH.same⟩
  | readMissing _ _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    exact ⟨.val rfl (VJ.prim rfl) ho, hH.same⟩
  | indexMissing _ _ _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    exact ⟨.val rfl (VJ.prim rfl) ho, hH.same⟩
  | elemAbsent _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    exact ⟨.val rfl (VJ.prim rfl) ho, hH.same⟩
  | lenV  =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    exact ⟨.val rfl (VJ.prim rfl) ho, hH.same⟩
  | lenStr _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    exact ⟨.val rfl (VJ.prim rfl) ho, hH.same⟩
  | elemStr =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    refine ⟨.val ?_ (VJ.prim ?_) ho, hH.same⟩ <;> (unfold codeUnitAt; split <;> rfl)
  | arrAllocThrow _ _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    refine ⟨.throw (.val rfl (VJ.thrown _) (fun _ => Sub.refl _)) ho, hH.append fun i u hu => ?_⟩
    have : u = .nul := by
      cases i with
      | zero => simpa using hu.symm
      | succ i => simp at hu
    subst this
    exact VJ.prim rfl
  | lenStrThrow _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    refine ⟨.throw (.val rfl (VJ.thrown _) (fun _ => Sub.refl _)) ho, hH.append fun i u hu => ?_⟩
    have : u = .nul := by
      cases i with
      | zero => simpa using hu.symm
      | succ i => simp at hu
    subst this
    exact VJ.prim rfl
  | arithThrow _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    refine ⟨.throw (.val rfl (VJ.thrown _) (fun _ => Sub.refl _)) ho, hH.append fun i u hu => ?_⟩
    have : u = .nul := by
      cases i with
      | zero => simpa using hu.symm
      | succ i => simp at hu
    subst this
    exact VJ.prim rfl
  | readField hl hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | readAt hx hq hcl hr =>
      obtain ⟨hs, hv'⟩ := hH.read (hx.value rfl) (a := .key _) (by simpa [next, Footprints.fieldsOf] using hl) hv
      exact ⟨.val hv'.val ((hv'.sub (hr _ (hq _ hs))).alloc (Nat.le_refl _)) ho, hH.same⟩
  | readProto hl hp hpv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | readAt hx hq hcl hr =>
      obtain ⟨hs, hv'⟩ := hH.read (hx.value rfl) (a := .key _) (by simpa [next, Footprints.fieldsOf] using hp) hpv
      have hq' := hcl _ (hq _ hs)
      exact ⟨.readAt (.val hv'.val (hv'.alloc (Nat.le_refl _)) (fun h => (hr _ (hq _ hs)).trans (ho h))) hq' hcl hr ho,
        hH.same⟩
  | indexField hk hl hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | indexAt hx _ hq hcl hr =>
      obtain ⟨hs, hv'⟩ := hH.read (hx.value rfl) (a := .key _) (by simpa [next, Footprints.fieldsOf] using hl) hv
      exact ⟨.val hv'.val ((hv'.sub (hr _ (hq _ hs))).alloc (Nat.le_refl _)) ho, hH.same⟩
  | indexProto hk hl hp hpv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | indexAt hx hkey hq hcl hr =>
      obtain ⟨hs, hv'⟩ := hH.read (hx.value rfl) (a := .key _) (by simpa [next, Footprints.fieldsOf] using hp) hpv
      have hq' := hcl _ (hq _ hs)
      exact ⟨.indexAt (.val hv'.val (hv'.alloc (Nat.le_refl _)) (fun h => (hr _ (hq _ hs)).trans (ho h)))
        (hkey.alloc (Nat.le_refl _)) hq' hcl hr ho, hH.same⟩
  | elemRead he hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | elemAt hx _ hc =>
      obtain ⟨k, hk⟩ := next_of_elemLoc he
      obtain ⟨hs, hv'⟩ := hH.read (hx.value rfl) hk hv
      exact ⟨.val hv'.val ((hv'.sub (hc _ hs)).alloc (Nat.le_refl _)) ho, hH.same⟩
  | writeField hv hl hlt =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | writeAt hx hy hst =>
      have hs := (hx.value rfl).sites _ (Leaves.of_next (a := .key _) (by simpa [next, Footprints.fieldsOf] using hl))
      have hy' := hy.value hv
      exact ⟨.val rfl (VJ.prim rfl) ho,
        hH.set_same (hy'.sub (hst _ hs))⟩
  | setPresent hv he hlt =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | setElem hx _ hy hst hS _ =>
      obtain ⟨k, hk⟩ := next_of_elemLoc he
      have hs := (hx.value rfl).sites _ (Leaves.of_next hk)
      have hy' := hy.value hv
      have hst' := hst _ (List.mem_cons_of_mem _ hs)
      exact ⟨.val rfl (((hx.value rfl).sub hS).alloc (by simp)) ho,
        hH.set_same (hy'.sub hst')⟩
  | setGrow hv hk he =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | setElem hx _ hy hst hS ha =>
      rw [stepSite_setElem hv]
      have hy' := hy.value hv
      have hst' := hst _ (List.mem_cons_self ..)
      refine ⟨.val rfl (VJ.arr fun l hl => ?_) ho, hH.append fun i u hu => ?_⟩
      · rcases mem_placeAt hl with hl | hl | hl
        · have hx' := hx.value rfl
          have hle := cells_leaves (P := P) rfl hl
          have hlt := hx'.below l hle
          refine ⟨by simp; omega, ?_⟩
          rw [(Ghost.alloc_old hlt)]
          exact hS _ (hx'.sites l hle)
        · cases hl
        · cases hl
          refine ⟨by simp, ?_⟩
          simp [Ghost.alloc, ha]
      · rcases i with _ | i
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
          subst hu
          exact (hy'.sub hst').alloc (by simp)
        · simp at hu
  | makeFields hvs hlen =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | makeAbsent Ss hst hi hs =>
      have hvj := fun x hx => (hi x hx).value (hvs x hx)
      rw [stepSite_makeAt hvs]
      refine ⟨.val rfl (VJ.obj (fun _ _ => rfl) (fun k l hk => ?_) (fun l hl => by simp [HeapKnowledge.descriptorSpine] at hl) (fun x hx => by simp [codeVals] at hx) (fun u hu => by rcases hu with ⟨_, _, _, _, _, _, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩ <;> cases he) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (fun x hx => by simp [codeVals] at hx) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (fun x hx => by simp [codeVals] at hx)) ho, ?_⟩
      · have := mem_slots hk
        refine ⟨by simp; omega, ?_⟩
        simp [Ghost.alloc, Nat.not_lt.mpr this.1, hs]
      · rw [List.append_assoc]
        exact hH.fresh hst hvj [.nul] (by simp [primVal])
    | makeView Ss hst hi hs hvw =>
      have hvj := fun x hx => (hi x hx).value (hvs x hx)
      rw [stepSite_makeAt hvs]
      refine ⟨.val rfl (VJ.obj (fun _ _ => rfl) (fun k l hk => ?_) (fun l hl => by cases hl; exact ⟨Nat.lt_of_lt_of_le (hvw.below _ (Leaves.of_next (a := .view) rfl)) (by simp), by rw [Ghost.alloc_old (hvw.below _ (Leaves.of_next (a := .view) rfl))]; exact hvw.sites _ (Leaves.of_next (a := .view) rfl)⟩) (fun x hx => by simp [codeVals] at hx) (fun u hu => by rcases hu with ⟨_, _, _, _, _, _, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩ <;> cases he) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (fun x hx => by simp [codeVals] at hx) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (fun x hx => by simp [codeVals] at hx)) ho, ?_⟩
      · have := mem_slots hk
        refine ⟨by simp; omega, ?_⟩
        simp [Ghost.alloc, Nat.not_lt.mpr this.1, hs]
      · rw [List.append_assoc]
        exact hH.fresh hst hvj [.nul] (by simp [primVal])
    | makeBound Ss hst hi hs Sb hb hnl hp =>
      have hvj := fun x hx => (hi x hx).value (hvs x hx)
      rw [stepSite_makeAt hvs]
      have hallb := fun y hy => (hp y hy).top
      have hall := fun y hy => (hallb y hy).sub hb
      refine ⟨.val rfl (VJ.obj (closed_bound (hall _ (List.mem_cons_self ..)).closed (hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).closed fun x hx => (hall x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).closed) (fun k l hk => ?_) (fun l hl => by simp [HeapKnowledge.descriptorSpine] at hl) (bound_code fun y hy => (hall y hy).alloc (by simp)) (bound_child fun y hy => (hall y hy).alloc (by simp)) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (bound_nl (fun y hy => (hallb y hy).alloc (by simp)) hnl) (by intro _ _ _ _ _ _ _ _ _ _ he; cases he) (bound_fns fun y hy => hall y hy)) ho, ?_⟩
      · have := mem_slots hk
        refine ⟨by simp; omega, ?_⟩
        simp [Ghost.alloc, Nat.not_lt.mpr this.1, hs]
      · rw [List.append_assoc]
        exact hH.fresh hst hvj [.nul] (by simp [primVal])
    | makeGraphC π Ss hst hi hs hc hcode hcaps htok hop hE =>
      have hvj := fun x hx => (hi x hx).value (hvs x hx)
      rw [stepSite_makeAt hvs]
      refine ⟨.val rfl (VJ.graphC hc hcode (fun k l hk => ?_)
        (fun c π' h' => ⟨fun i u hu => ((hcaps c π' h').1 i u hu).top.alloc (by simp), (hcaps c π' h').2⟩)
        htok hop (lowered_vj hE)) ho, ?_⟩
      · have := mem_slots hk
        refine ⟨by simp; omega, ?_⟩
        simp [Ghost.alloc, Nat.not_lt.mpr this.1, hs]
      · rw [List.append_assoc]
        exact hH.fresh hst hvj [.nul] (by simp [primVal])
    | makeGraphOut Ss hst hi hs hc hE Sc hb hnl hcaps _ hnone =>
      have hvj := fun x hx => (hi x hx).value (hvs x hx)
      rw [stepSite_makeAt hvs]
      refine ⟨.val rfl (VJ.graphOut hc (fun k l hk => ?_) (fun u hu => ((hcaps u hu).top.alloc (by simp)).sub hb)
        (lowered_vj hE) hE hnone (fun u hu l hl => hnl.origin (((hcaps u hu).top.sites.alloc (hcaps u hu).top.below) l hl))
        (fun u hu l hl => by have := ((lowered_vj (g := g) (n := 0) (S := []) hE u hu).sites l hl); cases this)) ho, ?_⟩
      · have := mem_slots hk
        refine ⟨by simp; omega, ?_⟩
        simp [Ghost.alloc, Nat.not_lt.mpr this.1, hs]
      · rw [List.append_assoc]
        exact hH.fresh hst hvj [.nul] (by simp [primVal])
  | arrAlloc hvs _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | arrLit Ss hst hi hs =>
      have hvj := fun x hx => (hi x hx).value (hvs x hx)
      rw [stepSite_arrLit hvs]
      refine ⟨.val rfl (VJ.arr fun l hl => ?_) ho, ?_⟩
      · simp only [elemSlots, List.mem_map, List.mem_range, Option.some.injEq] at hl
        obtain ⟨i, hi', rfl⟩ := hl
        refine ⟨by simp; omega, ?_⟩
        simp only [Ghost.alloc, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false]
        exact hs
      · have := hH.fresh hst hvj [] (by simp)
        rwa [List.append_nil] at this
  | frameRet hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨.val hv ((((ht.value hv).sub hk).sub hS).alloc (Nat.le_refl _)) ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨.val hv (((ht.value hv).sub hS).alloc (Nat.le_refl _)) ho, hH.same⟩
  | frameBind hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hk _ _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _)) ((ht.value hv).alloc (Nat.le_refl _)))
        (hkf _ _ _ hfn fun σ hσ => (hvfn σ hσ).fnIs hv) hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (envIn_cons (fun i => (henv i).alloc (Nat.le_refl _)) ((ht.value hv).alloc (Nat.le_refl _)))) hS ho hao, hH.same⟩
  | frameEffect hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hk _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _))) (hkf _ _ hfn) hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (fun i => (henv i).alloc (Nat.le_refl _))) hS ho hao, hH.same⟩
  | frameYes  =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hk _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _))).1 (hkf _ _ hfn).1 hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (fun i => (henv i).alloc (Nat.le_refl _))) hS ho hao, hH.same⟩
  | frameNo  =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hk _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _))).2 (hkf _ _ hfn).2 hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (fun i => (henv i).alloc (Nat.le_refl _))) hS ho hao, hH.same⟩
  | frameYesBind  =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hk _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _))).1 (hkf _ _ hfn).1 hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (envIn_cons (fun i => (henv i).alloc (Nat.le_refl _)) (VJ.prim rfl))) hS ho hao, hH.same⟩
  | frameNoBind  =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hk _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _))).2 (hkf _ _ hfn).2 hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (envIn_cons (fun i => (henv i).alloc (Nat.le_refl _)) (VJ.prim rfl))) hS ho hao, hH.same⟩
  | frameTag hv =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      refine ⟨?_, hH.same⟩
      split
      · exact fits_gotoC hc hcode
          (hk _ _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _)) ((ht.value hv).alloc (Nat.le_refl _))).1
          (hkf _ _ _ hfn fun σ hσ => (hvfn σ hσ).fnIs hv).1 hS ho
      · exact fits_gotoC hc hcode
          (hk _ _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _)) ((ht.value hv).alloc (Nat.le_refl _))).2
          (hkf _ _ _ hfn fun σ hσ => (hvfn σ hσ).fnIs hv).2 hS ho
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (envIn_cons (fun i => (henv i).alloc (Nat.le_refl _)) ((ht.value hv).alloc (Nat.le_refl _)))) hS ho hao, hH.same⟩
  | frameHandle hr =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      exact ⟨fits_gotoC hc hcode (hx _ _ _ _ _ (fun i => (henv i).alloc (Nat.le_refl _)) ((raises_fits hr ht).alloc (Nat.le_refl _)))
        (hxf _ _ _ hfn) hS ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      exact ⟨fits_gotoOut hc hE (envIn_map_O (envIn_cons (fun i => (henv i).alloc (Nat.le_refl _)) ((raises_fits hr ht).alloc (Nat.le_refl _)))) hS ho hao, hH.same⟩
  | frameRaise hr =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv' => simp [isVal] at hv'
    | frameC c π l hc hcode hn henv hfn hvfn ht hS =>
      obtain ⟨hk, hx⟩ := codeOk_node hF hcode hn
      obtain ⟨hkf, hxf⟩ := codeFn_node hF hcode hn
      have hv := raises_fits hr ht
      exact ⟨.throw (.val hv.val (hv.alloc (Nat.le_refl _)) (fun _ => Sub.refl _)) ho, hH.same⟩
    | frameOut hc hE henv ht hS _ hao =>
      have hv := raises_fits hr ht
      exact ⟨.throw (.val hv.val (hv.alloc (Nat.le_refl _)) (fun _ => Sub.refl _)) ho, hH.same⟩
  | letV hav =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | letE hx hb =>
      rw [← insertSites_zero] at hb
      exact ⟨(fits_subst (hx.value hav) hb).alloc (Nat.le_refl _), hH.same⟩
  | makeKeyV hav hk =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | makeKey _ hst hx hs =>
      exact ⟨.makeAbsent (fun _ => _) (fun _ hy => by simp at hy; subst hy; exact hst)
        (fun _ hy => by simp at hy; subst hy; exact hx.alloc (Nat.le_refl _)) hs ho, hH.same⟩
  | gotoEnter he hk =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | gotoC c π hc hcode henv hfn hS =>
      have henv' : EnvIn (VJ Fl g _) (π.env _) _ _ := fun i => (henv i).top
      obtain ⟨hent, -⟩ := hF.ok _ c π hcode _ _ _ _ he hk
      exact ⟨.frameC c π _ hc hcode ⟨hk, _, he⟩ (fun i => (henv' i).alloc (Nat.le_refl _)) hfn
        (hent g _ _ _ henv' hfn).2 (hent _ _ _ _ (fun i => (henv' i).alloc (Nat.le_refl _)) hfn).1 hS ho, hH.same⟩
    | gotoOut hc hE henv hS _ hao =>
      have henv' := fun i => (henv i).top
      refine ⟨.frameOut hc hE (fun i => (henv' i).alloc (Nat.le_refl _)) ?_ hS ho hao, hH.same⟩
      exact fits_lowered hF _ (fun i => (henv' i).alloc (Nat.le_refl _)) _ 0 _ (hE _ (List.mem_of_getElem? he))
        (fun i hi => absurd hi (Nat.not_lt_zero _))
  | callGraph hr hargs _ =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke hf hr' hargs' hS ha _ hSf hout =>
      exact ⟨fits_graphEntry hF (((hf.value rfl).sub hSf).alloc (Nat.le_refl _)) ((hr'.value hr).alloc (Nat.le_refl _))
        (fun x hx => ((hargs' x hx).value (hargs x hx)).alloc (Nat.le_refl _)) ha hS ho
        (fun hc => hout ((hf.value rfl).fns.notOut ⟨_, _, _, _, _, _, _, _, _, _, rfl, hc⟩)), hH.same⟩
    | invokeC σ c π Sa Sr hof hfn hcode hself hr' hargs' hat hpar hrest hS =>
      obtain ⟨fs', caps', k', comp', oid', he, hlen, hc⟩ := hfn
      cases he
      refine ⟨fits_graphEntryC hc hcode (by rw [hlen]; exact hself.alloc (Nat.le_refl _))
        ((hr'.value hr).alloc (Nat.le_refl _)) Sa Sr
        (fun i x hx => ((hargs' i x hx).value (hargs x (List.mem_of_getElem? hx))).alloc (Nat.le_refl _))
        hpar hrest hS hof, hH.same⟩
  | constructGraph hargs =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | construct hf hargs' hS ha _ hSf hout =>
      exact ⟨fits_graphEntry hF (((hf.value rfl).sub hSf).alloc (Nat.le_refl _)) (VJ.prim rfl)
        (fun x hx => ((hargs' x hx).value (hargs x hx)).alloc (Nat.le_refl _)) ha hS ho
        (fun hc => hout ((hf.value rfl).fns.notOut ⟨_, _, _, _, _, _, _, _, _, _, rfl, hc⟩)), hH.same⟩
  | callBound hr hargs =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke hf hr' hargs' hS ha _ hSf hout =>
      have hb := hf.value rfl
      have h1 := hb.boundPart (List.mem_cons_self ..)
      have h2 := hb.boundPart (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      refine ⟨.invoke (.val h1.val (h1.alloc (Nat.le_refl _)) (fun _ => hSf))
        (.val h2.val ((h2.sub hSf).alloc (Nat.le_refl _)) (fun _ => Sub.refl _)) (fun x hx => ?_) hS ha ho hSf hout, hH.same⟩
      rcases List.mem_append.mp hx with hx | hx
      · have := (hb.boundPart (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).sub hSf
        exact .val this.val (this.alloc (Nat.le_refl _)) (fun _ => Sub.refl _)
      · exact (hargs' x hx).alloc (Nat.le_refl _)
    | invokeC _ _ _ _ _ _ hfn => obtain ⟨_, _, _, _, _, he, _⟩ := hfn; cases he
  | callSpread hfv hrv heq hpre hre =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    subst heq
    cases hfit with
    | val hv => simp [isVal] at hv
    | invoke hf hr hargs hS ha _ hSf hout =>
      have hsp := hargs _ (List.mem_append_right _ (List.mem_cons_self ..))
      cases hsp with
      | val hv => simp [isVal] at hv
      | spread hx hc =>
        have hvs := spread_vj hH (hx.value rfl) hc hre
        refine ⟨.invoke (hf.alloc (Nat.le_refl _)) (hr.alloc (Nat.le_refl _)) (fun x hx' => ?_) hS ha ho hSf hout, hH.same⟩
        simp only [List.mem_append] at hx'
        rcases hx' with (hx' | hx') | hx'
        · exact (hargs x (List.mem_append_left _ hx')).alloc (Nat.le_refl _)
        · exact .val (hvs x hx').val ((hvs x hx').alloc (Nat.le_refl _)) (fun _ => Sub.refl _)
        · exact (hargs x (List.mem_append_right _ (List.mem_cons_of_mem _ hx'))).alloc (Nat.le_refl _)
    | invokeC _ _ _ _ _ _ _ _ _ _ _ hat =>
      rcases hat _ (List.mem_append_right _ (List.mem_cons_self ..)) with hv | ⟨j, hj⟩
      · simp [isVal] at hv
      · cases hj
  | constructSpread hfv heq hpre hre =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    subst heq
    cases hfit with
    | val hv => simp [isVal] at hv
    | construct hf hargs hS ha _ hSf hout =>
      have hsp := hargs _ (List.mem_append_right _ (List.mem_cons_self ..))
      cases hsp with
      | val hv => simp [isVal] at hv
      | spread hx hc =>
        have hvs := spread_vj hH (hx.value rfl) hc hre
        refine ⟨.construct (hf.alloc (Nat.le_refl _)) (fun x hx' => ?_) hS ha ho hSf hout, hH.same⟩
        simp only [List.mem_append] at hx'
        rcases hx' with (hx' | hx') | hx'
        · exact (hargs x (List.mem_append_left _ hx')).alloc (Nat.le_refl _)
        · exact .val (hvs x hx').val ((hvs x hx').alloc (Nat.le_refl _)) (fun _ => Sub.refl _)
        · exact (hargs x (List.mem_append_right _ (List.mem_cons_of_mem _ hx'))).alloc (Nat.le_refl _)
  | arrSpread heq hpre hre =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    subst heq
    rename_i pre post ls vs h₀
    cases hfit with
    | val hv => simp [isVal] at hv
    | arrLit Ss hst hi hs =>
      have hmem : Tm.spread (.arr ls) ∈ pre ++ Tm.spread (.arr ls) :: post := List.mem_append_right _ (List.mem_cons_self ..)
      have hsp := hi _ hmem
      have hspo := hsp.out
      cases hsp with
      | val hv => simp [isVal] at hv
      | spread hx hc =>
        have hvs := spread_vj hH (hx.value rfl) hc hre
        classical
        refine ⟨.arrLit (fun y => if y ∈ pre ++ post then Ss y ++ Ss (.spread (.arr ls)) else Ss (.spread (.arr ls)))
          (fun y _ => ?_) (fun y hy => ?_) hs ho, hH.same⟩
        · split
          · rename_i hy
            have h1 := hst y (by
              rcases List.mem_append.mp hy with hy | hy
              · exact List.mem_append_left _ hy
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy))
            have h2 := hst _ hmem
            exact fun s hs' => (List.mem_append.mp hs').elim (h1 s) (h2 s)
          · exact hst _ hmem
        · split
          · rename_i hy'
            simp only [List.mem_append] at hy'
            rcases hy' with hy' | hy'
            · have hy₀ := hi y (List.mem_append_left _ hy')
              exact (hy₀.sub VJ.mono (fun s h => List.mem_append_left _ h) fun h s hs' =>
                (List.mem_append.mp hs').elim (hy₀.out h s) (hspo h s)).alloc (Nat.le_refl _)
            · have hy₀ := hi y (List.mem_append_right _ (List.mem_cons_of_mem _ hy'))
              exact (hy₀.sub VJ.mono (fun s h => List.mem_append_left _ h) fun h s hs' =>
                (List.mem_append.mp hs').elim (hy₀.out h s) (hspo h s)).alloc (Nat.le_refl _)
          · rename_i hy'
            simp only [List.mem_append] at hy
            rcases hy with (hy | hy) | hy
            · exact absurd (List.mem_append_left _ hy) hy'
            · exact .val (hvs y hy).val ((hvs y hy).alloc (Nat.le_refl _)) hspo
            · exact absurd (List.mem_append_right _ hy) hy'
  | mergeV hav hbv hmp =>
    intro cur ou o S hfit hH
    have ho := hfit.out
    cases hfit with
    | val hv => simp [isVal] at hv
    | merge hx hy hq hcl hst hs hQ =>
      have hvals := merge_vals hH (hx.value hav) (hy.value hbv) hq hcl hmp
      refine ⟨fits_mergeAlloc hst hs hcl hQ ho fun v hv => ?_, hH.same⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      rcases hvals p hp with h₁ | ⟨s, hs', hv'⟩
      · exact .inl h₁
      · exact .inr ⟨s, hs', hv'.alloc (Nat.le_refl _)⟩

end Verification.TolerantFrames.ReadOnly
