import Verification.Semantics.Footprints

/-! # Path-closed supports and transitive composition

A support `U` is path-closed when every field read along a path region of `U`
(and the spine of any cell region of `U`) is kept with `.keep` in `U`. Under
`pathClosed U = true`, every transition satisfying `Supported U ρ h₀ h₁`
preserves all path reads and region memberships of `U`, so `Supported U`
composes transitively across arbitrary sequences of steps and relied calls for
every `Footprints.Change` bound (`keep` through `any`). -/

namespace Verification.SourceClaimJson.CallbackPathClosure
open Footprints HeapKnowledge

/-- Strip `.inCls r c` layers that admit the value category (`c.value = true`). -/
def fieldRegion : Region → Region
  | .inCls r c => if c.value then fieldRegion r else .inCls r c
  | r => r

/-- Every prefix field of `(x, p)` is kept with `.keep` in `support`
(either by an exact field/path entry, or by a `fields`/`pathFields` entry when
the key is not `arraySpineKey`). -/
def pathFieldsKept (support : Footprint) (x : Nat) (p : List String) : Bool :=
  (List.range p.length).all fun n =>
    let pre := p.take n
    let k := PropKey.str (p.getD n "")
    support.any fun (r, c) => c == .keep &&
      (fieldRegion r == (if pre.isEmpty then .field x k else .path x pre k) ||
        (k != arraySpineKey &&
          fieldRegion r == (if pre.isEmpty then .fields x else .pathFields x pre)))

/-- All array and view spines are kept with `.keep` in `support`, ensuring
`spineCells` is unchanged across transitions (needed only when a support
explicitly includes `.cells` or `.pathCells`). -/
def allSpinesKept (support : Footprint) : Bool :=
  support.any fun (r, c) => c == .keep &&
    (r == .all || match r with | .cls s => s.array && s.view | _ => false)

/-- Path-closed: every path a region of `support` reads goes through fields
that `support` keeps with `.keep` (and any cell region keeps spines with
`.keep`). -/
def pathClosed (support : Footprint) : Bool :=
  let rec closed : Region → Bool
    | .path x p _ | .pathFields x p | .spine x p => pathFieldsKept support x p
    | .cells _ => allSpinesKept support
    | .pathCells x p => pathFieldsKept support x p && allSpinesKept support
    | .inCls r _ => closed r
    | .field _ _ | .fields _ | .cls _ | .all => true
  support.all fun (r, _) => closed r

theorem supported_refl (S : Footprint) (ρ : Env) (h : Heap) : Supported S ρ h h :=
  fun e _ _ v _ hv => ⟨v, hv, Change.Holds.refl e.2 h.length v⟩

theorem supported_sub {S T : Footprint} {ρ : Env} {h h' : Heap}
    (hS : Supported S ρ h h') (hsub : ∀ e ∈ T, e ∈ S) : Supported T ρ h h' :=
  fun e he => hS e (hsub e he)

private theorem readPath_append (h : Heap) :
    ∀ (p₁ p₂ : List String) (v : Tm),
      readPath h v (p₁ ++ p₂) = (readPath h v p₁).bind fun u => readPath h u p₂
  | [], _, _ => rfl
  | f :: p₁, p₂, v => by
    cases v with
    | objAt fs cc oid =>
      simp only [List.cons_append, readPath]
      cases hlu : fs.lookup (.str f) with
      | none => rfl
      | some l =>
        dsimp only
        cases hget : h[l]? with
        | none => rfl
        | some u => exact readPath_append h p₁ p₂ u
    | _ => rfl

private theorem fieldRegion_mem {ρ : Env} {h : Heap} {l : Nat} {v : Val}
    (hv : h[l]? = some v) (hcat : contentsCategory v = .value) :
    ∀ {r target : Region}, fieldRegion r = target → target.mem ρ h l = true → r.mem ρ h l = true
  | .inCls r c, target, hfr, hm => by
    simp only [fieldRegion] at hfr
    by_cases hval : c.value = true
    · simp only [hval, ↓reduceIte] at hfr
      have hr := fieldRegion_mem hv hcat hfr hm
      simp only [Region.mem, hv, hr, Bool.true_and, Selector.selects, hcat, Selector.has, hval]
    · simp only [hval, Bool.false_eq_true, ↓reduceIte] at hfr
      subst hfr; exact hm
  | .field _ _, target, hfr, hm | .fields _, target, hfr, hm | .cells _, target, hfr, hm
  | .cls _, target, hfr, hm | .all, target, hfr, hm | .path _ _ _, target, hfr, hm
  | .pathFields _ _, target, hfr, hm | .pathCells _ _, target, hfr, hm | .spine _ _, target, hfr, hm => by
    simp only [fieldRegion] at hfr; subst hfr; exact hm

private theorem readPath_take_succ {h : Heap} {v : Val} {p : List String} {n : Nat}
    (hn : n < p.length) :
    readPath h v (p.take (n + 1)) =
      (readPath h v (p.take n)).bind fun u => readPath h u [p[n]] := by
  have htake : p.take (n + 1) = p.take n ++ [p[n]] := List.take_succ_eq_append_getElem hn
  rw [htake, readPath_append]

private theorem objAt_of_readPath_cons {h : Heap} {v w : Val} {f : String} {rest : List String}
    (hr : readPath h v (f :: rest) = some w) :
    ∃ fs cc oid l u, v = .objAt fs cc oid ∧ fs.lookup (.str f) = some l ∧
      h[l]? = some u ∧ readPath h u rest = some w := by
  cases v with
  | objAt fs cc oid =>
    simp only [readPath] at hr
    cases hlu : fs.lookup (.str f) with
    | none => simp [hlu] at hr
    | some l =>
      simp only [hlu] at hr
      cases hget : h[l]? with
      | none => simp [hget] at hr
      | some u =>
        simp only [hget] at hr
        exact ⟨fs, cc, oid, l, u, rfl, hlu, hget, hr⟩
  | _ => simp [readPath] at hr

/-- Under `pathFieldsKept U x p = true` and `Supported U ρ h₀ h₁`, if reading
`(ρ x)` along `p` yields an `.objAt` value `v` in `h₀`, then reading `(ρ x)`
along `p` yields the exact same `v` in `h₁`. -/
theorem pathFieldsKept_readPath_eq {U : Footprint} {ρ : Env} {h₀ h₁ : Heap} {x : Nat} {p : List String}
    (hkept : pathFieldsKept U x p = true) (hsup : Supported U ρ h₀ h₁)
    {fs cc oid} (hr₀ : readPath h₀ (ρ x) p = some (.objAt fs cc oid)) :
    readPath h₁ (ρ x) p = some (.objAt fs cc oid) := by
  have hstep : ∀ n (hn : n ≤ p.length),
      readPath h₁ (ρ x) (p.take n) = readPath h₀ (ρ x) (p.take n) := by
    intro n
    induction n with
    | zero => intro _; simp [readPath]
    | succ n ih =>
      intro hn
      have hlt : n < p.length := by omega
      have hprev := ih (by omega)
      rw [readPath_take_succ hlt, readPath_take_succ hlt, hprev]
      have hsplit : p = p.take (n + 1) ++ p.drop (n + 1) := (List.take_append_drop (n + 1) p).symm
      rw [hsplit, readPath_append] at hr₀
      cases hnext : readPath h₀ (ρ x) (p.take (n + 1)) with
      | none => simp [hnext] at hr₀
      | some w =>
        rw [hnext, Option.bind_some] at hr₀
        have hcat_w : contentsCategory w = .value := by
          cases hdrop : p.drop (n + 1) with
          | nil =>
            rw [hdrop] at hr₀; simp [readPath] at hr₀; subst w; rfl
          | cons g gs =>
            rw [hdrop] at hr₀
            obtain ⟨_, _, _, _, _, rfl, _, _, _⟩ := objAt_of_readPath_cons hr₀
            rfl
        rw [readPath_take_succ hlt] at hnext
        cases hcur : readPath h₀ (ρ x) (p.take n) with
        | none => simp [hcur] at hnext
        | some u =>
          rw [hcur] at hnext
          simp only [Option.bind_some] at hnext ⊢
          obtain ⟨ufs, ucc, uoid, l, u', rfl, hlu, hget₀, hu'⟩ := objAt_of_readPath_cons hnext
          simp only [readPath, Option.some.injEq] at hu'
          subst u'
          have hall := List.all_eq_true.mp hkept n (List.mem_range.mpr hlt)
          have hgetD : p.getD n "" = p[n] := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
          rw [hgetD] at hall
          obtain ⟨⟨r, c⟩, hrc_mem, hrc_ok⟩ := List.any_eq_true.mp hall
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hrc_ok
          obtain ⟨rfl, hmatch⟩ := hrc_ok
          have hrmem : r.mem ρ h₀ l = true := by
            rcases hmatch with hfield | ⟨hkne, hfields⟩
            · refine fieldRegion_mem hget₀ hcat_w hfield ?_
              cases hpre : (p.take n).isEmpty with
              | true =>
                have hnil : p.take n = [] := List.isEmpty_iff.mp hpre
                rw [hnil] at hcur; simp [readPath] at hcur
                simp [Region.mem, hcur, fieldsOf, hlu]
              | false =>
                simp [Region.mem, hcur, fieldsOf, hlu]
            · refine fieldRegion_mem hget₀ hcat_w hfields ?_
              have hfl : l ∈ fieldLocs (.objAt ufs ucc uoid) :=
                lookup_mem_fieldLocs (v := .objAt ufs ucc uoid) (by simpa [fieldsOf] using hlu) hkne
              cases hpre : (p.take n).isEmpty with
              | true =>
                have hnil : p.take n = [] := List.isEmpty_iff.mp hpre
                rw [hnil] at hcur; simp [readPath] at hcur
                simp [Region.mem, hcur, hfl]
              | false =>
                simp [Region.mem, hcur, hfl]
          obtain ⟨w', hget₁, hw'⟩ := hsup (r, .keep) hrc_mem l w hrmem hget₀
          change w' = w at hw'
          subst w'
          simp [readPath, hlu, hget₁, hget₀]
  have hfull := hstep p.length (Nat.le_refl _)
  rw [List.take_length] at hfull
  rw [hfull, hr₀]

private theorem entriesAt_mem {h : Heap} {loc : Option Nat} {l : Nat}
    (hm : some l ∈ entriesAt h loc) :
    ∃ sp sv, loc = some sp ∧ h[sp]? = some sv ∧
      (contentsCategory sv = .array ∨ contentsCategory sv = .view) := by
  cases loc with
  | none => simp [entriesAt] at hm
  | some sp =>
    simp only [entriesAt] at hm
    cases hget : h[sp]? with
    | none => simp [hget] at hm
    | some sv =>
      cases sv with
      | arr ls => exact ⟨sp, .arr ls, rfl, hget, .inl rfl⟩
      | viewSpine f cs => exact ⟨sp, .viewSpine f cs, rfl, hget, .inr rfl⟩
      | _ => simp [hget, spineEntries] at hm

private theorem allSpinesKept_entriesAt {U : Footprint} {ρ : Env} {h₀ h₁ : Heap}
    (hskept : allSpinesKept U = true) (hsup : Supported U ρ h₀ h₁)
    {loc : Option Nat} {l : Nat} (hm₀ : some l ∈ entriesAt h₀ loc) :
    some l ∈ entriesAt h₁ loc := by
  obtain ⟨sp, sv, rfl, hget₀, hcat⟩ := entriesAt_mem hm₀
  obtain ⟨⟨r, c⟩, hrc_mem, hrc_ok⟩ := List.any_eq_true.mp hskept
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrc_ok
  obtain ⟨rfl, hmatch⟩ := hrc_ok
  have hrmem : r.mem ρ h₀ sp = true := by
    rcases hmatch with rfl | hcls
    · simp [Region.mem, (List.getElem?_eq_some_iff.mp hget₀).1]
    · cases r with
      | cls s =>
        obtain ⟨ha, hv⟩ := Bool.and_eq_true_iff.mp hcls
        have hsel : s.selects sv = true := by
          rcases hcat with hc | hc <;> simp [Selector.selects, hc, Selector.has, ha, hv]
        simp [Region.mem, hget₀, hsel]
      | _ => simp at hcls
  obtain ⟨sv', hget₁, hsv'⟩ := hsup (r, .keep) hrc_mem sp sv hrmem hget₀
  change sv' = sv at hsv'; subst sv'
  simpa [entriesAt, hget₁] using (by simpa [entriesAt, hget₀] using hm₀)

private theorem allSpinesKept_cells_eq {U : Footprint} {ρ : Env} {h₀ h₁ : Heap}
    (hskept : allSpinesKept U = true) (hsup : Supported U ρ h₀ h₁)
    {v : Val} {l : Nat} (hm₀ : (spineCells h₀ v).contains (some l) = true) :
    (spineCells h₁ v).contains (some l) = true := by
  simp only [List.contains_iff_mem, spineCells, List.mem_append] at hm₀ ⊢
  rcases hm₀ with h₁' | h₂'
  · exact .inl (allSpinesKept_entriesAt hskept hsup h₁')
  · exact .inr (allSpinesKept_entriesAt hskept hsup h₂')

private theorem readPath_mem_obj {h : Heap} {v : Val} {p : List String} {w : Val}
    (hr : readPath h v p = some w) :
    (∀ k l, (fieldsOf w).lookup k = some l → ∃ fs cc oid, w = .objAt fs cc oid) ∧
    (∀ l, (fieldLocs w).contains l = true → ∃ fs cc oid, w = .objAt fs cc oid) ∧
    (∀ l, elementsOf w = some l → ∃ fs cc oid, w = .objAt fs cc oid) ∧
    (∀ l, (spineCells h w).contains (some l) = true → ∃ fs cc oid, w = .objAt fs cc oid) := by
  refine ⟨fun k l hlu => ?_, fun l hfl => ?_, fun l hel => ?_, fun l hsc => ?_⟩
  · cases w with
    | objAt fs cc oid => exact ⟨fs, cc, oid, rfl⟩
    | _ => simp [fieldsOf] at hlu
  · cases w with
    | objAt fs cc oid => exact ⟨fs, cc, oid, rfl⟩
    | _ => simp [fieldLocs, fieldsOf] at hfl
  · cases w with
    | objAt fs cc oid => exact ⟨fs, cc, oid, rfl⟩
    | _ => simp [elementsOf] at hel
  · cases w with
    | objAt fs cc oid => exact ⟨fs, cc, oid, rfl⟩
    | _ => simp [spineCells, fieldsOf, descriptorSpine, entriesAt] at hsc

/-- **Transitivity through a path-closed support** (for every `Change`
bound): if `pathClosed U = true`, `T ⊆ U`, `h₀.length ≤ h₁.length`,
`Supported U ρ h₀ h₁` and `Supported T ρ h₁ h₂`, then `Supported T ρ h₀ h₂`. -/
theorem supported_trans_of_pathClosed {U T : Footprint} {ρ : Env} {h₀ h₁ h₂ : Heap}
    (hclosed : pathClosed U = true) (hsub : ∀ e ∈ T, e ∈ U)
    (hlen₀₁ : h₀.length ≤ h₁.length) (hlen₁₂ : h₁.length ≤ h₂.length)
    (h₀₁ : Supported U ρ h₀ h₁) (h₁₂ : Supported T ρ h₁ h₂) :
    Supported T ρ h₀ h₂ := by
  intro ⟨r, δ⟩ hmemT l v hm₀ hv₀
  have hmem := hsub _ hmemT
  have hcl : pathClosed.closed U r = true := List.all_eq_true.mp hclosed (r, δ) hmem
  obtain ⟨v₁, hv₁, hch₁⟩ := h₀₁ (r, δ) hmem l v hm₀ hv₀
  by_cases hany : δ = .any
  · subst hany
    have hlt₂ : l < h₂.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hv₀).1 (Nat.le_trans hlen₀₁ hlen₁₂)
    exact ⟨h₂[l], List.getElem?_eq_getElem hlt₂, trivial⟩
  · have hrmem₁ : ∀ {r' : Region}, pathClosed.closed U r' = true →
        r'.mem ρ h₀ l = true →
        (∀ c : Selector, c.selects v = true → c.selects v₁ = true) →
        r'.mem ρ h₁ l = true := by
      intro r'
      induction r' with
      | field x k => intro _ hm _; exact hm
      | fields x => intro _ hm _; exact hm
      | cells x =>
        intro hcr hm _
        simp only [pathClosed.closed] at hcr
        exact allSpinesKept_cells_eq hcr h₀₁ hm
      | cls c =>
        intro _ hm hsel
        simp only [Region.mem, hv₀] at hm
        simp only [Region.mem, hv₁, hsel c hm]
      | all =>
        intro _ hm _
        simp only [Region.mem, decide_eq_true_eq] at hm ⊢
        omega
      | path x p k =>
        intro hcr hm _
        simp only [pathClosed.closed] at hcr
        simp only [Region.mem] at hm ⊢
        cases hr : readPath h₀ (ρ x) p with
        | none => simp [hr] at hm
        | some w =>
          simp only [hr, beq_iff_eq] at hm
          obtain ⟨fs, cc, oid, rfl⟩ := (readPath_mem_obj hr).1 k l hm
          rw [pathFieldsKept_readPath_eq hcr h₀₁ hr]
          simp [hm]
      | pathFields x p =>
        intro hcr hm _
        simp only [pathClosed.closed] at hcr
        simp only [Region.mem] at hm ⊢
        cases hr : readPath h₀ (ρ x) p with
        | none => simp [hr] at hm
        | some w =>
          simp only [hr] at hm
          obtain ⟨fs, cc, oid, rfl⟩ := (readPath_mem_obj hr).2.1 l hm
          rw [pathFieldsKept_readPath_eq hcr h₀₁ hr]
          exact hm
      | pathCells x p =>
        intro hcr hm _
        simp only [pathClosed.closed, Bool.and_eq_true] at hcr
        simp only [Region.mem] at hm ⊢
        cases hr : readPath h₀ (ρ x) p with
        | none => simp [hr] at hm
        | some w =>
          simp only [hr] at hm
          obtain ⟨fs, cc, oid, rfl⟩ := (readPath_mem_obj hr).2.2.2 l hm
          have hr₁ := pathFieldsKept_readPath_eq hcr.1 h₀₁ hr
          rw [hr₁]
          exact allSpinesKept_cells_eq hcr.2 h₀₁ hm
      | spine x p =>
        intro hcr hm _
        simp only [pathClosed.closed] at hcr
        simp only [Region.mem] at hm ⊢
        cases hr : readPath h₀ (ρ x) p with
        | none => simp [hr] at hm
        | some w =>
          simp only [hr, beq_iff_eq] at hm
          obtain ⟨fs, cc, oid, rfl⟩ := (readPath_mem_obj hr).2.2.1 l hm
          rw [pathFieldsKept_readPath_eq hcr h₀₁ hr]
          simp [hm]
      | inCls r' c ih =>
        intro hcr hm hsel
        simp only [pathClosed.closed] at hcr
        simp only [Region.mem, hv₀, Bool.and_eq_true] at hm
        simp only [Region.mem, hv₁, Bool.and_eq_true]
        exact ⟨ih hcr hm.1 hsel, hsel c hm.2⟩
    have hsel : ∀ c : Selector, c.selects v = true → c.selects v₁ = true :=
      fun c hc => (Change.Holds.same_class hany hch₁ c).symm ▸ hc
    have hm₁ : r.mem ρ h₁ l = true := hrmem₁ hcl hm₀ hsel
    obtain ⟨v₂, hv₂, hch₂⟩ := h₁₂ (r, δ) hmemT l v₁ hm₁ hv₁
    exact ⟨v₂, hv₂, Change.Holds.trans hlen₀₁ hch₁ hch₂⟩

end Verification.SourceClaimJson.CallbackPathClosure
