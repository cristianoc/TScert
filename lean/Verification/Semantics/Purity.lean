import Verification.Semantics.CallArguments

/-! Executable purity checks and their operational justification. -/
namespace Verification.Purity

/-- Source lowering inserts variable copies and literal nodes between
operations. These are pure: unlike calls they must not discard cell facts. -/
def pureTerm : Tm → Bool
  | .var _ => true
  | .letE a b => pureTerm a && pureTerm b
  | .test _ a => pureTerm a
  | .ite c t e => pureTerm c && pureTerm t && pureTerm e
  | .arith _ a b => pureTerm a && pureTerm b
  | .throw a => pureTerm a
  /- A length reads the store it is given, or a string's code units, and
  gives a number: it changes no heap. -/
  | .lenOf a => pureTerm a
  | t => isVal t

/-- Immutable binding substitutes a pure value without introducing effects. -/
theorem pure_subst {t a : Tm} {j : Nat}
    (ht : pureTerm t = true) (ha : pureTerm a = true) :
    pureTerm (subst j a t) = true := by
  induction t using Tm.induct generalizing j <;> simp_all [pureTerm, isVal, subst]
  case var i =>
    split
    · exact ha
    · split <;> rfl

/-- Purity is closed under actual reduction and keeps the heap as a prefix:
the one allocation is the identity of an error an operator throws. Stored
closure bodies need not be pure: observing an object does not invoke it. -/
theorem pure_step {h t h' t'} (hs : Step h t h' t') (hp : pureTerm t = true) :
    h.IsPrefix h' ∧ pureTerm t' = true := by
  induction hs <;> simp_all [pureTerm,isVal]
  case testV => split <;> simp [pureTerm,isVal]
  case arithV hb =>
    rcases (binop_result hb).2.2 with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  case arithThrow => rfl
  case letV => exact pure_subst hp.2 hp.1

/-- Substituting values for all free variables preserves purity. The graph
machine's environment is total, including its default slot. -/
theorem pure_instantiate_values {t : Tm} {ρ : Env} {d : Nat}
    (hp : pureTerm t = true) (he : ∀ i, isVal (ρ i) = true) :
    pureTerm (instantiate d ρ t) = true := by
  induction t using Tm.induct generalizing d <;> simp_all [pureTerm, isVal, instantiate]
  case var i =>
    split
    · rfl
    · have hv := he (i-d)
      cases h : ρ (i-d) <;> simp_all [pureTerm, isVal]

theorem pure_value {v : Tm} (hv : isVal v = true) : pureTerm v = true := by
  cases v <;> simp_all [pureTerm, isVal]

/-- The machine states reached by graph code whose node expressions are
pure. Continuations only rearrange values; they do not change the heap. -/
inductive PureRun : Tm → Prop where
  | term : pureTerm t = true → PureRun t
  | goto : (∀ e ∈ E, pureTerm e = true) →
      (∀ v ∈ L, isVal v = true) → isVal d = true → PureRun (.goto E K l L d)
  | frame : (∀ e ∈ E, pureTerm e = true) →
      (∀ v ∈ L, isVal v = true) → isVal d = true → pureTerm t = true →
      PureRun (.frame E K t L d k x)

private theorem env_values {L : List Tm} {d : Tm}
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) (i : Nat) :
    isVal (envOf L d i) = true := by
  rcases getD_mem_or L i d with h | h
  · exact hL _ h
  · change isVal (L.getD i d) = true
    rw [h]
    exact hd

private theorem mapped_values {L : List Tm} {d : Tm}
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) (m : Option (List Nat)) :
    (∀ v ∈ (envMap m L d).1, isVal v = true) ∧ isVal (envMap m L d).2 = true := by
  have all : ∀ v, v ∈ (envMap m L d).1 ∨ v = (envMap m L d).2 → isVal v = true := by
    intro v hv
    rcases envMap_mem hv with h | rfl
    · exact hL v h
    · exact hd
  exact ⟨fun v hv => all v (.inl hv), all _ (.inr rfl)⟩

private theorem mapped_goto {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm}
    {d : Tm} {l : Nat} {m : Option (List Nat)}
    (hE : ∀ e ∈ E, pureTerm e = true)
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) :
    PureRun (.goto E K l (envMap m L d).1 (envMap m L d).2) := by
  obtain ⟨hL', hd'⟩ := mapped_values hL hd m
  exact .goto hE hL' hd'

theorem PureRun.step {h t h' t'} (hp : PureRun t) (hs : Step h t h' t') :
    h.IsPrefix h' ∧ PureRun t' := by
  cases hp with
  | term hp =>
    obtain ⟨hpre, hp'⟩ := pure_step hs hp
    exact ⟨hpre, .term hp'⟩
  | goto hE hL hd =>
    cases hs with
    | gotoEnter he hk =>
      exact ⟨List.prefix_refl _, .frame hE hL hd
        (pure_instantiate_values (hE _ (List.mem_of_getElem? he)) (env_values hL hd))⟩
  | frame hE hL hd ht =>
    cases hs with
    | frameC st =>
      obtain ⟨hpre, ht'⟩ := pure_step st ht
      exact ⟨hpre, .frame hE hL hd ht'⟩
    | frameRet hv => exact ⟨List.prefix_refl _, .term (pure_value hv)⟩
    | frameBind hv =>
      refine ⟨List.prefix_refl _, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all
    | frameEffect hv =>
      refine ⟨List.prefix_refl _, ?_⟩
      exact mapped_goto hE hL hd
    | frameYes | frameNo =>
      refine ⟨List.prefix_refl _, ?_⟩
      exact mapped_goto hE hL hd
    | frameYesBind | frameNoBind =>
      refine ⟨List.prefix_refl _, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all [isVal]
    | frameTag hv =>
      refine ⟨List.prefix_refl _, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all
    | frameHandle hr =>
      have hv := raises_val hr
      refine ⟨List.prefix_refl _, ?_⟩
      apply mapped_goto hE (hd := hd)
      simp_all
    | frameRaise hr =>
      exact ⟨List.prefix_refl _, .term (by simpa [pureTerm] using pure_value (raises_val hr))⟩

/-- A rest-collecting entry allocates a fresh store before running the
body. This is compatible with preserving the input heap: fresh locations are
allowed. Values and scope are checked separately, so substitution cannot turn
a saved argument into executable code. -/
inductive CollectingRun : Tm → Prop where
  | pure : PureRun t → CollectingRun t
  | collect : (∀ e ∈ E, pureTerm e = true) →
      (∀ v ∈ L, isVal v = true) → (∀ v ∈ L, Scoped 0 v) →
      (∀ v ∈ vs, isVal v = true) →
      CollectingRun (.letE (.arrLit vs) (.goto E K start (.var 0 :: L) .nul))
  | collected : (∀ e ∈ E, pureTerm e = true) →
      (∀ v ∈ L, isVal v = true) → (∀ v ∈ L, Scoped 0 v) →
      CollectingRun (.letE (.arr ls) (.goto E K start (.var 0 :: L) .nul))

theorem CollectingRun.step {h t h' t'} (hp : CollectingRun t) (hs : Step h t h' t') :
    h.IsPrefix h' ∧ CollectingRun t' := by
  cases hp with
  | pure hp =>
    obtain ⟨hpre, hp'⟩ := hp.step hs
    exact ⟨hpre, .pure hp'⟩
  | collect hE hL hsc hvs =>
    obtain ⟨rfl, rfl⟩ := Step_det hs (.letC (.arrAlloc hvs))
    exact ⟨⟨_, rfl⟩, .collected hE hL hsc⟩
  | @collected E L ls K start hE hL hsc =>
    obtain ⟨rfl, rfl⟩ := Step_det hs (.letV (by rfl))
    have hm : L.map (subst 0 (.arr ls)) = L := by
      rw [List.map_congr_left (g := id) (fun v hv => subst_above (hsc v hv) (Nat.le_refl 0) _),
        List.map_id]
    refine ⟨⟨[], by simp⟩, ?_⟩
    simp only [subst, substArgs_eq_map, List.map_cons, hm]
    exact .pure (.goto hE (by simp_all [isVal]) rfl)

/-- Field and element reads over values: they look up locations of the heap
and change none. -/
def readTerm : Tm → Bool
  | .var _ => true
  | .readAt _ a => readTerm a
  | .elemAt a i => readTerm a && readTerm i
  | t => isVal t

theorem read_value {v : Tm} (hv : isVal v = true) : readTerm v = true := by
  cases v <;> simp_all [readTerm, isVal]

/-- A step of a read leaves the heap as it is, and what remains is a read,
when the heap holds only values. -/
theorem read_step {h t h' t'} (hs : Step h t h' t') (hp : readTerm t = true)
    (hv : ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true) : h' = h ∧ readTerm t' = true := by
  induction hs with
  | readC _ ih => simp only [readTerm] at hp ⊢; exact ih hp hv
  | readField _ hl => exact ⟨rfl, read_value (hv _ _ hl)⟩
  | readProto _ _ hl => exact ⟨rfl, by simp only [readTerm]; exact read_value (hv _ _ hl)⟩
  | readMissing => exact ⟨rfl, rfl⟩
  | elemC1 _ ih =>
    simp only [readTerm, Bool.and_eq_true] at hp ⊢
    exact ⟨(ih hp.1 hv).1, (ih hp.1 hv).2, hp.2⟩
  | elemC2 _ _ ih =>
    simp only [readTerm, Bool.and_eq_true] at hp ⊢
    exact ⟨(ih hp.2 hv).1, hp.1, (ih hp.2 hv).2⟩
  | elemRead _ hl => exact ⟨rfl, read_value (hv _ _ hl)⟩
  | elemAbsent => exact ⟨rfl, rfl⟩
  | elemStr => exact ⟨rfl, by unfold codeUnitAt; split <;> rfl⟩
  | _ => simp [readTerm, isVal] at hp

#print axioms CollectingRun.step
#print axioms read_step
#print axioms PureRun.step

end Verification.Purity
