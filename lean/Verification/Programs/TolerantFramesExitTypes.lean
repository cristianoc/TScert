import Verification.Programs.TolerantFramesNodeYieldChecks

/-! # Tolerant frames: an exit's types from the checks that pass first

`exitTypes` accepts an exit's types where every slot `differing` names has,
in the edge's context, a type below the target's (`diffSubtypes`), or where
the edge search accepts at the edge's context, the refined context or the
mixed one (`mixedContext`). Proved: (`differing_cover`) a target slot
`differing` leaves out reads a source slot of the same type;
(`diffSubtypes_covers`) where `diffSubtypes` passes over `differing`'s slots
and the subtype answers are sound, the edge's context covers the target's
through the mapping (`MappedCovers`), so the target's context types the
mapped environment; (`mixedContext_env`) the mixed context types every
environment that both the edge's context and the refined one type. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Differing
variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
theorem same_eq_beq {α : Type} [BEq α] [ReflBEq α] (a b : α) : same a b = (a == b) := rfl

/-- The loop of `differing` with no mapping, from the slot `i` and the
source types left `as`. -/
def differingNone (Γ : List (Ty ι)) : List (Ty ι) → Nat → List (Ty ι) → List (Nat × Nat) → List (Nat × Nat)
  | [], _, _, out => out
  | B :: Δ, i, xs, out =>
    match xs with
    | A :: rest => differingNone Γ Δ (i + 1) rest (if !same A B then (i, i) :: out else out)
    | [] => differingNone Γ Δ (i + 1) [] ((i, i) :: out)

/-- The loop of `differing` over a mapping's slots `ss`. -/
def differingSome (Γ : List (Ty ι)) : List (Ty ι) → Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], _, _, out => out
  | B :: Δ, i, ss, out =>
    match ss with
    | s :: rest => differingSome Γ Δ (i + 1) rest
        (match Γ.toArray[s]? with
          | some A => if !same A B then (i, s) :: out else out
          | none => (i, s) :: out)
    | [] => differingSome Γ Δ (i + 1) [] ((i, 0) :: out)

theorem differingNone_mono (Γ : List (Ty ι)) :
    ∀ (Δ : List (Ty ι)) i xs out, ∀ x ∈ out, x ∈ differingNone Γ Δ i xs out
  | [], _, _, _, x, hx => hx
  | B :: Δ, i, xs, out, x, hx => by
    cases xs with
    | cons A rest =>
      exact differingNone_mono Γ Δ _ _ _ x (by split <;> simp_all)
    | nil => exact differingNone_mono Γ Δ _ _ _ x (List.mem_cons_of_mem _ hx)

theorem differingSome_mono (Γ : List (Ty ι)) :
    ∀ (Δ : List (Ty ι)) i ss out, ∀ x ∈ out, x ∈ differingSome Γ Δ i ss out
  | [], _, _, _, x, hx => hx
  | B :: Δ, i, ss, out, x, hx => by
    cases ss with
    | cons s rest =>
      refine differingSome_mono Γ Δ _ _ _ x ?_
      split <;> (try split) <;> simp_all
    | nil => exact differingSome_mono Γ Δ _ _ _ x (List.mem_cons_of_mem _ hx)

/-- **`differing` with no mapping leaves out only slots of the same type**:
a target slot `i + j` outside it reads the source type `as[j]`, equal to
the target's. -/
theorem differingNone_cover (Γ : List (Ty ι)) :
    ∀ (Δ : List (Ty ι)) i xs out j B, Δ[j]? = some B → (i + j, i + j) ∉ differingNone Γ Δ i xs out →
      xs[j]? = some B
  | [], _, _, _, j, B, hB, _ => by simp at hB
  | B' :: Δ, i, xs, out, j, B, hB, hn => by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hB
      subst hB
      cases xs with
      | cons A rest =>
        simp only [differingNone] at hn
        by_cases hs : same A B'
        · rw [same_eq_beq, beq_iff_eq] at hs
          simp [hs]
        · exact (hn (by simp only [Nat.add_zero]; exact differingNone_mono _ _ _ _ _ _ (by simp [hs]))).elim
      | nil =>
        simp only [differingNone] at hn
        exact (hn (by simp only [Nat.add_zero]; exact differingNone_mono _ _ _ _ _ _ (by simp))).elim
    | succ j =>
      simp only [List.getElem?_cons_succ] at hB
      simp only [differingNone] at hn
      cases xs with
      | cons A rest =>
        have := differingNone_cover Γ Δ (i + 1) rest _ j B hB (by rw [Nat.add_right_comm]; simpa [Nat.add_assoc] using hn)
        simpa using this
      | nil =>
        have := differingNone_cover Γ Δ (i + 1) [] _ j B hB (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hn)
        simp at this

/-- **`differing` over a mapping leaves out only slots of the same type**:
a target slot `i + j` outside it reads, at the source slot `ss[j]` (or 0),
the target's type. -/
theorem differingSome_cover (Γ : List (Ty ι)) :
    ∀ (Δ : List (Ty ι)) i ss out j B, Δ[j]? = some B → (i + j, ss[j]?.getD 0) ∉ differingSome Γ Δ i ss out →
      Γ[ss[j]?.getD 0]? = some B
  | [], _, _, _, j, B, hB, _ => by simp at hB
  | B' :: Δ, i, ss, out, j, B, hB, hn => by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hB
      subst hB
      cases ss with
      | cons s rest =>
        simp only [differingSome] at hn
        simp only [List.getElem?_cons_zero, Option.getD_some, Nat.add_zero] at hn ⊢
        cases hA : Γ[s]? with
        | none =>
          have hA' : Γ.toArray[s]? = none := by simpa using hA
          exact (hn (by exact differingSome_mono _ _ _ _ _ _ (by simp [hA']))).elim
        | some A =>
          have hA' : Γ.toArray[s]? = some A := by simpa using hA
          by_cases hs : same A B'
          · rw [same_eq_beq, beq_iff_eq] at hs
            rw [hs]
          · exact (hn (by exact differingSome_mono _ _ _ _ _ _ (by simp [hA', hs]))).elim
      | nil =>
        simp only [differingSome] at hn
        exact (hn (by simp only [Nat.add_zero]; exact differingSome_mono _ _ _ _ _ _ (by simp))).elim
    | succ j =>
      simp only [List.getElem?_cons_succ] at hB
      simp only [differingSome] at hn
      cases ss with
      | cons s rest =>
        exact differingSome_cover Γ Δ (i + 1) rest _ j B hB (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hn)
      | nil =>
        have := differingSome_cover Γ Δ (i + 1) [] _ j B hB (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hn)
        simpa using this

theorem differingNone_forIn (Γ : List (Ty ι)) : ∀ (Δ : List (Ty ι)) (out : List (Nat × Nat)) (i : Nat) (xs : List (Ty ι)),
    (forIn (m := Id) Δ (out, i, xs) fun B __s =>
        match __s.snd.snd with
        | A :: rest =>
          if (!same A B) = true then
            pure (ForInStep.yield ((__s.snd.fst, __s.snd.fst) :: __s.fst, __s.snd.fst + 1, rest))
          else pure (ForInStep.yield (__s.fst, __s.snd.fst + 1, rest))
        | [] => pure (ForInStep.yield ((__s.snd.fst, __s.snd.fst) :: __s.fst, __s.snd.fst + 1, __s.snd.snd))).fst =
      differingNone Γ Δ i xs out
  | [], _, _, _ => rfl
  | B :: Δ, out, i, xs => by
    cases xs with
    | cons A rest =>
      simp only [List.forIn_cons, differingNone]
      split <;> exact differingNone_forIn Γ Δ _ _ _
    | nil => simp only [List.forIn_cons, differingNone]; exact differingNone_forIn Γ Δ _ _ _

theorem differingSome_forIn (Γ : List (Ty ι)) : ∀ (Δ : List (Ty ι)) (out : List (Nat × Nat)) (i : Nat) (ss : List Nat),
    (forIn (m := Id) Δ (out, i, ss) fun B __s =>
        match __s.snd.snd with
        | s :: rest =>
          match Γ.toArray[s]? with
          | some A =>
            if (!same A B) = true then pure (ForInStep.yield ((__s.snd.fst, s) :: __s.fst, __s.snd.fst + 1, rest))
            else pure (ForInStep.yield (__s.fst, __s.snd.fst + 1, rest))
          | none => pure (ForInStep.yield ((__s.snd.fst, s) :: __s.fst, __s.snd.fst + 1, rest))
        | [] => pure (ForInStep.yield ((__s.snd.fst, 0) :: __s.fst, __s.snd.fst + 1, __s.snd.snd))).fst =
      differingSome Γ Δ i ss out
  | [], _, _, _ => rfl
  | B :: Δ, out, i, ss => by
    cases ss with
    | cons s rest =>
      simp only [List.forIn_cons, differingSome]
      split <;> (try split) <;> exact differingSome_forIn Γ Δ _ _ _
    | nil => simp only [List.forIn_cons, differingSome]; exact differingSome_forIn Γ Δ _ _ _

/-- `differing` is its loops. -/
theorem differing_eq (Γ Δ : List (Ty ι)) (m : PointClaims.Mapping) :
    differing Γ Δ m = match m with
      | none => differingNone Γ Δ 0 Γ []
      | some slots => differingSome Γ Δ 0 slots [] := by
  unfold differing
  cases m with
  | none => exact differingNone_forIn Γ Δ [] 0 Γ
  | some slots => exact differingSome_forIn Γ Δ [] 0 slots

/-- **`differing` leaves out only slots of the same type**: a target slot
`i` outside it reads, at the source slot the mapping names, the target's
type. -/
theorem differing_cover (Γ Δ : List (Ty ι)) (m : PointClaims.Mapping) {i : Nat} {B : Ty ι} (hB : Δ[i]? = some B)
    (hn : (i, PointClaims.slot m i) ∉ differing Γ Δ m) : Γ[PointClaims.slot m i]? = some B := by
  rw [differing_eq] at hn
  cases m with
  | none =>
    simp only [PointClaims.slot] at hn ⊢
    exact differingNone_cover Γ Δ 0 Γ [] i B hB (by simpa using hn)
  | some slots =>
    simp only [PointClaims.slot] at hn ⊢
    exact differingSome_cover Γ Δ 0 slots [] i B hB (by simpa using hn)

end Differing

section Folds
variable {α β : Type}

/-- A fold whose flag, once false, stays false: where it ends true, it
started true and each step's own premise held. -/
theorem foldl_flag {P : β → Prop} (f : Bool × α → β → Bool × α)
    (hf : ∀ acc x, (f acc x).1 = true → acc.1 = true ∧ P x) :
    ∀ (l : List β) (acc : Bool × α), (l.foldl f acc).1 = true → acc.1 = true ∧ ∀ x ∈ l, P x
  | [], _, h => ⟨h, fun _ hx => by cases hx⟩
  | x :: l, acc, h => by
    obtain ⟨h1, hl⟩ := foldl_flag f hf l (f acc x) h
    obtain ⟨h0, hx⟩ := hf acc x h1
    exact ⟨h0, fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hl y hy⟩

end Folds

section Subtypes
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- **What `diffSubtypes` passing gives**: each named pair `(i, s)` reads
a source type at `s` and a target type at `i`, the first below the second
by an answer `subtypeUsing` accepts. -/
theorem diffSubtypes_pairs {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ Δ : List (Ty ι)}
    {diff : List (Nat × Nat)} {observed : Option BranchRefinement.Observation} {answers : Answered G}
    (h : (diffSubtypes G images Γ Δ diff observed answers).1 = true) :
    ∀ p ∈ diff, ∃ A B a, Γ[p.2]? = some A ∧ Δ[p.1]? = some B ∧
      ((subtypeUsing G images A B a).1).value.isSome = true := by
  unfold diffSubtypes at h
  refine (foldl_flag _ (fun acc x hx => ?_) diff _ h).2
  obtain ⟨i, s⟩ := x
  simp only at hx ⊢
  split at hx
  · rename_i A B hA hB
    split at hx
    · simp only [Bool.and_eq_true] at hx
      exact ⟨hx.1, A, B, acc.2, hA, hB, hx.2⟩
    · cases hx
  · cases hx

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- A fold pushing, at each slot `s`, the slot's refined type `A'` or its
type in `Γ`: each entry of the result is the refined context's or `Γ`'s at
its slot. -/
theorem mixed_fold {γ : Type} (Γ Γ' : List (Ty ι)) (f : Array (Ty ι) × γ → Ty ι × Nat → Array (Ty ι) × γ)
    (hf : ∀ acc A' s, ∃ b : Bool, (f acc (A', s)).1 = acc.1.push (if b then A' else (Γ[s]?).getD A')) :
    ∀ (l : List (Ty ι)) (k : Nat) (acc : Array (Ty ι) × γ), acc.1.size = k →
      (∀ (j : Nat) (X : Ty ι), acc.1[j]? = some X → Γ'[j]? = some X ∨ Γ[j]? = some X) →
      (∀ (j : Nat) (X : Ty ι), l[j]? = some X → Γ'[k + j]? = some X) →
      ∀ (j : Nat) (X : Ty ι), ((l.zipIdx k).foldl f acc).1[j]? = some X → Γ'[j]? = some X ∨ Γ[j]? = some X
  | [], _, acc, _, hacc, _ => by simpa using hacc
  | A' :: l, k, acc, hk, hacc, hl => by
    subst hk
    simp only [List.zipIdx_cons, List.foldl_cons]
    obtain ⟨b, hb⟩ := hf acc A' acc.1.size
    refine mixed_fold Γ Γ' f hf l (acc.1.size + 1) _ (by rw [hb]; simp) (fun j X hj => ?_) (fun j X hj => ?_)
    · rw [hb, Array.getElem?_push] at hj
      split at hj
      · rename_i hjk
        subst hjk
        have hA' : Γ'[acc.1.size]? = some A' := by simpa using hl 0 A' rfl
        cases b
        · cases hg : Γ[acc.1.size]? with
          | none =>
            simp only [hg, Option.getD_none, Bool.false_eq_true, if_false, Option.some.injEq] at hj
            exact .inl (hj ▸ hA')
          | some Y =>
            simp only [hg, Option.getD_some, Bool.false_eq_true, if_false, Option.some.injEq] at hj
            exact .inr (hj ▸ hg.symm ▸ rfl)
        · simp only [if_true, Option.some.injEq] at hj; exact .inl (hj ▸ hA')
      · exact hacc j X hj
    · have := hl (j + 1) X (by simpa using hj)
      rw [Nat.add_assoc, Nat.add_comm 1 j]; exact this

end Subtypes

end Verification.TolerantFrames
