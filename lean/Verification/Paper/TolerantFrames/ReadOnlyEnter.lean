import Verification.Paper.TolerantFrames.ReadOnlyPending
import Verification.Paper.TolerantFrames.ReadOnlyRealize
import Verification.Paper.TolerantFrames.ReadOnlyIsolate

/-! # Read-only handles: a call of the component in its context

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Certificates").

- **A context steps at its hole** (`EvalCtx.raises_hole`,
  `EvalCtx.step_hole`): a context around a term that is not a value
  throws only where the term does, and steps only where the term steps or
  throws.
- **A value in a context of a reached term enters no run**
  (`ctx_val_tags`): its path has the tags of the context's own, as the
  positions after the hole are free of runs (`wfS`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification HeapObservations

/-! ## A context steps at its hole -/

theorem set_get_ne {xs : List Tm} {i j : Nat} {a v : Tm} (hij : j ≠ i) (h : (xs.set i a)[j]? = some v) :
    xs[j]? = some v := by
  rwa [List.getElem?_set_ne (Ne.symm hij)] at h

/-- **The position of a list a context's hole is at**: the first term of
the list that is not a value. -/
theorem list_hole {K₀ : Tm → Tm} {args : List Tm} {i j : Nat} {u a : Tm} (hK : EvalCtx K₀) (hu : isVal u = false)
    (hi : i < args.length) (hpre : ∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true)
    (hj : (args.set i (K₀ u))[j]? = some a)
    (hpj : ∀ k, k < j → ∀ w, (args.set i (K₀ u))[k]? = some w → isVal w = true) (ha : isVal a = false) :
    j = i ∧ a = K₀ u := by
  by_cases hji : j = i
  · subst hji
    simp only [List.getElem?_set_self hi, Option.some.injEq] at hj
    exact ⟨rfl, hj.symm⟩
  · rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
    · have := hpre j hlt a (set_get_ne hji hj)
      simp [this] at ha
    · have := hpj i hgt (K₀ u) (by simp [hi])
      simp [hK.not_val hu] at this

/-- **A context throws only where its hole does** (proved, by induction on
the context). -/
theorem _root_.Verification.HeapObservations.EvalCtx.raises_hole {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {u w : Tm}, isVal u = false → Raises (K u) w → Raises u w := by
  induction hK with
  | hole => exact fun _ h => h
  | @callArg K₀ f r args i hf hr hi hpre hK ih =>
    intro u w hu h
    cases h with
    | callL h' => exact absurd (raises_not_val h') (by simp [hf])
    | callRecv _ h' => exact absurd (raises_not_val h') (by simp [hr])
    | callArg _ _ hj hpj h' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (raises_not_val h')
      exact ih hu h'
  | @constructArg K₀ f args i hf hi hpre hK ih =>
    intro u w hu h
    cases h with
    | constructL h' => exact absurd (raises_not_val h') (by simp [hf])
    | constructArg _ hj hpj h' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (raises_not_val h')
      exact ih hu h'
  | @makeArg K₀ cc ns inits i hi hpre hK ih =>
    intro u w hu h
    cases h with
    | makeArg hj hpj h' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (raises_not_val h')
      exact ih hu h'
  | @arrArg K₀ inits i hi hpre hK ih =>
    intro u w hu h
    cases h with
    | arrArg hj hpj h' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (raises_not_val h')
      exact ih hu h'
  | frameC => intro u w hu h; cases h
  | _ =>
    rename_i hK ih
    intro u w hu h
    have hn := hK.not_val hu
    cases h <;> first
      | (exact ih hu ‹_›)
      | (exfalso; have := raises_not_val ‹Raises _ _›; simp_all; done)
      | (exfalso; simp_all; done)

theorem set_mem {xs : List Tm} {i : Nat} {x : Tm} (hi : i < xs.length) : x ∈ xs.set i x :=
  List.mem_of_getElem? (List.getElem?_set_self hi)

/-- **A list holding a spread at the hole's position**: the hole's term is
that spread. -/
theorem list_spread {args pre post : List Tm} {i : Nat} {x s : Tm} (hi : i < args.length)
    (hpre : ∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) (hx : isVal x = false)
    (he : args.set i x = pre ++ .spread s :: post) (hp : ∀ v ∈ pre, isVal v = true) : x = .spread s := by
  have hlen : (args.set i x).length = args.length := List.length_set
  rcases Nat.lt_trichotomy i pre.length with hlt | heq | hgt
  · have h1 : (args.set i x)[i]? = some x := by simp [hi]
    rw [he, List.getElem?_append_left hlt] at h1
    have := hp x (List.mem_of_getElem? h1)
    simp [this] at hx
  · have h1 : (args.set i x)[i]? = some x := by simp [hi]
    rw [he, List.getElem?_append_right (by omega), heq, Nat.sub_self] at h1
    simpa using h1.symm
  · have h1 : (args.set i x)[pre.length]? = some (.spread s) := by
      rw [he, List.getElem?_append_right (by omega), Nat.sub_self]; rfl
    rw [List.getElem?_set_ne (by omega)] at h1
    have := hpre _ hgt _ h1
    simp at this

/-- A context around a term that is no spread is a spread only of a term
that is not a value (proved). -/
theorem ctx_spread {K : Tm → Tm} (hK : EvalCtx K) {u s : Tm} (hu : isVal u = false) (hsp : ∀ a, u ≠ .spread a)
    (he : K u = .spread s) : isVal s = false := by
  cases hK with
  | hole => exact absurd he (hsp s)
  | spreadC hK' => cases he; exact hK'.not_val hu
  | _ => cases he

/-- **A context steps only where its hole steps or throws** (proved, by
induction on the context): around a term that is no value and no spread. -/
theorem _root_.Verification.HeapObservations.EvalCtx.step_hole {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {h h' : Heap} {u t' : Tm}, isVal u = false → (∀ a, u ≠ .spread a) → Step h (K u) h' t' →
      (∃ h₂ u', Step h u h₂ u') ∨ ∃ w, Raises u w := by
  induction hK with
  | hole => exact fun _ _ hs => .inl ⟨_, _, hs⟩
  | @callArg K₀ f r args i hf hr hi hpre hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    cases hs with
    | callL hs' => exact absurd hs' (value_no_step hf)
    | callRecv _ hs' => exact absurd hs' (value_no_step hr)
    | callArg _ _ hj hpj hs' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (not_val_of_step hs')
      exact ih hu hsp hs'
    | callSpread _ _ he hp _ =>
      have := ctx_spread hK hu hsp (list_spread hi hpre hn he hp); simp at this
    | callBound _ ha => have := ha _ (set_mem hi); simp [hn] at this
    | callGraph _ ha => have := ha _ (set_mem hi); simp [hn] at this
  | @constructArg K₀ f args i hf hi hpre hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    cases hs with
    | constructL hs' => exact absurd hs' (value_no_step hf)
    | constructArg _ hj hpj hs' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (not_val_of_step hs')
      exact ih hu hsp hs'
    | constructSpread _ he hp _ =>
      have := ctx_spread hK hu hsp (list_spread hi hpre hn he hp); simp at this
    | constructGraph ha => have := ha _ (set_mem hi); simp [hn] at this
  | @makeArg K₀ cc ns inits i hi hpre hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    cases hs with
    | makeArg hj hpj hs' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (not_val_of_step hs')
      exact ih hu hsp hs'
    | makeFields hv _ => have := hv _ (set_mem hi); simp [hn] at this
  | @arrArg K₀ inits i hi hpre hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    cases hs with
    | arrArg hj hpj hs' =>
      obtain ⟨rfl, rfl⟩ := list_hole hK hu hi hpre hj hpj (not_val_of_step hs')
      exact ih hu hsp hs'
    | arrSpread he hp _ =>
      have := ctx_spread hK hu hsp (list_spread hi hpre hn he hp); simp at this
    | arrAlloc hv _ => have := hv _ (set_mem hi); simp [hn] at this
    | arrAllocThrow hv _ => have := hv _ (set_mem hi); simp [hn] at this
  | @frameC K₀ E Kc L d k x comp hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs with
    | frameC hs' => subst hy; exact ih hu hsp hs'
    | frameHandle hr => subst hy; exact .inr ⟨_, hK.raises_hole hu hr⟩
    | frameRaise hr => subst hy; exact .inr ⟨_, hK.raises_hole hu hr⟩
    | _ => exfalso; simp_all
  | @callL K₀ r args hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @callRecv K₀ f args hf hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @constructL K₀ args hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @letC K₀ b hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @spreadC K₀ hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @readC K₀ f hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @indexC1 K₀ key hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @indexC2 K₀ a ha hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @writeC1 K₀ f b hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @writeC2 K₀ f a ha hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @testC K₀ k hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @iteC K₀ a b hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @arithC1 K₀ op b hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @arithC2 K₀ op a ha hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @elemC1 K₀ i hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @elemC2 K₀ a ha hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @setC1 K₀ i v hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @setC2 K₀ a v ha hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @setC3 K₀ a i ha hi hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @lenC K₀ hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @throwC K₀ hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @mergeC1 K₀ d b hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @mergeC2 K₀ d a ha hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @makeKeyC1 K₀ a hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)
  | @makeKeyC2 K₀ k hk hK ih =>
    intro h h' u t' hu hsp hs
    have hn := hK.not_val hu
    dsimp only at hs
    obtain ⟨y, hy⟩ : ∃ y, K₀ u = y := ⟨_, rfl⟩
    rw [hy] at hs hn
    cases hs <;> first
      | (subst hy; exact ih hu hsp ‹_›)
      | (exfalso; simp_all; done)
      | (exfalso; have := not_val_of_step ‹Step _ _ _ _›; simp_all; done)
      | (exfalso; have := propertyKey_val ‹propertyKey _ = some _›; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).1; simp_all; done)
      | (exfalso; have := (binop_result ‹binop _ _ _ = some _›).2.1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).1; simp_all; done)
      | (exfalso; have := (binopThrows_values ‹binopThrows _ _ _ = true›).2; simp_all; done)

/-! ## A value in a context enters no run -/

/-- A path of one entry is tagged with its top segment's tag (proved). -/
theorem tags_one {c : ComponentTag} {t : Tm} (h : (path rl c nk t).length = 1) : (path rl c nk t).map Prod.fst = [c] := by
  obtain ⟨i, s, hl⟩ := path_last t c nk
  have hi : i = [] := by have := congrArg List.length hl; rw [h] at this; simpa using this
  subst hi; rw [hl]; rfl

/-- **One layer of a context** (proved): a layer whose path around a term
that is no value is the term's, wrapped, and whose path around a value is
its top segment, keeps the tags of a hole's value and of a variable equal. -/
theorem layer_tags {K₀ L : Tm → Tm} (hK : EvalCtx K₀) {v : Tm} {c : ComponentTag}
    (hP : ∀ t, isVal t = false → (path rl c nk (L t)).map Prod.fst = (path rl c nk t).map Prod.fst)
    (ih : (path rl c nk (K₀ v)).map Prod.fst = (path rl c nk (K₀ (.var 0))).map Prod.fst)
    (hQ : isVal (K₀ v) = true → (path rl c nk (L (K₀ v))).length = 1) :
    (path rl c nk (L (K₀ v))).map Prod.fst = (path rl c nk (L (K₀ (.var 0)))).map Prod.fst := by
  have hn0 : isVal (K₀ (.var 0)) = false := hK.not_val rfl
  rw [hP _ hn0]
  cases hv : isVal (K₀ v)
  · rw [hP _ hv, ih]
  · rw [tags_one (hQ hv), ← ih, path_val hv]; rfl

theorem wfArgsS_at_val : ∀ {xs : List Tm} {i : Nat} {a : Tm}, wfArgsS xs = true → xs[i]? = some a →
    (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → isVal a = true → free false a = true
  | [], _, _, _, h, _, _ => by simp at h
  | b :: bs, 0, a, hw, h, _, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [wfArgsS, ha, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact hw.1
  | b :: bs, i + 1, a, hw, h, hpre, ha => by
    have hb : isVal b = true := hpre 0 (Nat.succ_pos _) b rfl
    simp only [wfArgsS, hb, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hw
    exact wfArgsS_at_val hw.2 (by simpa using h) (fun j hj w hw' => hpre (j + 1) (by omega) w (by simpa using hw')) ha

/-- **The positions of a list around a value at the hole are free of runs**
(proved): those of the list around a term that is no value, and the value. -/
theorem list_free {args : List Tm} {i : Nat} {x y : Tm} (hi : i < args.length)
    (hpre : ∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) (hx : isVal x = false)
    (hwx : wfArgsS (args.set i x) = true) (hy : isVal y = true) (hwy : wfArgsS (args.set i y) = true) :
    ∀ a ∈ args.set i y, free false a = true := by
  obtain ⟨-, hoth⟩ := wfArgsS_split hwx (List.getElem?_set_self hi) (set_pre hpre) hx
  have hyf := wfArgsS_at_val hwy (List.getElem?_set_self hi) (set_pre hpre) hy
  intro a ha
  obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
  by_cases hji : j = i
  · subst hji; rw [List.getElem?_set_self hi] at hj; cases hj; exact hyf
  · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
    exact hoth j a (by rw [List.getElem?_set_ne (Ne.symm hji)]; exact hj) hji

/-- **A value at the hole of a context of a reached term enters no run**
(proved, by induction on the context): where the context around a term
that is no value is a reached term, so its positions after the hole are
free of runs, the path around a value has the tags of the path around a
variable, the context's own. -/
theorem ctx_val_tags {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {u v : Tm} (c : ComponentTag) (nk : Bool), isVal u = false → wfS (K u) = true → isVal v = true → wfS (K v) = true →
      (path rl c nk (K v)).map Prod.fst = (path rl c nk (K (.var 0))).map Prod.fst := by
  induction hK with
  | hole => intro u v c nk _ _ hv _; simp [path_val hv, path]
  | @frameC K₀ E Kc L d k x comp hK ih =>
    intro u v c nk hu hwu hv hwv
    simp only [wfS, Bool.and_eq_true] at hwu hwv
    simp only [path, List.map_append, wrap_fst, ih _ _ hu hwu.2 hv hwv.2]
  | @callL K₀ r args hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.invoke s r args) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @callRecv K₀ f args hf hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.invoke f s args) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @constructL K₀ args hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.construct s args) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @letC K₀ b hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.letE s b) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @spreadC K₀ hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.spread s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @readC K₀ f hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.readAt f s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @indexC1 K₀ key hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.indexAt s key) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @indexC2 K₀ a ha hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.indexAt a s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @writeC1 K₀ f b hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.writeAt f s b) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @writeC2 K₀ f a ha hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.writeAt f a s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @testC K₀ k hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.test k s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @iteC K₀ a b hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.ite s a b) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @arithC1 K₀ op b hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.arith op s b) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @arithC2 K₀ op a ha hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.arith op a s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @elemC1 K₀ i hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.elemAt s i) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @elemC2 K₀ a ha hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.elemAt a s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @setC1 K₀ i v hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.setElem s i v) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @setC2 K₀ a v ha hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.setElem a s v) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @setC3 K₀ a i ha hi hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.setElem a i s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @lenC K₀ hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.lenOf s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @throwC K₀ hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.throw s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @mergeC1 K₀ d b hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.merge d s b) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @mergeC2 K₀ d a ha hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.merge d a s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @makeKeyC1 K₀ a hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.makeKey s a) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @makeKeyC2 K₀ k hk hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hwu' : wfS (K₀ u₁) = true := by simp_all [wfS]
    have hwv' : wfS (K₀ v₁) = true := by
      cases hv' : isVal (K₀ v₁)
      · simp_all [wfS]
      · rw [wfS_val hv']
        simp only [wfS, hv', ↓reduceIte, Bool.true_eq_false] at hwv
        (repeat' split at hwv) <;> simp_all
    refine layer_tags (L := fun s => Tm.makeKey k s) hK (fun t ht => by simp [path, wrap_fst, *]) (ih c nk hu hwu' hv hwv') (fun hv' => ?_)
    first
      | (simp [path, *]; done)
      | exact nr_path _ (by
          simp only [wfS, hv', hn, ↓reduceIte, Bool.and_eq_true, Bool.true_eq_false] at hwv hwu
          (repeat' split at hwv) <;> simp_all [free]) c nk
  | @callArg K₀ f r args i hf hr hi hpre hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    simp only [wfS, hf, hr, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hwu hwv
    have hwa := wfArgsS_split (hwu.2) (List.getElem?_set_self hi) (set_pre hpre) hn
    refine layer_tags (L := fun s => Tm.invoke f r (args.set i s)) hK
      (fun t ht => by simp only [path, *, Bool.true_eq_false, ↓reduceIte]; rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre ht, wrap_fst])
      (ih c nk hu hwa.1 hv ?_) (fun hv' => nr_path _ ?_ c nk)
    · cases hv' : isVal (K₀ v₁)
      · exact (wfArgsS_split hwv.2 (List.getElem?_set_self hi) (set_pre hpre) hv').1
      · rw [wfS_val hv']; exact wfArgsS_at_val hwv.2 (List.getElem?_set_self hi) (set_pre hpre) hv'
    · have hl := list_free hi hpre hn hwu.2 hv' hwv.2
      simp_all [free]
  | @constructArg K₀ f args i hf hi hpre hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    simp only [wfS, hf, Bool.true_eq_false, ↓reduceIte, Bool.and_eq_true] at hwu hwv
    have hwa := wfArgsS_split (hwu.2) (List.getElem?_set_self hi) (set_pre hpre) hn
    refine layer_tags (L := fun s => Tm.construct f (args.set i s)) hK
      (fun t ht => by simp only [path, *, Bool.true_eq_false, ↓reduceIte]; rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre ht, wrap_fst])
      (ih c nk hu hwa.1 hv ?_) (fun hv' => nr_path _ ?_ c nk)
    · cases hv' : isVal (K₀ v₁)
      · exact (wfArgsS_split hwv.2 (List.getElem?_set_self hi) (set_pre hpre) hv').1
      · rw [wfS_val hv']; exact wfArgsS_at_val hwv.2 (List.getElem?_set_self hi) (set_pre hpre) hv'
    · have hl := list_free hi hpre hn hwu.2 hv' hwv.2
      simp_all [free]
  | @arrArg K₀ inits i hi hpre hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    simp only [wfS] at hwu hwv
    have hwa := wfArgsS_split hwu (List.getElem?_set_self hi) (set_pre hpre) hn
    refine layer_tags (L := fun s => Tm.arrLit (inits.set i s)) hK
      (fun t ht => by simp only [path, *]; rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre ht, wrap_fst])
      (ih c nk hu hwa.1 hv ?_) (fun hv' => nr_path _ ?_ c nk)
    · cases hv' : isVal (K₀ v₁)
      · exact (wfArgsS_split hwv (List.getElem?_set_self hi) (set_pre hpre) hv').1
      · rw [wfS_val hv']; exact wfArgsS_at_val hwv (List.getElem?_set_self hi) (set_pre hpre) hv'
    · have hl := list_free hi hpre hn hwu hv' hwv
      simp_all [free]
  | @makeArg K₀ cc ns inits i hi hpre hK ih =>
    intro u₁ v₁ c nk hu hwu hv hwv
    dsimp only at hwu hwv ⊢
    have hn := hK.not_val hu
    have hcode : ∀ xs, wfS (.makeAt cc ns xs) = true → wfArgsS xs = true := by
      intro xs hx; cases cc <;> simp only [wfS, Bool.and_eq_true] at hx <;> first | exact hx | exact hx.2
    have hwu₁ := hcode _ hwu
    have hwv₁ := hcode _ hwv
    have hwa := wfArgsS_split hwu₁ (List.getElem?_set_self hi) (set_pre hpre) hn
    refine layer_tags (L := fun s => Tm.makeAt cc ns (inits.set i s)) hK
      (fun t ht => by simp only [path]; rw [pathArgs_set _ (List.getElem?_eq_getElem hi) hpre ht, wrap_fst])
      (ih c nk hu hwa.1 hv ?_) (fun hv' => ?_)
    · cases hv' : isVal (K₀ v₁)
      · exact (wfArgsS_split hwv₁ (List.getElem?_set_self hi) (set_pre hpre) hv').1
      · rw [wfS_val hv']; exact wfArgsS_at_val hwv₁ (List.getElem?_set_self hi) (set_pre hpre) hv'
    · have hl := list_free hi hpre hn hwu₁ hv' hwv₁
      exact nr_path _ (by clear ih hcode hwa; cases cc <;> simp_all [wfS, free]) c nk

end Verification.TolerantFrames.ReadOnly
