import Verification.Paper.TolerantFrames.ReadOnlySegment

/-! # Read-only handles: two codes that agree on a body

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Realization", `prologue_sim` and
`chk_sim`). A receiverless module function's realized code is its
request's tables extended past the body by a prologue node. Two codes
that agree on the nodes below `n`, whose nodes below `n` target only labels
below `n`, run the same steps from a run at a label below `n`:

- **Agreement on a body** (`BodyAgree A B n`): the same node expression,
  continuation and handler at every label below `n`, each target of those
  nodes below `n` (`ContBelow`, `HandlerBelow`).
- **Related runs** (`TabRel A B n`): a run of `A` at a label below `n` and
  the same run of `B`; a frame of `A` at a node below `n` and the same frame
  of `B`, its running term the same; or the same term.
- **The simulation** (`tabRel_step`, `tabRel_steps`): a step of the first
  is the same step of the second, on the same heap, to related terms; both
  ways (`TabRel.symm`, `BodyAgree.symm`), so where one takes no step the other
  takes none (`tabRel_stuck`).
- **The site of a step** (`stepSite_tabRel`, the site part of `chk_sim`):
  in any context, related runs allocate at the same site where the two
  codes' proposals allocate at the same sites at every node key of the
  body.
- **The crossings out of a step** (`vals_tabRel`, `vals_ctx`,
  `actualXs_congr`, the crossings-out part of `chk_sim`): in any context,
  related runs hold the same values where the two codes' node expressions
  do, so a step of related runs crosses out the same values. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification HeapObservations ControlFlow

/-- **A continuation's targets are below `n`.** -/
def ContBelow (n : Nat) : Continuation → Prop
  | .ret => True
  | .bind t | .effect t => t.label < n
  | .branch y m | .branchBind y m | .tagBind _ y m => y.label < n ∧ m.label < n

/-- **A handler's target is below `n`.** -/
def HandlerBelow (n : Nat) (x : Option Target) : Prop := ∀ t, x = some t → t.label < n

/-- **Two codes agree on a body of `n` nodes**: the same node expression,
continuation and handler at each label below `n`, whose targets are below
`n`. -/
def BodyAgree (A B : Code) (n : Nat) : Prop :=
  (∀ l, l < n → A.1[l]? = B.1[l]? ∧ A.2[l]? = B.2[l]?) ∧
    ∀ l, l < n → ∀ k x, B.2[l]? = some (k, x) → ContBelow n k ∧ HandlerBelow n x

theorem BodyAgree.symm {A B : Code} {n : Nat} (h : BodyAgree A B n) : BodyAgree B A n :=
  ⟨fun l hl => ⟨(h.1 l hl).1.symm, (h.1 l hl).2.symm⟩,
    fun l hl k x hk => h.2 l hl k x (by rw [← (h.1 l hl).2]; exact hk)⟩

/-- **Related runs of two codes**: a run of `A` at a label below `n` and the
same run of `B`; a frame of `A` at a node below `n` and the same frame of
`B`; or the same term. -/
inductive TabRel (A B : Code) (n : Nat) : Tm → Tm → Prop where
  | goto {l : Nat} {L : List Tm} {d : Tm} {c : ComponentTag} : l < n →
      TabRel A B n (.goto A.1 A.2 l L d c) (.goto B.1 B.2 l L d c)
  | frame {l : Nat} {u : Tm} {L : List Tm} {d : Tm} {k : Continuation} {x : Option Target} {c : ComponentTag} :
      l < n → B.2[l]? = some (k, x) → TabRel A B n (.frame A.1 A.2 u L d k x c) (.frame B.1 B.2 u L d k x c)
  | same {t : Tm} : TabRel A B n t t

/-- Related runs, the other way (proved). -/
theorem TabRel.symm {A B : Code} {n : Nat} (hA : BodyAgree A B n) {t₁ t₂ : Tm} (h : TabRel A B n t₁ t₂) :
    TabRel B A n t₂ t₁ := by
  cases h with
  | goto hl => exact .goto hl
  | frame hl hk => exact .frame hl (by rw [(hA.1 _ hl).2]; exact hk)
  | same => exact .same

/-- A run at a target below `n` is related (proved). -/
theorem tabRel_goto {A B : Code} {n : Nat} {t : Target} (ht : t.label < n) (L : List Tm) (d : Tm)
    (c : ComponentTag) : TabRel A B n (.goto A.1 A.2 t.label L d c) (.goto B.1 B.2 t.label L d c) :=
  .goto ht

/-- **A step of a run is the same step of the related run** (proved, by
cases on the step): entering a node reads the same node expression,
continuation and handler below `n`; a frame's steps run its term, which is
the same, or continue at a target below `n`, or leave the run with the same
value or throw. -/
theorem tabRel_step {A B : Code} {n : Nat} (hA : BodyAgree A B n) {h h' : Heap} {t₁ t₂ t₁' : Tm}
    (hr : TabRel A B n t₁ t₂) (hs : Step h t₁ h' t₁') : ∃ t₂', Step h t₂ h' t₂' ∧ TabRel A B n t₁' t₂' := by
  cases hr with
  | same => exact ⟨t₁', hs, .same⟩
  | @goto l L d c hl =>
    cases hs with
    | gotoEnter he hk =>
      rename_i e k x
      obtain ⟨hE, hK⟩ := hA.1 l hl
      exact ⟨_, .gotoEnter (hE ▸ he) (hK ▸ hk), .frame hl (hK ▸ hk)⟩
  | @frame l u L d k x c hl hk =>
    obtain ⟨hc, hx⟩ := hA.2 l hl k x hk
    cases hs with
    | frameC s => exact ⟨_, .frameC s, .frame hl hk⟩
    | frameRet hv => exact ⟨_, .frameRet hv, .same⟩
    | frameBind hv => exact ⟨_, .frameBind hv, .goto hc⟩
    | frameEffect hv => exact ⟨_, .frameEffect hv, .goto hc⟩
    | frameYes => exact ⟨_, .frameYes, .goto hc.1⟩
    | frameNo => exact ⟨_, .frameNo, .goto hc.2⟩
    | frameYesBind => exact ⟨_, .frameYesBind, .goto hc.1⟩
    | frameNoBind => exact ⟨_, .frameNoBind, .goto hc.2⟩
    | frameTag hv =>
      refine ⟨_, .frameTag hv, .goto ?_⟩
      split
      · exact hc.1
      · exact hc.2
    | frameHandle hr => exact ⟨_, .frameHandle hr, .goto (hx _ rfl)⟩
    | frameRaise hr => exact ⟨_, .frameRaise hr, .same⟩

/-- **Related runs take the same steps** (proved, `tabRel_step` at each
step). -/
theorem tabRel_steps {A B : Code} {n : Nat} (hA : BodyAgree A B n) :
    ∀ {j : Nat} {h h' : Heap} {t₁ t₂ t₁' : Tm}, TabRel A B n t₁ t₂ → Steps j h t₁ h' t₁' →
      ∃ t₂', Steps j h t₂ h' t₂' ∧ TabRel A B n t₁' t₂'
  | 0, _, _, _, _, _, hr, .refl => ⟨_, .refl, hr⟩
  | _ + 1, _, _, _, _, _, hr, .next st hrest => by
    obtain ⟨u, hu, hr'⟩ := tabRel_step hA hr st
    obtain ⟨v, hv, hr''⟩ := tabRel_steps hA hr' hrest
    exact ⟨v, .next hu hv, hr''⟩

/-- **Where one run takes no step the other takes none** (proved,
`tabRel_step` the other way). -/
theorem tabRel_stuck {A B : Code} {n : Nat} (hA : BodyAgree A B n) {h : Heap} {t₁ t₂ : Tm}
    (hr : TabRel A B n t₁ t₂) (hn : ∀ h' t', ¬ Step h t₁ h' t') : ∀ h' t', ¬ Step h t₂ h' t' := by
  intro h' t' hs
  obtain ⟨u, hu, -⟩ := tabRel_step hA.symm (hr.symm hA) hs
  exact hn _ _ hu

/-! ## The site of a step -/

mutual
/-- **The term the next step reduces does not depend on the frame outside**
(proved, by structural induction, following `activeFrame`). -/
theorem activeFrame_snd : ∀ (t : Tm) (c c' : Option FrameKey), (activeFrame c t).2 = (activeFrame c' t).2
  | .invoke f r args, c, c' => by
    simp only [activeFrame]; split
    · exact activeFrame_snd f c c'
    · split
      · exact activeFrame_snd r c c'
      · exact activeArgs_snd args c c' _
  | .construct f args, c, c' => by
    simp only [activeFrame]; split
    · exact activeFrame_snd f c c'
    · exact activeArgs_snd args c c' _
  | .letE a b, c, c' => by
    simp only [activeFrame]; split
    · exact activeFrame_snd a c c'
    · rfl
  | .makeAt cc ns xs, c, c' => by simp only [activeFrame]; exact activeArgs_snd xs c c' _
  | .readAt fd a, c, c' | .test fd a, c, c' | .lenOf a, c, c' | .spread a, c, c' | .throw a, c, c'
  | .ite a fd _, c, c' => by
    simp only [activeFrame]; split
    · exact activeFrame_snd a c c'
    · rfl
  | .indexAt a b, c, c' | .writeAt _ a b, c, c' | .arith _ a b, c, c' | .elemAt a b, c, c' | .merge _ a b, c, c'
  | .makeKey a b, c, c' => by
    simp only [activeFrame]; split
    · exact activeFrame_snd a c c'
    · split
      · exact activeFrame_snd b c c'
      · rfl
  | .setElem a i v, c, c' => by
    simp only [activeFrame]; split
    · exact activeFrame_snd a c c'
    · split
      · exact activeFrame_snd i c c'
      · split
        · exact activeFrame_snd v c c'
        · rfl
  | .arrLit xs, c, c' => by simp only [activeFrame]; exact activeArgs_snd xs c c' _
  | .frame .., _, _ => by simp only [activeFrame]
  | .var _, _, _ | .nul, _, _ | .undef, _, _ | .tru, _, _ | .fls, _, _ | .num _, _, _ | .str _, _, _
  | .bigint _, _, _ | .sym _, _, _ | .objAt .., _, _ | .arr _, _, _ | .viewSpine .., _, _ | .goto .., _, _ => by
    simp only [activeFrame]
termination_by structural t => t

/-- The term the next step reduces through a list (proved). -/
theorem activeArgs_snd : ∀ (xs : List Tm) (c c' : Option FrameKey) (t : Tm),
    (activeArgs c t xs).2 = (activeArgs c' t xs).2
  | [], _, _, _ => by simp only [activeArgs]
  | a :: as, c, c', t => by
    simp only [activeArgs]; split
    · exact activeFrame_snd a c c'
    · exact activeArgs_snd as c c' t
termination_by structural xs => xs
end

section Site
variable {P : Package} {Fl : Flow P}

/-- **Related runs allocate at the same site in any context** (proved,
`activeFrame_ctx`, `activeFrame_innermost`, `activeFrame_redex`; the site
part of `chk_sim`): where the two codes' entry proposals allocate at the
same sites at each node key of the body, a step of the related terms in a
context reads the same site. A frame's site is read at its innermost frame
inside the frame's term, the same in both, or at the frame itself, whose
node key is the body's. -/
theorem stepSite_tabRel {A B : Code} {n : Nat} {K : Tm → Tm} (hK : EvalCtx K) {t₁ t₂ : Tm}
    (hr : TabRel A B n t₁ t₂)
    (hal : ∀ comp l, l < n → ∀ kx, B.2[l]? = some kx →
      allocOf Fl (some ((A, comp), kx)) = allocOf Fl (some ((B, comp), kx))) :
    stepSite Fl none (K t₁) = stepSite Fl none (K t₂) := by
  cases hr with
  | same => rfl
  | @goto l L d c hl =>
    obtain ⟨c', hc'⟩ := activeFrame_ctx hK none
    simp only [stepSite, hc' (.goto A.1 A.2 l L d c) rfl, hc' (.goto B.1 B.2 l L d c) rfl]
    simp [activeFrame]
  | @frame l u L d k x c hl hk =>
    obtain ⟨c', hc'⟩ := activeFrame_ctx hK none
    simp only [stepSite, hc' (.frame A.1 A.2 u L d k x c) rfl, hc' (.frame B.1 B.2 u L d k x c) rfl]
    simp only [activeFrame]
    have hA := (activeFrame_innermost u (some ((A, c), (k, x)))).1
    have hB := (activeFrame_innermost u (some ((B, c), (k, x)))).1
    have hred : (activeFrame (some ((A, c), (k, x))) u).2 = (activeFrame (some ((B, c), (k, x))) u).2 :=
      activeFrame_snd u _ _
    cases hi : (innermost u).bind frameOf with
    | some key =>
      rw [hi] at hA hB
      simp only [Option.some_or] at hA hB
      have he : activeFrame (some ((A, c), (k, x))) u = activeFrame (some ((B, c), (k, x))) u :=
        Prod.ext (hA.trans hB.symm) hred
      rw [he]
    | none =>
      rw [hi] at hA hB
      simp only [Option.none_or] at hA hB
      have hal' := hal c l hl (k, x) hk
      generalize activeFrame (some ((A, c), (k, x))) u = pA at hA hred ⊢
      generalize activeFrame (some ((B, c), (k, x))) u = pB at hB hred ⊢
      obtain ⟨p₁, q₁⟩ := pA
      obtain ⟨p₂, q₂⟩ := pB
      simp only at hA hB hred
      subst hA hB hred
      split <;> simp_all

end Site

/-! ## The crossings of a step -/

section Crossings
variable {ofC : ComponentTag → Bool}

theorem flatMap_set_congr {α β : Type} {f : α → List β} {a b : α} (hab : f a = f b) :
    ∀ (l : List α) (i : Nat), (l.set i a).flatMap f = (l.set i b).flatMap f
  | [], _ => rfl
  | x :: xs, 0 => by simp [hab]
  | x :: xs, i + 1 => by simp [flatMap_set_congr hab xs i]

/-- **Related runs hold the same values** (proved): where the two codes'
node expressions hold the same values, related runs do, their slots,
default and running term being the same. -/
theorem vals_tabRel {A B : Code} {n : Nat} (hv : valsArgs ofC true A.1 = valsArgs ofC true B.1) {t₁ t₂ : Tm}
    (hr : TabRel A B n t₁ t₂) (o : Bool) : vals ofC o t₁ = vals ofC o t₂ := by
  cases hr with
  | same => rfl
  | goto => simp only [vals, hv]
  | frame => simp only [vals, hv]

/-- **A context around terms holding the same values holds the same
values** (proved, by induction on the context). -/
theorem vals_ctx {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {t₁ t₂ : Tm}, (∀ o, vals ofC o t₁ = vals ofC o t₂) → ∀ o, vals ofC o (K t₁) = vals ofC o (K t₂) := by
  induction hK with
  | hole => exact fun h => h
  | callArg _ _ _ _ _ ih =>
    intro t₁ t₂ h o
    simp only [vals, valsArgs_eq]
    rw [flatMap_set_congr (ih h o)]
  | constructArg _ _ _ _ ih =>
    intro t₁ t₂ h o
    simp only [vals, valsArgs_eq]
    rw [flatMap_set_congr (ih h o)]
  | @makeArg _ c _ _ _ _ _ _ ih =>
    intro t₁ t₂ h o
    cases c <;> simp only [vals, valsArgs_eq] <;> rw [flatMap_set_congr (ih h o)]
  | arrArg _ _ _ ih =>
    intro t₁ t₂ h o
    simp only [vals, valsArgs_eq]
    rw [flatMap_set_congr (ih h o)]
  | frameC _ _ _ _ _ _ _ _ ih =>
    intro t₁ t₂ h o
    simp only [vals, ih h]
  | _ =>
    rename_i ih
    intro t₁ t₂ h o
    simp only [vals, ih h]

/-- **Steps holding the same values cross the same values out** (proved,
by the definitions): the new roots and the values left where outside code
reaches are read from the terms' values and the heaps. -/
theorem actualXs_congr {F : Family} {C : Nat} {tv : TypeView} (T : tv.Ty) (h h' : Heap) {t₁ t₂ t₁' t₂' : Tm}
    (hv : ∀ o, vals (F.ofC C) o t₁ = vals (F.ofC C) o t₂) (hv' : ∀ o, vals (F.ofC C) o t₁' = vals (F.ofC C) o t₂') :
    actualXs F C T h t₁ h' t₁' = actualXs F C T h t₂ h' t₂' := by
  have e : rootsOf F C none t₁ = rootsOf F C none t₂ := hv _
  have e' : rootsOf F C none t₁' = rootsOf F C none t₂' := hv' _
  unfold actualXs newRoots leftVals
  rw [e, e']

end Crossings

end Verification.TolerantFrames.ReadOnly
