import Verification.Types.PositiveRules

/-! Executable certificates for PositiveRules. Completeness concerns existence
of accepted evidence for a declarative derivation, not semantic completeness or
automatic proof search. -/
namespace Verification.PositiveCertificates
open PositiveNormalization PositiveGraphs PositiveRules CallEffects

inductive ArrowCert (ι : Type) where
  | empty
  | source (p : Arrow (List ι))
  /-- A variadic source signature covers the target arrow. -/
  | rest (s : RestArrow (List ι))
  | union (pre : List (List ι)) (a b : List ι) (suffix : List (List ι))
      (left right : ArrowCert ι)
  | combine (b b' : List ι) (effect other : Effect) (left right : ArrowCert ι)
  /-- The target's receiver admits no value: it names no call. -/
  | emptyRecv
  /-- The target's receiver is a union: each part is covered separately. -/
  | recvUnion (a b : List ι) (left right : ArrowCert ι)
  deriving Repr, DecidableEq

@[nospecialize] def checkDomainsWith (R : List ι → List ι → Prop) [DecidableRel R] : List (List ι) → List (List ι) → Bool
  | [], [] => true
  | a :: As, b :: Bs => decide (R a b) && checkDomainsWith R As Bs
  | _, _ => false

theorem checkDomainsWith_iff {R : List ι → List ι → Prop} [DecidableRel R] (As Bs : List (List ι)) :
    checkDomainsWith R As Bs = true ↔ Domains R As Bs := by
  induction As generalizing Bs with
  | nil => cases Bs <;> simp [checkDomainsWith, Domains]
  | cons a As ih => cases Bs <;> simp [checkDomainsWith, Domains, ih]

instance {elem : List ι → Option (List ι)} {R : List ι → List ι → Prop} [DecidableRel R]
    (As : List (List ι)) (E : List ι) : Decidable (ElemRest elem R As E) := by
  unfold ElemRest; split <;> infer_instance

instance [DecidableEq ι] {elem : List ι → Option (List ι)} {R : List ι → List ι → Prop}
    [DecidableRel R] (As : List (List ι)) (E : List ι) : Decidable (IntoRest elem R As E) := by
  unfold IntoRest; infer_instance

/-- A variadic source signature covering a fixed arrow, decided. -/
@[nospecialize] def checkRestFixedWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (s : RestArrow (List ι)) (q : Arrow (List ι)) : Bool :=
  decide (R q.receiver s.receiver) &&
    checkDomainsWith R (q.arguments.take s.arguments.1.length) s.arguments.1 &&
    decide (ElemRest (restElem G) (R) (q.arguments.drop s.arguments.1.length) s.arguments.2 ∧
      (s.result = [] ∨ R s.result q.result)) && s.effect.covers q.effect

theorem checkRestFixedWith_iff [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] {s q} :
    checkRestFixedWith G R s q = true ↔ RestFixed (restElem G) R s q := by
  simp [checkRestFixedWith, RestFixed, checkDomainsWith_iff, and_assoc]

/-- Every recursive premise retains the target contract. Splitting a domain
changes only that domain; combining results states and checks both effects. -/
@[nospecialize] def checkArrowWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (L : Ops ι) (S : List (RestArrow (List ι))) (q : Arrow (List ι)) : ArrowCert ι → Bool
  | .empty => decide ([] ∈ q.arguments)
  | .emptyRecv => decide (q.receiver = [])
  | .source p => decide (p ∈ L ∧ R q.receiver p.receiver ∧
      (p.result = [] ∨ R p.result q.result)) &&
      checkDomainsWith R q.arguments p.arguments && p.effect.covers q.effect
  | .rest s => decide (s ∈ S) && checkRestFixedWith G R s q
  | .union pre a b suffix left right => decide (q.arguments = pre ++ (a ++ b) :: suffix) &&
      checkArrowWith G R L S { q with arguments := pre ++ a :: suffix } left &&
      checkArrowWith G R L S { q with arguments := pre ++ b :: suffix } right
  | .recvUnion a b left right => decide (q.receiver = a ++ b) &&
      checkArrowWith G R L S { q with receiver := a } left &&
      checkArrowWith G R L S { q with receiver := b } right
  | .combine b b' effect other left right =>
      checkArrowWith G R L S { q with result := b, effect := effect } left &&
      checkArrowWith G R L S { q with result := b', effect := other } right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → R [i] q.result) &&
      (effect.meet other).covers q.effect

theorem checkArrowWith_sound [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] {L S q cert}
    (h : checkArrowWith G R L S q cert = true) :
    CallArrow (compatible G) (restElem G) R L S q := by
  induction cert generalizing q with
  | empty => exact .empty (of_decide_eq_true h)
  | emptyRecv => exact .emptyRecv (of_decide_eq_true h)
  | source p =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq, checkDomainsWith_iff] at h
    exact .source h.1.1.1 h.1.1.2.1 h.1.2 h.1.1.2.2 h.2
  | rest s =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq, checkRestFixedWith_iff] at h
    exact .rest h.1 h.2
  | union pre a b suffix left right ih ih' =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .union h.1.1 (ih h.1.2) (ih' h.2)
  | recvUnion a b left right ih ih' =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .recvUnion h.1.1 (ih h.1.2) (ih' h.2)
  | combine b b' effect other left right ih ih' =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .combine (ih h.1.1.1) (ih' h.1.1.2) h.1.2 h.2

abbrev Evidence (ι : Type) := List (Ops ι × ((Arrow (List ι)) × ArrowCert ι))

instance {R : List ι → List ι → Prop} [DecidableRel R] (a b : Option (List ι)) :
    Decidable (CoversRest R readonly a b) := by
  cases a <;> cases b <;> simp only [CoversRest] <;> infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversShape R p q) := by
  unfold CoversShape; infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversPack R p q) := by
  unfold CoversPack; infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversTuple G R p q) := by
  unfold CoversTuple; infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (p : List (List ι) × List ι) (t : List (List ι) × List ι × List ι) :
    Decidable (FixedCoversPack G R p t) := by
  unfold FixedCoversPack; split <;> infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (p : Arrow (List ι)) (t : RestArrow (List ι)) :
    Decidable (FixedCallsPack G R p t) := by
  unfold FixedCallsPack; split <;> infer_instance

/-- Every target arrow has checked evidence from the source's signatures. -/
abbrev ArrowsCheckedWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop)
    [DecidableRel R] (proofs : Evidence ι)
    (L : Ops ι) (S : List (RestArrow (List ι))) (M : Ops ι) : Prop :=
  ∀ p ∈ M, ∃ e ∈ proofs, e.1 = L ∧ e.2.1 = p ∧
    checkArrowWith G R L S p e.2.2 = true

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (proofs : Evidence ι) :
    ∀ L S M, Decidable (ArrowsCheckedWith G R proofs L S M) := by
  intro L S M
  unfold ArrowsCheckedWith
  infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R]
    {elem : List ι → Option (List ι)} [DecidableEq ι] (p q) :
    Decidable (RestCovers elem R p q) := by
  unfold RestCovers; infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R]
    {elem : List ι → Option (List ι)} [DecidableEq ι] (p q) :
    Decidable (CoversSig elem R p q) := by
  unfold CoversSig; infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (self : List ι) (L S q) : Decidable (CoversArrows G R self L S q) := by
  unfold CoversArrows; infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (s : SchemeRow ι) (L : Ops ι) (M : List (RestArrow (List ι))) :
    Decidable (BoundSigsCover G R s L M) := by
  unfold BoundSigsCover; infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} [DecidableRel R]
    (s : SchemeRow ι) (S' : List ι) : Decidable (SchemeBinds G sub R s S') := by
  unfold SchemeBinds; split
  · split
    · cases sub <;> dsimp only <;> infer_instance
    · infer_instance
  · infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} [DecidableRel R]
    (self F : List ι) (q) : Decidable (CoversByScheme G sub R self F q) := by
  unfold CoversByScheme; split
  · split <;> infer_instance
  · infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} [DecidableRel R]
    (self F : List ι) (q) : Decidable (CoversByFunction G sub R self F q) := by
  unfold CoversByFunction; split <;> infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} (P : List ι) (k : PropKey) :
    Decidable (lacksKey G P k) := by
  unfold lacksKey; split <;> infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} [DecidableRel R]
    (known : Known ι) (self : List ι) (q P) : Decidable (FoundOn G sub R known self q P) := by
  unfold FoundOn; infer_instance

instance instDecidableProtoHolds [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop}
    [DecidableRel R] (known : Known ι) (self : List ι) (q) :
    (d : Nat) → (P : List ι) → Decidable (ProtoHolds G sub R known self q d P)
  | 0, P => decidable_of_iff (FoundOn G sub R known self q P) (by rw [ProtoHolds])
  | d + 1, P =>
    have := instDecidableProtoHolds (G := G) (sub := sub) (R := R) known self q d
    decidable_of_iff (FoundOn G sub R known self q P ∨ (lacksKey G P q.key ∧
        ∃ P' ∈ (viewOf G P CallArguments.protoField).toList, ProtoHolds G sub R known self q d P'))
      (by rw [ProtoHolds])

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} [DecidableRel R]
    (known : Known ι) (self : List ι) (fields bounds q) :
    Decidable (CoversByProto G sub R known self fields bounds q) := by
  unfold CoversByProto; infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} [DecidableRel R]
    {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (self a b) :
    Decidable (CoversWith G sub R known arrows self a b) := by
  cases a <;> cases b <;> unfold CoversWith <;> infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (i j : ι) :
    Decidable (SchemeCoversWith G R known arrows i j) := by
  unfold SchemeCoversWith; split <;> infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sc : ι → ι → Prop} [DecidableRel sc]
    {cover : Clause (List ι) → Prop} [DecidablePred cover] (T : List ι) (i : ι) :
    Decidable (MeetOpaque G sc cover T i) := by
  unfold MeetOpaque MeetSource MeetTarget; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The executable checker is the shared coverage rule interpreted with checked
arrow evidence, premises read through `R`. Adding a coverage condition changes
the checker automatically. -/
@[nospecialize] def checkClauseWith [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) [DecidableRel R]
    (known : Known ι) (proofs : Evidence ι) (self : List ι) (a b : Clause (List ι)) : Bool :=
  decide (CoversWith G sub R known (ArrowsCheckedWith G R proofs) self a b)

theorem checkClauseWith_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop}
    [DecidableRel R] {known proofs self a b}
    (h : checkClauseWith G sub R known proofs self a b = true) : Covers G sub R known self a b := by
  apply CoversWith.mono (h := of_decide_eq_true h)
  intro L S M hs p hp
  obtain ⟨e, _, _, _, he⟩ := hs p hp
  exact checkArrowWith_sound he

/-! ## Family certificates

Family entries (RECURSIVE-EQUATIONS §4.2) are checked by the core
conditions with premises read in each entry, decided with checked arrow
evidence. The premise judgment is decided by `premB`, recursion on a size
that `Inst`'s premises decrease (`prem_iff`). A claim is a pair of a
variable-free entry (`checkStructural_sound`). -/

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {e : Entry ι}
    {l : ι} {B : List ι} {xs : List (List ι)} : Decidable (InstanceAt G sub e l B xs) := by
  unfold InstanceAt; infer_instance

/-- `Mem`, `Hyp` and `MeetHyp`, decided. -/
@[nospecialize] def premBase [DecidableEq ι] (G : NormalGraph ι) (f : Entry ι) (l : ι) (B : List ι) : Bool :=
  decide (l ∈ B) || f.hypotheses.any (fun h => decide (h.1 = l) && decide (h.2 ∈ B)) ||
    (G.meetRow l && B.any fun y => meetBelow G l y f.hypotheses)

/-- `Tab` and `TabRen`, decided: the renaming is the representation's own
proposal, checked. -/
@[nospecialize] def premTable [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (f : Entry ι)
    (A B : List ι) : Bool :=
  decide ((A, B) ∈ f.table) || match sub with
    | some r => f.table.any fun p => decide (RenamesBound G r (r.rename p A B)) &&
        A.all (fun l => decide (l ∈ r.substitute (r.rename p A B) p.1)) &&
        (r.substitute (r.rename p A B) p.2).all (fun b => decide (b ∈ B))
    | none => false

/-- `Inst` at the instance `w`, its hypotheses decided by `prem` on strictly
smaller types. -/
@[nospecialize] def instanceB [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (prem : List ι → List ι → Bool) (l : ι) (B : List ι) (w : Nat × List (List ι)) : Bool :=
  match look w.1 with
  | some e => decide (InstanceAt G sub e l B w.2) && e.hypotheses.all fun h =>
      decide (typeSize sub (replace (e.variables.zip w.2) h.1) +
        typeSize sub (replace (e.variables.zip w.2) h.2) < labelSize sub l + typeSize sub B) &&
      prem (replace (e.variables.zip w.2) h.1) (replace (e.variables.zip w.2) h.2)
  | none => false

/-- A label's premise, decided with `k` levels of nested instances. -/
@[nospecialize] def premLabelB [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) : Nat → ι → List ι → Bool
  | 0, l, B => premBase G f l B
  | k + 1, l, B => premBase G f l B || (f.instances ++ gen l B).any fun w =>
      instanceB G sub look (fun X Y => premTable G sub f X Y || X.all fun l' =>
        premLabelB G sub look gen f k l' Y) l B w

/-- A premise, decided with `k` levels of nested instances. -/
@[nospecialize] def premB [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) (k : Nat) (A B : List ι) : Bool :=
  premTable G sub f A B || A.all fun l => premLabelB G sub look gen f k l B

theorem premLabelB_succ [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} {k : Nat}
    {l : ι} {B : List ι} :
    premLabelB G sub look gen f (k + 1) l B = (premBase G f l B || (f.instances ++ gen l B).any
      fun w => instanceB G sub look (premB G sub look gen f k) l B w) := rfl

theorem premBase_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {l : ι} {B : List ι} (h : premBase G f l B = true) : PremLabel G sub look gen f l B := by
  simp only [premBase, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with (h | ⟨q, hq, rfl, hy⟩) | ⟨hm, y, hy, hb⟩
  · exact .mem h
  · exact .hyp hq hy
  · exact .meetHyp hm hy hb

theorem premTable_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {A B : List ι} (h : premTable G sub f A B = true) : Prem G sub look gen f A B := by
  unfold premTable at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact .tab h
  · cases sub with
    | none => cases h
    | some r =>
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      obtain ⟨p, hp, ⟨hren, hA⟩, hB⟩ := h
      exact .tabRen r p rfl hp hren hA hB

theorem prem_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} :
    ∀ k, (∀ l B, premLabelB G sub look gen f k l B = true → PremLabel G sub look gen f l B) ∧
      ∀ A B, premB G sub look gen f k A B = true → Prem G sub look gen f A B := by
  intro k
  induction k with
  | zero =>
    have hl : ∀ l B, premLabelB G sub look gen f 0 l B = true → PremLabel G sub look gen f l B :=
      fun l B h => premBase_sound h
    refine ⟨hl, fun A B h => ?_⟩
    simp only [premB, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with h | h
    · exact premTable_sound h
    · exact .union fun l hl' => hl l B (h l hl')
  | succ k ih =>
    have hl : ∀ l B, premLabelB G sub look gen f (k + 1) l B = true →
        PremLabel G sub look gen f l B := by
      intro l B h
      rw [premLabelB_succ] at h
      simp only [Bool.or_eq_true, List.any_eq_true] at h
      rcases h with h | ⟨w, hw, h⟩
      · exact premBase_sound h
      · unfold instanceB at h
        split at h
        · rename_i e he
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
          obtain ⟨hi, hh⟩ := h
          exact .inst w e hw he hi (fun h' hh' => (hh h' hh').1)
            (fun h' hh' => ih.2 _ _ (hh h' hh').2)
        · cases h
    refine ⟨hl, fun A B h => ?_⟩
    simp only [premB, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with h | h
    · exact premTable_sound h
    · exact .union fun l hl' => hl l B (h l hl')

theorem le_typeSize [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {l : ι} :
    ∀ {A : List ι}, l ∈ A → labelSize sub l ≤ typeSize sub A
  | a :: A, h => by
    simp only [typeSize, List.map_cons, List.sum_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_typeSize (sub := sub) h
      simp only [typeSize] at this
      omega

theorem premBase_of_label [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {l : ι} {B : List ι} (h : premBase G f l B = true) :
    ∀ k, premLabelB G sub look gen f k l B = true
  | 0 => h
  | _ + 1 => by rw [premLabelB_succ, h, Bool.true_or]

/-- **Completeness of the decision.** A derivation fits the size of its
conclusion: each `Inst` decreases it. -/
theorem prem_complete [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} :
    (∀ {A B}, Prem G sub look gen f A B →
      ∀ k, typeSize sub A + typeSize sub B < k → premB G sub look gen f k A B = true) ∧
    ∀ {l B}, PremLabel G sub look gen f l B →
      ∀ k, labelSize sub l + typeSize sub B < k → premLabelB G sub look gen f k l B = true := by
  let motive_1 := fun (A B : List ι) (_ : Prem G sub look gen f A B) =>
    ∀ k, typeSize sub A + typeSize sub B < k → premB G sub look gen f k A B = true
  let motive_2 := fun (l : ι) (B : List ι) (_ : PremLabel G sub look gen f l B) =>
    ∀ k, labelSize sub l + typeSize sub B < k → premLabelB G sub look gen f k l B = true
  have tab : ∀ {A B} (h : (A, B) ∈ f.table), motive_1 A B (.tab h) := fun h k _ => by
    simp [premB, premTable, h]
  have ren : ∀ {A B} r p hs hp hren hA hB, motive_1 A B (.tabRen r p hs hp hren hA hB) := by
    intro A B r p hs hp hren hA hB k _
    subst hs
    have : premTable G (some r) f A B = true := by
      simp only [premTable, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true]
      exact .inr ⟨p, hp, ⟨hren, hA⟩, hB⟩
    simp [premB, this]
  have union : ∀ {A B} (h : ∀ l ∈ A, PremLabel G sub look gen f l B),
      (∀ l hl, motive_2 l B (h l hl)) → motive_1 A B (.union h) := by
    intro A B _ ih k hk
    simp only [premB, Bool.or_eq_true, List.all_eq_true]
    exact .inr fun l hl => ih l hl k (by have := le_typeSize (sub := sub) hl; omega)
  have mem : ∀ {l B} (h : l ∈ B), motive_2 l B (.mem h) := fun h k _ =>
    premBase_of_label (by simp [premBase, h]) k
  have hyp : ∀ {l y B} (hh : (l, y) ∈ f.hypotheses) (hy : y ∈ B), motive_2 l B (.hyp hh hy) := by
    intro l y B hh hy k _
    refine premBase_of_label ?_ k
    simp only [premBase, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact .inl (.inr ⟨(l, y), hh, rfl, hy⟩)
  have meetHyp : ∀ {l y B} (hm : G.meetRow l = true) (hy : y ∈ B)
      (hb : meetBelow G l y f.hypotheses = true), motive_2 l B (.meetHyp hm hy hb) := by
    intro l y B hm hy hb k _
    refine premBase_of_label ?_ k
    simp only [premBase, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact .inr ⟨hm, y, hy, hb⟩
  have inst : ∀ {l B} (w : Nat × List (List ι)) (e : Entry ι) hw hl hi hdec
      (hps : ∀ h ∈ e.hypotheses, Prem G sub look gen f (replace (e.variables.zip w.2) h.1)
        (replace (e.variables.zip w.2) h.2)),
      (∀ h hh, motive_1 _ _ (hps h hh)) → motive_2 l B (.inst w e hw hl hi hdec hps) := by
    intro l B w e hw hl hi hdec _ ih k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [premLabelB_succ]
    simp only [Bool.or_eq_true, List.any_eq_true]
    refine .inr ⟨w, hw, ?_⟩
    simp only [instanceB, hl, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true]
    exact ⟨hi, fun h hh => ⟨hdec h hh, ih h hh k (by have := hdec h hh; omega)⟩⟩
  exact ⟨fun h => Prem.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h,
    fun h => PremLabel.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h⟩

/-- The premise judgment is decided by its checker at its conclusion's size. -/
theorem prem_iff [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {A B : List ι} :
    Prem G sub look gen f A B ↔
      premB G sub look gen f (typeSize sub A + typeSize sub B + 1) A B = true :=
  ⟨fun h => prem_complete.1 h _ (by omega), fun h => (prem_sound _).2 _ _ h⟩

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {look : Lookup ι}
    {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} :
    DecidableRel (Prem G sub look gen f) := fun _ _ => decidable_of_iff _ prem_iff.symm

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (i j : ι) :
    Decidable (SchemeRenames G sub R known arrows i j) := by
  unfold SchemeRenames; split <;> infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (hyps : List (ι × ι)) (S T : List ι) :
    Decidable (OpaqueFamily G sub R known arrows hyps S T) := by
  unfold OpaqueFamily PartCovers SchemeCoversAlpha; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The entries' core conditions, premises read in each entry, arrows by
checked evidence. -/
@[nospecialize] def checkEntries [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (known : Known ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (look : Lookup ι) (F : List (Entry ι))
    (arrows : Evidence ι) : Bool :=
  decide (∀ f ∈ F, ∀ p ∈ f.pairs, SameKind G p.1 p.2 = true ∧
    OpaqueFamily G sub (Prem G sub look gen f) known
      (ArrowsCheckedWith G (Prem G sub look gen f) arrows) f.hypotheses p.1 p.2 ∧
    ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2 f.hypotheses, ∃ b ∈ clausesOf G p.2,
      checkClauseWith G sub (Prem G sub look gen f) known arrows p.1 a b = true)

theorem checkEntries_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    {arrows : Evidence ι} (h : checkEntries G sub known gen look F arrows = true) :
    FamilyValid G sub known gen look F := by
  simp only [checkEntries, decide_eq_true_eq] at h
  intro f hf p hp
  obtain ⟨hk, ho, hc⟩ := h f hf p hp
  refine ⟨hk, OpaqueFamily.mono (fun L S M hs q hq => ?_) ho, fun a ha => ?_⟩
  · obtain ⟨e, _, _, _, he⟩ := hs q hq
    exact checkArrowWith_sound he
  · obtain ⟨b, hb, hcb⟩ := hc a ha
    exact ⟨b, hb, checkClauseWith_sound hcb⟩

/-- The variable discipline, decided. -/
@[nospecialize] def variablesOk [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (F : List (Entry ι)) : Bool :=
  match sub with
  | some r => decide ((∀ f ∈ F, ∀ h ∈ f.hypotheses, h.1 ∈ f.variables ∧ h.2 ∈ f.variables) ∧
      ∀ f ∈ F, ∀ x ∈ f.variables, r.familyVar x = true)
  | none => F.all fun f => f.variables.isEmpty && f.hypotheses.isEmpty

theorem variablesOk_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {F : List (Entry ι)} (h : variablesOk sub F = true) : VariablesOk sub F := by
  cases sub with
  | some r =>
    simp only [variablesOk, decide_eq_true_eq] at h
    exact ⟨h.1, fun f hf x hx => h.2 f hf x hx⟩
  | none =>
    simp only [variablesOk, List.all_eq_true, Bool.and_eq_true, List.isEmpty_iff] at h
    refine ⟨fun f hf p hp => ?_, fun f hf x hx => ?_⟩
    · rw [(h f hf).2] at hp; cases hp
    · rw [(h f hf).1] at hx; cases hx

/-- A checked instance of a scheme row's signatures: the instance table, the
types the binders are instantiated at, the table's domain and the domain's
free parameter rows. The common comparison operation discharges each bound. -/
structure Instance (ι : Type) where
  table : InstTable ι
  instances : List (List ι)
  domain : List ι
  free : FreeMap ι
  deriving Repr

/-- A known row with the instance proving it: a scheme row, the arrows it is
below, and the instance. -/
abbrev KnownInstance (ι : Type) := List ι × Ops ι × List (RestArrow (List ι)) × Instance ι

/-- Untrusted instantiation choices for a subtype obligation. Structural
comparison and rule selection belong to the checker. -/
structure SubtypeChoices (ι : Type) where
  instantiation : Option (Instance ι) := none
  members : List (KnownInstance ι) := []
  deriving Repr

theorem exists_mem_zip {xs : List α} {ys : List β} (hl : ys.length = xs.length) :
    ∀ x ∈ xs, ∃ y, (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => intro x hx; cases hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hl
    | cons b ys =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp⟩
      · obtain ⟨y, hy⟩ := ih (by simpa using hl) x hx
        exact ⟨y, by simp [hy]⟩

/-- Entries already sound, which instances may cite by index below `size`:
a representation's checked variances (§4.3), or none. Supplied by verified
code with its proof, never by a certificate. -/
structure Base [DecidableEq ι] (G : NormalGraph ι) where
  size : Nat := 0
  entry : Nat → Option (Entry ι) := fun _ => none
  sound : ∀ k e, entry k = some e → EntrySound G e ∧ HypParams G e := by
    intro _ _ h; cases h

/-- The entries a family certificate's instances cite: the base's, then its
own after them. -/
@[nospecialize] def Base.lookup [DecidableEq ι] {G : NormalGraph ι} (base : Base G) (F : List (Entry ι)) :
    Lookup ι := fun k =>
  if k < base.size then base.entry k else F[k - base.size]?

theorem Base.lookup_cases [DecidableEq ι] {G : NormalGraph ι} (base : Base G) (F : List (Entry ι))
    (k : Nat) (e : Entry ι) (h : base.lookup F k = some e) :
    e ∈ F ∨ (EntrySound G e ∧ HypParams G e) := by
  unfold Base.lookup at h
  split at h
  · exact .inr (base.sound k e h)
  · exact .inl (List.mem_of_getElem? h)

/-- A renaming at a reassignment of the graph's parameter rows: its laws
quantify over every assignment and read no `env`. -/
@[nospecialize] def _root_.Verification.PositiveRules.Renaming.reassign [DecidableEq ι] {G : NormalGraph ι} (r : Renaming G) (η : MixedAssignment ι) :
    Renaming (PositiveRules.reassign G η) where
  substitute := r.substitute
  free := r.free
  familyVar := r.familyVar
  mentions := r.mentions
  substitute_meaning := r.substitute_meaning
  agree_free := r.agree_free
  familyVar_param := r.familyVar_param
  familyVar_unbound := r.familyVar_unbound
  size := r.size
  rename := r.rename
  head := r.head

/-- Sound entries at a reassignment: soundness quantifies over every
assignment and reads no `env`. -/
@[nospecialize] def Base.reassign [DecidableEq ι] {G : NormalGraph ι} (b : Base G) (η : MixedAssignment ι) :
    Base (PositiveRules.reassign G η) where
  size := b.size
  entry := b.entry
  sound := b.sound

/-- Execution resources for dependency discovery. Each round unfolds a frontier;
its size is unrestricted. -/
structure SearchBudget where
  rounds : Nat := 4096
  deriving Repr

/-- An outcome of checked comparison search. Successful search returns its
result; exhaustion records the work already performed. -/
inductive ComparisonResult (α : Type) where
  | established (value : α)
  | notEstablished
  | exhausted (rounds visited : Nat)
  deriving Repr

@[nospecialize] def ComparisonResult.accepted : ComparisonResult α → Bool
  | .established _ => true
  | .notEstablished | .exhausted _ _ => false

/-- Conjunction stops at the first unsuccessful premise, retaining its outcome. -/
@[nospecialize] def ComparisonResult.all (f : β → ComparisonResult Unit) :
    List β → ComparisonResult Unit
  | [] => .established ()
  | x :: xs => match f x with
    | .established () => all f xs
    | .notEstablished => .notEstablished
    | .exhausted rounds visited => .exhausted rounds visited

@[simp] theorem ComparisonResult.accepted_all (f : β → ComparisonResult Unit) (xs : List β) :
    (all f xs).accepted = xs.all (fun x => (f x).accepted) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x with
    | established u => cases u; simpa only [all, h, accepted, List.all_cons, Bool.true_and] using ih
    | notEstablished => simp only [all, h, accepted, List.all_cons, Bool.false_and]
    | exhausted rounds visited => simp only [all, h, accepted, List.all_cons, Bool.false_and]

/-- Alternative rules share success; exhaustion survives when neither succeeds. -/
@[nospecialize] def ComparisonResult.orElse (a : ComparisonResult α)
    (next : Unit → ComparisonResult α) : ComparisonResult α :=
  match a with
  | .established x => .established x
  | .notEstablished => next ()
  | .exhausted rounds visited => match next () with
    | .established x => .established x
    | .notEstablished | .exhausted _ _ => .exhausted rounds visited

@[simp] theorem ComparisonResult.accepted_orElse (a : ComparisonResult α)
    (next : Unit → ComparisonResult α) :
    (a.orElse next).accepted = (a.accepted || (next ()).accepted) := by
  cases a <;> simp [orElse, accepted] <;> cases next () <;> rfl

/-- An unfinished member rule cannot establish the root comparison. Its
resource outcome remains relevant if every root rule is unsuccessful. -/
@[nospecialize] def ComparisonResult.exhaustion : List (ComparisonResult Unit) → ComparisonResult α
  | [] => .notEstablished
  | .exhausted rounds visited :: _ => .exhausted rounds visited
  | .established _ :: xs | .notEstablished :: xs => exhaustion xs

@[simp] theorem ComparisonResult.accepted_exhaustion (xs : List (ComparisonResult Unit)) :
    (exhaustion xs : ComparisonResult α).accepted = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [exhaustion] <;> first | exact ih | rfl

@[nospecialize] def ComparisonResult.map (f : α → β) : ComparisonResult α → ComparisonResult β
  | .established value => .established (f value)
  | .notEstablished => .notEstablished
  | .exhausted rounds visited => .exhausted rounds visited

theorem ComparisonResult.accepted_map (f : α → β) (r : ComparisonResult α) :
    (r.map f).accepted = r.accepted := by cases r <;> rfl

/-- A decidable validator has no search frontier to exhaust. -/
@[nospecialize] def ComparisonResult.fromBool (holds : Bool) : ComparisonResult Unit :=
  if holds then .established () else .notEstablished

@[simp] theorem ComparisonResult.accepted_fromBool (holds : Bool) :
    (fromBool holds).accepted = holds := by cases holds <;> rfl

/-- Sequential validation retains an unsuccessful prerequisite's outcome. -/
@[nospecialize] def ComparisonResult.andThen (a : ComparisonResult Unit)
    (next : Unit → ComparisonResult α) : ComparisonResult α :=
  match a with
  | .established _ => next ()
  | .notEstablished => .notEstablished
  | .exhausted rounds visited => .exhausted rounds visited

@[simp] theorem ComparisonResult.accepted_andThen (a : ComparisonResult Unit)
    (next : Unit → ComparisonResult α) :
    (a.andThen next).accepted = (a.accepted && (next ()).accepted) := by
  cases a <;> simp only [andThen, accepted, Bool.true_and, Bool.false_and]

/-- Thread completed comparison state through alternatives. An exhausted
alternative retains its outcome unless a later alternative establishes the goal. -/
@[nospecialize] def ComparisonResult.orElseState (a : ComparisonResult α × σ)
    (next : σ → ComparisonResult α × σ) : ComparisonResult α × σ :=
  match a with
  | (.established x, state) => (.established x, state)
  | (.notEstablished, state) => next state
  | (.exhausted rounds visited, state) =>
    let (r, state') := next state
    match r with
    | .established x => (.established x, state')
    | .notEstablished | .exhausted _ _ => (.exhausted rounds visited, state')

/-- A conjunction retains the state of every completed premise, including
premises checked before the first unsuccessful one. -/
@[nospecialize] def ComparisonResult.collectState
    (f : β → σ → ComparisonResult α × σ) : List β → σ → ComparisonResult (List α) × σ
  | [], state => (.established [], state)
  | x :: xs, state =>
    let (r, state') := f x state
    match r with
    | .established a =>
      let (tail, state'') := collectState f xs state'
      (tail.map (a :: ·), state'')
    | .notEstablished => (.notEstablished, state')
    | .exhausted rounds visited => (.exhausted rounds visited, state')

/-- Check alternatives against the completed results of preceding alternatives. -/
@[nospecialize] def ComparisonResult.firstState
    (f : β → σ → ComparisonResult α × σ) : List β → σ → ComparisonResult α × σ
  | [], state => (.notEstablished, state)
  | x :: xs, state => orElseState (f x state) (firstState f xs)

/-- Evaluate every action while threading its completed comparison state. -/
@[nospecialize] def mapResultsState (f : β → σ → α × σ) : List β → σ → List α × σ
  | [], state => ([], state)
  | x :: xs, state =>
    let (a, state') := f x state
    let (tail, state'') := mapResultsState f xs state'
    (a :: tail, state'')

/-- Every premise of an established conjunction was established at a state
reached during the traversal. -/
theorem ComparisonResult.collectState_sound
    (f : β → σ → ComparisonResult α × σ) (xs : List β) (state : σ)
    (h : (collectState f xs state).1.accepted = true) :
    ∀ x ∈ xs, ∃ prior, (f x prior).1.accepted = true := by
  induction xs generalizing state with
  | nil => simp
  | cons x xs ih =>
    rcases step : f x state with ⟨head, next⟩
    cases head with
    | notEstablished => simp only [collectState, step, accepted] at h; cases h
    | exhausted rounds visited => simp only [collectState, step, accepted] at h; cases h
    | established value =>
      have tail : (collectState f xs next).1.accepted = true := by
        simpa only [collectState, step, accepted_map] using h
      intro y hy
      rcases List.mem_cons.mp hy with same | rest
      · subst y
        exact ⟨state, by rw [step]; rfl⟩
      · exact ih next tail y rest

/-- Established alternatives contain an established member check. -/
theorem ComparisonResult.firstState_sound
    (f : β → σ → ComparisonResult α × σ) (xs : List β) (state : σ)
    (h : (firstState f xs state).1.accepted = true) :
    ∃ x ∈ xs, ∃ prior, (f x prior).1.accepted = true := by
  induction xs generalizing state with
  | nil => cases h
  | cons x xs ih =>
    rcases step : f x state with ⟨head, next⟩
    cases head with
    | established value => exact ⟨x, List.mem_cons_self, state, by rw [step]; rfl⟩
    | notEstablished =>
      have tail : (firstState f xs next).1.accepted = true := by
        simpa only [firstState, step, orElseState] using h
      obtain ⟨y, hy, prior, checked⟩ := ih next tail
      exact ⟨y, List.mem_cons_of_mem x hy, prior, checked⟩
    | exhausted rounds visited =>
      have tail : (firstState f xs next).1.accepted = true := by
        simp only [firstState, step, orElseState] at h
        cases result : (firstState f xs next).1 <;> simp only [result, accepted] at h ⊢
        all_goals first | rfl | cases h
      obtain ⟨y, hy, prior, checked⟩ := ih next tail
      exact ⟨y, List.mem_cons_of_mem x hy, prior, checked⟩

@[simp] theorem ComparisonResult.orElseState_accepted (a : ComparisonResult α × σ)
    (next : σ → ComparisonResult α × σ) :
    (orElseState a next).1.accepted = (a.1.accepted || (next a.2).1.accepted) := by
  rcases a with ⟨a, state⟩
  cases a with
  | established value => rfl
  | notEstablished => rfl
  | exhausted rounds visited =>
    rcases step : next state with ⟨result, last⟩
    cases result <;> simp only [orElseState, step, accepted, Bool.false_or]

/-- Each produced value belongs to an action evaluated during the traversal. -/
theorem mapResultsState_mem (f : β → σ → α × σ) (xs : List β) (state : σ)
    {value : α} (h : value ∈ (mapResultsState f xs state).1) :
    ∃ x ∈ xs, ∃ prior, value = (f x prior).1 := by
  induction xs generalizing state with
  | nil => cases h
  | cons x xs ih =>
    rcases step : f x state with ⟨head, next⟩
    simp only [mapResultsState, step, List.mem_cons] at h
    rcases h with same | tail
    · exact ⟨x, List.mem_cons_self, state, by rw [step]; exact same⟩
    · obtain ⟨y, hy, prior, produced⟩ := ih next tail
      exact ⟨y, List.mem_cons_of_mem x hy, prior, produced⟩

/-- The representation-specific checks, with their semantic obligations:
the image and admissibility checks of instances, and, for a representation with one, the
renaming, the sound entries instances may cite (a representation's computed
variances) and the verified proposal of `Var` instances. Supplied by
verified code, never read from a certificate. Bound, kind, signature and
effect checks remain in the shared instance checker. -/
structure InstanceImageCheck [DecidableEq ι] (G : NormalGraph ι) where
  compare : List ι → Instance ι → ComparisonResult Unit
  sound : ∀ bs c, c.instances.length = bs.length → instKinds G bs c.instances = true →
    (compare bs c).accepted = true → ∀ η, InstanceImages G η bs c.instances c.table
  /-- Admissibility is checked independently of substitution images. -/
  compareAllowed : SchemeRow ι → Instance ι → ComparisonResult Unit
  allowed_sound : ∀ s c, (compareAllowed s c).accepted = true → ∀ η,
    G.domain.allowed s (c.instances.map fun U =>
      ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)
  sub : Option (Renaming G) := none
  base : Base G := {}
  gen : ι → List ι → List (Nat × List (List ι)) := fun _ _ => []
  /-- Execution policy shared by comparisons and their bound/image obligations. -/
  budget : SearchBudget := {}

/-- Finite closed-table images use the domain's proved ordinary admission law. -/
@[nospecialize] def finiteInstanceImages [DecidableEq ι] (G : NormalGraph ι) : InstanceImageCheck G where
  compare := fun _ c => ComparisonResult.fromBool (TableOk G c.table c.domain c.free)
  sound := fun _ _ hlen hkinds hok η => table_instanceImages η hlen hkinds (by simpa only [ComparisonResult.accepted_fromBool] using hok)
  compareAllowed := fun s _ => ComparisonResult.fromBool s.resolution.isEmpty
  allowed_sound := by
    intro s c h η
    apply G.domain.ordinary_allowed
    exact List.isEmpty_iff.mp (by simpa only [ComparisonResult.accepted_fromBool] using h)

/-- The same check at a reassignment of the graph's parameter rows. Its
obligation quantifies over every assignment and reads no `env`, so one proof
serves every reassignment (`Parametricity`). -/
@[nospecialize] def InstanceImageCheck.reassign [DecidableEq ι] {G : NormalGraph ι} (images : InstanceImageCheck G)
    (η : MixedAssignment ι) : InstanceImageCheck (PositiveRules.reassign G η) where
  compare := images.compare
  sound := images.sound
  compareAllowed := images.compareAllowed
  allowed_sound := images.allowed_sound
  sub := images.sub.map fun r => r.reassign η
  base := images.base.reassign η
  gen := images.gen
  budget := images.budget

/-! ### The fallback's search (RECURSIVE-EQUATIONS §4.2–4.3)

The pairs reachable from a pair, grown on demand, and the uncovered ones
deleted. The search decides nothing: the pairs it finds are checked
(`checkStructural`, `compareUsing`). -/

/-- Small arrow search: source, receiver and domain union, and pairwise
compatible codomain combination, with operand premises decided by `rel`.
The checker, not this search strategy, defines the rules. -/
@[nospecialize] def arrowSearch [DecidableEq ι] (G : NormalGraph ι) (rel : List ι → List ι → Bool) (L : Ops ι)
    (S : List (RestArrow (List ι)))
    (q : Arrow (List ι)) : Nat → Option (ArrowCert ι)
  | 0 => none
  | fuel+1 => Id.run do
    let R : List ι → List ι → Prop := fun a b => rel a b = true
    let basic := ArrowCert.empty :: .emptyRecv ::
      L.map (.source ·) ++ S.map (.rest ·)
    if let some p := basic.find? (fun p => checkArrowWith G R L S q p) then
      return some p
    if let a :: rest := q.receiver then
      if !rest.isEmpty then
        if let some left := arrowSearch G rel L S {q with receiver := [a]} fuel then
          if let some right := arrowSearch G rel L S {q with receiver := rest} fuel then
            let p := ArrowCert.recvUnion [a] rest left right
            if checkArrowWith G R L S q p then return some p
    for i in List.range q.arguments.length do
      if let some (a :: rest) := q.arguments[i]? then
        if !rest.isEmpty then
          if let some left := arrowSearch G rel L S {q with arguments := q.arguments.set i [a]} fuel then
            if let some right := arrowSearch G rel L S {q with arguments := q.arguments.set i rest} fuel then
              let p := ArrowCert.union (q.arguments.take i) [a] rest (q.arguments.drop (i+1)) left right
              if checkArrowWith G R L S q p then return some p
    return (L.flatMap fun p => L.map fun q =>
      ArrowCert.combine p.result q.result p.effect q.effect (.source p) (.source q)).find?
        (fun p => checkArrowWith G R L S q p)

/-- The pairs one signature list's coverage of another compares: each target
signature against each source one, position by position (receivers,
parameters contravariantly, results covariantly), and each part of a target
parameter's union against the source's parameter, as arrow coverage splits
it. -/
@[nospecialize] def signaturePairs (source target : List (Arrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => source.flatMap fun s =>
    (t.receiver, s.receiver) :: (s.result, t.result) :: (t.arguments.zip s.arguments).flatMap fun (q, p) =>
      (q, p) :: q.map fun l => ([l], p)

/-- The same, for variadic signatures: fixed parameters, rest and result. -/
@[nospecialize] def restPairs (source target : List (RestArrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => source.flatMap fun s =>
    (t.receiver, s.receiver) :: (t.arguments.2, s.arguments.2) :: (s.result, t.result) :: t.arguments.1.zip s.arguments.1

/-- The pairs a variadic signature's coverage reads past the source's fixed
parameters: each further target parameter against the source rest's
element. -/
@[nospecialize] def elemPairs (G : NormalGraph ι) (source target : List (RestArrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => source.flatMap fun s => match PositiveRules.restElem G s.arguments.2 with
    | some E => (t.arguments.1.drop s.arguments.1.length).map (·, E)
    | none => []

/-- The pairs a variadic signature's coverage of a fixed one binding more
parameters compares past `signaturePairs` (`RestFixed`): the target's further
parameters against the source rest's element. -/
@[nospecialize] def restFixedPairs (G : NormalGraph ι) (source : List (RestArrow (List ι))) (target : List (Arrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => source.flatMap fun s =>
    match PositiveRules.restElem G s.arguments.2 with
    | some E => (t.arguments.drop s.arguments.1.length).map (·, E)
    | none => []

/-- The pairs a fixed signature's coverage of a variadic one whose rest is one
exact tuple compares: receivers, the fixed parameters and then the tuple's
positions against the source's parameters, and results. -/
@[nospecialize] def packPairs (G : NormalGraph ι) (source : List (Arrow (List ι))) (target : List (RestArrow (List ι))) :
    List (List ι × List ι) :=
  target.flatMap fun t => match expand G t.arguments.2 with
    | [.pack τ []] => source.flatMap fun p =>
        (t.receiver, p.receiver) :: (p.result, t.result) :: (t.arguments.1 ++ τ.required).zip p.arguments
    | _ => []

/-- The pairs a record's coverage of another compares, key by key: fields
both ways, views and optional fields, methods signature by signature and
scheme by scheme, the target's receivers against the source's, and a method
the source's prototype holds under the key (its receiver against the source
and the target's receivers, its signatures against the target's schemes'). -/
@[nospecialize] def protoChain (G : NormalGraph ι) : Nat → List ι → List (List ι)
  | 0, P => [P]
  | d + 1, P => P :: ((PositiveRules.viewOf G P CallArguments.protoField).toList.flatMap (protoChain G d))

@[nospecialize] def recordPairs [DecidableEq ι] (G : NormalGraph ι) (known : Known ι) (self : List ι)
    (fs vs : List (PropKey × List ι)) (os : List (OptionalField (List ι)))
    (ms : List (MethodMembers.Sig (List ι)))
    (fs' vs' : List (PropKey × List ι)) (os' : List (OptionalField (List ι)))
    (ms' : List (MethodMembers.Sig (List ι))) : List (List ι × List ι) :=
  let slots := fs ++ vs ++ os.map fun o => (o.key, o.type)
  let keyed (k : PropKey) : List (List ι) := (slots.filter (·.1 == k)).map (·.2)
  let proto : List (List ι) := (fs ++ vs).filter (·.1 == CallArguments.protoField) |>.map (·.2)
  let schemeSigs (F : List ι) := F.filterMap G.schemes
  (fs'.flatMap fun f => (keyed f.1).flatMap fun A => [(A, f.2), (f.2, A)]) ++
  (vs'.flatMap fun f => (keyed f.1).map fun A => (A, f.2)) ++
  (os'.flatMap fun o => (keyed o.key).flatMap fun A => [(A, o.type), (o.type, A)]) ++
  ms'.flatMap fun q =>
    let own := ms.filter (·.key == q.key)
    let targetSchemes := q.schemes.flatMap schemeSigs
    (own.flatMap fun p =>
      signaturePairs (p.calls.map (·.withReceiver [])) (q.calls.map (·.withReceiver [])) ++
      (q.schemes.flatMap fun S' => p.schemes.map fun S => (S, S')) ++
      (p.receivers.flatMap fun T => q.receivers.map fun T' => (T', T))) ++
    ((keyed q.key ++ (proto.flatMap (protoChain G PositiveRules.protoChainDepth)).flatMap fun P =>
        (PositiveRules.viewOf G P q.key).toList).flatMap fun F =>
      (((match expand G F with
        | [.arrs L S] => [(L, S)]
        | _ => []) ++ (known.filter (·.1 == F)).map (·.2)).flatMap fun (L, S) =>
          (L.map fun s => (self, s.receiver)) ++ (S.map fun s => (self, s.receiver)) ++
          (q.receivers.flatMap fun T => L.map (fun s => (T, s.receiver)) ++ S.map (fun s => (T, s.receiver))) ++
          signaturePairs (L.map (·.withReceiver [])) (q.calls.map (·.withReceiver [])) ++
          restPairs (S.map (·.withReceiver [])) (q.rests.map (·.withReceiver []))) ++
      (if targetSchemes.isEmpty then [] else schemeSigs F).flatMap fun s =>
        (s.signatures.map fun p => (self, p.receiver)) ++
        targetSchemes.flatMap fun s' => if s.binders = s'.binders then
          signaturePairs s.signatures s'.signatures ++ restPairs s.variadic s'.variadic else [])

/-- The pairs one clause's coverage of another compares. -/
@[nospecialize] def clausePairs [DecidableEq ι] (G : NormalGraph ι) (known : Known ι) (self : List ι) :
    Clause (List ι) → Clause (List ι) → List (List ι × List ι)
  | .refs a bs vs os ms _, .refs c ds ws ps ns _
  | .dict a bs vs _ os ms _ _, .refs c ds ws ps ns _ =>
    recordPairs G known self (a :: bs).flatten vs os ms (c :: ds).flatten ws ps ns
  | .refs a bs vs os ms _, .dict c ds ws iy ps ns _ cy =>
    recordPairs G known self (a :: bs).flatten vs os ms (c :: ds).flatten ws ps ns ++
      (iy.flatMap fun y => ((a :: bs).flatten ++ vs).map fun p => (p.2, y.2)) ++
      (cy.flatMap fun y => (a :: bs).flatten.flatMap fun p => [(p.2, y.2), (y.2, p.2)])
  | .dict a bs vs ix os ms _ cx, .dict c ds ws iy ps ns _ cy =>
    recordPairs G known self (a :: bs).flatten vs os ms (c :: ds).flatten ws ps ns ++
      ((iy ++ cy).flatMap fun y => (ix ++ cx).flatMap fun x => [(x.2, y.2), (y.2, x.2)]) ++
      (cy.flatMap fun y => os.map fun o => (y.2, o.type))
  | .arrs L S, .arrs M T | .callable _ _ L S, .arrs M T =>
    signaturePairs L M ++ restPairs S T ++ elemPairs G S T ++ packPairs G L T ++
      restFixedPairs G S M
  | .callable a bs L S, .callable c ds M T =>
    recordPairs G known self (a :: bs).flatten [] [] [] (c :: ds).flatten [] [] [] ++
    signaturePairs L M ++ restPairs S T ++ elemPairs G S T ++ packPairs G L T ++
      restFixedPairs G S M
  | .ctors L S a bs vs, .ctors M T c ds ws =>
    let fixed (p : List (List ι) × List ι) : Arrow (List ι) := ⟨[], p.1, p.2, .unrestricted⟩
    let rest (p : List (List ι) × List ι × List ι) : RestArrow (List ι) := ⟨[], (p.1, p.2.1), p.2.2, .unrestricted⟩
    recordPairs G known self (a :: bs).flatten vs [] [] (c :: ds).flatten ws [] [] ++
    signaturePairs (L.map fixed) (M.map fixed) ++ restPairs (S.map rest) (T.map rest) ++
      packPairs G (L.map fixed) (T.map rest)
  | .list a bs, .list c ds | .pack a bs, .pack c ds =>
    (c :: ds).flatMap fun q => (a :: bs).flatMap fun p =>
      let pos (t : PositiveNormalization.Tuple (List ι)) := t.required ++ t.optional ++ t.rest.toList
      (pos p).flatMap fun x => (pos q).flatMap fun y => [(x, y), (y, x)]
  | _, _ => []

/-- Quantified rows supplied directly or as opaque components of a meet.
Dependency and arrow discovery read the same components as `MeetOpaque`. -/
@[nospecialize] def schemeComponents [DecidableEq ι] (G : NormalGraph ι) (X : List ι) : List ι :=
  (X ++ (X.filter G.meetRow).flatMap (meetParts G)).filter (fun i => (G.schemes i).isSome) |>.eraseDups

/-- The pairs a row's coverage compares: its clauses' against the target's,
and a scheme's signatures against a target scheme's binding the same rows. -/
@[nospecialize] def demandPairs [DecidableEq ι] (G : NormalGraph ι) (known : Known ι) (X Y : List ι) : List (List ι × List ι) :=
  (clausesOf G X).flatMap (fun a => (clausesOf G Y).flatMap (clausePairs G known X a)) ++
  (schemeComponents G X).flatMap fun i => (schemeComponents G Y).flatMap fun j => match G.schemes i, G.schemes j with
    | some s, some s' => if s.binders = s'.binders then
        signaturePairs s.signatures s'.signatures ++ restPairs s.variadic s'.variadic else []
    | _, _ => []

/-- How deep a pair's rows follow `Var`: search only. -/
def varDepthDefault : Nat := 8

/-! ### Fallback coinduction up to renaming (RECURSIVE-EQUATIONS §4.3)

A pair `Var` does not decide is unfolded into a table grown on demand. Two
applications of one head with a computed variance add no row: `Var` covers
them, and their per-position pairs are what the table needs. A pair that is
a table pair at renamed bound rows adds none either: `TabRen` reuses it.
Quantified members declared alike in two declarations are compared after
renaming the target's binders to the source's. A head pair recurring,
neither renamed nor smaller, with larger arguments than every earlier one is
growth: the search refuses there. Untrusted: the checker decides
(`checkFamilyAt`). -/

/-- `Var`'s per-position pairs for two applications of one head whose
variance the checker computed. -/
@[nospecialize] def varPairs [DecidableEq ι] {G : NormalGraph ι} (images : InstanceImageCheck G) (A B : List ι) :
    Option (List (List ι × List ι)) :=
  match A, B with
  | [l], [b] => match images.gen l [b] with
    | [w] => (images.base.entry w.1).map fun e => e.hypotheses.map fun h =>
        (replace (e.variables.zip w.2) h.1, replace (e.variables.zip w.2) h.2)
    | _ => none
  | _, _ => none

/-- The rows a pair needs: none for an inclusion, its per-position pairs'
through `Var`, else the pair itself. -/
@[nospecialize] def rowsFor [DecidableEq ι] {G : NormalGraph ι} (images : InstanceImageCheck G) :
    Nat → List ι → List ι → List (List ι × List ι)
  | 0, A, B => [(A, B)]
  | d + 1, A, B => if A.all (· ∈ B) then [] else match varPairs images A B with
    | some ps => ps.flatMap fun (X, Y) => rowsFor images d X Y
    | none => [(A, B)]

/-- Quantified members declared alike, their signatures compared after
renaming the target's binders to the source's. Record members include schemes
stored on the prototype and received by the source object. -/
@[nospecialize] def renamedPairs [DecidableEq ι] (G : NormalGraph ι) (r : Renaming G) (X Y : List ι) :
    List (List ι × List ι) :=
  let pairs (i j : ι) := match G.schemes i, G.schemes j with
    | some s, some s' =>
      if s.binders = s'.binders || s.binders.length != s'.binders.length then [] else
      let σ := s'.binders.zip (s.binders.map fun p => [p])
      signaturePairs s.signatures (s'.signatures.map (Arrow.map (r.substitute σ))) ++
        restPairs s.variadic (s'.variadic.map (RestArrow.map (r.substitute σ))) ++
        s.bounds.flatMap fun b => s'.bounds.filterMap fun b' =>
          if (s.binders.zip s'.binders).lookup b.1 == some b'.1 then some (b'.2, b.2) else none
    | _, _ => []
  let direct := (schemeComponents G X).flatMap fun i => (schemeComponents G Y).flatMap (pairs i)
  let methods := (clausesOf G Y).flatMap fun c => match c with
    | .refs _ _ _ _ ms _ | .dict _ _ _ _ _ ms _ _ => ms
    | _ => []
  direct ++ methods.flatMap fun m =>
    let sources := (protoChain G PositiveRules.protoChainDepth X).flatMap fun P =>
      (PositiveRules.viewOf G P m.key).toList.flatten
    sources.flatMap fun i => m.schemes.flatten.flatMap (pairs i)

/-- A head pair recurring with larger arguments than each of its two or more
earlier occurrences, none of which it renames: growth. -/
@[nospecialize] def grows [DecidableEq ι] {G : NormalGraph ι} (r : Renaming G) (table : Table ι) (A B : List ι) : Bool :=
  let heads (X Y : List ι) : Option (Nat × Nat) := match X, Y with
    | [a], [b] => do some (← r.head a, ← r.head b)
    | _, _ => none
  let size (X Y : List ι) : Nat := ((X ++ Y).map r.size).sum
  match heads A B with
  | some hs =>
    let same := table.filter fun p => heads p.1 p.2 == some hs
    same.length ≥ 2 && same.all fun p => size p.1 p.2 < size A B
  | none => false

/-- Why dependency discovery stops before its frontier closes. -/
inductive SearchStop where
  | growth
  | exhausted
  deriving Repr, DecidableEq

/-- How a table's growth ended, with its counts: the rounds of unfolding, the
candidate pairs visited, and the table. -/
structure Fallback (ι : Type) where
  table : Table ι
  rounds : Nat := 0
  visited : Nat := 0
  /-- A closed frontier has no stop reason. -/
  refused : Option SearchStop := none

/-- The arrow evidence a table's rows ask for, premises decided by `rel`:
each row's arrow clauses against its target's, and each quantified member
against the target's, as declared and with the target's binders renamed to
the source's. -/
@[nospecialize] def rowArrows [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (rel : List ι → List ι → Bool) (table : Table ι) : Evidence ι :=
  let arrows (L : Ops ι) (S : List (RestArrow (List ι))) (M : Ops ι) :=
    M.filterMap fun q =>
      (arrowSearch G rel L S q (q.arguments.length + q.receiver.length + 1)).map (L, q, ·)
  table.flatMap fun (X, Y) =>
    let sources := (sourceClauses G X ++ PositiveRules.meetSources G X Y ++ expand G X).eraseDups
    (sources.flatMap fun a => (clausesOf G Y ++ expand G Y).eraseDups.flatMap fun b => match a, b with
      | .arrs L S, .arrs M _ | .callable _ _ L S, .arrs M _ | .callable _ _ L S, .callable _ _ M _ =>
        arrows L S M
      | _, _ => []) ++
    ((schemeComponents G X).flatMap fun i => (schemeComponents G Y).flatMap fun j => match G.schemes i, G.schemes j with
      | some s, some s' =>
        let renamed := match sub with
          | some r =>
            let σ := s'.binders.zip (s.binders.map fun p => [p])
            s'.signatures.map (Arrow.map (r.substitute σ))
          | none => []
        arrows s.signatures s.variadic (s'.signatures ++ renamed)
      | _, _ => [])

/-- Whether the table covers the pair `p`, premises read in the entry of
`(A, B)` with the table (RECURSIVE-EQUATIONS §4.2), arrows by the evidence
searched for its rows. The check decides (`compareUsing`). -/
@[nospecialize] def coveredIn [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (A B : List ι)
    (known : PositiveRules.Known ι) (table : Table ι) : Evidence ι × (List ι × List ι → Bool) :=
  let f : Entry ι := { source := A, target := B, table }
  let look := images.base.lookup [f]
  let rel : List ι → List ι → Bool := fun X Y => decide (Prem G images.sub look images.gen f X Y)
  let R : List ι → List ι → Prop := fun X Y => rel X Y = true
  let es := rowArrows G images.sub rel (f.pairs)
  (es, fun p =>
    PositiveRules.SameKind G p.1 p.2 &&
    decide (OpaqueFamily G images.sub R known
      (ArrowsCheckedWith G R es) [] p.1 p.2) &&
    (sourceClauses G p.1 ++ PositiveRules.meetSources G p.1 p.2).all fun a =>
      (clausesOf G p.2).any fun b => checkClauseWith G images.sub R known es p.1 a b)

/-- Grow the table from its frontier: each row adds the pairs its coverage
compares (`demandPairs`, and quantified members after renaming), each read
through `Var` where it applies, that no inclusion, row or renamed row already
answers. A pair that reaches no further pair and is not covered by itself
alone is left out: the deletion would remove it. Refuse at growth or past
the execution budget. -/
@[nospecialize] def growTable [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (known : Known ι)
    : Nat → Fallback ι → Table ι → Fallback ι
  | 0, fb, _ => { fb with refused := some .exhausted }
  | fuel + 1, fb, frontier =>
    let reached (p : List ι × List ι) := demandPairs G known p.1 p.2 ++ (match images.sub with
        | some r => renamedPairs G r p.1 p.2
        | none => [])
    let cand := (frontier.flatMap fun p =>
      (reached p).flatMap fun p => match images.sub with
          | some _ => rowsFor images varDepthDefault p.1 p.2
          | none => if p.1.all (· ∈ p.2) then [] else [p])
    let step (st : Except SearchStop (Table ι × Table ι)) (p : List ι × List ι) :
        Except SearchStop (Table ι × Table ι) := do
      let (tbl, fresh) ← st
      let f : Entry ι := { source := [], target := [], table := tbl }
      if premTable G images.sub f p.1 p.2 then return (tbl, fresh)
      if (reached p).isEmpty && (p.1 ++ p.2).all G.plain && !(SameKind G p.1 p.2 &&
          (sourceClauses G p.1).all fun a => (clausesOf G p.2).any fun b =>
            checkClauseWith G images.sub (Rel []) [] [] p.1 a b) then return (tbl, fresh)
      if let some r := images.sub then
        if grows r tbl p.1 p.2 then throw .growth
      return (tbl ++ [p], fresh ++ [p])
    let fb := { fb with rounds := fb.rounds + 1, visited := fb.visited + cand.length }
    match cand.foldl step (.ok (fb.table, [])) with
    | .error why => { fb with refused := some why }
    | .ok (tbl, fresh) =>
      if fresh.isEmpty then { fb with table := tbl }
      else growTable G images known fuel { fb with table := tbl } fresh

/-- Delete the rows a table does not cover, premises read in the table
itself, until every row is covered: the greatest fixed point below the
reachable pairs. With a renaming a premise is the judgment of §4.2 in the
entry of `(A, B)` (`Var`, `Inst`, `TabRen`); without one, a row or an
inclusion. The check decides (`compareUsing`). -/
@[nospecialize] def gfp [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (A B : List ι)
    (known : PositiveRules.Known ι) : Nat → Table ι → Table ι × Evidence ι
  | 0, table => (table, [])
  | fuel + 1, table =>
    let (es, covered) := coveredIn G images A B known table
    let next := table.filter covered
    if next.length = table.length then (table, es) else gfp G images A B known fuel next

/-- A closed structural comparison checked with the equation representation's
renaming and validated base entries. Bound checking uses this same kernel. -/
@[nospecialize] def checkStructural [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (S T : List ι) (known : Known ι) (table : Table ι)
    (arrows : Evidence ι) : Bool :=
  let e := ParameterAssignment.empty .mixed
  let images' := images.reassign e
  let f : Entry ι := { source := S, target := T, table }
  checkEntries (PositiveRules.reassign G e) images'.sub known images'.gen
    (images'.base.lookup [f]) [f] arrows

theorem checkStructural_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T known table arrows}
    (h : checkStructural G images S T known table arrows = true)
    (hk : ∀ η : MixedAssignment ι, ∀ k ∈ known,
      FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  let f : Entry ι := { source := S, target := T, table }
  exact family_closed_sound (G := PositiveRules.reassign G (ParameterAssignment.empty .mixed))
    (checkEntries_sound h)
    ⟨fun g hg => by simp only [List.mem_singleton] at hg; subst hg; simp [],
      fun g hg => by simp only [List.mem_singleton] at hg; subst hg; simp []⟩
    ((images.reassign (ParameterAssignment.empty .mixed)).base.lookup_cases [f]) hk
    List.mem_cons_self rfl List.mem_cons_self

/-- The entry a pair is checked in when no certificate names one: the pair
itself, with no hypothesis and no table. -/
@[nospecialize] def pairEntry (S T : List ι) : Entry ι := { source := S, target := T }

/-- **The premise judgment on a pair** (RECURSIVE-EQUATIONS §4.2–4.3): each
label of `S` in `T`, or below it by `Inst` of a base entry, which is `Var`
with a computed variance, its per-position premises discharged recursively
the same way. Checked at the graph with its assignment fixed, as
`checkFamilyAt`. -/
@[nospecialize] def premAt [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (r : Renaming G)
    (S T : List ι) : Bool :=
  let e := ParameterAssignment.empty .mixed
  let sub := some (r.reassign (G := G) e)
  let fuel := typeSize sub S + typeSize sub T + 1
  premB (PositiveRules.reassign G e) sub ((images.base.reassign e).lookup []) images.gen (pairEntry S T)
      fuel S T

/-- A premise judged in the pair's own entry, citing sound base entries only,
holds at every assignment. -/
theorem premAt_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {r : Renaming G} {S T : List ι} (h : premAt G images r S T = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  let G' := PositiveRules.reassign G (ParameterAssignment.empty .mixed)
  unfold premAt at h
  have hp := (prem_sound (G := G') _).2 _ _ h
  intro η n W x hx
  have hlook := (images.base.reassign (ParameterAssignment.empty .mixed)).lookup_cases
    (G := G') []
  refine (prem_mixed (G := G') (n := n + 1) (η := η) (f := pairEntry S T)
    (fun _ _ h hh => by simp [pairEntry] at hh) (fun h hh => by simp [pairEntry] at hh)
    (fun k e hl _ => ((hlook k e hl).resolve_left (by simp)).2)
    (fun _ _ _ _ p hp => by simp [pairEntry] at hp) (fun h hh => by simp [pairEntry] at hh)
    (fun j _ k e η' hl hh => ((hlook k e hl).resolve_left (by simp)).1.1 j η' hh)).1 hp n
    (Nat.lt_succ_self n) W x hx

/-- `subset`: each label of `S` among `T`'s, or, with a renaming, the
premise judgment on the pair (`Var` for two applications of one head). -/
@[nospecialize] def subsetUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S T : List ι) : Bool :=
  decide (∀ i ∈ S, i ∈ T) || match images.sub with
    | some r => premAt G images r S T
    | none => false

theorem subsetUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T}
    (h : subsetUsing G images S T = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  simp only [subsetUsing, Bool.or_eq_true] at h
  rcases h with h | h
  · exact fun _ => mixed_subset (of_decide_eq_true h)
  · split at h
    · exact premAt_sound h
    · cases h

/-- Check the shared dependencies discovered for a comparison. The family
validator checks recurrence through the guarded rule, at a fixed assignment. -/
@[nospecialize] def comparePrepared [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (S T : List ι) (known : Known ι) (fb : Fallback ι) :
    ComparisonResult Unit :=
  let e := ParameterAssignment.empty .mixed
  let G' := PositiveRules.reassign G e
  let images' := images.reassign e
  -- Instantiated prototype signatures bring their own receiver and argument
  -- premises. Discover these before deleting unsupported table rows.
  let fb := if known.isEmpty then fb else
    growTable G' images' known images.budget.rounds fb fb.table
  let result :=
    match fb.refused with
    | some .exhausted => .exhausted fb.rounds fb.visited
    | some .growth => .notEstablished
    | none =>
      let (table, arrows) := gfp G' images' S T known (fb.table.length + 1) fb.table
      if checkStructural G images S T known table arrows then .established ()
      else .notEstablished
  result

theorem comparePrepared_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T known fb}
    (h : (comparePrepared G images S T known fb).accepted = true)
    (hk : ∀ η : MixedAssignment ι, ∀ k ∈ known,
      FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold comparePrepared at h
  simp only at h
  split at h
  · simp [ComparisonResult.accepted] at h
  · simp [ComparisonResult.accepted] at h
  · split at h <;> split at h
    all_goals first
      | exact checkStructural_sound (by assumption) hk
      | simp [ComparisonResult.accepted] at h

/-- Structural comparison over equations. Identity and validated variance
share the guarded dependency kernel used by quantified instantiation. -/
@[nospecialize] def compareStructural [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (S T : List ι) (known : Known ι := []) : ComparisonResult Unit :=
  let e := ParameterAssignment.empty .mixed
  let G' := PositiveRules.reassign G e
  let images' := images.reassign e
  if subsetUsing G' images' S T then .established () else
  comparePrepared G images S T known
    (growTable G' images' [] images.budget.rounds { table := [(S, T)] } [(S, T)])

theorem compareStructural_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T known}
    (h : (compareStructural G images S T known).accepted = true)
    (hk : ∀ η : MixedAssignment ι, ∀ k ∈ known,
      FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold compareStructural at h
  simp only at h
  split at h
  · exact subsetUsing_sound (G := PositiveRules.reassign G (ParameterAssignment.empty .mixed))
      (by assumption)
  · exact comparePrepared_sound h hk

/-- An instantiated binder's bound is a comparison supplied by the enclosing
engine. The identity value represents a binder absent from this instance. -/
@[nospecialize] def compareBoundState [DecidableEq ι]
    (compare : List ι → List ι → σ → ComparisonResult α × σ) (empty : α)
    (binders : List ι) (θs : List (List ι)) (b : ι × List ι) (state : σ) : ComparisonResult α × σ :=
  match (binders.zip θs).lookup b.1 with
  | none => (.established empty, state)
  | some U => compare U b.2 state

/-- The instance rule validates kinds, signature images, admissibility and the
representation's image table, then asks its enclosing subtype operation to
discharge every bound. Successful bound comparisons retain their proposal data. -/
@[nospecialize] def compareInstArrsState [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (compare : List ι → List ι → σ → ComparisonResult α × σ) (empty : α)
    (S : List ι) (L : Ops ι) (M : List (RestArrow (List ι))) (c : Instance ι) (state : σ)
    (admission : SchemeRow ι → Instance ι → ComparisonResult Unit := images.compareAllowed) :
    ComparisonResult (List α) × σ :=
  match S with
  | [i] =>
    match G.schemes i with
    | some s =>
      if !G.params i && !s.construct && c.instances.length == s.binders.length &&
          instKinds G s.binders c.instances &&
          (L.all fun q => s.signatures.any fun p => instSig G c.table (s.binders.zip c.instances) p q) &&
          (M.all fun q => s.variadic.any fun p => instRest G c.table (s.binders.zip c.instances) p q) then
        match (images.compare s.binders c).andThen (fun _ => admission s c) with
        | .established _ =>
          ComparisonResult.collectState (compareBoundState compare empty s.binders c.instances) s.bounds state
        | .notEstablished => (.notEstablished, state)
        | .exhausted rounds visited => (.exhausted rounds visited, state)
      else (.notEstablished, state)
    | none => (.notEstablished, state)
  | _ => (.notEstablished, state)

/-- State carried between bound premises affects search reuse, while each
established premise has its own semantic justification. -/
theorem compareInstArrsState_sound_at [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {compare : List ι → List ι → σ → ComparisonResult α × σ} {empty S L M c state}
    {admission : SchemeRow ι → Instance ι → ComparisonResult Unit}
    (η : MixedAssignment ι)
    (hadmission : ∀ s c, (admission s c).accepted = true →
      G.domain.allowed s (c.instances.map fun U =>
        ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩))
    (hc : ∀ U V prior, (compare U V prior).1.accepted = true →
      FamLe (mixedMeaning G η U) (mixedMeaning G η V))
    (h : (compareInstArrsState G images compare empty S L M c state admission).1.accepted = true) :
    FamLe (mixedValues G η S) (mixedSem G η (.arrs L M)) := by
  unfold compareInstArrsState at h
  split at h
  · rename_i i
    split at h
    · rename_i s hs
      split at h
      · rename_i shape
        split at h
        · rename_i image imagesOk
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
            beq_iff_eq] at shape
          obtain ⟨⟨⟨⟨⟨hp, hcon⟩, hlen⟩, hkinds⟩, hL⟩, hM⟩ := shape
          have checked : ((images.compare s.binders c).andThen
              (fun _ => admission s c)).accepted = true := by rw [imagesOk]; rfl
          simp only [ComparisonResult.accepted_andThen, Bool.and_eq_true] at checked
          have himg := checked.1
          intro n W v hv
          refine ⟨inst_images_sound η hp hs hcon hlen (hadmission s c checked.2) ?_
            (images.sound s.binders c hlen hkinds himg η) hL hM n W v hv,
            builtinInvariant_of_withoutInvariant rfl n W v⟩
          intro b hb U hU
          obtain ⟨prior, checked⟩ := ComparisonResult.collectState_sound _ _ _ h b hb
          unfold compareBoundState at checked
          rw [hU] at checked
          exact hc U b.2 prior checked
        · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Unconditional instance evidence is the special case valid at every
assignment. The executable instance check is shared with scoped evidence. -/
theorem compareInstArrsState_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {compare : List ι → List ι → σ → ComparisonResult α × σ} {empty S L M c state}
    (hc : ∀ U V prior, (compare U V prior).1.accepted = true →
      ∀ η, FamLe (mixedMeaning G η U) (mixedMeaning G η V))
    (h : (compareInstArrsState G images compare empty S L M c state).1.accepted = true) :
    ∀ η, FamLe (mixedValues G η S) (mixedSem G η (.arrs L M)) := by
  intro η
  exact compareInstArrsState_sound_at η
    (fun s c hc => images.allowed_sound s c hc η)
    (fun U V prior h => hc U V prior h η) h

#print axioms compareInstArrsState_sound_at

/-- Quantified instantiation establishes a value, rather than an argument pack. -/
theorem compareInstArrsState_source [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {compare : List ι → List ι → σ → ComparisonResult α × σ} {empty S L M c state}
    (h : (compareInstArrsState G images compare empty S L M c state).1.accepted = true) :
    ∃ i s, S = [i] ∧ G.schemes i = some s ∧ G.params i = false := by
  unfold compareInstArrsState at h
  split at h
  · rename_i i
    split at h
    · rename_i s hs
      split at h
      · rename_i shape
        exact ⟨i, s, rfl, hs, by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at shape
          exact shape.1.1.1.1.1⟩
      · cases h
    · cases h
  · cases h

/-- An arrow contract, together with every opaque part of its target meet. -/
@[nospecialize] def instanceTarget (G : NormalGraph ι) (T : List ι) :
    Option (Ops ι × List (RestArrow (List ι)) × List ι) :=
  match expand G T with
  | [.arrs L M] => some (L, M, [])
  | _ => match T with
    | [j] =>
      if G.meetRow j && (meetParts G j).all G.partRow then
        match meetClauses G j with
        | [.arrs L M] => some (L, M, meetParts G j)
        | _ => none
      else none
    | _ => none

/-- The target is established by its arrow contract and each opaque meet part. -/
theorem instanceTarget_value [DecidableEq ι] {G : NormalGraph ι} {T L M parts}
    (h : instanceTarget G T = some (L, M, parts)) (η : MixedAssignment ι) (n : Nat) (W : WorldT n) (v : Val)
    (ha : mixedSem G η (.arrs L M) n W v)
    (hp : ∀ q ∈ parts, mixedMeaning G η [q] n W (.inl v)) :
    mixedMeaning G η T n W (.inl v) := by
  unfold instanceTarget at h
  split at h
  · cases h
    exact mixed_of_expand (by assumption) ha
  · split at h
    · rename_i j hT
      split at h
      · rename_i hm
        split at h
        · rename_i L' M' hclauses
          cases h
          simp only [Bool.and_eq_true, List.all_eq_true] at hm
          refine ⟨j, List.mem_singleton_self _, (meet_row_iff hm.1).mpr ⟨?_, ?_⟩⟩
          · intro q hq
            obtain ⟨r, hr, hv⟩ := hp q hq
            cases List.mem_singleton.mp hr
            exact (part_denote (hm.2 q hq)).mp hv
          · exact ⟨.arrs L M, by rw [hclauses]; exact List.mem_singleton_self _, ha⟩
        · cases h
      · cases h
    · cases h

/-- Instantiate the arrow portion of a target and independently establish every
opaque meet part through the enclosing comparison operation. -/
@[nospecialize] def compareInstState [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (compare : List ι → List ι → σ → ComparisonResult α × σ) (empty : α)
    (S T : List ι) (c : Instance ι) (state : σ) : ComparisonResult (List α) × σ :=
  match instanceTarget G T with
  | some (L, M, parts) =>
    let (arrows, next) := compareInstArrsState G images compare empty S L M c state
    match arrows with
    | .established bounds =>
      let (components, last) := ComparisonResult.collectState (fun q => compare S [q]) parts next
      (components.map fun partials => bounds ++ partials, last)
    | .notEstablished => (.notEstablished, next)
    | .exhausted rounds visited => (.exhausted rounds visited, next)
  | none => (.notEstablished, state)

theorem compareInstState_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {compare : List ι → List ι → σ → ComparisonResult α × σ} {empty S T c state}
    (hc : ∀ U V prior, (compare U V prior).1.accepted = true →
      ∀ η, FamLe (mixedMeaning G η U) (mixedMeaning G η V))
    (h : (compareInstState G images compare empty S T c state).1.accepted = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold compareInstState at h
  split at h
  · rename_i L M parts htarget
    rcases step : compareInstArrsState G images compare empty S L M c state with ⟨arrows, next⟩
    cases arrows with
    | notEstablished => simp only [step, ComparisonResult.accepted] at h; cases h
    | exhausted rounds visited => simp only [step, ComparisonResult.accepted] at h; cases h
    | established bounds =>
      have ha : (compareInstArrsState G images compare empty S L M c state).1.accepted = true := by
        rw [step]; rfl
      have values := compareInstArrsState_sound hc ha
      obtain ⟨i, s, hS, hs, hi⟩ := compareInstArrsState_source ha
      subst S
      have components : (ComparisonResult.collectState (fun q => compare [i] [q]) parts next).1.accepted = true := by
        simpa only [step, ComparisonResult.accepted_map] using h
      intro η n W x hx
      cases x with
      | inl v =>
        apply instanceTarget_value htarget η n W v (values η n W v hx)
        intro q hq
        obtain ⟨prior, checked⟩ := ComparisonResult.collectState_sound _ _ _ components q hq
        exact hc [i] [q] prior checked η n W (.inl v) hx
      | inr vs =>
        have hk : G.parameterKinds i = none := by simpa [NormalGraph.params] using hi
        have hcs : G i = [] := by simp [NormalGraph.clauses, NormalGraph.plain, hs]
        simp [mixedMeaning, mixedParameters, graphArguments, hk, hcs, NormalGraph.listParam] at hx
  · cases h

/-- Candidate construction supplies choices; this operation selects an instance
only after checking its images, bounds and every target component. -/
@[nospecialize] def compareInstancesState [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (compare : List ι → List ι → σ → ComparisonResult α × σ) (empty : α)
    (S T : List ι) (candidates : List (Instance ι)) (state : σ) : ComparisonResult (Instance ι × List α) × σ :=
  ComparisonResult.firstState (fun c prior =>
    let (result, next) := compareInstState G images compare empty S T c prior
    (result.map (c, ·), next)) candidates state

theorem compareInstancesState_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {compare : List ι → List ι → σ → ComparisonResult α × σ} {empty S T candidates state}
    (hc : ∀ U V prior, (compare U V prior).1.accepted = true →
      ∀ η, FamLe (mixedMeaning G η U) (mixedMeaning G η V))
    (h : (compareInstancesState G images compare empty S T candidates state).1.accepted = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold compareInstancesState at h
  obtain ⟨c, _, prior, checked⟩ := ComparisonResult.firstState_sound _ _ _ h
  simp only [ComparisonResult.accepted_map] at checked
  exact compareInstState_sound hc checked

/-- The rows a family certificate's instances prove. -/
@[nospecialize] def knownOf (ks : List (KnownInstance ι)) :
    Known ι := ks.map fun k => (k.1, k.2.1, k.2.2.1)

/-- Entries checked on their own, such as a component of variances citing
the ones computed before it, are sound. -/
theorem checkEntries_entries_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι} {F : List (Entry ι)}
    {arrows : Evidence ι} (h : checkEntries G sub [] gen look F arrows = true)
    (hv : variablesOk sub F = true)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e)) :
    ∀ e ∈ F, EntrySound G e :=
  family_entries_sound (checkEntries_sound h) (variablesOk_sound hv) hlook
    (fun _ _ h => by simp at h)

/-- The instantiation choices used below a comparison, including its root
instance when its target is an arrow contract. The checker validates every use. -/
@[nospecialize] def SubtypeChoices.dependencies [DecidableEq ι] (G : NormalGraph ι)
    (S T : List ι) (p : SubtypeChoices ι) : List (KnownInstance ι) :=
  p.members ++ match p.instantiation, instanceTarget G T with
    | some c, some (L, M, _) => [(S, L, M, c)]
    | _, _ => []

/-- One comparison step: select a checked instance or validate the shared
structural dependencies. Its bound premises use the supplied comparison operation. -/
@[nospecialize] def compareStepState [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (compare : List ι → List ι → σ → ComparisonResult (List (KnownInstance ι)) × σ)
    (S T : List ι) (instantiation : List ι → List ι → List (Instance ι))
    (members : Table ι → List (KnownInstance ι)) (state : σ) : ComparisonResult (SubtypeChoices ι) × σ :=
  if subsetUsing G images S T then (.established {}, state) else
  let (selected, next) := compareInstancesState G images compare [] S T (instantiation S T) state
  let root : ComparisonResult (SubtypeChoices ι) := selected.map fun (c, dependencies) =>
    { instantiation := some c, members := dependencies.flatten }
  ComparisonResult.orElseState (root, next) fun prior =>
    let e := ParameterAssignment.empty .mixed
    let fb := growTable (PositiveRules.reassign G e) (images.reassign e) [] images.budget.rounds
      { table := [(S, T)] } [(S, T)]
    let (tested, last) := mapResultsState (fun k current =>
      let (checked, next) := compareInstArrsState G images compare [] k.1 k.2.1 k.2.2.1 k.2.2.2 current
      ((k, checked), next)) (members fb.table) prior
    let accepted := tested.filter fun k => k.2.accepted
    let ks := accepted.map Prod.fst
    let dependencies : List (KnownInstance ι) := accepted.flatMap fun k => match k.2 with
      | .established ds => ds.flatten
      | .notEstablished | .exhausted _ _ => []
    ComparisonResult.orElseState
      ((comparePrepared G images S T (knownOf ks) fb).map fun _ => { members := ks ++ dependencies }, last)
      fun current => (ComparisonResult.exhaustion (tested.map fun k => k.2.map fun _ => ()), current)

theorem compareStepState_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {compare : List ι → List ι → σ → ComparisonResult (List (KnownInstance ι)) × σ}
    {S T instantiation members state}
    (hc : ∀ A B prior, (compare A B prior).1.accepted = true →
      ∀ η, FamLe (mixedMeaning G η A) (mixedMeaning G η B))
    (h : (compareStepState G images compare S T instantiation members state).1.accepted = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold compareStepState at h
  split at h
  · exact subsetUsing_sound (by assumption)
  · rcases selection : compareInstancesState G images compare [] S T (instantiation S T) state with ⟨selected, next⟩
    simp only [selection, ComparisonResult.orElseState_accepted, ComparisonResult.accepted_map] at h
    rcases Bool.or_eq_true_iff.mp h with root | fallback
    · apply compareInstancesState_sound hc
      rw [selection]
      exact root
    · let e : MixedAssignment ι := ParameterAssignment.empty .mixed
      let fb := growTable (PositiveRules.reassign G e) (images.reassign e) [] images.budget.rounds
        { table := [(S, T)] } [(S, T)]
      let checkMember (k : KnownInstance ι) (current : σ) :=
        let (checked, next) := compareInstArrsState G images compare [] k.1 k.2.1 k.2.2.1 k.2.2.2 current
        ((k, checked), next)
      rcases traversal : mapResultsState checkMember (members fb.table) next with ⟨tested, last⟩
      simp only [ComparisonResult.accepted_exhaustion, Bool.or_false] at fallback
      change (comparePrepared G images S T
        (knownOf (((mapResultsState checkMember (members fb.table) next).1.filter fun k => k.2.accepted).map Prod.fst)) fb).accepted = true at fallback
      rw [traversal] at fallback
      apply comparePrepared_sound fallback
      intro η k hm
      simp only [knownOf, List.mem_map, List.mem_filter] at hm
      obtain ⟨q, ⟨pair, ⟨member, checked⟩, hq⟩, hk⟩ := hm
      obtain ⟨candidate, _, prior, produced⟩ := mapResultsState_mem checkMember (members fb.table) next
        (by rw [traversal]; exact member)
      have same : pair.1 = candidate := congrArg Prod.fst produced
      have checked' : (compareInstArrsState G images compare [] candidate.1 candidate.2.1 candidate.2.2.1 candidate.2.2.2 prior).1.accepted = true := by
        simpa only [produced, checkMember] using checked
      subst q
      subst k
      rw [same]
      exact compareInstArrsState_sound hc checked' η

/-- A completed comparison carries the semantic judgment its choices establish.
The proof quantifies over every assignment of the equation parameters. -/
structure CheckedComparison (G : NormalGraph ι) (S T : List ι) where
  choices : SubtypeChoices ι
  sound : ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T)

/-- Search-local completed results. Equation labels identify the binder context;
the enclosing engine fixes the equation store and its image checker. -/
structure CompletedComparison (G : NormalGraph ι) where
  source : List ι
  target : List ι
  checked : CheckedComparison G source target

/-- Exact queries reuse completed judgments. In-progress queries have no entry. -/
@[nospecialize] def completedLookup [DecidableEq ι] (G : NormalGraph ι)
    (S T : List ι) : List (CompletedComparison G) → Option (CheckedComparison G S T)
  | [] => none
  | entry :: rest =>
    if hs : entry.source = S then
      if ht : entry.target = T then
        some {
          choices := entry.checked.choices
          sound := by
            rw [← hs, ← ht]
            exact entry.checked.sound }
      else completedLookup G S T rest
    else completedLookup G S T rest

theorem CheckedComparison.result_sound {G : NormalGraph ι} {S T : List ι}
    {result : ComparisonResult (CheckedComparison G S T)} (h : result.accepted = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  cases result with
  | established checked => exact checked.sound
  | notEstablished => cases h
  | exhausted rounds visited => cases h

/-- Guarded structural evidence can complete a repeated query. Only an
established structural check publishes a completed result. -/
@[nospecialize] def compareStructuralCached [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (S T : List ι) (cache : List (CompletedComparison G)) :
    ComparisonResult (CheckedComparison G S T) × List (CompletedComparison G) :=
  match completedLookup G S T cache with
  | some checked => (.established checked, cache)
  | none =>
    match h : compareStructural G images S T with
    | .established _ =>
      let checked : CheckedComparison G S T :=
        { choices := {}, sound := compareStructural_sound (by rw [h]; rfl) (fun _ _ hm => by simp at hm) }
      (.established checked, { source := S, target := T, checked } :: cache)
    | .notEstablished => (.notEstablished, cache)
    | .exhausted rounds visited => (.exhausted rounds visited, cache)

/-- Instance premises share completed results across siblings and alternatives.
A repeated unfinished query requires the guarded structural checker. -/
@[nospecialize] def compareCheckedStep [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (instantiation : List ι → List ι → List (Instance ι))
    (members : Table ι → List (KnownInstance ι))
    (recur : ∀ A B : List ι, List (CompletedComparison G) →
      ComparisonResult (CheckedComparison G A B) × List (CompletedComparison G))
    (path : Table ι) (S T : List ι) (cache : List (CompletedComparison G)) :
    ComparisonResult (CheckedComparison G S T) × List (CompletedComparison G) :=
  match completedLookup G S T cache with
  | some checked => (.established checked, cache)
  | none =>
    let compare : List ι → List ι → List (CompletedComparison G) →
        ComparisonResult (List (KnownInstance ι)) × List (CompletedComparison G) := fun A B prior =>
      if (A, B) ∈ (S, T) :: path then
        let (result, next) := compareStructuralCached G images A B prior
        (result.map fun checked => checked.choices.dependencies G A B, next)
      else
        let (result, next) := recur A B prior
        (result.map fun checked => checked.choices.dependencies G A B, next)
    have hc : ∀ A B prior, (compare A B prior).1.accepted = true →
        ∀ η, FamLe (mixedMeaning G η A) (mixedMeaning G η B) := by
      intro A B prior h
      dsimp only [compare] at h
      split at h
      · rw [ComparisonResult.accepted_map] at h
        exact CheckedComparison.result_sound h
      · rw [ComparisonResult.accepted_map] at h
        exact CheckedComparison.result_sound h
    let step := compareStepState G images compare S T instantiation members cache
    match h : step.1 with
    | .established choices =>
      let checked : CheckedComparison G S T :=
        { choices, sound := compareStepState_sound hc (by change step.1.accepted = true; rw [h]; rfl) }
      (.established checked, { source := S, target := T, checked } :: step.2)
    | .notEstablished => (.notEstablished, step.2)
    | .exhausted rounds visited => (.exhausted rounds visited, step.2)

@[nospecialize] def compareUsingCoreState [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (instantiation : List ι → List ι → List (Instance ι))
    (members : Table ι → List (KnownInstance ι))
    (depth : Nat) (path : Table ι) (S T : List ι) (cache : List (CompletedComparison G)) :
    ComparisonResult (CheckedComparison G S T) × List (CompletedComparison G) :=
  match depth with
  | 0 => compareCheckedStep G images instantiation members (fun A B prior =>
      let (result, next) := compareStructuralCached G images A B prior
      (result.orElse (fun _ => .exhausted images.budget.rounds 0), next)) path S T cache
  | remaining + 1 => compareCheckedStep G images instantiation members
      (fun A B prior => compareUsingCoreState G images instantiation members remaining ((S, T) :: path) A B prior)
      path S T cache
termination_by depth

/-- The engine's cache belongs to one fixed equation environment. Parameter
reassignment changes meanings, while every cached proof holds for all of them. -/
@[nospecialize] def compareUsingCore [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (instantiation : List ι → List ι → List (Instance ι))
    (members : Table ι → List (KnownInstance ι))
    (depth : Nat) (path : Table ι) (S T : List ι) : ComparisonResult (SubtypeChoices ι) :=
  let e := ParameterAssignment.empty .mixed
  ((compareUsingCoreState (PositiveRules.reassign G e) (images.reassign e)
    instantiation members depth path S T []).1).map (·.choices)

theorem compareUsingCore_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {instantiation members depth path S T}
    (h : (compareUsingCore G images instantiation members depth path S T).accepted = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold compareUsingCore at h
  rw [ComparisonResult.accepted_map] at h
  exact CheckedComparison.result_sound (G := PositiveRules.reassign G (ParameterAssignment.empty .mixed)) h

/-- Explicit type arguments select from supplied instances with the same checked
comparison state used by ordinary instantiation and its bound premises. -/
@[nospecialize] def selectInstancesUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S T : List ι) (candidates : List (Instance ι))
    (instantiation : List ι → List ι → List (Instance ι))
    (members : Table ι → List (KnownInstance ι)) : ComparisonResult (Instance ι × List (List (KnownInstance ι))) :=
  let e := ParameterAssignment.empty .mixed
  let G' := PositiveRules.reassign G e
  let images' := images.reassign e
  let compare := fun A B prior =>
    let (result, next) := compareUsingCoreState G' images' instantiation members images.budget.rounds [(S, T)] A B prior
    (result.map fun checked => checked.choices.dependencies G' A B, next)
  (compareInstancesState G' images' compare [] S T candidates []).1

/-- One subtype operation for evidence production and checking. Proposal functions
choose instances for the comparisons requested by the engine. -/
@[nospecialize] def compareUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S T : List ι) (instantiation : List ι → List ι → List (Instance ι))
    (members : Table ι → List (KnownInstance ι)) : ComparisonResult (SubtypeChoices ι) :=
  compareUsingCore G images instantiation members images.budget.rounds [] S T

theorem compareUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T instantiation members}
    (h : (compareUsing G images S T instantiation members).accepted = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) :=
  compareUsingCore_sound h

/-- Find a supplied instance for the comparison the engine requests. Root choices
and supporting choices carry the same instance data and receive the same validation. -/
@[nospecialize] def SubtypeChoices.proposal [DecidableEq ι] (G : NormalGraph ι)
    (S T : List ι) (p : SubtypeChoices ι) (A B : List ι) : List (Instance ι) :=
  (if A == S && B == T then p.instantiation.toList else []) ++
    (p.members.filter fun k => k.1 == A &&
      ((instanceTarget G B).map fun target => (target.1, target.2.1)) == some (k.2.1, k.2.2.1)).map (·.2.2.2)

/-- Public evidence carries instantiation choices. The common operation
selects and validates the subtype rule. -/
@[nospecialize] def checkUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S T : List ι) (p : SubtypeChoices ι) : Bool :=
  (compareUsing G images S T (p.proposal G S T) (fun _ => p.members)).accepted

theorem checkUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T proof}
    (h : checkUsing G images S T proof = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) :=
  compareUsing_sound h

/-- A proved image checker supplies ordinary value subsumption as well as
mixed inclusion. Program typing uses this interface. -/
theorem acceptedUsing [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T proof}
    (h : checkUsing G images S T proof = true) : FamLe (meaning G S) (meaning G T) :=
  fun n W v hv => checkUsing_sound h G.env n W (.inl v) hv

#print axioms compareInstState_sound
#print axioms checkUsing_sound
#print axioms checkEntries_sound
#print axioms checkEntries_entries_sound
#print axioms prem_iff
#print axioms premAt_sound
#print axioms compareUsing_sound
#print axioms comparePrepared_sound
#print axioms checkStructural_sound
#print axioms compareStructural_sound
#print axioms compareInstancesState_sound
#print axioms compareInstArrsState_sound
#print axioms compareUsingCore_sound
end Verification.PositiveCertificates
