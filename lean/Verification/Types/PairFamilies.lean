import Verification.Types.SchemeInstances

/-! ## Families of pairs

A family entry
(RECURSIVE-EQUATIONS §7) holds its pairs where its hypotheses hold: its
variables are parameter rows, and one entry stands for every pair that is
an instance of it. One level induction justifies both (`pairs_sound`),
parameterized by the relation premises are read through: an ordinary table
is the case without hypotheses, a family the case whose
premises may be instances of its entries (`family_sound`). -/
namespace Verification.PositiveRules
open PositiveNormalization PositiveGraphs ReferenceConjunctions Tower CallEffects

/-- Sorted argument types contribute pack clauses only. -/
private theorem argument_clause {G : NormalGraph ι} {S : List ι}
    (hs : G.hasKind .arguments S = true) {c : Clause (List ι)} (hc : c ∈ clausesOf G S) :
    ∃ a bs, c = .pack a bs := by
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  have hp := NormalGraph.plain_of_clauses hc
  have hparts := NormalGraph.plain_iff.mp hp
  have hkind : G.parameterKinds i = none := by simpa [NormalGraph.params] using hparts.1
  have hk := List.all_eq_true.mp hs i hi
  have hm : c ∈ G.rows i := by simpa [NormalGraph.clauses, hp] using hc
  simp only [hkind, hparts.2.1, hparts.2.2, Option.isSome_none, Bool.or_false,
    Bool.false_eq_true, ite_false] at hk
  have hh := List.all_eq_true.mp hk c hm
  cases c <;> simp_all


/-- Both components of one type within another's, at one level. -/
@[nospecialize] def MixedLe (G : NormalGraph ι) (η : MixedAssignment ι) (A B : List ι) (n : Nat) : Prop :=
  ∀ (W : WorldT n) x, mixedMeaning G η A n W x → mixedMeaning G η B n W x

theorem MixedLe.values {G : NormalGraph ι} {η : MixedAssignment ι} {A B : List ι} {n : Nat}
    (h : MixedLe G η A B n) : FamLeAt G η A B n := fun W v hv => h W (.inl v) hv

/-- Hypotheses hold at every level up to `n`, in both components. -/
@[nospecialize] def HypsHold (G : NormalGraph ι) (η : MixedAssignment ι) (hyps : List (ι × ι)) (n : Nat) : Prop :=
  ∀ h ∈ hyps, ∀ j, j ≤ n → MixedLe G η [h.1] [h.2] j

/-- Hypotheses hold below `n`, and for values at `n`: what proving values at
`n` reads. -/
@[nospecialize] def HypsHoldValues (G : NormalGraph ι) (η : MixedAssignment ι) (hyps : List (ι × ι))
    (n : Nat) : Prop :=
  (∀ h ∈ hyps, ∀ j, j < n → MixedLe G η [h.1] [h.2] j) ∧ ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] n

theorem HypsHold.values {G : NormalGraph ι} {η : MixedAssignment ι} {hyps : List (ι × ι)}
    {n : Nat} (h : HypsHold G η hyps n) : HypsHoldValues G η hyps n :=
  ⟨fun p hp j hj => h p hp j (Nat.le_of_lt hj), fun p hp => (h p hp n (Nat.le_refl n)).values⟩

/-- **Quantified-α** (RECURSIVE-EQUATIONS §6). A scheme row's quantified
signatures cover another's up to renaming the target's binders to the
source's: as many binders, distinct on each side, of pairwise equal kinds;
each source bound on a binder matched by the target's bound on the renamed
binder, which is within it (read outside both schemes); no source binder free
in the target's signatures unless it is also a target binder; and the
source's signatures cover the target's renamed. The renaming is the
checker's own substitution, never a certificate's. -/
@[nospecialize] def SchemeRenames [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop) (i j : ι) : Prop :=
  match sub, G.schemes i, G.schemes j with
  | some r, some s, some s' =>
    G.params i = false ∧ G.params j = false ∧
    s.binders.length = s'.binders.length ∧ s.binders.Nodup ∧ s'.binders.Nodup ∧
    (∀ pq ∈ s.binders.zip s'.binders, G.parameterKinds pq.1 = G.parameterKinds pq.2) ∧
    (∀ b ∈ s.bounds, ∃ b' ∈ s'.bounds,
      (s.binders.zip s'.binders).lookup b.1 = some b'.1 ∧ R b'.2 b.2) ∧
    (∀ A ∈ s'.body.operands, ∀ x ∈ r.free A,
      x ∈ s.binders → x ∈ s'.binders) ∧ sameShape s s' = true ∧
    CoversWith G none R known arrows [] s.body
      (s'.body.map (r.substitute (s'.binders.zip (s.binders.map fun p => [p]))))
  | _, _, _ => False

/-- The quantified rule: the same binders (`SchemeCoversWith`), of which
renaming is the general case. -/
@[nospecialize] def SchemeCoversAlpha [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop) (i j : ι) : Prop :=
  SchemeCoversWith G R known arrows i j ∨ SchemeRenames G sub R known arrows i j

/-- A meet part of a family pair below another (RECURSIVE-EQUATIONS §3.3,
§7.3): a scheme whose signatures cover the other's up to renaming, or a
variable below the other by a hypothesis. Without hypotheses it is
quantified coverage alone. -/
@[nospecialize] def PartCovers [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop)
    (hyps : List (ι × ι)) (a b : ι) : Prop :=
  SchemeCoversAlpha G sub R known arrows a b ∨ (a, b) ∈ hyps

/-- Opaque rows of a family pair: as for a pair without hypotheses, and a
row may also be below a target row by a hypothesis, and a scheme row below
one whose signatures its own cover up to renaming. A meet reads its parts
the same way (`PartCovers`): a target meet's variable part is covered by a
source part, or the source row, below it by a hypothesis. -/
@[nospecialize] def OpaqueFamily [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop)
    (hyps : List (ι × ι)) (S T : List ι) : Prop :=
  ∀ i ∈ S, G.plain i = true ∨ i ∈ T ∨ OpaqueUniverse G T i ∨
    MeetOpaque G (PartCovers G sub R known arrows hyps)
      (fun a => ∃ b ∈ clausesOf G T, CoversWith G sub R known arrows S a b) T i ∨
    (∃ y ∈ T, (i, y) ∈ hyps) ∨ ∃ j ∈ T, SchemeCoversAlpha G sub R known arrows i j

theorem SchemeCoversAlpha.mono [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι}
    {arrows arrows' : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    (ha : ∀ L S M, arrows L S M → arrows' L S M) {i j : ι}
    (h : SchemeCoversAlpha G sub R known arrows i j) : SchemeCoversAlpha G sub R known arrows' i j := by
  rcases h with h | h
  · left
    unfold SchemeCoversWith at h ⊢
    split at h
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        CoversWith.mono ha h.2.2.2.2.2⟩
    · exact h.elim
  · right
    unfold SchemeRenames at h ⊢
    split at h
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hord, h9⟩ := h
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hord, CoversWith.mono ha h9⟩
    · exact h.elim

theorem OpaqueFamily.mono [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι}
    {arrows arrows' : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    (ha : ∀ L S M, arrows L S M → arrows' L S M) {hyps : List (ι × ι)} {S T : List ι}
    (h : OpaqueFamily G sub R known arrows hyps S T) : OpaqueFamily G sub R known arrows' hyps S T := by
  intro i hi
  rcases h i hi with h | h | h | h | h | ⟨j, hj, hc⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl (h.mono (fun _ _ => Or.imp_left (SchemeCoversAlpha.mono ha))
      fun a ⟨b, hb, hc⟩ => ⟨b, hb, CoversWith.mono ha hc⟩))))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨j, hj, SchemeCoversAlpha.mono ha hc⟩))))

/-- The three core conditions for one pair (POSITIVE-TYPES "Core tables",
RECURSIVE-EQUATIONS §7.3), premises read through `R`. -/
@[nospecialize] def PairOk [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (known : Known ι)
    (R : List ι → List ι → Prop) (hyps : List (ι × ι)) (A B : List ι) : Prop :=
  SameKind G A B = true ∧
    OpaqueFamily G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) hyps A B ∧
    ∀ a ∈ sourceClauses G A ++ meetSources G A B hyps, ClauseCovered G sub R known A a B

/-- **Quantified-α, soundly.** At every instance the target admits, the
source admits it too at its own binders (each bound is matched); there the
source's signatures give the target's renamed ones, whose meaning at the
source's instance is the target's at its own (`renamed_meaning`). -/
theorem renames_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {sub : Option (Renaming G)} {R : List ι → List ι → Prop} {known : Known ι} {i j : ι}
    (hc : SchemeRenames G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n) (W : WorldT n) (v : Val)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  unfold SchemeRenames at hc
  split at hc
  · rename_i r s s' hs hs'
    obtain ⟨hpi, hpj, hlen, hnp, hnq, hkinds, hbnd, hfresh, hord, hcov⟩ := hc
    rw [qDenoteWithArgs_unfold] at hv ⊢
    simp only [qLayerWithArgs, hpi, hpj, hs, hs', Bool.false_eq_true, if_false] at hv ⊢
    refine ⟨sameShape_construct hord ▸ hv.1, fun q hq As hl _hal hb => ?_⟩
    have hall := hv.2 q hq
    have hre : ReassignSound G η R q := fun i s As hs =>
      ⟨fun k hk => (hre i s As hs).1 k (by omega),
       fun k hk => (hre i s As hs).2 k (by omega)⟩
    have hr := fun k (hk : k < q) => hr k (by omega)
    have hpa := fun k (hk : k < q) => hpa k (by omega)
    let W := trunc q hq W
    let n := q
    have hal := (sameShape_allowed G.domain hord As).mpr _hal
    have hb' : Bounded (fun θ S => (mixedParameters G).bound θ
        (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As n := by
      intro b hbm hbin k hk U u hu
      obtain ⟨b', hb'm, hlk, hR⟩ := hbnd b hbm
      obtain ⟨m, hm1, hm2, hpb', hqb'⟩ := lookup_zip_index hlk
      have heq : (assign η s.binders As).1 b.1 = (assign η s'.binders As).1 b'.1 := by
        rw [← hpb', ← hqb', assign_getElem η hnp (by omega) m hm1,
          assign_getElem η hnq (by omega) m hm2]
      have hin : b'.1 ∈ s'.binders := hqb' ▸ List.getElem_mem hm2
      have hu' := hb b' hb'm hin k hk U u (heq ▸ hu)
      cases u with
      | inl w => exact hr k hk _ _ hR U w hu'
      | inr ws => exact hpa k hk _ _ hR U ws hu'
    have hi : semWithArgs (excOf G) (mixedValues G (assign η s.binders As)) (mixedArgs G (assign η s.binders As))
        s.body n W v := (instance_body G η s As) ▸ hall As (by rw [hlen]; exact hl) hal hb'
    have hcovered := covers_body_sound hcov (by
      unfold SchemeRow.body; rw [sameShape_construct hord]
      cases s'.construct <;> simp [Clause.map, mapFields]) n (hre i s As hs).1 (hre i s As hs).2 W v hi
    show instanceTWithArgs _ _ η s' As _ n W v
    rw [instance_body]
    rw [← semWithArgs_map_meaning (η := assign η s.binders As)
      (f := r.substitute (s'.binders.zip (s.binders.map fun p => [p]))) fun S hS => ?_]
    · exact hcovered
    · apply renamed_meaning r η hlen hnp hnq hkinds (by omega) S
      rcases hS with hS | rfl
      · exact .inr (hfresh S hS)
      · exact .inl rfl
  · exact hc.elim

/-- **Quantified signatures, soundly.** A member of a scheme row is a member of
one its quantified signatures cover: at each instance the target admits, the
source admits it too, and there the arrow coverage holds, its premises read
at that instance's assignment. -/
theorem scheme_covers_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} {R known i j}
    (hc : SchemeCoversWith G R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) (n : Nat)
    (hre : ReassignSound G η R n)
    (W : WorldT n) (v : Val)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  unfold SchemeCoversWith at hc
  split at hc
  · rename_i s s' hs hs'
    obtain ⟨hpi, hpj, hbs, hbnd, hord, hcov⟩ := hc
    rw [qDenoteWithArgs_unfold] at hv ⊢
    simp only [qLayerWithArgs, hpi, hpj, hs, hs', Bool.false_eq_true, if_false] at hv ⊢
    refine ⟨sameShape_construct hord ▸ hv.1, fun q hq As hl _hal hb => ?_⟩
    have hall := hv.2 q hq
    have hre : ReassignSound G η R q := fun i s As hs =>
      ⟨fun k hk => (hre i s As hs).1 k (by omega),
       fun k hk => (hre i s As hs).2 k (by omega)⟩
    let W := trunc q hq W
    let n := q
    have hal := (sameShape_allowed G.domain hord As).mpr _hal
    have hb' : Bounded (fun θ S => (mixedParameters G).bound θ
        (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As n := by
      intro b hbm hbin j hj U u hu
      rw [hbs] at hbin hu
      exact hb b (hbnd b hbm) hbin j hj U u hu
    have hi : semWithArgs (excOf G) (mixedValues G (assign η s.binders As)) (mixedArgs G (assign η s.binders As))
        s.body n W v := (instance_body G η s As) ▸ hall As (by rw [hbs]; exact hl) hal hb'
    show instanceTWithArgs _ _ η s' As _ n W v
    rw [instance_body, ← hbs]
    exact covers_body_sound hcov (by
      unfold SchemeRow.body; rw [sameShape_construct hord]
      cases s'.construct <;> simp) n (hre i s As hs).1 (hre i s As hs).2 W v hi
  · exact hc.elim

theorem alpha_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {sub : Option (Renaming G)} {R : List ι → List ι → Prop} {known : Known ι} {i j : ι}
    (hc : SchemeCoversAlpha G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n) (W : WorldT n) (v : Val)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  rcases hc with hc | hc
  · exact scheme_covers_sound hc n hre W v hv
  · exact renames_sound hc n hr hpa hre W v hv

/-- A scheme row is no parameter row. -/
theorem SchemeCoversAlpha.not_param [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop} {i j : ι}
    (h : SchemeCoversAlpha G sub R known arrows i j) : G.params i = false := by
  rcases h with h | h
  · unfold SchemeCoversWith at h
    split at h
    · exact h.1
    · exact h.elim
  · unfold SchemeRenames at h
    split at h
    · exact h.1
    · exact h.elim

/-- **Values of a pair, at a level.** Each split source clause is covered,
its premises read below the level; each opaque row is in the target, below
`top`, a meet row covered through its clauses or below a target row by its
parameters, below a target row by a hypothesis, or a scheme row whose
signatures cover a target scheme's, renaming binders. -/
theorem pair_values_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {R : List ι → List ι → Prop} {hyps : List (ι × ι)} {A B : List ι}
    {η : MixedAssignment ι} {n : Nat} (hc : PairOk G sub known R hyps A B)
    (hknown : ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n) (hhyp : ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] n) :
    FamLeAt G η A B n := by
  intro W v hv
  have hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η A j U v := fun j hj U hU =>
    (setSem_adm (fun i => qDenoteWithArgs_adm G (mixedParameters G) (η, i)) A).transfer
      hv j (Nat.le_of_lt hj) U hU
  -- A meet part below another holds the value: by quantified coverage, or by
  -- a hypothesis, which holds at `n` for values.
  have hpart : ∀ a b, PartCovers G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) hyps a b →
      qDenoteWithArgs G (mixedParameters G) (η, a) n W v →
      qDenoteWithArgs G (mixedParameters G) (η, b) n W v := by
    intro a b h hv
    rcases h with h | h
    · exact alpha_sound h n hr hpa hre W v hv
    · obtain ⟨b', hb', hv'⟩ := hhyp (a, b) h W v ⟨a, List.mem_singleton_self a, hv⟩
      cases List.mem_singleton.mp hb'
      exact hv'
  rcases mixed_cases hv with ⟨c, hcm, hv⟩ | ⟨i, hi, hp, hv⟩
  · obtain ⟨a, ha, hv⟩ := (splitClause_row G _ _ _ c n W v).mpr hv
    exact (hc.2.2 a (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hcm, ha⟩))).sound
      hknown n hr hpa hre W v hself hv
  · rcases (hc.2.1 i hi).resolve_left (by simp [hp]) with
      hB | htop | hmeet | ⟨y, hy, hh⟩ | ⟨j, hj, hsc⟩
    · exact ⟨i, hB, hv⟩
    · rcases htop with htop | ⟨hsource, hparam, hscheme⟩
      · exact mixed_expand_mpr ⟨.top, htop, mixedDenote_value G η i hv,
          builtinInvariant_of_withoutInvariant rfl n W v⟩
      · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hscheme
        rw [qDenoteWithArgs_unfold] at hv
        simp only [qLayerWithArgs, hparam, hs, Bool.false_eq_true, ite_false] at hv
        have hn := hv.1.not_plain
        obtain ⟨fs, code, oid, rfl, hscoped⟩ := hv.1.obj
        exact mixed_expand_mpr ⟨.source, hsource, ⟨rfl, hscoped⟩,
          builtinInvariant_of_not_plain hn⟩
    · rcases hmeet with ⟨hmeet, hsm | hsrc⟩ | ⟨j, hj, hjm, hparts, hcl⟩
      · by_cases hB : i ∈ B
        · exact ⟨i, hB, hv⟩
        · by_cases hbelow : B.any (meetBelow G i · hyps) = true
          · obtain ⟨j, hj, hij⟩ := List.any_eq_true.mp hbelow
            exact ⟨j, hj, meetBelow_sound hmeet hij hhyp hv⟩
          obtain ⟨c, hcm, hv⟩ := meet_clause_of hmeet hv
          obtain ⟨a, ha, hv⟩ := (splitClause_row G _ _ _ c n W v).mpr hv
          have hmem : a ∈ meetSources G A B hyps := List.mem_flatMap.mpr ⟨c,
            List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hmeet, hB, hbelow, hsm]⟩,
              hcm⟩, ha⟩
          exact (hc.2.2 a (List.mem_append_right _ hmem)).sound hknown n hr hpa hre W v hself hv
      · rcases hsrc with hbelow | ⟨q, hq, hqp, j, hj, hsc⟩ | hcov
        · obtain ⟨j, hj, hij⟩ := List.any_eq_true.mp hbelow
          exact ⟨j, hj, meetBelow_sound hmeet hij (by simp) hv⟩
        · exact ⟨j, hj, hpart _ _ hsc (meet_part_value hmeet hq hqp hv)⟩
        · obtain ⟨c, hcm, hv⟩ := meet_clause_of hmeet hv
          obtain ⟨a, ha, hv⟩ := (splitClause_row G _ _ _ c n W v).mpr hv
          obtain ⟨b, hb, hcover⟩ := hcov a (List.mem_flatMap.mpr ⟨c, hcm, ha⟩)
          exact mixed_expand_mpr ⟨b, hb, Covers.sound hcover hknown n hr hpa hre W v hself hv⟩
      · exact ⟨j, hj, meet_target_value hjm hpart hparts hcl hv⟩
    · obtain ⟨y', hy', hv'⟩ := hhyp (i, y) hh W v ⟨i, List.mem_singleton_self i, hv⟩
      cases List.mem_singleton.mp hy'
      exact ⟨y, hy, hv'⟩
    · exact ⟨j, hj, alpha_sound hsc n hr hpa hre W v hv⟩

/-- **Argument lists of a pair, at a level,** from value premises at the same
level. This uses the executable kind condition, so value top cannot discharge
a list edge. A pack parameter of the source is in the target or below a
target row by a hypothesis. -/
theorem pair_arguments_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {R : List ι → List ι → Prop} {hyps : List (ι × ι)} {A B : List ι}
    {η : MixedAssignment ι} {n : Nat} (hc : PairOk G sub known R hyps A B)
    (hv : ∀ S T, R S T → FamLeAt G η S T n)
    (hhyp : ∀ h ∈ hyps, ∀ (W : WorldT n) vs,
      mixedMeaning G η [h.1] n W (.inr vs) → mixedMeaning G η [h.2] n W (.inr vs)) :
    ∀ (W : WorldT n) vs, mixedMeaning G η A n W (.inr vs) → mixedMeaning G η B n W (.inr vs) := by
  intro W vs ha
  have ⟨hsort, hopaque, hcover⟩ := hc
  simp only [SameKind, Bool.or_eq_true, Bool.and_eq_true] at hsort
  rcases hsort with ⟨hav, _⟩ | ⟨haa, hba⟩
  · exact False.elim (mixedMeaning_noArguments G η A hav n W vs ha)
  have noTop : .top ∉ clausesOf G B := by
    intro h
    obtain ⟨a, bs, he⟩ := argument_clause hba h
    cases he
  change graphArguments G η (mixedValues G η) A n W vs at ha
  change graphArguments G η (mixedValues G η) B n W vs
  obtain ⟨i, hi, ha⟩ := ha
  by_cases hp : G.parameterKinds i = some .arguments
  · have hn : G.plain i = false := by simp [NormalGraph.plain, NormalGraph.params, hp]
    rcases hopaque i hi with h | h | h | h | ⟨y, hy, hh⟩ | ⟨j, -, h⟩
    · simp [hn] at h
    · exact ⟨i, h, by simpa [hp, NormalGraph.listParam] using ha⟩
    · rcases h with h | ⟨_, hparam, _⟩
      · exact False.elim (noTop h)
      · simp [NormalGraph.params, hp] at hparam
    · rcases h with ⟨h, -⟩ | ⟨j, hj, hjm, -, -⟩
      · simp [NormalGraph.meetRow, NormalGraph.params, hp] at h
      · -- A meet row is a value row, which a list-sorted target has none of.
        have hk := List.all_eq_true.mp hba j hj
        simp only [NormalGraph.meetRow, NormalGraph.params, Bool.and_eq_true, Bool.not_eq_true',
          Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hjm
        obtain ⟨⟨hjp, _⟩, hjs⟩ := hjm
        cases hq : G.parameterKinds j <;> simp_all
    · obtain ⟨y', hy', h2⟩ := hhyp (i, y) hh W vs ⟨i, List.mem_singleton_self i, ha⟩
      cases List.mem_singleton.mp hy'
      exact ⟨y, hy, h2⟩
    · have := h.not_param
      simp [NormalGraph.params, hp] at this
  · have hlp : G.listParam i = false := by
      have hk := List.all_eq_true.mp haa i hi
      cases hq : G.parameterKinds i with
      | none => simp [NormalGraph.listParam, hq]
      | some k => cases k <;> simp_all [NormalGraph.listParam]
    simp only [hlp, Bool.false_eq_true, ite_false] at ha
    obtain ⟨c, hci, hca⟩ := ha
    cases c <;> try contradiction
    case pack a bs =>
      have hsrc : .pack a bs ∈ sourceClauses G A :=
        List.mem_flatMap.mpr ⟨.pack a bs, List.mem_flatMap.mpr ⟨i, hi, hci⟩, by simp [splitClause]⟩
      obtain ⟨b, hb, hcov⟩ := (hcover _ (List.mem_append_left _ hsrc)).single rfl
      obtain ⟨d, ds, rfl⟩ := argument_clause hba hb
      obtain ⟨j, hj, hbj⟩ := List.mem_flatMap.mp hb
      have hjplain := NormalGraph.plain_of_clauses hbj
      have hjkind : G.parameterKinds j ≠ some .arguments := by
        intro h
        simp [NormalGraph.plain, NormalGraph.params, h] at hjplain
      refine ⟨j, hj, ?_⟩
      simp only [NormalGraph.listParam_of_plain hjplain, Bool.false_eq_true, ite_false]
      refine ⟨.pack d ds, hbj, ?_⟩
      change ∀ q ∈ d :: ds, ArgumentContracts.Fits (tupleFams (mixedValues G η) q) n W vs
      intro q hq
      obtain ⟨p, hp, hpq⟩ := hcov q hq
      exact covers_arguments hpq (mixedValues G η) (fun A v => A n W v)
        (fun S T h v hv' => hv S T h W v hv') vs (hca p hp)

/-- **Pairs by level induction.** Families of pairs indexed by `E`, each with
the relation its premises are read through and its hypotheses, whose pairs
all meet the core conditions, hold at every level where their hypotheses
do, provided premises are sound given the pairs below the level
(`below`), and, for the values an argument list's contracts read, at the
level once all values there are (`same`). Entering a scheme must keep the
hypotheses (`fixed`). Values at a level come first, from premises below it;
argument lists at the level then from values at it. -/
theorem pairs_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {E : Type} (R : E → List ι → List ι → Prop) (hyps : E → List (ι × ι))
    (pairs : E → List (List ι × List ι))
    (hvalid : ∀ e, ∀ p ∈ pairs e, PairOk G sub known (R e) (hyps e) p.1 p.2)
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (fixed : ∀ e (η : MixedAssignment ι) n i s As, G.schemes i = some s →
      HypsHoldValues G η (hyps e) n → HypsHoldValues G (assign η s.binders As) (hyps e) n)
    (below : ∀ n, (∀ j, j < n → ∀ e η, HypsHold G η (hyps e) j → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 j) →
      ∀ e η, HypsHoldValues G η (hyps e) n → ∀ S T, R e S T → ∀ j, j < n → MixedLe G η S T j)
    (same : ∀ n, (∀ j, j < n → ∀ e η, HypsHold G η (hyps e) j → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 j) →
      (∀ e η, HypsHoldValues G η (hyps e) n → ∀ p ∈ pairs e, FamLeAt G η p.1 p.2 n) →
      ∀ e η, HypsHold G η (hyps e) n → ∀ S T, R e S T → FamLeAt G η S T n) :
    ∀ n, (∀ e η, HypsHoldValues G η (hyps e) n → ∀ p ∈ pairs e, FamLeAt G η p.1 p.2 n) ∧
      ∀ e η, HypsHold G η (hyps e) n → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have lower : ∀ j, j < n → ∀ e η, HypsHold G η (hyps e) j → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 j :=
      fun j hj => (ih j hj).2
    have prem := below n lower
    have values : ∀ e η, HypsHoldValues G η (hyps e) n → ∀ p ∈ pairs e, FamLeAt G η p.1 p.2 n := by
      intro e η hη p hp
      exact pair_values_sound (hvalid e p hp) (hk η)
        (fun j hj S T h => (prem e η hη S T h j hj).values)
        (fun j hj S T h W vs hvs => prem e η hη S T h j hj W (.inr vs) hvs)
        (fun i s As hs => ⟨fun j hj S T h => (prem e _ (fixed e η n i s As hs hη) S T h j hj).values,
          fun j hj S T h W vs hvs => prem e _ (fixed e η n i s As hs hη) S T h j hj W (.inr vs) hvs⟩)
        hη.2
    refine ⟨values, fun e η hη p hp W x hx => ?_⟩
    cases x with
    | inl v => exact values e η hη.values p hp W v hx
    | inr vs =>
      exact pair_arguments_sound (hvalid e p hp) (same n lower values e η hη)
        (fun h hh W vs hvs => hη h hh n (Nat.le_refl n) W (.inr vs) hvs) W vs hx

/-! ### Family entries

An entry is an assumption of RECURSIVE-EQUATIONS §4.2: a goal pair with
variables, hypotheses between them and a table. Its premises are the rules
`Tab`, `TabRen` and `Union` (`Prem`) and `Mem`, `Hyp`, `MeetHyp` and `Inst`
(`PremLabel`); `Inst` discharges an instance's hypotheses by further
premises, on strictly smaller types. `family_sound` is Theorem 1. -/

theorem MixedLe.of_labels {G : NormalGraph ι} {η : MixedAssignment ι} {A B : List ι} {m : Nat}
    (h : ∀ l ∈ A, MixedLe G η [l] B m) : MixedLe G η A B m := by
  intro W x hx
  obtain ⟨l, hl, hx⟩ := (mixedMeaning_union G η A m W x).mp hx
  exact h l hl W x hx

theorem FamLeAt.of_labels {G : NormalGraph ι} {η : MixedAssignment ι} {A B : List ι} {m : Nat}
    (h : ∀ l ∈ A, FamLeAt G η [l] B m) : FamLeAt G η A B m := by
  intro W v hv
  obtain ⟨l, hl, hx⟩ := (mixedMeaning_union G η A m W (.inl v)).mp hv
  exact h l hl W v hx

theorem MixedLe.of_mem {G : NormalGraph ι} {η : MixedAssignment ι} {l : ι} {B : List ι} {m : Nat}
    (h : l ∈ B) : MixedLe G η [l] B m :=
  fun W x hx => mixed_subset (fun i hi => by rw [List.mem_singleton.mp hi]; exact h) m W x hx

theorem MixedLe.congr {G : NormalGraph ι} {η θ : MixedAssignment ι} {A A' B B' : List ι} {m : Nat}
    (ha : mixedMeaning G η A = mixedMeaning G θ A') (hb : mixedMeaning G η B = mixedMeaning G θ B')
    (h : MixedLe G θ A' B' m) : MixedLe G η A B m := by
  intro W x hx
  rw [ha] at hx
  rw [hb]
  exact h W x hx

theorem FamLeAt.congr {G : NormalGraph ι} {η θ : MixedAssignment ι} {A A' B B' : List ι} {m : Nat}
    (ha : mixedMeaning G η A = mixedMeaning G θ A') (hb : mixedMeaning G η B = mixedMeaning G θ B')
    (h : FamLeAt G θ A' B' m) : FamLeAt G η A B m := by
  intro W v hv
  have hv' : mixedMeaning G η A m W (.inl v) := hv
  rw [ha] at hv'
  show mixedMeaning G η B m W (.inl v)
  rw [hb]
  exact h W v hv'

/-- Instantiating parameters at types of their kinds: each parameter row
means its replacement. -/
theorem assignment_images [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (bs : List ι) (θs : List (List ι)) (hlen : θs.length = bs.length)
    (kinds : instKinds G bs θs = true) (p : ι) (hp : G.params p = true) :
    mixedMeaning G (assign η bs (θs.map fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) [p] =
      mixedMeaning G η (replace (bs.zip θs) p) := by
  obtain ⟨kind, hk⟩ : ∃ kind, G.parameterKinds p = some kind := by
    simpa [NormalGraph.params, Option.isSome_iff_exists] using hp
  have hr := mixed_assignment_substitution G η bs θs hlen kinds [p]
  cases lookup : (bs.zip θs).lookup p with
  | some U =>
    simpa only [replace, lookup, Option.getD_some] using
      mixed_parameter_image G (bs.zip θs) _ η p kind U hk lookup hr
  | none =>
    rw [mixedMeaning_parameter _ _ _ _ hk]
    simp only [replace, lookup, Option.getD_none]
    rw [mixedMeaning_parameter _ _ _ _ hk]
    have he := hr p (by simp)
    rw [lookup] at he
    change selectParameter (G.parameterKinds p) _ =
      selectParameter (G.parameterKinds p) _ at he
    simpa only [hk] using he

/-- A family entry, an assumption (RECURSIVE-EQUATIONS §4.2): its goal
`source ≤ target`, its variables, hypotheses between them, its table
`T_a`, and the instances its premises use, each an entry's index and the
types its variables are instantiated at, in order. -/
structure Entry (ι : Type) where
  source : List ι
  target : List ι
  variables : List ι := []
  hypotheses : List (ι × ι) := []
  table : Table ι := []
  instances : List (Nat × List (List ι)) := []
  deriving DecidableEq, Repr

/-- The goal, then the table. -/
@[nospecialize] def Entry.pairs (e : Entry ι) : List (List ι × List ι) := (e.source, e.target) :: e.table

/-- A type at an instance: its variables replaced, when a renaming exists. -/
@[nospecialize] def image [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (σ : List (ι × List ι)) (A : List ι) : List ι :=
  match sub with
  | some r => r.substitute σ A
  | none => A

/-- The entries an instance may cite, by index (the set `𝒜` of §4.2). -/
abbrev Lookup (ι : Type) := Nat → Option (Entry ι)

/-- An entry's hypotheses relate parameter rows. -/
@[nospecialize] def HypParams (G : NormalGraph ι) (e : Entry ι) : Prop :=
  ∀ h ∈ e.hypotheses, G.params h.1 = true ∧ G.params h.2 = true

/-- The instance of entry `e` at the types `xs` relates the label `l` to
`B`: `xs` of `e`'s variables' kinds, `e`'s substituted source holding `l`,
its substituted target within `B`. -/
@[nospecialize] def InstanceAt [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (e : Entry ι)
    (l : ι) (B : List ι) (xs : List (List ι)) : Prop :=
  xs.length = e.variables.length ∧ instKinds G e.variables xs = true ∧
    (sub.isNone = true → e.variables = []) ∧
    l ∈ image sub (e.variables.zip xs) e.source ∧
    ∀ b ∈ image sub (e.variables.zip xs) e.target, b ∈ B

/-- A label's size, by which `Inst`'s premises decrease: the renaming's, and
nothing without one (no instance then has a hypothesis). -/
@[nospecialize] def labelSize [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G)) (l : ι) : Nat :=
  match sub with
  | some r => r.size l
  | none => 0

/-- A union's size: its labels'. -/
@[nospecialize] def typeSize [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G)) (A : List ι) : Nat :=
  (A.map (labelSize sub)).sum

/-- A renaming of bound rows (`TabRen`): each renamed row a parameter row
and no family variable, given one such row of its kind. Hypotheses relate
family variables only, so a renaming leaves them in place. -/
@[nospecialize] def boundRow [DecidableEq ι] {G : NormalGraph ι} (r : Renaming G) (x : ι) : Bool :=
  G.params x && !r.familyVar x

@[nospecialize] def RenamesBound [DecidableEq ι] (G : NormalGraph ι) (r : Renaming G) (σ : List (ι × List ι)) : Prop :=
  instKinds G σ.unzip.1 σ.unzip.2 = true ∧
    ∀ q ∈ σ, boundRow r q.1 = true ∧ q.2.length = 1 ∧ ∀ y ∈ q.2, boundRow r y = true

instance [DecidableEq ι] (G : NormalGraph ι) (r : Renaming G) (σ : List (ι × List ι)) :
    Decidable (RenamesBound G r σ) := by
  unfold RenamesBound; infer_instance

mutual
/-- **Premises** (RECURSIVE-EQUATIONS §4.2), `Π;T ⊢ A ⊑ B` in the entry
`f`, whose hypotheses are `Π` and table `T`: a table pair (`tab`), a table
pair at renamed bound rows (`tabRen`, the renaming the representation's own
matcher proposes), or each label of `A` below `B` (`union`). -/
inductive Prem [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) : List ι → List ι → Prop where
  | tab {A B : List ι} : (A, B) ∈ f.table → Prem G sub look gen f A B
  | tabRen {A B : List ι} (r : Renaming G) (p : List ι × List ι) : sub = some r → p ∈ f.table →
      RenamesBound G r (r.rename p A B) →
      (∀ l ∈ A, l ∈ r.substitute (r.rename p A B) p.1) →
      (∀ b ∈ r.substitute (r.rename p A B) p.2, b ∈ B) → Prem G sub look gen f A B
  | union {A B : List ι} : (∀ l ∈ A, PremLabel G sub look gen f l B) → Prem G sub look gen f A B
/-- A label below a union: a member (`mem`), below a member by a hypothesis
(`hyp`), a meet below a member by its parts and the hypotheses (`meetHyp`),
or by an instance of a cited entry (`inst`), its hypotheses discharged by
premises on strictly smaller types. The instances are the entry's own
(`f.instances`) and those `gen` proposes, verified code (`Var` proposes
same-head instances); what it proposes is checked like any other. -/
inductive PremLabel [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) : ι → List ι → Prop where
  | mem {l : ι} {B : List ι} : l ∈ B → PremLabel G sub look gen f l B
  | hyp {l y : ι} {B : List ι} : (l, y) ∈ f.hypotheses → y ∈ B → PremLabel G sub look gen f l B
  | meetHyp {l y : ι} {B : List ι} : G.meetRow l = true → y ∈ B → meetBelow G l y f.hypotheses = true →
      PremLabel G sub look gen f l B
  | inst {l : ι} {B : List ι} (w : Nat × List (List ι)) (e : Entry ι) :
      w ∈ f.instances ++ gen l B → look w.1 = some e → InstanceAt G sub e l B w.2 →
      (∀ h ∈ e.hypotheses, typeSize sub (replace (e.variables.zip w.2) h.1) +
        typeSize sub (replace (e.variables.zip w.2) h.2) < labelSize sub l + typeSize sub B) →
      (∀ h ∈ e.hypotheses,
        Prem G sub look gen f (replace (e.variables.zip w.2) h.1) (replace (e.variables.zip w.2) h.2)) →
      PremLabel G sub look gen f l B
end

/-- A meet label below a target label by its parts holds where the
hypotheses do, for values; it admits no argument list. -/
theorem meetBelow_mixed [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} {l : ι}
    {B : List ι} {hyps : List (ι × ι)} {m : Nat} (hl : G.meetRow l = true)
    (hb : ∃ y ∈ B, meetBelow G l y hyps = true) (hh : ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] m) :
    MixedLe G η [l] B m := by
  obtain ⟨y, hy, hly⟩ := hb
  intro W x hx
  cases x with
  | inl v =>
    obtain ⟨i, hi, hv⟩ := hx
    cases List.mem_singleton.mp hi
    exact ⟨y, hy, meetBelow_sound hl hly hh hv⟩
  | inr vs =>
    refine (mixedMeaning_noArguments G η [l] ?_ m W vs hx).elim
    simp only [NormalGraph.meetRow, Bool.and_eq_true, Bool.not_eq_true'] at hl
    simp [NormalGraph.hasKind, NormalGraph.params, Option.isNone_iff_eq_none] at hl ⊢
    obtain ⟨⟨hp, _⟩, hm⟩ := hl
    simp [hp, hm]

/-- **Valid entries** (`Valid`, §4.2): every pair of every entry of `F`
meets the core conditions, its premises read in its entry, instances citing
the entries `look` names. -/
@[nospecialize] def FamilyValid [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (known : Known ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (look : Lookup ι) (F : List (Entry ι)) : Prop :=
  ∀ f ∈ F, ∀ p ∈ f.pairs, PairOk G sub known (Prem G sub look gen f) f.hypotheses p.1 p.2

/-- The variable discipline: hypotheses relate an entry's own variables, and
variables are rows the representation reserves for them, parameter rows no
scheme binds (none without a renaming). -/
@[nospecialize] def VariablesOk [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (F : List (Entry ι)) : Prop :=
  (∀ f ∈ F, ∀ h ∈ f.hypotheses, h.1 ∈ f.variables ∧ h.2 ∈ f.variables) ∧
    ∀ f ∈ F, ∀ x ∈ f.variables, match sub with
      | some r => r.familyVar x = true
      | none => False

/-- An entry's goal holds wherever its hypotheses do. -/
@[nospecialize] def EntrySound (G : NormalGraph ι) (e : Entry ι) : Prop :=
  (∀ n η, HypsHold G η e.hypotheses n → MixedLe G η e.source e.target n) ∧
    ∀ n η, HypsHoldValues G η e.hypotheses n → FamLeAt G η e.source e.target n

/-- A hypothesis names a family variable: a parameter row no scheme binds. -/
theorem VariablesOk.hyp [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {F : List (Entry ι)} (hv : VariablesOk sub F) {f : Entry ι} (hf : f ∈ F) {h : ι × ι}
    (hh : h ∈ f.hypotheses) :
    ∀ x, x = h.1 ∨ x = h.2 → G.params x = true ∧ (∀ i s, G.schemes i = some s → x ∉ s.binders) ∧
      ∀ r, sub = some r → r.familyVar x = true := by
  intro x hx
  have hmem : x ∈ f.variables := by
    rcases hx with rfl | rfl
    · exact (hv.1 f hf h hh).1
    · exact (hv.1 f hf h hh).2
  have hvar := hv.2 f hf x hmem
  cases sub with
  | none => exact hvar.elim
  | some r =>
    exact ⟨r.familyVar_param x hvar, fun i s hs => r.familyVar_unbound i s x hs hvar,
      fun r' hr => by cases hr; exact hvar⟩

theorem VariablesOk.params [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {F : List (Entry ι)} (hv : VariablesOk sub F) {f : Entry ι} (hf : f ∈ F) : HypParams G f :=
  fun h hh => ⟨(hv.hyp hf hh h.1 (.inl rfl)).1, (hv.hyp hf hh h.2 (.inr rfl)).1⟩

theorem zip_unzip_eq (σ : List (α × β)) : σ.unzip.1.zip σ.unzip.2 = σ := List.zip_unzip σ

/-- An instance moves the entry's goal to the use: at the assignment giving
its variables their types' meanings, each hypothesis means its instance, the
source holds the label and the target is within `B`. -/
theorem InstanceAt.transport [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {e : Entry ι} {l : ι} {B : List ι} {xs : List (List ι)}
    (hi : InstanceAt G sub e l B xs) (hpar : sub.isSome = true → HypParams G e)
    (η : MixedAssignment ι) :
    ∃ η' : MixedAssignment ι,
      (∀ h ∈ e.hypotheses,
        mixedMeaning G η' [h.1] = mixedMeaning G η (replace (e.variables.zip xs) h.1) ∧
        mixedMeaning G η' [h.2] = mixedMeaning G η (replace (e.variables.zip xs) h.2)) ∧
      FamLe (mixedMeaning G η [l]) (mixedMeaning G η' e.source) ∧
      FamLe (mixedMeaning G η' e.target) (mixedMeaning G η B) := by
  obtain ⟨hlen, hkinds, hnone, hl, hB⟩ := hi
  cases sub with
  | none =>
    have hv : e.variables = [] := hnone rfl
    refine ⟨η, fun h _ => ?_, ?_, ?_⟩
    · simp [hv, replace]
    · exact mixed_subset fun i hi => by
        rw [List.mem_singleton.mp hi]; simpa [image] using hl
    · exact mixed_subset fun b hb => hB b (by simpa [image] using hb)
  | some r =>
    have images := assignment_images G η e.variables xs hlen hkinds
    have hp := hpar rfl
    refine ⟨_, fun h hh => ⟨images _ (hp h hh).1, images _ (hp h hh).2⟩, ?_, ?_⟩
    · rw [r.substitute_meaning _ η _ images e.source]
      exact mixed_subset fun i hi => by
        rw [List.mem_singleton.mp hi]; simpa [image] using hl
    · rw [r.substitute_meaning _ η _ images e.target]
      exact mixed_subset fun b hb => hB b (by simpa [image] using hb)

/-- `TabRen` moves a table pair to its renaming: at the assignment giving the
renamed rows their images' meanings, the hypotheses keep theirs, and the
renamed pair means the pair there. -/
theorem RenamesBound.transport [DecidableEq ι] {G : NormalGraph ι} {r : Renaming G}
    {σ : List (ι × List ι)} (hren : RenamesBound G r σ) {hyps : List (ι × ι)}
    (hfv : ∀ h ∈ hyps, r.familyVar h.1 = true ∧ r.familyVar h.2 = true)
    (hfp : ∀ h ∈ hyps, G.params h.1 = true ∧ G.params h.2 = true) (η : MixedAssignment ι) :
    ∃ η' : MixedAssignment ι,
      (∀ h ∈ hyps, mixedMeaning G η' [h.1] = mixedMeaning G η [h.1] ∧
        mixedMeaning G η' [h.2] = mixedMeaning G η [h.2]) ∧
      ∀ A, mixedMeaning G η' A = mixedMeaning G η (r.substitute σ A) := by
  have hlen : σ.unzip.2.length = σ.unzip.1.length := by simp
  have images := assignment_images G η σ.unzip.1 σ.unzip.2 hlen hren.1
  rw [zip_unzip_eq] at images
  refine ⟨_, fun h hh => ?_, r.substitute_meaning _ η σ images⟩
  have keep : ∀ x, G.params x = true → r.familyVar x = true →
      mixedMeaning G (assign η σ.unzip.1 (σ.unzip.2.map fun U =>
        ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) [x] = mixedMeaning G η [x] := by
    intro x hx hvar
    apply mixedMeaning_param_eq rfl hx
    apply assign_nmem
    intro hmem
    obtain ⟨q, hq, rfl⟩ : ∃ q ∈ σ, q.1 = x := by
      simp only [List.unzip_fst, List.mem_map] at hmem
      exact hmem
    have := (hren.2 q hq).1
    simp [boundRow, hvar] at this
  exact ⟨keep _ (hfp h hh).1 (hfv h hh).1, keep _ (hfp h hh).2 (hfv h hh).2⟩

/-- **Premises below the level** (the inner induction of Theorem 1, §4.2).
Read at `η` below `n`, a premise holds where the entry's table pairs hold at
every assignment meeting its hypotheses, its hypotheses hold at `η`, and every
cited entry's goal holds where its hypotheses do. -/
theorem prem_mixed [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {look : Lookup ι}
    {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} {η : MixedAssignment ι} {n : Nat}
    (hfv : ∀ r, sub = some r → ∀ h ∈ f.hypotheses, r.familyVar h.1 = true ∧ r.familyVar h.2 = true)
    (hfp : HypParams G f)
    (hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e)
    (htab : ∀ j, j < n → ∀ η', HypsHold G η' f.hypotheses j → ∀ p ∈ f.table, MixedLe G η' p.1 p.2 j)
    (hhyp : ∀ h ∈ f.hypotheses, ∀ j, j < n → MixedLe G η [h.1] [h.2] j)
    (hent : ∀ j, j < n → ∀ k e η', look k = some e → HypsHold G η' e.hypotheses j →
      MixedLe G η' e.source e.target j) :
    (∀ {A B}, Prem G sub look gen f A B → ∀ j, j < n → MixedLe G η A B j) ∧
      ∀ {l B}, PremLabel G sub look gen f l B → ∀ j, j < n → MixedLe G η [l] B j := by
  have tabRen : ∀ (r : Renaming G) (p : List ι × List ι) (A B : List ι), sub = some r →
      p ∈ f.table → RenamesBound G r (r.rename p A B) →
      (∀ l ∈ A, l ∈ r.substitute (r.rename p A B) p.1) →
      (∀ b ∈ r.substitute (r.rename p A B) p.2, b ∈ B) → ∀ j, j < n → MixedLe G η A B j := by
    intro r p A B hs hp hren hA hB j hj
    obtain ⟨η', hkeep, hsub⟩ := hren.transport (hfv r hs) hfp η
    have hyps' : HypsHold G η' f.hypotheses j := fun h hh k hk =>
      MixedLe.congr (hkeep h hh).1 (hkeep h hh).2 (hhyp h hh k (by omega))
    have hpair := MixedLe.congr (hsub _).symm (hsub _).symm (htab j hj η' hyps' p hp)
    intro W x hx
    exact mixed_subset hB j W x (hpair W x (mixed_subset hA j W x hx))
  let motive_1 := fun (A B : List ι) (_ : Prem G sub look gen f A B) =>
    ∀ j, j < n → MixedLe G η A B j
  let motive_2 := fun (l : ι) (B : List ι) (_ : PremLabel G sub look gen f l B) =>
    ∀ j, j < n → MixedLe G η [l] B j
  have tab : ∀ {A B} (h : (A, B) ∈ f.table), motive_1 A B (.tab h) := fun h j hj =>
    htab j hj η (fun h' hh k hk => hhyp h' hh k (by omega)) _ h
  have ren : ∀ {A B} r p hs hp hren hA hB, motive_1 A B (.tabRen r p hs hp hren hA hB) :=
    fun r p hs hp hren hA hB => tabRen r p _ _ hs hp hren hA hB
  have union : ∀ {A B} (h : ∀ l ∈ A, PremLabel G sub look gen f l B),
      (∀ l hl, motive_2 l B (h l hl)) → motive_1 A B (.union h) :=
    fun _ ih j hj => MixedLe.of_labels fun l hl => ih l hl j hj
  have mem : ∀ {l B} (h : l ∈ B), motive_2 l B (.mem h) := fun h _ _ => MixedLe.of_mem h
  have hyp : ∀ {l y B} (hh : (l, y) ∈ f.hypotheses) (hy : y ∈ B), motive_2 l B (.hyp hh hy) :=
    fun hh hy j hj W x hx => MixedLe.of_mem hy W x (hhyp _ hh j hj W x hx)
  have meetHyp : ∀ {l y B} (hm : G.meetRow l = true) (hy : y ∈ B) (hb : meetBelow G l y f.hypotheses = true),
      motive_2 l B (.meetHyp hm hy hb) :=
    fun hm hy hb j hj => meetBelow_mixed hm ⟨_, hy, hb⟩ fun h hh => (hhyp h hh j hj).values
  have inst : ∀ {l B} (w : Nat × List (List ι)) (e : Entry ι) hw hl hi hdec
      (hps : ∀ h ∈ e.hypotheses, Prem G sub look gen f (replace (e.variables.zip w.2) h.1)
        (replace (e.variables.zip w.2) h.2)),
      (∀ h hh, motive_1 _ _ (hps h hh)) → motive_2 l B (.inst w e hw hl hi hdec hps) := by
    intro l B w e _ hl hi _ _ ih j hj
    obtain ⟨η', himg, hsrc, htgt⟩ := hi.transport (hpar w.1 e hl) η
    have hyps' : HypsHold G η' e.hypotheses j := fun h hh k hk =>
      MixedLe.congr (himg h hh).1 (himg h hh).2 (ih h hh k (by omega))
    have goal := hent j hj w.1 e η' hl hyps'
    exact fun W x hx => htgt j W x (goal W x (hsrc j W x hx))
  exact ⟨fun h => Prem.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h,
    fun h => PremLabel.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h⟩

/-- **Premises for values at the level.** As `prem_mixed`, at `n` itself
for values: table pairs, hypotheses and cited goals for values at `n`, and
everything below `n`. -/
theorem prem_values [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {look : Lookup ι}
    {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} {η : MixedAssignment ι} {n : Nat}
    (hfv : ∀ r, sub = some r → ∀ h ∈ f.hypotheses, r.familyVar h.1 = true ∧ r.familyVar h.2 = true)
    (hfp : HypParams G f)
    (hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e)
    (htab : ∀ j, j < n → ∀ η', HypsHold G η' f.hypotheses j → ∀ p ∈ f.table, MixedLe G η' p.1 p.2 j)
    (htabv : ∀ η', HypsHoldValues G η' f.hypotheses n → ∀ p ∈ f.table, FamLeAt G η' p.1 p.2 n)
    (hη : HypsHoldValues G η f.hypotheses n)
    (hent : ∀ j, j < n → ∀ k e η', look k = some e → HypsHold G η' e.hypotheses j →
      MixedLe G η' e.source e.target j)
    (hentv : ∀ k e η', look k = some e → HypsHoldValues G η' e.hypotheses n →
      FamLeAt G η' e.source e.target n) :
    (∀ {A B}, Prem G sub look gen f A B → FamLeAt G η A B n) ∧
      ∀ {l B}, PremLabel G sub look gen f l B → FamLeAt G η [l] B n := by
  have below := prem_mixed (look := look) (gen := gen) hfv hfp hpar htab hη.1 hent
  let motive_1 := fun (A B : List ι) (_ : Prem G sub look gen f A B) => FamLeAt G η A B n
  let motive_2 := fun (l : ι) (B : List ι) (_ : PremLabel G sub look gen f l B) =>
    FamLeAt G η [l] B n
  have tab : ∀ {A B} (h : (A, B) ∈ f.table), motive_1 A B (.tab h) := fun h => htabv η hη _ h
  have ren : ∀ {A B} r p hs hp hren hA hB, motive_1 A B (.tabRen r p hs hp hren hA hB) := by
    intro A B r p hs hp hren hA hB
    obtain ⟨η', hkeep, hsub⟩ := hren.transport (hfv r hs) hfp η
    have hyps' : HypsHoldValues G η' f.hypotheses n :=
      ⟨fun h hh k hk => MixedLe.congr (hkeep h hh).1 (hkeep h hh).2 (hη.1 h hh k hk),
        fun h hh => FamLeAt.congr (hkeep h hh).1 (hkeep h hh).2 (hη.2 h hh)⟩
    have hpair := htabv η' hyps' p hp
    have hpair' : FamLeAt G η (r.substitute (r.rename p A B) p.1)
        (r.substitute (r.rename p A B) p.2) n :=
      FamLeAt.congr (hsub _).symm (hsub _).symm hpair
    intro W v hv
    exact (mixed_subset hB n W (.inl v) (hpair' W v (mixed_subset hA n W (.inl v) hv)))
  have union : ∀ {A B} (h : ∀ l ∈ A, PremLabel G sub look gen f l B),
      (∀ l hl, motive_2 l B (h l hl)) → motive_1 A B (.union h) :=
    fun _ ih => FamLeAt.of_labels fun l hl => ih l hl
  have mem : ∀ {l B} (h : l ∈ B), motive_2 l B (.mem h) := fun h => (MixedLe.of_mem h).values
  have hyp : ∀ {l y B} (hh : (l, y) ∈ f.hypotheses) (hy : y ∈ B), motive_2 l B (.hyp hh hy) :=
    fun hh hy W v hv => (MixedLe.of_mem hy).values W v (hη.2 _ hh W v hv)
  have meetHyp : ∀ {l y B} (hm : G.meetRow l = true) (hy : y ∈ B) (hb : meetBelow G l y f.hypotheses = true),
      motive_2 l B (.meetHyp hm hy hb) :=
    fun hm hy hb => (meetBelow_mixed hm ⟨_, hy, hb⟩ hη.2).values
  have inst : ∀ {l B} (w : Nat × List (List ι)) (e : Entry ι) hw hl hi hdec
      (hps : ∀ h ∈ e.hypotheses, Prem G sub look gen f (replace (e.variables.zip w.2) h.1)
        (replace (e.variables.zip w.2) h.2)),
      (∀ h hh, motive_1 _ _ (hps h hh)) → motive_2 l B (.inst w e hw hl hi hdec hps) := by
    intro l B w e _ hl hi _ hps ih
    obtain ⟨η', himg, hsrc, htgt⟩ := hi.transport (hpar w.1 e hl) η
    have hyps' : HypsHoldValues G η' e.hypotheses n :=
      ⟨fun h hh k hk => MixedLe.congr (himg h hh).1 (himg h hh).2 (below.1 (hps h hh) k hk),
        fun h hh => FamLeAt.congr (himg h hh).1 (himg h hh).2 (ih h hh)⟩
    have goal := hentv w.1 e η' hl hyps'
    exact fun W v hv => htgt n W (.inl v) (goal W v (hsrc n W (.inl v) hv))
  exact ⟨fun h => Prem.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h,
    fun h => PremLabel.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h⟩

/-- **Theorem 1** (RECURSIVE-EQUATIONS §4.2). Valid entries, whose instances
cite entries of `F` or entries already sound (`look`), hold at every
assignment meeting their hypotheses, at every level, in both components:
by level induction (`pairs_sound`), each premise by the inner induction
on its derivation (`prem_mixed`, `prem_values`). -/
theorem family_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ f ∈ F, (∀ n η, HypsHold G η f.hypotheses n → ∀ p ∈ f.pairs, MixedLe G η p.1 p.2 n) ∧
      ∀ n η, HypsHoldValues G η f.hypotheses n → ∀ p ∈ f.pairs, FamLeAt G η p.1 p.2 n := by
  let E := {f : Entry ι // f ∈ F}
  have hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e := by
    intro k e hl _
    rcases hlook k e hl with he | he
    · exact hvars.params he
    · exact he.2
  have hfv : ∀ e : E, ∀ r, sub = some r → ∀ h ∈ e.1.hypotheses,
      r.familyVar h.1 = true ∧ r.familyVar h.2 = true := fun e r hr h hh =>
    ⟨(hvars.hyp e.2 hh h.1 (.inl rfl)).2.2 r hr, (hvars.hyp e.2 hh h.2 (.inr rfl)).2.2 r hr⟩
  have hs := pairs_sound (G := G) (sub := sub) (known := known) (E := E)
    (fun e => Prem G sub look gen e.1) (fun e => e.1.hypotheses) (fun e => e.1.pairs)
    (fun e p hp => hvalid e.1 e.2 p hp) hk
    (by
      intro e η n i s As hs hη
      have heq : ∀ h ∈ e.1.hypotheses, ∀ x, x = h.1 ∨ x = h.2 →
          mixedMeaning G (assign η s.binders As) [x] = mixedMeaning G η [x] := by
        intro h hh x hx
        have hvx := hvars.hyp e.2 hh x hx
        exact mixedMeaning_param_eq rfl hvx.1 (assign_nmem η s.binders As (hvx.2.1 i s hs))
      exact ⟨fun h hh j hj => MixedLe.congr (heq h hh _ (.inl rfl)) (heq h hh _ (.inr rfl))
          (hη.1 h hh j hj),
        fun h hh => FamLeAt.congr (heq h hh _ (.inl rfl)) (heq h hh _ (.inr rfl)) (hη.2 h hh)⟩)
    (by
      intro n lower e η hη S T h j hj
      refine (prem_mixed (hfv e) (hvars.params e.2) hpar
        (fun j hj η' hh p hp => lower j hj e η' hh p (List.mem_cons_of_mem _ hp)) hη.1
        (fun j hj k e' η' hl hh => ?_)).1 h j hj
      rcases hlook k e' hl with he | he
      · exact lower j hj ⟨e', he⟩ η' hh _ List.mem_cons_self
      · exact he.1.1 j η' hh)
    (by
      intro n lower values e η hη S T h
      refine (prem_values (hfv e) (hvars.params e.2) hpar
        (fun j hj η' hh p hp => lower j hj e η' hh p (List.mem_cons_of_mem _ hp))
        (fun η' hh p hp => values e η' hh p (List.mem_cons_of_mem _ hp)) hη.values
        (fun j hj k e' η' hl hh => ?_) (fun k e' η' hl hh => ?_)).1 h
      · rcases hlook k e' hl with he | he
        · exact lower j hj ⟨e', he⟩ η' hh _ List.mem_cons_self
        · exact he.1.1 j η' hh
      · rcases hlook k e' hl with he | he
        · exact values ⟨e', he⟩ η' hh _ List.mem_cons_self
        · exact he.1.2 n η' hh)
  intro f hf
  exact ⟨fun n η hη => (hs n).2 ⟨f, hf⟩ η hη, fun n η hη => (hs n).1 ⟨f, hf⟩ η hη⟩

/-- Every entry of a valid family is sound. -/
theorem family_entries_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ e ∈ F, EntrySound G e := by
  intro e he
  have h := family_sound hvalid hvars hlook hk e he
  exact ⟨fun n η hη => h.1 n η hη _ List.mem_cons_self,
    fun n η hη => h.2 n η hη _ List.mem_cons_self⟩

/-- A pair of a variable-free entry holds at every assignment: the claims a
family certificate proves. -/
theorem family_closed_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    {f : Entry ι} (hf : f ∈ F) (hclosed : f.hypotheses = []) {S T : List ι} (hp : (S, T) ∈ f.pairs) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  intro η n W x hx
  refine (family_sound hvalid hvars hlook hk f hf).1 n η ?_ (S, T) hp W x hx
  intro h hh
  rw [hclosed] at hh
  cases hh

/-- The graph whose parameter rows mean `η`. No check reads the assignment, so
every derivation over `G` is one over each reassignment. -/
@[nospecialize] def reassign (G : NormalGraph ι) (η : MixedAssignment ι) : NormalGraph ι := { G with env := η }

end Verification.PositiveRules
