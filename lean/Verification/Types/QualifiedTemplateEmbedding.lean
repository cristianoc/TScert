import Verification.Types.PositiveGraphs
import Verification.Types.PositiveRules

/- A syntax-preserving import of a closed normal graph. The correspondence is
   proved from mapped production rows, including quantified callable rows and
   the array builtins; no denotation equality is a hypothesis.

   A native kernel must include the reviewed Promise/PromiseLike equations,
   stable-value bounds and the built-in ArrayProto closure. Payloads enter by
   semantic assignment. This file does not construct that reviewed kernel,
   validate an EquationLowering head map, or identify a source application
   Promise<User> with such a semantic application. -/
namespace Verification.QualifiedTemplateEmbedding
open PositiveGraphs PositiveNormalization Tower CallEffects

variable {ι κ : Type}


variable {υ : Type}

section DomainChange
open PositiveRules
variable [DecidableEq ι]

/-- A dependency-closed portion of the graph whose quantified rows admit
exactly the same substitutions in two domains. -/
structure DomainRegion (G : NormalGraph ι) (domain : SchemeDomain ι .mixed)
    (D : ι → Prop) : Prop where
  reads : ∀ i, D i → ∀ j ∈ PositiveRules.reads G i, D j
  parts : ∀ i, D i → ∀ j ∈ meetParts G i, D j
  builtins : ∀ r, G.builtins = some r → ∀ j ∈ r.proto, D j
  unknown : ∀ r, G.builtins = some r → ∀ j ∈ r.unknown, D j
  allowed : ∀ i, D i → ∀ s, G.schemes i = some s → ∀ As,
    domain.allowed s As ↔ G.domain.allowed s As

omit [DecidableEq ι] in
private theorem region_set {D : ι → Prop}
    {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (S : List ι) (hs : ∀ i ∈ S, D i) :
    setSem (fun i => Y (η,i)) S = setSem (fun i => X (η,i)) S := by
  funext n W v
  apply propext
  exact exists_congr fun i => and_congr_right fun hi =>
    iff_of_eq (congrFun (congrFun (congrFun (h η i (hs i hi)) n) W) v)

private theorem DomainRegion.arguments {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (S : List ι) (hs : ∀ i ∈ S, D i) :
    graphArguments G η (setSem fun i => Y (η,i)) S =
      graphArguments G η (setSem fun i => X (η,i)) S := by
  funext n W vs
  apply propext
  apply exists_congr fun i => and_congr_right fun hi => ?_
  by_cases hp : G.listParam i = true
  · simp only [hp, if_true]
  · simp only [hp, Bool.false_eq_true, if_false]
    apply exists_congr fun c => and_congr_right fun hc => ?_
    have hq := (NormalGraph.plain_iff.mp (NormalGraph.plain_of_clauses hc)).2.1
    apply clauseArguments_congr_on (D := PositiveRules.reads G i) (fun T hT j hj => ?_)
      _ _ n (fun j hj U v => ?_) W vs
    · simp only [PositiveRules.reads, hq]
      exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc,
        List.mem_flatten.mpr ⟨T,hT,hj⟩⟩
    · rw [h η j (R.reads i (hs i hi) j hj)]

omit [DecidableEq ι] in
private theorem DomainRegion.builtins_eq {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i)) (c : Clause (List ι)) :
    builtinInvariant { G with domain := domain }
      (setSem fun j => Y (ParameterAssignment.empty .mixed,j)) c =
      builtinInvariant G (setSem fun j => X (ParameterAssignment.empty .mixed,j)) c := by
  simp only [builtinInvariant]
  cases hr : G.builtins with
  | none => rfl
  | some r =>
    dsimp only
    rw [region_set h (ParameterAssignment.empty .mixed) r.proto (R.builtins r hr),
      region_set h (ParameterAssignment.empty .mixed) r.unknown (R.unknown r hr)]

omit [DecidableEq ι] in
private theorem DomainRegion.exc {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i)) :
    builtinExc { G with domain := domain }
      (setSem fun j => Y (ParameterAssignment.empty .mixed,j)) =
      builtinExc G (setSem fun j => X (ParameterAssignment.empty .mixed,j)) := by
  unfold builtinExc
  rw [R.builtins_eq h .source]

private theorem DomainRegion.row {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i)
    (c : Clause (List ι))
    (hc : ∀ S ∈ c.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i) :
    rowSem { G with domain := domain }
      (setSem fun j => Y (ParameterAssignment.empty .mixed,j))
      (setSem fun j => Y (η,j)) (graphArguments G η (setSem fun j => Y (η,j))) c =
    rowSem G (setSem fun j => X (ParameterAssignment.empty .mixed,j))
      (setSem fun j => X (η,j)) (graphArguments G η (setSem fun j => X (η,j))) c := by
  funext n W v
  apply propext
  unfold rowSem
  rw [R.builtins_eq h c, R.exc h]
  apply and_congr _ Iff.rfl
  apply semWithArgs_congr_on hc _ _ _ _ n
    (fun j hj => ?_) (fun S hS => ?_) W v
  · rw [h η j (R.reads i hi j hj)]
    exact fun _ _ _ _ => Iff.rfl
  · rw [R.arguments h η S (fun j hj => R.reads i hi j (hS j hj))]
    exact fun _ _ _ _ => Iff.rfl

private theorem DomainRegion.scheme {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i)
    (s : SchemeRow ι) (hs : G.schemes i = some s) :
    schemeSemWithArgs (mixedParameters { G with domain := domain }) Ξ
      (fun θ S => setSem (fun j => Y (θ,j)) S) η s =
    schemeSemWithArgs (mixedParameters G) Ξ
      (fun θ S => setSem (fun j => X (θ,j)) S) η s := by
  have hv : ∀ θ S, (∀ j ∈ S, j ∈ PositiveRules.reads G i) →
      setSem (fun j => Y (θ,j)) S = setSem (fun j => X (θ,j)) S :=
    fun θ S hS => region_set h θ S (fun j hj => R.reads i hi j (hS j hj))
  have hp : ∀ θ S, (∀ j ∈ S, j ∈ PositiveRules.reads G i) →
      graphArguments G θ (setSem fun j => Y (θ,j)) S =
      graphArguments G θ (setSem fun j => X (θ,j)) S :=
    fun θ S hS => R.arguments h θ S (fun j hj => R.reads i hi j (hS j hj))
  have hb : ∀ b ∈ s.bounds, ∀ j ∈ b.2, j ∈ PositiveRules.reads G i := by
    intro b hb j hj
    simp only [PositiveRules.reads, hs]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hb,hj⟩))
  have hbound : ∀ As n,
      Bounded (fun θ S => (mixedParameters { G with domain := domain }).bound θ
        (setSem fun j => Y (θ,j)) S) η s As n ↔
      Bounded (fun θ S => (mixedParameters G).bound θ
        (setSem fun j => X (θ,j)) S) η s As n := by
    intro As n
    unfold Bounded
    refine forall_congr' fun b => forall_congr' fun hbm =>
      forall_congr' fun _ => forall_congr' fun j => forall_congr' fun _ =>
      forall_congr' fun W => forall_congr' fun u => imp_congr_right fun _ => ?_
    cases u with
    | inl v => exact iff_of_eq (congrFun (congrFun (congrFun (hv η b.2 (hb b hbm)) j) W) v)
    | inr vs => exact iff_of_eq (congrFun (congrFun (congrFun (hp η b.2 (hb b hbm)) j) W) vs)
  have sigs : ∀ θ,
      s.signatures.map (Arrow.map (setSem fun j => Y (θ,j))) =
      s.signatures.map (Arrow.map (setSem fun j => X (θ,j))) := by
    intro θ
    apply List.map_congr_left
    intro a ha
    have hop : ∀ S ∈ a.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i := by
      intro S hS j hj
      simp only [PositiveRules.reads, hs]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatten.mpr ⟨S,hS,hj⟩⟩))
    cases a
    simp only [Arrow.map, Contract.map, Arrow.operands] at *
    congr 1
    · exact hv θ _ (hop _ (by simp))
    · apply List.map_congr_left
      intro S hS
      exact hv θ S (hop S (by simp [hS]))
    · exact hv θ _ (hop _ (by simp))
  have rests : ∀ θ,
      s.variadic.map (RestArrow.mapWith (setSem fun j => Y (θ,j))
        (graphArguments G θ (setSem fun j => Y (θ,j)))) =
      s.variadic.map (RestArrow.mapWith (setSem fun j => X (θ,j))
        (graphArguments G θ (setSem fun j => X (θ,j)))) := by
    intro θ
    apply List.map_congr_left
    intro a ha
    have hop : ∀ S ∈ a.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i := by
      intro S hS j hj
      simp only [PositiveRules.reads, hs]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatten.mpr ⟨S,hS,hj⟩⟩)
    cases a
    simp only [RestArrow.mapWith, Contract.map, RestArrow.operands] at *
    congr 1
    · exact hv θ _ (hop _ (by simp))
    · congr 1
      · apply List.map_congr_left
        intro S hS
        exact hv θ S (hop S (by simp [hS]))
      · exact hp θ _ (hop _ (by simp))
    · exact hv θ _ (hop _ (by simp))
  funext n W v
  apply propext
  unfold schemeSemWithArgs boundedSem
  refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => imp_congr_right fun _ => ?_)
  refine imp_congr (R.allowed i hi s hs As) (imp_congr (hbound As q) ?_)
  simp only [instanceTWithArgs, instanceSigs, instanceRestsWithArgs]
  change sigsT _ s.construct _ _ q (trunc q hq W) v ↔ sigsT _ s.construct _ _ q (trunc q hq W) v
  dsimp only [mixedParameters]
  have sameArgs : graphArguments { G with domain := domain } = graphArguments G := rfl
  rw [sameArgs, sigs, rests]

private theorem DomainRegion.part {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    partSemWithArgs { G with domain := domain } (mixedParameters { G with domain := domain }) Y η i =
      partSemWithArgs G (mixedParameters G) X η i := by
  unfold partSemWithArgs
  change (if G.params i then _ else match G.schemes i with | some _ => _ | none => _) = _
  split
  · rfl
  · cases hs : G.schemes i with
    | some s =>
      show schemeSemWithArgs _ (builtinExc _ (setSem fun l => Y (ParameterAssignment.empty .mixed, l))) _ η s = _
      rw [R.exc h]
      exact R.scheme h η i hi s hs
    | none =>
      funext n W v
      apply propext
      apply exists_congr fun c => and_congr_right fun hc => ?_
      have hop : ∀ S ∈ c.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i := by
        intro S hS j hj
        simp only [PositiveRules.reads, hs]
        exact List.mem_flatMap.mpr ⟨c,List.mem_append_left _ hc,
          List.mem_flatten.mpr ⟨S,hS,hj⟩⟩
      exact iff_of_eq (congrFun (congrFun (congrFun (R.row h η i hi c hop) n) W) v)

/-- Domain replacement agrees at each approximation on the closed region. -/
theorem DomainRegion.layer {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    qLayerWithArgs { G with domain := domain } (mixedParameters { G with domain := domain }) Y (η,i) =
      qLayerWithArgs G (mixedParameters G) X (η,i) := by
  by_cases hp : G.params i = true
  · rw [qLayer_part (Or.inl (show ({ G with domain := domain } : NormalGraph ι).params i = true from hp)),
      qLayer_part (Or.inl hp)]
    exact R.part h η i hi
  · cases hs : G.schemes i with
    | some s =>
      rw [qLayer_part (Or.inr (Or.inl (show (({ G with domain := domain } : NormalGraph ι).schemes i).isSome = true by simp [hs]))),
        qLayer_part (Or.inr (Or.inl (by simp [hs])))]
      exact R.part h η i hi
    | none =>
      cases hm : G.meets i with
      | none =>
        rw [qLayer_part (Or.inr (Or.inr (show ({ G with domain := domain } : NormalGraph ι).meets i = none from hm))),
          qLayer_part (Or.inr (Or.inr hm))]
        exact R.part h η i hi
      | some pc =>
        have parts : ∀ j ∈ pc.1 :: G.meetParams i,
            partSemWithArgs { G with domain := domain } (mixedParameters { G with domain := domain }) Y η j =
              partSemWithArgs G (mixedParameters G) X η j := by
          intro j hj
          exact R.part h η j (R.parts i hi j (by simpa [meetParts, hm] using hj))
        have rows : ∀ c ∈ pc.2,
            rowSem { G with domain := domain }
              (setSem fun j => Y (ParameterAssignment.empty .mixed,j))
              (setSem fun j => Y (η,j)) (graphArguments G η (setSem fun j => Y (η,j))) c =
            rowSem G (setSem fun j => X (ParameterAssignment.empty .mixed,j))
              (setSem fun j => X (η,j)) (graphArguments G η (setSem fun j => X (η,j))) c := by
          intro c hc
          apply R.row h η i hi c
          intro S hS j hj
          simp only [PositiveRules.reads, hs]
          exact List.mem_flatMap.mpr ⟨c,List.mem_append_right _ (by simpa [meetClauses,hm] using hc),
            List.mem_flatten.mpr ⟨S,hS,hj⟩⟩
        funext n W v
        apply propext
        have hp' : G.params i = false := Bool.eq_false_iff.mpr hp
        have hpH : ({ G with domain := domain } : NormalGraph ι).params i = false := hp'
        simp only [qLayerWithArgs, hp', hpH, Bool.false_eq_true, ite_false, hs, hm]
        refine and_congr (and_congr ?_ (forall_congr' fun j => imp_congr_right fun hj => ?_)) ?_
        · rw [parts pc.1 (by simp)]
        · rw [parts j (by simp [hj])]
        · apply exists_congr fun c => and_congr_right fun hc => ?_
          exact iff_of_eq (congrFun (congrFun (congrFun (rows c hc) n) W) v)

theorem DomainRegion.approx {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) (k : Nat)
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    Tower.approx (qLayerWithArgs { G with domain := domain }
      (mixedParameters { G with domain := domain })) k (η,i) =
    Tower.approx (qLayerWithArgs G (mixedParameters G)) k (η,i) := by
  induction k generalizing η i with
  | zero => rfl
  | succ k ih => exact R.layer ih η i hi

/-- Native definitions retain their exact meaning when a source graph uses
a descriptor domain, provided their dependency region retains admission. -/
theorem DomainRegion.denote {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D)
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    qDenoteWithArgs { G with domain := domain }
      (mixedParameters { G with domain := domain }) (η,i) =
      qDenoteWithArgs G (mixedParameters G) (η,i) := by
  funext n W v
  exact congrFun (congrFun (congrFun (R.approx (n+1) η i hi) n) W) v

#print axioms DomainRegion.denote

end DomainChange

end Verification.QualifiedTemplateEmbedding
