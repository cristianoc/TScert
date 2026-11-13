import Verification.Types.PositiveRules

/-! # Store maps: one type's meaning in two stores

A type's meaning is the guarded fixed point of its graph's rows
(`qDenoteWithArgs`, `normalDenote`, `meaning`). Two stores that hold the same
rows under different labels give their types the same meanings. A **store
map** (`StoreMap`) is a label map `φ` from one graph's labels to another's, on
a region `D` of the first graph closed under what its rows read, that is a
row homomorphism there: each label's kind is its image's; its clauses and
its image's cover each other, clause by clause, constructor by constructor,
each operand a union of the same labels renamed (`ClauseRel`: the clause
mapped by an operand map `σ` with `σ S` and `S.map φ` of the same members,
up to the order of a record's or a dictionary's conjunctions, `Reordered`);
its scheme is the image's with binders renamed by `φ` and operands by such a
`σ` (`mapSchemeWith`); its meet's parameter is renamed, its clauses related,
its further parameters the renamed ones; the built-ins are the renamed
built-ins; the domain admits the image scheme's substitutions as it admits
the scheme's; the image's own assignment gives each image label its label's
family. `φ` is injective on `D`, so binders rename to distinct binders.

**The invariance** (`StoreMap.meaning_eq`, proved): for every type `A` of
labels in `D`, `meaning H (A.map φ) = meaning G A`, by induction on the
approximation index over pairs of related assignments
(`StoreMap.Related`). Arrows keep their effects (`Contract.map`), so the
footprints, throw flags and fresh results of callable types are covered;
schemes are covered with their binders, bounds, variadic signatures,
qualification and construct flag; argument packs and parameter rows of
every kind are covered. docs/SINGLE-PASS-THEOREM.md, section 7, states
how the importer's signature agreement follows. -/

namespace Verification.StoreMaps
open PositiveGraphs PositiveNormalization Tower CallEffects PositiveRules

variable {ι κ : Type}

/-! ## Related rows -/

/-- An operand map `σ` agrees with `φ` on the operands `ops`: each operand,
and the empty one, maps to a union of the same members as its renaming. -/
def Equiv (φ : ι → κ) (σ : List ι → List κ) (ops : List (List ι)) : Prop :=
  ∀ S, (S ∈ ops ∨ S = []) → ∀ x, x ∈ σ S ↔ x ∈ S.map φ

/-- Two lists of the same members, in any order. -/
def SameMembers {α : Type} (l l' : List α) : Prop := ∀ x, x ∈ l ↔ x ∈ l'

/-- **Two clauses alike up to the order of their conjunctions**: a record's
or a dictionary's lists (its fields, further record operands, views,
optional fields, methods, key bounds and stable keys, a dictionary's index
views and cells too), each a conjunction its meaning reads by membership,
with the same members; any other clause the same. A meet lists its parts'
conjunctions in its parts' order (`meetClause`), which is a store's. -/
def Reordered {α : Type} : Clause α → Clause α → Prop
  | .refs a bs vs os ms ks st, c' => ∃ a' bs' vs' os' ms' ks' st', c' = .refs a' bs' vs' os' ms' ks' st' ∧
      SameMembers a a' ∧ SameMembers bs bs' ∧ SameMembers vs vs' ∧ SameMembers os os' ∧ SameMembers ms ms' ∧
      SameMembers ks ks' ∧ SameMembers st st'
  | .dict a bs vs ds os ms ks cs st, c' => ∃ a' bs' vs' ds' os' ms' ks' cs' st',
      c' = .dict a' bs' vs' ds' os' ms' ks' cs' st' ∧
      SameMembers a a' ∧ SameMembers bs bs' ∧ SameMembers vs vs' ∧ SameMembers ds ds' ∧ SameMembers os os' ∧
      SameMembers ms ms' ∧ SameMembers ks ks' ∧ SameMembers cs cs' ∧ SameMembers st st'
  | c, c' => c' = c

/-- **Related clauses**: the image clause is the clause, constructor by
constructor, each operand mapped by an operand map agreeing with `φ`, its
conjunctions in any order (`Reordered`). -/
def ClauseRel (φ : ι → κ) (c : Clause (List ι)) (c' : Clause (List κ)) : Prop :=
  ∃ σ, Equiv φ σ c.operands ∧ Reordered (c.map σ) c'

section Reordered
variable {α : Type}

theorem SameMembers.map {β : Type} {l l' : List α} (h : SameMembers l l') (g : α → β) :
    SameMembers (l.map g) (l'.map g) := fun x => by
  have h : ∀ y, y ∈ l ↔ y ∈ l' := h
  simp only [List.mem_map, h]

theorem SameMembers.nil_iff {l l' : List α} (h : SameMembers l l') : l = [] ↔ l' = [] := by
  have h : ∀ y, y ∈ l ↔ y ∈ l' := h
  simp only [List.eq_nil_iff_forall_not_mem, h]

/-- A record's conjunctions read by membership (proved). -/
theorem refsT_reordered {A A' : Fields} {Bs Bs' : List Fields}
    (hA : SameMembers A A') (hB : SameMembers Bs Bs') :
    ReferenceConjunctions.refsT A' Bs' = ReferenceConjunctions.refsT A Bs := by
  funext n W v
  have hn := hA.nil_iff
  have hA : ∀ y, y ∈ A ↔ y ∈ A' := hA
  have hB : ∀ y, y ∈ Bs ↔ y ∈ Bs' := hB
  have hne : ((A' :: Bs').flatten ≠ []) = ((A :: Bs).flatten ≠ []) := by
    simp only [ne_eq, List.flatten_cons, List.append_eq_nil_iff, List.flatten_eq_nil_iff, hn, hB]
  simp only [ReferenceConjunctions.refsT, recT, hA, hB, hne]

/-- **Reordering a clause's conjunctions keeps its meaning** (proved). -/
theorem semWithArgs_reordered {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {c c' : Clause α}
    (h : Reordered c c') : semWithArgs Ξ X P c' = semWithArgs Ξ X P c := by
  cases c
  case refs a bs vs os ms ks st =>
    obtain ⟨a', bs', vs', os', ms', ks', st', rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
    funext n W v
    have h3 : ∀ y, y ∈ vs ↔ y ∈ vs' := h3
    have h4 : ∀ y, y ∈ os ↔ y ∈ os' := h4
    have h5 : ∀ y, y ∈ ms ↔ y ∈ ms' := h5
    have h6 : ∀ y, y ∈ ks ↔ y ∈ ks' := h6
    have h7 : ∀ y, y ∈ st ↔ y ∈ st' := h7
    simp only [semWithArgs]
    have hA : SameMembers (ReferenceConjunctions.famsOf X a) (ReferenceConjunctions.famsOf X a') := h1.map _
    rw [refsT_reordered hA (h2.map (ReferenceConjunctions.famsOf X))]
    simp only [viewsT, optT, MethodMembers.methodT, stableKeysT, ReferenceConjunctions.famsOf,
      ReferenceConjunctions.viewsOf, List.mem_map, h3,
      h4, h5, h6, h7]
  case dict a bs vs ds os ms ks cs st =>
    obtain ⟨a', bs', vs', ds', os', ms', ks', cs', st', rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    funext n W v
    have h3 : ∀ y, y ∈ vs ↔ y ∈ vs' := h3
    have h4 : ∀ y, y ∈ ds ↔ y ∈ ds' := h4
    have h5 : ∀ y, y ∈ os ↔ y ∈ os' := h5
    have h6 : ∀ y, y ∈ ms ↔ y ∈ ms' := h6
    have h7 : ∀ y, y ∈ ks ↔ y ∈ ks' := h7
    have h8 : ∀ y, y ∈ cs ↔ y ∈ cs' := h8
    have h9 : ∀ y, y ∈ st ↔ y ∈ st' := h9
    simp only [semWithArgs]
    have hA : SameMembers (ReferenceConjunctions.famsOf X a) (ReferenceConjunctions.famsOf X a') := h1.map _
    rw [refsT_reordered hA (h2.map (ReferenceConjunctions.famsOf X))]
    simp only [viewsT, optT, MethodMembers.methodT, stableKeysT, ReferenceConjunctions.famsOf,
      ReferenceConjunctions.viewsOf, List.mem_map, h3,
      h4, h5, h6, h7, h8, h9]
  all_goals (cases h; rfl)

/-- Reordering keeps the constructor, so whether the built-ins' invariant
applies (proved). -/
theorem carriesInvariant_reordered {c c' : Clause α} (h : Reordered c c') :
    c'.carriesInvariant = c.carriesInvariant := by
  cases c
  case refs => obtain ⟨_, _, _, _, _, _, _, rfl, -⟩ := h; rfl
  case dict => obtain ⟨_, _, _, _, _, _, _, _, _, rfl, -⟩ := h; rfl
  all_goals (cases h; rfl)

/-- Reordering keeps an argument list's reading: a record or a dictionary
is no argument list (proved). -/
theorem clauseArguments_reordered {X : α → Fam} {c c' : Clause α} (h : Reordered c c') :
    clauseArguments X c' = clauseArguments X c := by
  cases c
  case refs => obtain ⟨_, _, _, _, _, _, _, rfl, -⟩ := h; rfl
  case dict => obtain ⟨_, _, _, _, _, _, _, _, _, rfl, -⟩ := h; rfl
  all_goals (cases h; rfl)

end Reordered

/-- **Related clause lists**: each clause of one is related to a clause of
the other, both ways. -/
def RowsRel (φ : ι → κ) (L : List (Clause (List ι))) (L' : List (Clause (List κ))) : Prop :=
  (∀ c ∈ L, ∃ c' ∈ L', ClauseRel φ c c') ∧ ∀ c' ∈ L', ∃ c ∈ L, ClauseRel φ c c'

/-- Every operand of a scheme row: its signatures', its bounds' types and its
variadic signatures'. -/
def schemeOps (s : SchemeRow ι) : List (List ι) :=
  s.signatures.flatMap Arrow.operands ++ s.bounds.map (·.2) ++ s.variadic.flatMap RestArrow.operands

/-- A scheme row with its binders renamed by `φ` and every operand by `σ`;
its qualification and construct flag kept. -/
def mapSchemeWith (φ : ι → κ) (σ : List ι → List κ) (s : SchemeRow ι) : SchemeRow κ where
  binders := s.binders.map φ
  signatures := s.signatures.map (Arrow.map σ)
  bounds := s.bounds.map fun b => (φ b.1, σ b.2)
  variadic := s.variadic.map (RestArrow.map σ)
  resolution := s.resolution
  construct := s.construct

/-- Related built-ins: none in both graphs, or the same keys and types of
the same labels renamed. -/
def BuiltinsRel (φ : ι → κ) : Option (ArrayBuiltins ι) → Option (ArrayBuiltins κ) → Prop
  | none, none => True
  | some r, some r' => r'.keys = r.keys ∧ (∀ x, x ∈ r'.proto ↔ x ∈ r.proto.map φ) ∧
      ∀ x, x ∈ r'.unknown ↔ x ∈ r.unknown.map φ
  | _, _ => False

/-- **A store map** from graph `G` to graph `H` on the region `D`: a label
map giving a parameter or a binder of a scheme of `D` an image no other label
of `D` has, under which every label of `D` has a row related to its image's.
Two labels of other rows may share an image: a store may hold one type at two
labels. `D` is closed under the rows its labels read, their meet parts,
their schemes' binders and bound binders, and holds the built-ins' types. -/
structure StoreMap (G : NormalGraph ι) (H : NormalGraph κ) where
  φ : ι → κ
  D : ι → Prop
  inj : ∀ a b, D a → D b →
    (G.params a = true ∨ ∃ i, D i ∧ ∃ s, G.schemes i = some s ∧ (a ∈ s.binders ∨ ∃ c ∈ s.bounds, c.1 = a)) →
    φ a = φ b → a = b
  reads : ∀ i, D i → ∀ j ∈ PositiveRules.reads G i, D j
  parts : ∀ i, D i → ∀ j ∈ meetParts G i, D j
  binders : ∀ i, D i → ∀ s, G.schemes i = some s → (∀ b ∈ s.binders, D b) ∧ ∀ b ∈ s.bounds, D b.1
  builtins : BuiltinsRel φ G.builtins H.builtins
  builtinsIn : ∀ r, G.builtins = some r → (∀ j ∈ r.proto, D j) ∧ ∀ j ∈ r.unknown, D j
  kinds : ∀ i, D i → H.parameterKinds (φ i) = G.parameterKinds i
  schemesNone : ∀ i, D i → G.schemes i = none → H.schemes (φ i) = none
  schemes : ∀ i, D i → ∀ s, G.schemes i = some s →
    ∃ σ, Equiv φ σ (schemeOps s) ∧ H.schemes (φ i) = some (mapSchemeWith φ σ s)
  meetsNone : ∀ i, D i → G.meets i = none → H.meets (φ i) = none
  meets : ∀ i, D i → ∀ p cs, G.meets i = some (p, cs) →
    ∃ cs', H.meets (φ i) = some (φ p, cs') ∧ RowsRel φ cs cs'
  meetParams : ∀ i, D i → ∀ x, x ∈ H.meetParams (φ i) ↔ x ∈ (G.meetParams i).map φ
  rows : ∀ i, D i → G.plain i = true → RowsRel φ (G.rows i) (H.rows (φ i))
  allowed : ∀ i, D i → ∀ s, G.schemes i = some s → ∀ s', H.schemes (φ i) = some s' → ∀ As,
    H.domain.allowed s' As ↔ G.domain.allowed s As
  env : ∀ p, D p → H.env.1 (φ p) = G.env.1 p

namespace StoreMap
variable {G : NormalGraph ι} {H : NormalGraph κ} (m : StoreMap G H)

/-- Two assignments related by the map: the image of each label of the
region is given that label's family. -/
def Related (η : MixedAssignment ι) (θ : MixedAssignment κ) : Prop :=
  ∀ p, m.D p → θ.1 (m.φ p) = η.1 p

theorem related_empty : m.Related (ParameterAssignment.empty .mixed) (ParameterAssignment.empty .mixed) :=
  fun _ _ => rfl

theorem related_env : m.Related G.env H.env := m.env

/-- A scheme's reassignment keeps related assignments related. -/
theorem related_assign {η : MixedAssignment ι} {θ : MixedAssignment κ} (h : m.Related η θ) :
    ∀ (bs : List ι) (As : List MixedFamily), (∀ b ∈ bs, m.D b) →
      (∀ b ∈ bs, G.params b = true ∨ ∃ i, m.D i ∧ ∃ s, G.schemes i = some s ∧ (b ∈ s.binders ∨ ∃ c ∈ s.bounds, c.1 = b)) →
      m.Related (assign η bs As) (assign θ (bs.map m.φ) As)
  | [], As, _, _ => by
    intro p hp
    have h1 : (assign θ ([] : List κ) As).1 (m.φ p) = θ.1 (m.φ p) := assign_nmem θ [] As (by simp)
    have h2 : (assign η ([] : List ι) As).1 p = η.1 p := assign_nmem η [] As (by simp)
    simp only [List.map_nil]
    rw [h1, h2, h p hp]
  | b :: bs, [], hbs, _ => by
    intro p hp
    have h1 : (assign θ ((b :: bs).map m.φ) []).1 (m.φ p) = θ.1 (m.φ p) := by
      simp [assign]
    have h2 : (assign η (b :: bs) []).1 p = η.1 p := by simp [assign]
    rw [h1, h2, h p hp]
  | b :: bs, A :: As, hbs, hbind => by
    intro p hp
    simp only [List.map_cons]
    by_cases hpb : p = b
    · subst hpb
      rw [assign_cons_head, assign_cons_head]
    · have hne : m.φ p ≠ m.φ b := fun he =>
        hpb (m.inj b p (hbs b List.mem_cons_self) hp (hbind b List.mem_cons_self) he.symm).symm
      rw [assign_cons_ne _ _ _ _ hne, assign_cons_ne _ _ _ _ hpb]
      exact related_assign h bs As (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' => hbind b' (List.mem_cons_of_mem _ hb')) p hp

theorem params_eq {i : ι} (hi : m.D i) : H.params (m.φ i) = G.params i := by
  simp [NormalGraph.params, m.kinds i hi]

theorem listParam_eq {i : ι} (hi : m.D i) : H.listParam (m.φ i) = G.listParam i := by
  simp [NormalGraph.listParam, m.kinds i hi]

theorem schemes_isNone {i : ι} (hi : m.D i) : (H.schemes (m.φ i)).isNone = (G.schemes i).isNone := by
  cases hs : G.schemes i with
  | none => rw [m.schemesNone i hi hs]; rfl
  | some s => obtain ⟨σ, -, h⟩ := m.schemes i hi s hs; rw [h]; rfl

theorem meets_isNone {i : ι} (hi : m.D i) : (H.meets (m.φ i)).isNone = (G.meets i).isNone := by
  cases hs : G.meets i with
  | none => rw [m.meetsNone i hi hs]; rfl
  | some pc => obtain ⟨cs', h, -⟩ := m.meets i hi pc.1 pc.2 hs; rw [h]; rfl

theorem plain_eq {i : ι} (hi : m.D i) : H.plain (m.φ i) = G.plain i := by
  unfold NormalGraph.plain
  rw [m.params_eq hi, m.schemes_isNone hi, m.meets_isNone hi]

/-- The image label's clauses and the label's are related. -/
theorem clauses_rel {i : ι} (hi : m.D i) : RowsRel m.φ (G i) (H (m.φ i)) := by
  show RowsRel m.φ (G.clauses i) (H.clauses (m.φ i))
  unfold NormalGraph.clauses
  rw [m.plain_eq hi]
  cases hp : G.plain i
  · exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  · simp only [if_true]
    exact m.rows i hi hp

theorem mem_map_iff {bs : List ι} (hbs : ∀ b ∈ bs, m.D b)
    (hbind : ∀ b ∈ bs, G.params b = true ∨ ∃ i, m.D i ∧ ∃ s, G.schemes i = some s ∧ (b ∈ s.binders ∨ ∃ c ∈ s.bounds, c.1 = b))
    {p : ι} (hp : m.D p) :
    m.φ p ∈ bs.map m.φ ↔ p ∈ bs := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    rw [m.inj b p (hbs b hb) hp (hbind b hb) he] at hb
    exact hb
  · exact List.mem_map_of_mem

/-! ## Families agreeing on renamed types -/

theorem setSem_ext {F : κ → Fam} {T T' : List κ} (h : ∀ x, x ∈ T ↔ x ∈ T') : setSem F T = setSem F T' := by
  funext n W v
  exact propext (exists_congr fun x => and_congr_left fun _ => h x)

theorem setSem_map {F : κ → Fam} {E : ι → Fam} {S : List ι} (h : ∀ j ∈ S, F (m.φ j) = E j) :
    setSem F (S.map m.φ) = setSem E S := by
  funext n W v
  apply propext
  constructor
  · rintro ⟨i', hi', hv⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact ⟨j, hj, h j hj ▸ hv⟩
  · rintro ⟨j, hj, hv⟩
    exact ⟨m.φ j, List.mem_map_of_mem hj, (h j hj).symm ▸ hv⟩

/-- A clause whose operands each mean the same under two readings, the empty
operand included, means the same under both. -/
theorem semWithArgs_on {Ξ : Fam} {c : Clause (List ι)} {X X' : List ι → Fam} {P P' : List ι → ArgFam}
    (h : ∀ S, S ∈ c.operands ∨ S = [] → X S = X' S ∧ P S = P' S) :
    semWithArgs Ξ X P c = semWithArgs Ξ X' P' c := by
  classical
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [← hcr, semWithArgs_map, semWithArgs_map]
  have hr : ∀ S, X (r S) = X' (r S) ∧ P (r S) = P' (r S) := fun S => by
    by_cases hS : S ∈ c.operands
    · simp only [r, hS, if_true]; exact h S (.inl hS)
    · simp only [r, hS, if_false]; exact h [] (.inr rfl)
  have h1 : (fun a => X (r a)) = fun a => X' (r a) := funext fun a => (hr a).1
  have h2 : (fun a => P (r a)) = fun a => P' (r a) := funext fun a => (hr a).2
  rw [h1, h2]

theorem clauseArguments_on {c : Clause (List ι)} {X X' : List ι → Fam}
    (h : ∀ S, S ∈ c.operands ∨ S = [] → X S = X' S) :
    clauseArguments X c = clauseArguments X' c := by
  classical
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [← hcr, clauseArguments_map, clauseArguments_map]
  have h1 : (fun a => X (r a)) = fun a => X' (r a) := funext fun a => by
    by_cases hS : a ∈ c.operands
    · simp only [r, hS, if_true]; exact h a (.inl hS)
    · simp only [r, hS, if_false]; exact h [] (.inr rfl)
  rw [h1]

/-- A reading of `κ`-types agrees with a reading of `ι`-types: a union of the
members of a region type renamed reads as that type. -/
def Agrees {β : Type} (A : List κ → β) (B : List ι → β) : Prop :=
  ∀ S T, (∀ j ∈ S, m.D j) → (∀ x, x ∈ T ↔ x ∈ S.map m.φ) → A T = B S

theorem agrees_ops {β : Type} {A : List κ → β} {B : List ι → β} (h : m.Agrees A B) {σ : List ι → List κ}
    {ops : List (List ι)} (he : Equiv m.φ σ ops) (hops : ∀ S ∈ ops, ∀ j ∈ S, m.D j) :
    ∀ S, S ∈ ops ∨ S = [] → A (σ S) = B S := by
  intro S hS
  refine h S (σ S) ?_ (he S hS)
  rcases hS with hS | rfl
  · exact hops S hS
  · simp

theorem builtinInvariant_eq {A : List κ → Fam} {B : List ι → Fam} (h : m.Agrees A B)
    {c : Clause (List ι)} {c' : Clause (List κ)} (hc : c'.carriesInvariant = c.carriesInvariant) :
    builtinInvariant H A c' = builtinInvariant G B c := by
  unfold builtinInvariant
  rw [hc]
  have hb := m.builtins
  cases hr : G.builtins with
  | none =>
    rw [hr] at hb
    cases hr' : H.builtins with
    | none => rfl
    | some _ => rw [hr'] at hb; exact hb.elim
  | some r =>
    obtain ⟨hp, hu⟩ := m.builtinsIn r hr
    rw [hr] at hb
    cases hr' : H.builtins with
    | none => rw [hr'] at hb; exact hb.elim
    | some r' =>
      rw [hr'] at hb
      obtain ⟨hk, hpe, hue⟩ := hb
      dsimp only
      rw [h r.proto r'.proto hp hpe, h r.unknown r'.unknown hu hue, hk]

theorem builtinExc_eq {A : List κ → Fam} {B : List ι → Fam} (h : m.Agrees A B) :
    builtinExc H A = builtinExc G B := by
  unfold builtinExc
  rw [m.builtinInvariant_eq h (c := .source) (c' := .source) rfl]

theorem rowSem_eq {A X : List κ → Fam} {P : List κ → ArgFam} {A' X' : List ι → Fam} {P' : List ι → ArgFam}
    (hA : m.Agrees A A') (hX : m.Agrees X X') (hP : m.Agrees P P')
    {c : Clause (List ι)} {c' : Clause (List κ)} (hrel : ClauseRel m.φ c c')
    (hc : ∀ S ∈ c.operands, ∀ j ∈ S, m.D j) :
    rowSem H A X P c' = rowSem G A' X' P' c := by
  obtain ⟨σ, he, hr⟩ := hrel
  funext n W v
  unfold rowSem
  rw [semWithArgs_reordered hr, m.builtinInvariant_eq hA ((carriesInvariant_reordered hr).trans
    (Clause.carriesInvariant_map _ _)), m.builtinExc_eq hA, semWithArgs_map]
  rw [semWithArgs_on (X' := X') (P' := P') fun S hS =>
    ⟨m.agrees_ops hX he hc S hS, m.agrees_ops hP he hc S hS⟩]

theorem clauseArguments_eq {X : List κ → Fam} {X' : List ι → Fam} (hX : m.Agrees X X')
    {c : Clause (List ι)} {c' : Clause (List κ)} (hrel : ClauseRel m.φ c c')
    (hc : ∀ S ∈ c.operands, ∀ j ∈ S, m.D j) :
    clauseArguments X c' = clauseArguments X' c := by
  obtain ⟨σ, he, hr⟩ := hrel
  rw [clauseArguments_reordered hr, clauseArguments_map, clauseArguments_on (X' := X') fun S hS => m.agrees_ops hX he hc S hS]

/-- Related clause lists, each clause read the same as its related clause,
mean the same. -/
theorem rows_eq {F : Clause (List κ) → Fam} {E : Clause (List ι) → Fam} {L : List (Clause (List ι))}
    {L' : List (Clause (List κ))} (hrel : RowsRel m.φ L L')
    (h : ∀ c ∈ L, ∀ c', ClauseRel m.φ c c' → F c' = E c) : setSem F L' = setSem E L := by
  funext n W v
  apply propext
  constructor
  · rintro ⟨c', hc', hv⟩
    obtain ⟨c, hc, hr⟩ := hrel.2 c' hc'
    exact ⟨c, hc, h c hc c' hr ▸ hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨c', hc', hr⟩ := hrel.1 c hc
    exact ⟨c', hc', (h c hc c' hr).symm ▸ hv⟩

theorem rows_exists {P : Clause (List κ) → Prop} {Q : Clause (List ι) → Prop} {L : List (Clause (List ι))}
    {L' : List (Clause (List κ))} (hrel : RowsRel m.φ L L')
    (h : ∀ c ∈ L, ∀ c', ClauseRel m.φ c c' → (P c' ↔ Q c)) : (∃ c' ∈ L', P c') ↔ ∃ c ∈ L, Q c := by
  constructor
  · rintro ⟨c', hc', hv⟩
    obtain ⟨c, hc, hr⟩ := hrel.2 c' hc'
    exact ⟨c, hc, (h c hc c' hr).mp hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨c', hc', hr⟩ := hrel.1 c hc
    exact ⟨c', hc', (h c hc c' hr).mpr hv⟩

/-- A clause row's operands are read labels of the region. -/
theorem clause_reads {i : ι} (hi : m.D i) {c : Clause (List ι)} (hc : c ∈ G i) :
    ∀ S ∈ c.operands, ∀ j ∈ S, m.D j := by
  have hq := (NormalGraph.plain_iff.mp (NormalGraph.plain_of_clauses hc)).2.1
  intro T hT j hj
  refine m.reads i hi j ?_
  simp only [PositiveRules.reads, hq]
  exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨T, hT, hj⟩⟩

/-! ## One step of the denotation, on related assignments -/

section Step
variable {X : MixedAssignment ι × ι → Fam} {Y : MixedAssignment κ × κ → Fam}

/-- The step's premise: the readings agree on the region at related
assignments. -/
def StepPremise (X : MixedAssignment ι × ι → Fam) (Y : MixedAssignment κ × κ → Fam) : Prop :=
  ∀ η θ, m.Related η θ → ∀ i, m.D i → Y (θ, m.φ i) = X (η, i)

variable {m}

theorem values_agree (h : m.StepPremise X Y) {η θ} (hr : m.Related η θ) :
    m.Agrees (setSem fun l => Y (θ, l)) (setSem fun l => X (η, l)) :=
  fun _ _ hS he => (setSem_ext he).trans (m.setSem_map fun j hj => h η θ hr j (hS j hj))

theorem arguments_agree (h : m.StepPremise X Y) {η θ} (hr : m.Related η θ) :
    m.Agrees (graphArguments H θ (setSem fun l => Y (θ, l))) (graphArguments G η (setSem fun l => X (η, l))) := by
  intro S T hS he
  funext n W vs
  apply propext
  unfold graphArguments
  have body : ∀ i ∈ S,
      (if H.listParam (m.φ i) then θ.1 (m.φ i) n W (.inr vs)
        else ∃ c ∈ H (m.φ i), clauseArguments (setSem fun l => Y (θ, l)) c n W vs) ↔
      (if G.listParam i then η.1 i n W (.inr vs)
        else ∃ c ∈ G i, clauseArguments (setSem fun l => X (η, l)) c n W vs) := by
    intro i hi
    have hD := hS i hi
    rw [m.listParam_eq hD, hr i hD]
    split
    · exact Iff.rfl
    · exact m.rows_exists (m.clauses_rel hD) fun c hc c' hrel => by
        rw [m.clauseArguments_eq (values_agree h hr) hrel (m.clause_reads hD hc)]
  constructor
  · rintro ⟨i', hi', hv⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ((he i').mp hi')
    exact ⟨i, hi, (body i hi).mp hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨m.φ i, (he _).mpr (List.mem_map_of_mem hi), (body i hi).mpr hv⟩

theorem bound_agree (h : m.StepPremise X Y) {η θ} (hr : m.Related η θ) :
    m.Agrees ((mixedParameters H).bound θ (setSem fun l => Y (θ, l)))
      ((mixedParameters G).bound η (setSem fun l => X (η, l))) := by
  intro S T hS he
  funext n W x
  cases x with
  | inl v =>
    show setSem (fun l => Y (θ, l)) T n W v = setSem (fun l => X (η, l)) S n W v
    rw [values_agree h hr S T hS he]
  | inr vs =>
    show graphArguments H θ _ T n W vs = graphArguments G η _ S n W vs
    rw [arguments_agree h hr S T hS he]

theorem exc_eq (h : m.StepPremise X Y) :
    builtinExc H (setSem fun l => Y (ParameterAssignment.empty .mixed, l)) =
      builtinExc G (setSem fun l => X (ParameterAssignment.empty .mixed, l)) :=
  m.builtinExc_eq (values_agree h m.related_empty)

/-- A scheme row's operands are read labels of the region. -/
theorem scheme_reads {i : ι} (hi : m.D i) {s : SchemeRow ι} (hs : G.schemes i = some s) :
    ∀ S ∈ schemeOps s, ∀ j ∈ S, m.D j := by
  intro S hS j hj
  refine m.reads i hi j ?_
  simp only [PositiveRules.reads, hs]
  simp only [schemeOps, List.mem_append, List.mem_flatMap, List.mem_map] at hS
  rcases hS with (⟨a, ha, hS⟩ | ⟨b, hb, rfl⟩) | ⟨a, ha, hS⟩
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨a, ha, List.mem_flatten.mpr ⟨S, hS, hj⟩⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hj⟩))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, List.mem_flatten.mpr ⟨S, hS, hj⟩⟩)

theorem scheme_eq (h : m.StepPremise X Y) {η θ} (hr : m.Related η θ) {i : ι} (hi : m.D i)
    {s : SchemeRow ι} (hs : G.schemes i = some s) {σ : List ι → List κ} (he : Equiv m.φ σ (schemeOps s))
    (hs' : H.schemes (m.φ i) = some (mapSchemeWith m.φ σ s)) :
    schemeSemWithArgs (mixedParameters H)
        (builtinExc H (setSem fun l => Y (ParameterAssignment.empty .mixed, l)))
        (fun θ' S => setSem (fun l => Y (θ', l)) S) θ (mapSchemeWith m.φ σ s) =
      schemeSemWithArgs (mixedParameters G)
        (builtinExc G (setSem fun l => X (ParameterAssignment.empty .mixed, l)))
        (fun η' S => setSem (fun l => X (η', l)) S) η s := by
  have hops := scheme_reads hi hs
  have hsig : ∀ a ∈ s.signatures, ∀ S ∈ a.operands, S ∈ schemeOps s := fun a ha S hS => by
    simp only [schemeOps, List.mem_append, List.mem_flatMap]; exact .inl (.inl ⟨a, ha, hS⟩)
  have hbd : ∀ b ∈ s.bounds, b.2 ∈ schemeOps s := fun b hb => by
    simp only [schemeOps, List.mem_append, List.mem_map]; exact .inl (.inr ⟨b, hb, rfl⟩)
  have hvar : ∀ a ∈ s.variadic, ∀ S ∈ a.operands, S ∈ schemeOps s := fun a ha S hS => by
    simp only [schemeOps, List.mem_append, List.mem_flatMap]; exact .inr ⟨a, ha, hS⟩
  obtain ⟨hbs, hbb⟩ := m.binders i hi s hs
  rw [exc_eq h]
  funext n W v
  apply propext
  unfold schemeSemWithArgs boundedSem
  refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => ?_)
  have hlen : (mapSchemeWith m.φ σ s).binders.length = s.binders.length := by simp [mapSchemeWith]
  rw [hlen]
  refine imp_congr_right fun hAs => imp_congr (m.allowed i hi s hs _ hs' As) ?_
  have hbind : ∀ b ∈ s.binders, G.params b = true ∨
      ∃ i', m.D i' ∧ ∃ s', G.schemes i' = some s' ∧ (b ∈ s'.binders ∨ ∃ c ∈ s'.bounds, c.1 = b) :=
    fun b hb => .inr ⟨i, hi, s, hs, .inl hb⟩
  have hr' := m.related_assign hr s.binders As hbs hbind
  refine imp_congr ?_ ?_
  · unfold Bounded
    simp only [mapSchemeWith, List.forall_mem_map]
    refine forall_congr' fun b => forall_congr' fun hb => ?_
    rw [m.mem_map_iff hbs hbind (hbb b hb)]
    refine forall_congr' fun _ => forall_congr' fun j => forall_congr' fun _ =>
      forall_congr' fun U => forall_congr' fun u => ?_
    rw [hr' b.1 (hbb b hb)]
    rw [bound_agree h hr b.2 (σ b.2) (hops _ (hbd b hb)) (he _ (.inl (hbd b hb)))]
  · have hv := values_agree h hr'
    have sigs : (instanceSigs (fun θ' S => setSem (fun l => Y (θ', l)) S) θ (mapSchemeWith m.φ σ s) As) =
        instanceSigs (fun η' S => setSem (fun l => X (η', l)) S) η s As := by
      unfold instanceSigs
      simp only [mapSchemeWith, List.map_map]
      apply List.map_congr_left
      intro a ha
      have hop : ∀ S ∈ a.operands, setSem (fun l => Y (assign θ (s.binders.map m.φ) As, l)) (σ S) =
          setSem (fun l => X (assign η s.binders As, l)) S :=
        fun S hS => hv S (σ S) (hops S (hsig a ha S hS)) (he S (.inl (hsig a ha S hS)))
      obtain ⟨rc, args, res, eff⟩ := a
      simp only [Function.comp, Arrow.map, Contract.map, Arrow.operands] at hop ⊢
      congr 1
      · exact hop rc (by simp)
      · simp only [List.map_map]
        apply List.map_congr_left
        intro S hS
        exact hop S (by simp [hS])
      · exact hop res (by simp)
    have rests : instanceRestsWithArgs (fun θ' S => setSem (fun l => Y (θ', l)) S) θ (mapSchemeWith m.φ σ s) As
          (mixedParameters H).arguments =
        instanceRestsWithArgs (fun η' S => setSem (fun l => X (η', l)) S) η s As
          (mixedParameters G).arguments := by
      unfold instanceRestsWithArgs
      simp only [mapSchemeWith, List.map_map]
      apply List.map_congr_left
      intro a ha
      have hop : ∀ S ∈ a.operands, setSem (fun l => Y (assign θ (s.binders.map m.φ) As, l)) (σ S) =
          setSem (fun l => X (assign η s.binders As, l)) S :=
        fun S hS => hv S (σ S) (hops S (hvar a ha S hS)) (he S (.inl (hvar a ha S hS)))
      have hap : ∀ S ∈ a.operands, graphArguments H (assign θ (s.binders.map m.φ) As)
            (setSem fun l => Y (assign θ (s.binders.map m.φ) As, l)) (σ S) =
          graphArguments G (assign η s.binders As) (setSem fun l => X (assign η s.binders As, l)) S :=
        fun S hS => arguments_agree h hr' S (σ S) (hops S (hvar a ha S hS)) (he S (.inl (hvar a ha S hS)))
      obtain ⟨rc, ⟨args, rest⟩, res, eff⟩ := a
      simp only [Function.comp, RestArrow.map, RestArrow.mapWith, Contract.map, RestArrow.operands] at hop hap ⊢
      congr 1
      · exact hop rc (by simp)
      · congr 1
        · simp only [List.map_map]
          apply List.map_congr_left
          intro S hS
          exact hop S (by simp [hS])
        · exact hap rest (by simp)
      · exact hop res (by simp)
    dsimp only
    unfold instanceTWithArgs
    rw [sigs, rests]
    rfl

theorem part_eq (h : m.StepPremise X Y) {η θ} (hr : m.Related η θ) {q : ι} (hq : m.D q) :
    partSemWithArgs H (mixedParameters H) Y θ (m.φ q) = partSemWithArgs G (mixedParameters G) X η q := by
  unfold partSemWithArgs
  rw [m.params_eq hq]
  split
  · funext n W v
    show selectParameter (H.parameterKinds (m.φ q)) (θ.1 (m.φ q)) n W (.inl v) =
      selectParameter (G.parameterKinds q) (η.1 q) n W (.inl v)
    rw [m.kinds q hq, hr q hq]
  · cases hs : G.schemes q with
    | some s =>
      obtain ⟨σ, he, hs'⟩ := m.schemes q hq s hs
      rw [hs']
      exact scheme_eq h hr hq hs he hs'
    | none =>
      rw [m.schemesNone q hq hs]
      exact m.rows_eq (m.clauses_rel hq) fun c hc c' hrel =>
        m.rowSem_eq (values_agree h m.related_empty) (values_agree h hr) (arguments_agree h hr) hrel
          (fun S hS j hj => m.reads q hq j (by
            simp only [PositiveRules.reads, hs]
            exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨S, hS, hj⟩⟩))

theorem layer_eq (h : m.StepPremise X Y) {η θ} (hr : m.Related η θ) {i : ι} (hi : m.D i) :
    qLayerWithArgs H (mixedParameters H) Y (θ, m.φ i) = qLayerWithArgs G (mixedParameters G) X (η, i) := by
  have hpart := part_eq h hr hi
  by_cases hp : G.params i = true
  · rw [qLayer_part (Or.inl (by rw [m.params_eq hi]; exact hp)), qLayer_part (Or.inl hp)]
    exact hpart
  · cases hs : G.schemes i with
    | some s =>
      obtain ⟨σ, -, hs'⟩ := m.schemes i hi s hs
      rw [qLayer_part (Or.inr (Or.inl (by rw [hs']; rfl))),
        qLayer_part (Or.inr (Or.inl (by rw [hs]; rfl)))]
      exact hpart
    | none =>
      cases hmt : G.meets i with
      | none =>
        rw [qLayer_part (Or.inr (Or.inr (m.meetsNone i hi hmt))), qLayer_part (Or.inr (Or.inr hmt))]
        exact hpart
      | some pc =>
        obtain ⟨p, cs⟩ := pc
        obtain ⟨cs', hm', hrel⟩ := m.meets i hi p cs hmt
        have hparts : ∀ j ∈ meetParts G i, m.D j := m.parts i hi
        have hmp : meetParts G i = p :: G.meetParams i := meetParts_of hmt
        have hp1 : m.D p := hparts _ (by rw [hmp]; exact List.mem_cons_self)
        have hpq : ∀ q ∈ G.meetParams i, m.D q := fun q hq => hparts _ (by rw [hmp]; exact List.mem_cons_of_mem _ hq)
        have hcs : ∀ c ∈ cs, ∀ S ∈ c.operands, ∀ j ∈ S, m.D j := by
          intro c hc S hS j hj
          refine m.reads i hi j ?_
          simp only [PositiveRules.reads, hs]
          exact List.mem_flatMap.mpr ⟨c, List.mem_append_right _ (by simp [meetClauses, hmt, hc]),
            List.mem_flatten.mpr ⟨S, hS, hj⟩⟩
        have hpH : H.params (m.φ i) = false := by rw [m.params_eq hi]; simpa using hp
        have hpG : G.params i = false := by simpa using hp
        have hsH : H.schemes (m.φ i) = none := m.schemesNone i hi hs
        have hrows := m.rows_eq hrel fun c hc c' hrc =>
          m.rowSem_eq (values_agree h m.related_empty) (values_agree h hr) (arguments_agree h hr) hrc (hcs c hc)
        funext n W v
        apply propext
        simp only [qLayerWithArgs, hpH, hpG, Bool.false_eq_true, ite_false, hsH, hs, hm', hmt]
        refine and_congr (and_congr ?_ ?_) ?_
        · rw [part_eq h hr hp1]
        · constructor
          · intro hall q hq
            rw [← part_eq h hr (hpq q hq)]
            exact hall _ ((m.meetParams i hi _).mpr (List.mem_map_of_mem hq))
          · intro hall q' hq'
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((m.meetParams i hi q').mp hq')
            rw [part_eq h hr (hpq q hq)]
            exact hall q hq
        · exact iff_of_eq (congrFun (congrFun (congrFun hrows n) W) v)

end Step

/-! ## The invariance -/

theorem approx_eq (k : Nat) :
    ∀ η θ, m.Related η θ → ∀ i, m.D i →
      Tower.approx (qLayerWithArgs H (mixedParameters H)) k (θ, m.φ i) =
        Tower.approx (qLayerWithArgs G (mixedParameters G)) k (η, i) := by
  induction k with
  | zero => intro _ _ _ _ _; rfl
  | succ k ih => intro η θ hr i hi; exact layer_eq ih hr hi

/-- **A label means in the image store what it means in its own** (proved),
at related assignments. -/
theorem denote_eq {η θ} (hr : m.Related η θ) {i : ι} (hi : m.D i) :
    qDenoteWithArgs H (mixedParameters H) (θ, m.φ i) = qDenoteWithArgs G (mixedParameters G) (η, i) := by
  funext n W v
  exact congrFun (congrFun (congrFun (m.approx_eq (n + 1) η θ hr i hi) n) W) v

theorem normalDenote_eq {i : ι} (hi : m.D i) : normalDenote H (m.φ i) = normalDenote G i :=
  m.denote_eq m.related_env hi

/-- **The invariance of meaning under a store map** (proved): a type of the
region means in the image store, renamed, what it means in its own, at every
budget and world. -/
theorem meaning_eq {A : List ι} (hA : ∀ j ∈ A, m.D j) : meaning H (A.map m.φ) = meaning G A :=
  m.setSem_map fun j hj => m.normalDenote_eq (hA j hj)

/-- The same for a union of the same members, in either order (proved). -/
theorem meaning_eq_of_mem {A : List ι} {B : List κ} (hA : ∀ j ∈ A, m.D j) (hB : ∀ x, x ∈ B ↔ x ∈ A.map m.φ) :
    meaning H B = meaning G A :=
  (setSem_ext hB).trans (m.meaning_eq hA)

end StoreMap

/-- The ordinary domains admit a renamed scheme's substitutions as the
scheme's (proved): `allowed` holds of two graphs with ordinary domains. -/
theorem ordinary_allowed (φ : ι → κ) (σ : List ι → List κ) (s : SchemeRow ι) (As : List MixedFamily) :
    (SchemeDomain.ordinary : SchemeDomain κ .mixed).allowed (mapSchemeWith φ σ s) As ↔
      (SchemeDomain.ordinary : SchemeDomain ι .mixed).allowed s As := Iff.rfl

end Verification.StoreMaps
