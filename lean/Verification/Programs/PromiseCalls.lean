import Verification.Programs.ExpressionEffects

/-! # Promises between slots

A call at a promise signature (`CallEffects.Effect.guards`, `.asserts`)
establishes a type for its promised actual: where its result is `true`, or
wherever it returns. A graph carries such a fact between nodes as an
implication between two immutable slots, `test = true ⟹ target : T`; a node's
expression establishes facts about its own result as yields. A branch on the
result consumes them, and a return under a promise goal states them of the
argument. Types are world-indexed, so each fact holds at the state's world and
is carried, like an environment's types, by transfer to later worlds. -/
namespace Verification.PromiseCalls
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapObservations BranchRefinement
open CallEffects (Effect Arrow Contract)
open PositiveCertificates (InstanceImageCheck)

/-- Where the slot `test` holds `true`, the slot `target` holds a value of `type`. -/
structure Implication (ι : Type) where
  test : Nat
  target : Nat
  type : Ty ι
  deriving DecidableEq, Repr

/-- What a node's result promises of a slot of the node's entry: its type,
where the result is `true` (`conditional`), or wherever the expression returns.
A tag test's yield carries the evidence that the test's slice is within it. -/
structure Yield (ι : Type) where
  conditional : Bool
  target : Nat
  type : Ty ι
  evidence : Option (PositiveCertificates.SubtypeChoices ι) := none

section
variable {ι : Type}

def ImpliesOk (G : NormalGraph ι) (xs : List (Implication ι)) (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  ∀ x ∈ xs, ρ x.test = .tru → meaning G x.type n W (ρ x.target)

/-- The yields of a result `u`, over the entry environment `ρ`. -/
def YieldsOk (G : NormalGraph ι) (ys : List (Yield ι)) (ρ : Env) : Fam := fun n W u =>
  ∀ y ∈ ys, (y.conditional = true → u = .tru) → meaning G y.type n W (ρ y.target)

theorem meaning_within [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} (h : within A B = true) {n W v}
    (hv : meaning G A n W v) : meaning G B n W v := by
  obtain ⟨a, ha, hv⟩ := hv
  exact ⟨a, within_mem h ha, hv⟩

theorem ImpliesOk.transfer {G : NormalGraph ι} {xs ρ n W} (h : ImpliesOk G xs ρ n W)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) : ImpliesOk G xs ρ j U :=
  fun x hx' ht => (meaning_adm G x.type).mono j _ U hx _
    ((meaning_adm G x.type).down_le n j hj W _ (h x hx' ht))

theorem YieldsOk.transfer {G : NormalGraph ι} {ys ρ n W u} (h : YieldsOk G ys ρ n W u)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) : YieldsOk G ys ρ j U u :=
  fun y hy hc => (meaning_adm G y.type).mono j _ U hx _
    ((meaning_adm G y.type).down_le n j hj W _ (h y hy hc))

theorem ImpliesOk.nil (G : NormalGraph ι) (ρ : Env) (n : Nat) (W : WorldT n) : ImpliesOk G [] ρ n W := by
  intro x hx; cases hx

/-- The facts a result's yields establish: every yield where the result
answered `true`, else the unconditional ones. -/
def yieldFacts (ys : List (Yield ι)) (answered : Bool) : List (Nat × Ty ι) :=
  ys.filterMap fun y => if !y.conditional || answered then some (y.target, y.type) else none

theorem yieldFacts_holds {G : NormalGraph ι} {ys : List (Yield ι)} {ρ n W u} {answered : Bool}
    (hy : YieldsOk G ys ρ n W u) (ha : answered = true → u = .tru) :
    ∀ f ∈ yieldFacts ys answered, meaning G f.2 n W (ρ f.1) := by
  intro f hf
  obtain ⟨y, hy', he⟩ := List.mem_filterMap.mp hf
  split at he
  · rename_i hc
    cases he
    refine hy y hy' fun hcond => ?_
    simp only [hcond, Bool.not_true, Bool.false_or] at hc
    exact ha hc
  · cases he

/-- A context with the slots of `facts`, past `shift` slots, at their types. -/
def refineBy (Γ : List (Ty ι)) (facts : List (Nat × Ty ι)) (shift : Nat) : List (Ty ι) :=
  facts.foldl (fun Δ f => Δ.set (f.1 + shift) f.2) Γ

theorem envOk_set {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W i T}
    (h : EnvOk G Γ ρ n W) (hT : meaning G T n W (ρ i)) : EnvOk G (Γ.set i T) ρ n W := by
  refine ⟨h.1, fun k A hk => ?_⟩
  rw [List.getElem?_set] at hk
  split at hk
  · rename_i heq
    subst heq
    split at hk
    · cases hk; exact hT
    · cases hk
  · exact h.2 k A hk

theorem envOk_refineBy {G : NormalGraph ι} {ρ n W shift} :
    ∀ {Γ : List (Ty ι)} {facts : List (Nat × Ty ι)}, EnvOk G Γ ρ n W →
      (∀ f ∈ facts, meaning G f.2 n W (ρ (f.1 + shift))) → EnvOk G (refineBy Γ facts shift) ρ n W
  | _, [], h, _ => h
  | _, f :: fs, h, hf => by
    simp only [PromiseCalls.refineBy, List.foldl_cons]
    exact envOk_refineBy (envOk_set h (hf f (by simp))) (fun g hg => hf g (by simp [hg]))

/-- The implications a state establishes on an edge, in its own slots: the
entry's, and, where the result is pushed into slot 0, the result's
conditional yields as implications on it. -/
def edgeImplications (xs : List (Implication ι)) (ys : List (Yield ι)) (pushed : Bool) : List (Implication ι) :=
  if pushed then
    xs.map (fun x => ⟨x.test + 1, x.target + 1, x.type⟩) ++
      ys.filterMap (fun y => if y.conditional then some ⟨0, y.target + 1, y.type⟩ else none)
  else xs

theorem edgeImplications_holds {G : NormalGraph ι} {xs : List (Implication ι)} {ys ρ n W u}
    (hx : ImpliesOk G xs ρ n W) (hy : YieldsOk G ys ρ n W u) :
    ImpliesOk G (edgeImplications xs ys true) (push u ρ) n W := by
  intro x hm ht
  simp only [edgeImplications, ↓reduceIte, List.mem_append, List.mem_map, List.mem_filterMap] at hm
  rcases hm with ⟨x', hx', rfl⟩ | ⟨y, hy', he⟩
  · exact hx x' hx' ht
  · split at he
    · rename_i hc
      cases he
      exact hy y hy' fun _ => ht
    · cases he

variable [DecidableEq ι]

/-- A target implication follows on an edge mapping `m`: one the source
states, at the slots the mapping reads, at a type within the target's; the
source's own type of the target slot, within it; or none at all, where the
source's tested slot never holds `true`. -/
def impliesFollows (G : NormalGraph ι) (Γ : List (Ty ι)) (xs : List (Implication ι))
    (m : PointClaims.Mapping) (x : Implication ι) : Bool :=
  xs.any (fun y => y.test == PointClaims.slot m x.test && y.target == PointClaims.slot m x.target &&
    within y.type x.type) ||
  (Γ[PointClaims.slot m x.target]?).any (fun A => within A x.type) ||
  (Γ[PointClaims.slot m x.test]?).any (fun A => impossible G A (.boolean true))

def impliesCheck (G : NormalGraph ι) (Γ : List (Ty ι)) (xs : List (Implication ι))
    (m : PointClaims.Mapping) (targets : List (Implication ι)) : Bool :=
  targets.all (impliesFollows G Γ xs m)

theorem impliesCheck_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {xs m targets ρ n W}
    (hc : impliesCheck G Γ xs m targets = true) (he : EnvOk G Γ ρ n W) (hx : ImpliesOk G xs ρ n W) :
    ImpliesOk G targets (PointClaims.mapEnv m ρ) n W := by
  intro x hm ht
  have hf := List.all_eq_true.mp hc x hm
  change ρ (PointClaims.slot m x.test) = .tru at ht
  change meaning G x.type n W (ρ (PointClaims.slot m x.target))
  simp only [impliesFollows, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Option.any_eq_true] at hf
  rcases hf with (⟨y, hy, ⟨htest, htarget⟩, hw⟩ | ⟨A, hA, hw⟩) | ⟨A, hA, himp⟩
  · rw [← htarget]
    exact meaning_within hw (hx y hy (htest ▸ ht))
  · exact meaning_within hw (he.2 _ A hA)
  · exact (impossible_sound himp (he.2 _ A hA) (show Observation.holds (.boolean true) _ from ht)).elim

/-- The slots of a state's environment holding the promised argument. -/
def ArgumentsOk (sources : List Nat) (ρ : Env) (v0 : Tm) : Prop := ∀ p ∈ sources, ρ p = v0

/-- A target's argument slots are ones the mapping reads from source slots
holding it. -/
def argFollows (sources : List Nat) (m : PointClaims.Mapping) (targets : List Nat) : Bool :=
  targets.all fun p => sources.contains (PointClaims.slot m p)

theorem argFollows_sound {sources m targets ρ v0} (hc : argFollows sources m targets = true)
    (hs : ArgumentsOk sources ρ v0) : ArgumentsOk targets (PointClaims.mapEnv m ρ) v0 := by
  intro p hp
  exact hs _ (List.contains_iff_mem.mp (List.all_eq_true.mp hc p hp))

/-! ### Slots holding one value

An alias link of the heap knowledge relates two slots holding the same value
(`HeapLinks.Holds`): an implication about one is about the other, and the
promised argument in one is in the other. -/

/-- The slots alias links relate, both ways. -/
def aliasPairs (links : HeapLinks.Links) : List (Nat × Nat) :=
  links.flatMap fun g => if g.alias then [(g.cell, g.value), (g.value, g.cell)] else []

theorem aliasPairs_holds {links : HeapLinks.Links} {ρ h} (hl : HeapLinks.Holds links ρ h) :
    ∀ q ∈ aliasPairs links, ρ q.1 = ρ q.2 := by
  intro q hq
  obtain ⟨g, hg, hq⟩ := List.mem_flatMap.mp hq
  have hh := hl g hg
  split at hq
  · rename_i hc
    simp only [hc, ↓reduceIte] at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hh
    · exact hh.symm
  · cases hq

/-- The slots holding a slot's value by alias links, the slot included: the
set `known` grown by every partner of its members, `fuel` times. -/
def aliasesOf (pairs : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, known => known
  | fuel + 1, known =>
    let grown := (known ++ pairs.filterMap fun q => if known.contains q.1 then some q.2 else none).eraseDups
    if grown.length == known.length then known else aliasesOf pairs fuel grown

theorem aliasesOf_holds {pairs : List (Nat × Nat)} {ρ : Env} {v : Tm} (hp : ∀ q ∈ pairs, ρ q.1 = ρ q.2) :
    ∀ fuel known, (∀ j ∈ known, ρ j = v) → ∀ j ∈ aliasesOf pairs fuel known, ρ j = v := by
  intro fuel
  induction fuel with
  | zero => intro known hk j hj; exact hk j hj
  | succ fuel ih =>
    intro known hk j hj
    simp only [aliasesOf] at hj
    split at hj
    · exact hk j hj
    · refine ih _ (fun k hk' => ?_) j hj
      rcases List.mem_append.mp (List.mem_eraseDups.mp hk') with hk' | hk'
      · exact hk k hk'
      · obtain ⟨q, hq, he⟩ := List.mem_filterMap.mp hk'
        split at he
        · rename_i hc
          cases he
          rw [← hp q hq]
          exact hk q.1 (List.contains_iff_mem.mp hc)
        · cases he

/-- Implications and argument slots at every slot the links say holds the
same value. -/
def aliasImplications (links : HeapLinks.Links) (xs : List (Implication ι)) : List (Implication ι) :=
  let pairs := aliasPairs links
  (xs.flatMap fun x => (aliasesOf pairs pairs.length [x.test]).flatMap fun t =>
    (aliasesOf pairs pairs.length [x.target]).map fun a => ⟨t, a, x.type⟩).eraseDups

def aliasSources (links : HeapLinks.Links) (sources : List Nat) : List Nat :=
  let pairs := aliasPairs links
  aliasesOf pairs pairs.length sources.eraseDups

theorem aliasImplications_holds {links : HeapLinks.Links} {xs : List (Implication ι)} {ρ h n W G}
    (hl : HeapLinks.Holds links ρ h) (hx : ImpliesOk G xs ρ n W) :
    ImpliesOk G (aliasImplications links xs) ρ n W := by
  intro y hy ht
  simp only [aliasImplications] at hy
  obtain ⟨x, hx', hy⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hy)
  obtain ⟨t, htm, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hy
  have hpairs := aliasPairs_holds hl
  have ht' := aliasesOf_holds (v := ρ x.test) hpairs _ _ (by simp) t htm
  have ha' := aliasesOf_holds (v := ρ x.target) hpairs _ _ (by simp) a ham
  change ρ t = .tru at ht
  change meaning G x.type n W (ρ a)
  rw [ha']
  exact hx x hx' (by rw [← ht', ht])

theorem aliasSources_holds {links : HeapLinks.Links} {sources : List Nat} {ρ h v0}
    (hl : HeapLinks.Holds links ρ h) (hs : ArgumentsOk sources ρ v0) :
    ArgumentsOk (aliasSources links sources) ρ v0 := by
  intro p hp
  simp only [aliasSources] at hp
  exact aliasesOf_holds (aliasPairs_holds hl) _ _ (fun j hj => hs j (List.mem_eraseDups.mp hj)) p hp

/-- Facts about slots past `shift`, at every slot the links say holds the
same value: what refining a context by them may state. -/
def aliasFacts (links : HeapLinks.Links) (facts : List (Nat × Ty ι)) (shift : Nat) : List (Nat × Ty ι) :=
  let pairs := aliasPairs links
  facts.flatMap fun f => (aliasesOf pairs pairs.length [f.1 + shift]).map (·, f.2)

omit [DecidableEq ι] in
theorem aliasFacts_holds {G : NormalGraph ι} {links : HeapLinks.Links} {facts : List (Nat × Ty ι)}
    {shift : Nat} {ρ h n W} (hl : HeapLinks.Holds links ρ h)
    (hf : ∀ f ∈ facts, meaning G f.2 n W (ρ (f.1 + shift))) :
    ∀ f ∈ aliasFacts links facts shift, meaning G f.2 n W (ρ (f.1 + 0)) := by
  intro f hm
  obtain ⟨g, hg, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  rw [Nat.add_zero, aliasesOf_holds (v := ρ (g.1 + shift)) (aliasPairs_holds hl) _ _ (by simp) k hk]
  exact hf g hg

/-! ### Yields of a slot read and of a tag test -/

/-- A tag test's yield about the object the tested value was read from: a
current read link says field `f` of the object in `y.target` holds the tested
slot's value, and the object's arms whose field answers the test so
(`fieldSlice`) are within the yield's type, by the yield's evidence. -/
@[nospecialize] def fieldYield (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (y : Yield ι) (i : Nat) (tag : Tag) (q : Bool) : Bool :=
  (Γ[i]?).isSome &&
  links.any fun g => !g.alias && !g.optional && g.value == i && g.cell == y.target &&
    match Γ[g.cell]?, y.evidence with
    | some A, some p => PositiveCertificates.checkUsing G images (fieldSlice G A g.field tag q) y.type p
    | _, _ => false

theorem fieldYield_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ links y i tag q}
    (hf : fieldYield G images Γ links y i tag q = true) {ρ m W h}
    (he : EnvOk G Γ ρ (m+1) W) (hh : HeapOk (m+1) W h) (hl : HeapLinks.Holds links ρ h)
    (htag : tagHoldsIn h tag (ρ i) = q) : meaning G y.type (m+1) W (ρ y.target) := by
  unfold fieldYield at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨g, hg, hc⟩ := List.any_eq_true.mp hf.2
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨ha, ho⟩, hv⟩, hcell⟩, hp⟩ := hc
  split at hp
  · rename_i A p hA _
    have hlink := hl g hg
    simp only [ha, ho, Bool.false_eq_true, ite_false] at hlink
    obtain ⟨flds, c, oid, l, hobj, hlk, hu⟩ := hlink
    have hs := fieldSlice_sound (he.2 g.cell A hA) hh hobj hlk hu
      (tagHolds_of_heap (hv ▸ htag))
    rw [← hcell]
    exact PositiveCertificates.acceptedUsing hp _ _ _ hs
  · cases hp

/-- One yield of a node's expression, without a call: a slot read, whose value
is the slot's, yields what an implication on the slot states; a tag test of a
slot, read as a Boolean, yields where it answers `true` what its observation
leaves of the slot, or of the object the slot's value was read from
(`fieldYield`). -/
@[nospecialize] def yieldFollows (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (xs : List (Implication ι)) (links : HeapLinks.Links) (t : Tm) (y : Yield ι) : Bool :=
  match t with
  | .var i => y.conditional && (Γ[i]?).isSome &&
      xs.any fun x => x.test == i && x.target == y.target && within x.type y.type
  | .ite (.test tag (.var i)) .tru .fls => y.conditional &&
      (y.target == i && observed i tag true || fieldYield G images Γ links y i tag true)
  | .ite (.test tag (.var i)) .fls .tru => y.conditional &&
      (y.target == i && observed i tag false || fieldYield G images Γ links y i tag false)
  | _ => false
where
  observed (i : Nat) (tag : Tag) (q : Bool) : Bool :=
    match Γ[i]?, y.evidence with
    | some A, some p => checkObservedSubUsing G images A y.type (.tag tag q) p
    | _, _ => false

/-- A safe run, strengthened by a property of every value it returns at a
world reached from its own: the property holds of the values the run's own
derivation reaches. -/
theorem conj_reached {T : Fam} {Q : Post} {P : (k : Nat) → WorldT k → Tm → Prop} :
    ∀ {n W h t}, SafePost Ξ T Q n W h t →
      (∀ k (hk : k ≤ n) (U : WorldT k), WExt (trunc k hk W) U → ∀ m h' u,
        Steps m h t h' u → isVal u = true → P k U u) →
      SafePost Ξ (fun k U u => T k U u ∧ P k U u) Q n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs hp
    rcases hs with (⟨hv, ht, hq⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ⟨ht, hp (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) 0 h t
        .refl hv⟩, hq⟩)
    · exact .inl (.inr hth)
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ih hs fun k hk V hV m h'' u run hval => ?_⟩
      apply hp k (by omega) V _ (m+1) h'' u (.next step run) hval
      have he := WExt_trunc hk hx
      rw [trunc_trunc] at he
      exact WExt_trans he hV

/-- A tag test read as a Boolean returns at once, in its heap. -/
theorem test_ite_run {h tag v h' u m} {yes no : Tm} (hv : isVal v = true)
    (hyes : isVal yes = true) (hno : isVal no = true)
    (run : Steps m h (.ite (.test tag v) yes no) h' u) (hu : isVal u = true) :
    u = (if tagHoldsIn h tag v then yes else no) := by
  cases run with
  | refl => simp [isVal] at hu
  | next st run =>
    cases st with
    | iteC st =>
      cases st with
      | testC st => exact absurd st (value_no_step hv)
      | testV _ =>
        cases run with
        | refl => split at hu <;> simp [isVal] at hu
        | next st run =>
          split at st
          · cases st with
            | iteC st => exact absurd st (value_no_step rfl)
            | iteT => cases run with
              | refl => simp_all
              | next st _ => exact absurd st (value_no_step hyes)
          · cases st with
            | iteC st => exact absurd st (value_no_step rfl)
            | iteF => cases run with
              | refl => simp_all
              | next st _ => exact absurd st (value_no_step hno)

theorem steps_value {h v h' u m} (hv : isVal v = true) (run : Steps m h v h' u) : u = v := by
  cases run with
  | refl => rfl
  | next st _ => exact absurd st (value_no_step hv)

theorem yieldFollows_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ xs links t} {ys : List (Yield ι)}
    (hc : ys.all (yieldFollows G images Γ xs links t) = true) {ρ n W h} {T : Fam} {Q : Post}
    (he : EnvOk G Γ ρ n W) (hx : ImpliesOk G xs ρ n W) (hh : HeapOk n W h)
    (hl : HeapLinks.Holds links ρ h)
    (hs : SafePost (excOf G) T Q n W h (instantiate 0 ρ t)) :
    SafePost (excOf G) (fun k U u => T k U u ∧ YieldsOk G ys ρ k U u) Q n W h (instantiate 0 ρ t) := by
  cases n with
  | zero => trivial
  | succ m =>
  apply conj_reached hs
  intro k hk U hU r h' u run hu y hy hcond
  have he' := he.transfer k hk U hU
  have hx' := hx.transfer k hk U hU
  have hf := List.all_eq_true.mp hc y hy
  -- The object's slice, at the run's own level, carried to the reached world.
  have later : ∀ {B : Ty ι} {v}, meaning G B (m+1) W v → meaning G B k U v := fun hv =>
    (meaning_adm G _).mono k _ U hU _ ((meaning_adm G _).down_le (m+1) k hk W _ hv)
  unfold yieldFollows at hf
  split at hf
  · rename_i i
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hf
    obtain ⟨⟨hcy, A, hA⟩, x, hxm, ⟨htest, htarget⟩, hw⟩ := hf
    have hval : isVal (ρ i) = true := (meaning_value (he.2 i A hA)).1
    have hui : u = ρ i := steps_value hval (by simpa [instantiate] using run)
    have htru := hcond hcy
    rw [← htarget]
    exact meaning_within hw (hx' x hxm (by rw [htest, ← hui, htru]))
  · rename_i tag i
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
    obtain ⟨hcy, ⟨rfl, hob⟩ | hfy⟩ := hf
    · unfold yieldFollows.observed at hob
      split at hob
      · rename_i A p hA _
        have hval : isVal (ρ y.target) = true := (meaning_value (he.2 _ A hA)).1
        have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
        have htag : tagHoldsIn h tag (ρ y.target) = true := by
          cases htg : tagHoldsIn h tag (ρ y.target) <;> simp_all
        exact checkObservedSub_sound hob k U _ (he'.2 _ A hA) (tagHolds_of_heap htag)
      · cases hob
    · have hval : isVal (ρ i) = true := by
        unfold fieldYield at hfy
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfy
        obtain ⟨⟨A, hA⟩, -⟩ := hfy
        exact (meaning_value (he.2 i A hA)).1
      have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
      have htag : tagHoldsIn h tag (ρ i) = true := by
        cases htg : tagHoldsIn h tag (ρ i) <;> simp_all
      exact later (fieldYield_sound hfy he hh hl htag)
  · rename_i tag i
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
    obtain ⟨hcy, ⟨rfl, hob⟩ | hfy⟩ := hf
    · unfold yieldFollows.observed at hob
      split at hob
      · rename_i A p hA _
        have hval : isVal (ρ y.target) = true := (meaning_value (he.2 _ A hA)).1
        have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
        have htag : tagHoldsIn h tag (ρ y.target) = false := by
          cases htg : tagHoldsIn h tag (ρ y.target) <;> simp_all
        exact checkObservedSub_sound hob k U _ (he'.2 _ A hA) (tagHolds_of_heap htag)
      · cases hob
    · have hval : isVal (ρ i) = true := by
        unfold fieldYield at hfy
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfy
        obtain ⟨⟨A, hA⟩, -⟩ := hfy
        exact (meaning_value (he.2 i A hA)).1
      have hu' := test_ite_run hval rfl rfl (by simpa [instantiate] using run) hu
      have htag : tagHoldsIn h tag (ρ i) = false := by
        cases htg : tagHoldsIn h tag (ρ i) <;> simp_all
      exact later (fieldYield_sound hfy he hh hl htag)
  · cases hf

/-! ### A call at a promise signature -/

/-- Whether a type holds `undefined`: by a clause of `undefined`, or of every
value (`top`, `source`). -/
def admitsUndef (G : NormalGraph ι) (A : Ty ι) : Bool :=
  (expand G A).any fun c => match c with | .undef | .top | .source => true | _ => false

omit [DecidableEq ι] in
/-- What the built-ins ask of a clause holds of `undefined`, which is no object. -/
theorem builtinInvariant_undef (G : NormalGraph ι) (X : List ι → Fam) (c : PositiveNormalization.Clause (List ι)) (n W) :
    builtinInvariant G X c n W .undef := by
  unfold builtinInvariant
  cases G.builtins <;> (cases c.carriesInvariant <;> simp only [Bool.false_eq_true, ↓reduceIte])
  · intro flds oid h; cases h
  · intro flds oid h; cases h

omit [DecidableEq ι] in
theorem admitsUndef_sound {G : NormalGraph ι} {A : Ty ι} (h : admitsUndef G A = true) (n W) :
    meaning G A n W .undef := by
  obtain ⟨c, hc, ht⟩ := List.any_eq_true.mp h
  refine expand_sem_mpr ⟨c, expand_sub hc, ?_, builtinInvariant_undef G _ c n W⟩
  cases c <;> simp_all [PositiveNormalization.semWithArgs, PositiveNormalization.topT,
    PositiveNormalization.sourceT, undefT, isVal, isSourceVal, Scoped]

/-- The promise a call node's evidence states of its actual: the evidence is a
call at a signature of its callee (`app`), every operand evaluated, and the
callee's type holds, beside that signature, a promise signature with the same
receiver and parameters, whose promised actual is the slot `a`. The promise's
effect, the slot and the promise's type. -/
@[nospecialize] def promiseOf (G : NormalGraph ι) : Evidence ι → Option (Effect × Nat × Ty ι)
  | .node j (.app _) ps =>
    if ps.all (fun p => ExpressionEffects.valueTerm (claim p).term &&
        checkScope (claim p).context.length (claim p).term) then
      match j.term, ps.map claim with
      | .invoke _ _ args, jf :: jr :: jas =>
        match expand G jf.type with
        | [.arrs L _] => L.findSome? fun s =>
          if s.receiver = jr.type ∧ s.arguments = jas.map Sequent.type then
            match s.effect.promise with
            | some (.guards p) | some (.asserts p) => match args[p]? with
              | some (.var a) => some (s.effect, a, s.result)
              | _ => none
            | _ => none
          else none
        | _ => none
      | _, _ => none
    else none
  | _ => none

/-- A promise node's yields and result: each yield is the promise's slot, at a
type the promise's is within, conditional for a type guard's; the result's type
holds `true` and `false` for a type guard, `undefined` for an assertion
function. -/
def promiseYields (G : NormalGraph ι) (A : Ty ι) (effect : Effect) (a : Nat) (T : Ty ι)
    (ys : List (Yield ι)) : Bool :=
  (match effect.promise with
    | some (.guards _) => booleanMember G A true && booleanMember G A false
    | some (.asserts _) => admitsUndef G A
    | none => false) &&
  ys.all fun y => y.target == a && within T y.type &&
    (match effect.promise with | some (.guards _) => y.conditional | _ => true)

theorem ordinaryOutput_holds {k : HeapKnowledge.Knowledge} {ρ h} (hk : HeapKnowledge.Holds k ρ h)
    (v : Tm) {h' : Heap} (hl : h.length ≤ h'.length) :
    HeapKnowledge.Holds (HeapExpressionRules.ordinaryOutput k) (push v ρ) h' :=
  ⟨HeapFacts.holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,
    HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.1,
    (HeapKnowledge.shift_holds (v := v) hk).2.2.2.grow hl⟩

/-- **A call at a promise signature** returns where the promise holds: its
callee meets the promise signature it holds beside the one the call is
checked at, at the same receiver and actuals, so the call's own run is one the
promise is about (`CallEffects.call_safe`). The result meets the claim's type,
and the facts kept are those no call changes. -/
theorem promiseCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {e : Evidence ι}
    {codes : CodeEntry ι → Bool} {effect a T} {ys : List (Yield ι)}
    (hp : promiseOf G e = some (effect, a, T))
    (ht : checkTreeUsing G images e codes = true) (hcodes : CodesSound G codes)
    (hy : promiseYields G (claim e).type effect a T ys = true)
    {k ρ n W h} (he : EnvOk G (claim e).context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (fun m U u => meaning G (claim e).type m U u ∧ YieldsOk G ys ρ m U u)
      (fun h' v => HeapKnowledge.Holds (HeapExpressionRules.ordinaryOutput k) (push v ρ) h') n W h
      (instantiate 0 ρ (claim e).term) := by
  rcases e with ⟨⟨Γ, t, A⟩, r, ps⟩
  simp only [claim] at he hy ⊢
  cases r <;> try (simp only [promiseOf] at hp; contradiction)
  rename_i r0
  simp only [promiseOf] at hp
  split at hp
  case isFalse => contradiction
  rename_i hvals
  simp only [List.all_eq_true, Bool.and_eq_true] at hvals
  simp only [checkTreeUsing_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
    intro p hm
    obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hm
    exact checkTreeUsing_sound e (ht.2 ⟨e, heq⟩ (by simp)) hcodes
  have hvals' : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
      checkScope p.context.length p.term = true := by
    intro p hm
    obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hm
    exact hvals e heq
  have hlocal := ht.1
  generalize ps.map claim = qs at hp hlocal typed hvals'
  split at hp
  case h_2 => contradiction
  rename_i f rv args jf jr jas
  obtain ⟨hΓf, htf, hΓr, htr, hargs, hundef, hcontexts, hL⟩ := hlocal
  split at hp
  case h_2 => contradiction
  rename_i L S hF
  obtain ⟨s, hs, hsome⟩ := List.exists_of_findSome?_eq_some hp
  split at hsome
  case isFalse => contradiction
  rename_i hsig
  obtain ⟨hrecv, hargsig⟩ := hsig
  have context : ∀ p ∈ jf::jr::jas, p.context = Γ := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact hΓf
    · exact hΓr
    · exact hcontexts p hp
  have typed' : ∀ p ∈ jf::jr::jas, HasTyUsing G images Γ p.term p.type := by
    intro p hp
    simpa only [context p hp] using typed p hp
  have values : ∀ p ∈ jf::jr::jas, isVal (instantiate 0 ρ p.term) = true := by
    intro p hp
    exact ExpressionEffects.valueTerm_instantiate (hvals' p hp).1 (hvals' p hp).2
      (by simpa [context p hp] using he)
  cases n with
  | zero => trivial
  | succ n =>
    have member : ∀ p ∈ jf::jr::jas, meaning G p.type (n+1) W (instantiate 0 ρ p.term) := by
      intro p hp
      exact safe_value_mem (values p hp) ((typed' p hp).sound _ _ h ρ he hw hh)
    have hf := ((represents_raw hF (n+1) W _) (member jf (by simp))).1
    have hpw := hf.2 _ (List.mem_map_of_mem hs)
    simp only [CallEffects.Arrow.map, CallEffects.Contract.map] at hpw
    have hArgs := ExpressionEffects.argument_values (ps := jas)
      (fun p hp => typed' p (by simp [hp])) (fun p hp => values p (by simp [hp])) he hw hh
    have actual : (jas.take args.length).map (fun p => instantiate 0 ρ p.term)
        = args.map (instantiate 0 ρ) := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (instantiate 0 ρ)) hargs
    have ha : ArgsShort (jas.map (fun p => meaning G p.type)) (n+1) W
        (args.map (instantiate 0 ρ)) := by
      rw [← actual]
      apply ArgsShort_of_pad (pad := (jas.drop args.length).map (fun p => instantiate 0 ρ p.term))
      · intro v hv'
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
        simp [hundef p hp, instantiate]
      · simpa [← List.map_append, List.take_append_drop] using hArgs
    have hvs : CallArguments.Values (args.map (instantiate 0 ρ)) := by
      rw [← actual]
      intro v hv'
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv'
      exact values p (by simp [List.mem_of_mem_take hp])
    have hr := member jr (by simp)
    have hrval := values jr (by simp)
    rw [hargsig, hrecv] at hpw
    have hs' := CallEffects.call_safe
      (P := ArgsShort (jas.map (fun p => meaning G p.type)))
      (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer (fun T hm => by
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm; exact meaning_adm G p.type) ha j hj U hx))
      (meaning_adm G jr.type) (by simpa [List.map_map, Function.comp_def] using hpw) hr hrval hvs ha hw hh
    have hterm : instantiate 0 ρ (.invoke f rv args) = .invoke (instantiate 0 ρ jf.term)
        (instantiate 0 ρ jr.term) (args.map (instantiate 0 ρ)) := by
      simp [instantiate, instantiateArgs_eq_map, htf, htr]
    rw [hterm]
    refine consequence (fun m U u hu => ?_) (fun h' v hp => ordinaryOutput_holds hk v hp.1) hs'
    split at hsome
    · rename_i p heff
      split at hsome
      · rename_i a' harg
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨he', rfl, hT⟩ := hsome
        subst he' hT
        have hpromised : s.effect.promised (args.map (instantiate 0 ρ)) = ρ a' := by
          simp [CallEffects.Effect.promised, heff, CallEffects.TypePromise.param,
            List.getD_eq_getElem?_getD, harg, instantiate]
        rw [hpromised] at hu
        simp only [CallEffects.Effect.result, heff, CallEffects.TypePromise.result] at hu
        simp only [promiseYields, heff, Bool.and_eq_true, List.all_eq_true] at hy
        obtain ⟨⟨hbt, hbf⟩, hall⟩ := hy
        refine ⟨?_, fun y hym hcond => ?_⟩
        · rcases hu with ⟨rfl, _⟩ | rfl
          · exact booleanMember_sound (q := true) hbt m U
          · exact booleanMember_sound (q := false) hbf m U
        · obtain ⟨⟨htarget, hw⟩, hc⟩ := hall y hym
          rw [beq_iff_eq.mp htarget]
          rcases hu with ⟨_, hT⟩ | rfl
          · exact meaning_within hw hT
          · exact absurd (hcond hc) (by simp)
      · contradiction
    · rename_i p heff
      split at hsome
      · rename_i a' harg
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨he', rfl, hT⟩ := hsome
        subst he' hT
        have hpromised : s.effect.promised (args.map (instantiate 0 ρ)) = ρ a' := by
          simp [CallEffects.Effect.promised, heff, CallEffects.TypePromise.param,
            List.getD_eq_getElem?_getD, harg, instantiate]
        rw [hpromised] at hu
        simp only [CallEffects.Effect.result, heff, CallEffects.TypePromise.result] at hu
        simp only [promiseYields, heff, Bool.and_eq_true, List.all_eq_true] at hy
        obtain ⟨hundefA, hall⟩ := hy
        obtain ⟨rfl, hT⟩ := hu
        refine ⟨admitsUndef_sound hundefA m U, fun y hym _ => ?_⟩
        obtain ⟨⟨htarget, hw⟩, _⟩ := hall y hym
        rw [beq_iff_eq.mp htarget]
        exact meaning_within hw hT
      · contradiction
    · contradiction

/-- Whether every value of a type is `undefined`. -/
def onlyUndef (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with | .undef => true | _ => false

omit [DecidableEq ι] in
theorem onlyUndef_sound {G : NormalGraph ι} {A : Ty ι} {n W v}
    (h : onlyUndef G A = true) (hv : meaning G A n W v) : v = .undef := by
  simp only [onlyUndef, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c, hc, hv, -⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [PositiveNormalization.semWithArgs, undefT]

end
end Verification.PromiseCalls
