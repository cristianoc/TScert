import Verification.Programs.ExpressionEffects
import Verification.Programs.IndexWrites

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
where the result is `true` (`conditional`), where it is `false` (`onFalse`),
or wherever the expression returns. A tag test's yield carries the evidence
that the test's slice is within it. -/
structure Yield (ι : Type) where
  conditional : Bool
  target : Nat
  type : Ty ι
  evidence : Option (PositiveCertificates.SubtypeChoices ι) := none
  onFalse : Bool := false

section
variable {ι : Type}

def ImpliesOk (G : NormalGraph ι) (xs : List (Implication ι)) (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  ∀ x ∈ xs, ρ x.test = .tru → meaning G x.type n W (ρ x.target)

/-- The yields of a result `u`, over the entry environment `ρ`. -/
def YieldsOk (G : NormalGraph ι) (ys : List (Yield ι)) (ρ : Env) : Fam := fun n W u =>
  ∀ y ∈ ys, (y.conditional = true → u = .tru) → (y.onFalse = true → u = .fls) →
    meaning G y.type n W (ρ y.target)

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
  fun y hy hc hf => (meaning_adm G y.type).mono j _ U hx _
    ((meaning_adm G y.type).down_le n j hj W _ (h y hy hc hf))

theorem ImpliesOk.nil (G : NormalGraph ι) (ρ : Env) (n : Nat) (W : WorldT n) : ImpliesOk G [] ρ n W := by
  intro x hx; cases hx

/-- The facts a result's yields establish: every yield where the result
answered `true`, else the unconditional ones; where it answered `false`
(`falsified`), also those stated of that answer. -/
def yieldFacts (ys : List (Yield ι)) (answered : Bool) (falsified : Bool := false) : List (Nat × Ty ι) :=
  ys.filterMap fun y => if (!y.onFalse || falsified) && (!y.conditional || answered) then some (y.target, y.type) else none

theorem yieldFacts_holds {G : NormalGraph ι} {ys : List (Yield ι)} {ρ n W u} {answered falsified : Bool}
    (hy : YieldsOk G ys ρ n W u) (ha : answered = true → u = .tru) (hfl : falsified = true → u = .fls) :
    ∀ f ∈ yieldFacts ys answered falsified, meaning G f.2 n W (ρ f.1) := by
  intro f hf
  obtain ⟨y, hy', he⟩ := List.mem_filterMap.mp hf
  split at he
  · rename_i hc
    cases he
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    refine hy y hy' (fun hcond => ?_) (fun hneg => ?_)
    · rcases hc.2 with h | h
      · rw [hcond] at h; cases h
      · exact ha h
    · rcases hc.1 with h | h
      · rw [hneg] at h; cases h
      · exact hfl h
  · cases he

/-- A context with the slots of `facts`, past `shift` slots, refined: each
at the fact's type filtered by its own (`BranchRefinement.factFilter`). -/
@[nospecialize] def refineBy [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (facts : List (Nat × Ty ι)) (shift : Nat) :
    List (Ty ι) :=
  facts.foldl (fun Δ f => match Δ[f.1 + shift]? with
    | some A => Δ.set (f.1 + shift) (BranchRefinement.factFilter G A f.2)
    | none => Δ) Γ

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

/-- A context refined by facts its values meet, given a heap meeting the
world: the meet's exclusions read the heap's field contents. -/
theorem envOk_refineBy [DecidableEq ι] {G : NormalGraph ι} {ρ n W shift} {h : Heap} (hh : HeapOk (n+1) W h) :
    ∀ {Γ : List (Ty ι)} {facts : List (Nat × Ty ι)}, EnvOk G Γ ρ (n+1) W →
      (∀ f ∈ facts, meaning G f.2 (n+1) W (ρ (f.1 + shift))) → EnvOk G (refineBy G Γ facts shift) ρ (n+1) W
  | _, [], he, _ => he
  | Γ, f :: fs, he, hf => by
    simp only [PromiseCalls.refineBy, List.foldl_cons]
    have step : EnvOk G (match Γ[f.1 + shift]? with
        | some A => Γ.set (f.1 + shift) (BranchRefinement.factFilter G A f.2)
        | none => Γ) ρ (n+1) W := by
      split
      · rename_i A hA
        exact envOk_set he (BranchRefinement.factFilter_sound (he.2 _ A hA) (hf f (by simp)) hh)
      · exact he
    exact envOk_refineBy hh step (fun g hg => hf g (by simp [hg]))

/-- The implications a state establishes on an edge, in its own slots: the
entry's, and, where the result is pushed into slot 0, the result's
conditional yields as implications on it. -/
def edgeImplications (xs : List (Implication ι)) (ys : List (Yield ι)) (pushed : Bool) : List (Implication ι) :=
  if pushed then
    xs.map (fun x => ⟨x.test + 1, x.target + 1, x.type⟩) ++
      ys.filterMap (fun y => if y.conditional && !y.onFalse then some ⟨0, y.target + 1, y.type⟩ else none)
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
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      exact hy y hy' (fun _ => ht) (fun hf => by rw [hc.2] at hf; cases hf)
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

/-! ### Yields of a membership test -/

/-- The test of a value against a finite list of tags, in order: `true`
where one of them holds of it, else `false` (`member_run`). -/
def memberOn (tags : List Tag) (x : Tm) : Tm :=
  tags.foldr (fun t rest => .ite (.test t x) .tru rest) .fls

/-- The tags and the slot of a membership test of a slot's value, of one tag
or more. -/
def memberParts : Tm → Option (List Tag × Nat)
  | .ite (.test t (.var i)) .tru rest =>
    match rest with
    | .fls => some ([t], i)
    | _ => match memberParts rest with
      | some (ts, j) => if i == j then some (t :: ts, i) else none
      | none => none
  | _ => none

/-- Whether a term is the membership test of the slot `i`'s value against
the tags `ts`, in order (`memberOn`). -/
def isMemberOn : List Tag → Nat → Tm → Bool
  | [], _, .fls => true
  | t :: ts, i, .ite (.test t' (.var j)) .tru rest => t == t' && i == j && isMemberOn ts i rest
  | _, _, _ => false

theorem isMemberOn_sound : ∀ {ts : List Tag} {i : Nat} {t : Tm}, isMemberOn ts i t = true →
    t = memberOn ts (.var i) := by
  intro ts
  induction ts with
  | nil =>
    intro i t h
    unfold isMemberOn at h
    split at h <;> first | rfl | simp_all
  | cons t ts ih =>
    intro i e h
    unfold isMemberOn at h
    split at h
    · simp_all
    · rename_i t' j rest heq
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      rw [ih h]
      rfl
    · simp_all

/-- What a membership test's answer `q` leaves of a type, by a slice of one
tag: where it answered `true`, the labels one tag's passing slice keeps;
where `false`, those every tag's failing slice keeps, one after another. -/
def memberSlice (slice : Ty ι → Tag → Bool → Ty ι) (A : Ty ι) (ts : List Tag) (q : Bool) : Ty ι :=
  if q then (ts.flatMap fun t => slice A t true).eraseDups else ts.foldl (fun B t => slice B t false) A

/-- What a membership test's answer `q` leaves of a slot's type: by each tag's
slice (`memberSlice`), and where it answered `false`, less the labels the
whole set covers (`uncovered`, PROGRAM-TYPING.md, "A membership test"). -/
def memberSlotSlice (G : NormalGraph ι) (A : Ty ι) (ts : List Tag) (q : Bool) : Ty ι :=
  if q then memberSlice (tagSlice G) A ts true
  else BranchRefinement.uncovered G (memberSlice (tagSlice G) A ts false) ts

/-- What a membership test's answer `q` of an object's field `f` leaves of
the object's type: by each tag's field slice, and where it answered `false`,
less the arms the whole set covers and with an arm partly covered at a stable
key read as a label of `candidates` (`uncoveredField`, member-split). -/
def memberFieldSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (ts : List Tag) (q : Bool)
    (candidates : Ty ι) : Ty ι :=
  if q then memberSlice (fun B t q => fieldSlice G B f t q) A ts true
  else BranchRefinement.uncoveredField G (memberSlice (fun B t q => fieldSlice G B f t q) A ts false) f ts candidates

/-- `memberFieldSlice` as a check reads it: the function, or the function's
values at the keys a check meets, read from a table (`FieldSlices.eq_direct`). -/
structure FieldSlices (G : NormalGraph ι) where
  slice : Ty ι → PropKey → List Tag → Bool → Ty ι → Ty ι
  slice_eq : slice = memberFieldSlice G

@[nospecialize] def FieldSlices.direct (G : NormalGraph ι) : FieldSlices G := ⟨memberFieldSlice G, rfl⟩

theorem FieldSlices.eq_direct {G : NormalGraph ι} (s : FieldSlices G) : s = FieldSlices.direct G := by
  cases s with
  | mk f h => subst h; rfl

/-- A membership test's yield (`memberOn`) about the tested slot, or about
the object a current read link says its value was read from: where the test
answered `q`, the labels `memberSlice` keeps of the slot's or the object's
type are within the yield's type, by the yield's evidence. A yield of `true`
is conditional; one of `false` is stated of that answer (`onFalse`). -/
@[nospecialize] def memberYield (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (y : Yield ι) (ts : List Tag) (i : Nat)
    (slices : FieldSlices G := FieldSlices.direct G) : Bool :=
  y.conditional == !y.onFalse && (Γ[i]?).isSome &&
  match y.evidence with
  | none => false
  | some p =>
    (y.target == i && match Γ[i]? with
      | some A => PositiveCertificates.checkUsing G images (memberSlotSlice G A ts !y.onFalse) y.type p
      | none => false) ||
    links.any fun g => !g.alias && !g.optional && g.value == i && g.cell == y.target &&
      match Γ[g.cell]? with
      | some A => PositiveCertificates.checkUsing G images
          (slices.slice A g.field ts (!y.onFalse) y.type) y.type p
      | none => false

/-- Whether a yield follows from a node's membership test (`memberYield`). -/
@[nospecialize] def memberFollows (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (links : HeapLinks.Links) (t : Tm) (y : Yield ι) (slices : FieldSlices G := FieldSlices.direct G) : Bool :=
  match memberParts t with
  | some (ts, i) => isMemberOn ts i t && memberYield G images Γ links y ts i slices
  | none => false

/-- One yield of a node's expression, without a call: a slot read, whose value
is the slot's, yields what an implication on the slot states; a tag test of a
slot, read as a Boolean, yields where it answers `true` what its observation
leaves of the slot, or of the object the slot's value was read from
(`fieldYield`). -/
@[nospecialize] def yieldFollows (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι))
    (xs : List (Implication ι)) (links : HeapLinks.Links) (t : Tm)
    (slices : FieldSlices G := FieldSlices.direct G) (y : Yield ι) : Bool :=
  memberFollows G images Γ links t y slices || match t with
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

theorem instantiate_memberOn (ρ : Env) (i : Nat) :
    ∀ ts : List Tag, instantiate 0 ρ (memberOn ts (.var i)) = memberOn ts (ρ i)
  | [] => rfl
  | t :: ts => by
    simp only [memberOn, List.foldr_cons] at *
    have := instantiate_memberOn ρ i ts
    simp only [memberOn] at this
    simp [instantiate, this]

/-- A membership test of a value returns at once, in its heap: `true` where
one of its tags holds of the value there, `false` where none does. -/
theorem member_run {h : Heap} {v : Tm} (hv : isVal v = true) : ∀ {ts : List Tag} {m h' u},
    Steps m h (memberOn ts v) h' u → isVal u = true →
    (u = .tru ∧ ∃ t ∈ ts, tagHoldsIn h t v = true) ∨ (u = .fls ∧ ∀ t ∈ ts, tagHoldsIn h t v = false)
  | [], _, _, _, run, _ => by
    have := steps_value (v := .fls) rfl run
    exact .inr ⟨this, by simp⟩
  | t :: ts, _, _, _, run, hu => by
    simp only [memberOn, List.foldr_cons] at run
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
            · rename_i hq
              cases st with
              | iteC st => exact absurd st (value_no_step rfl)
              | iteT => exact .inl ⟨steps_value rfl run, t, by simp, hq⟩
            · rename_i hq
              cases st with
              | iteC st => exact absurd st (value_no_step rfl)
              | iteF =>
                rcases member_run hv (ts := ts) run hu with ⟨hu', t', ht', hq'⟩ | ⟨hu', hall⟩
                · exact .inl ⟨hu', t', by simp [ht'], hq'⟩
                · refine .inr ⟨hu', fun t' ht' => ?_⟩
                  rcases List.mem_cons.mp ht' with rfl | ht'
                  · simpa using hq
                  · exact hall t' ht'

omit [DecidableEq ι] in
theorem memberSlice_sound [DecidableEq ι] {slice : Ty ι → Tag → Bool → Ty ι} {M : Ty ι → Prop}
    {Q : Tag → Bool → Prop} (hmono : ∀ {A B : Ty ι}, (∀ a ∈ A, a ∈ B) → M A → M B)
    (hs : ∀ {B t q}, M B → Q t q → M (slice B t q)) {q : Bool} :
    ∀ {A : Ty ι} {ts : List Tag}, M A →
      (q = true → ∃ t ∈ ts, Q t true) → (q = false → ∀ t ∈ ts, Q t false) → M (memberSlice slice A ts q) := by
  intro A ts hA hyes hno
  cases q with
  | true =>
    obtain ⟨t, ht, hQ⟩ := hyes rfl
    simp only [memberSlice, ↓reduceIte]
    exact hmono (fun a ha => List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨t, ht, ha⟩)) (hs hA hQ)
  | false =>
    have hall := hno rfl
    simp only [memberSlice, Bool.false_eq_true, ↓reduceIte]
    clear hyes hno
    induction ts generalizing A with
    | nil => exact hA
    | cons t ts ih =>
      simp only [List.foldl_cons]
      exact ih (hs hA (hall t (by simp))) (fun t' ht' => hall t' (by simp [ht']))

theorem memberYield_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {Γ links y ts i}
    (hf : memberYield G images Γ links y ts i = true) {ρ m W h} {u : Tm}
    (he : EnvOk G Γ ρ (m+1) W) (hh : HeapOk (m+1) W h) (hl : HeapLinks.Holds links ρ h)
    (hrun : (u = .tru ∧ ∃ t ∈ ts, tagHoldsIn h t (ρ i) = true) ∨ (u = .fls ∧ ∀ t ∈ ts, tagHoldsIn h t (ρ i) = false))
    (hcond : y.conditional = true → u = .tru) (hneg : y.onFalse = true → u = .fls) :
    meaning G y.type (m+1) W (ρ y.target) := by
  unfold memberYield at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨hq, -⟩, hp⟩ := hf
  -- The answer the yield is about, and what the run says of it.
  have hyes : (!y.onFalse) = true → ∃ t ∈ ts, tagHoldsIn h t (ρ i) = true := by
    intro ho
    have hu : u = .tru := hcond (by rw [hq]; exact ho)
    rcases hrun with ⟨_, h1⟩ | ⟨hf', _⟩
    · exact h1
    · rw [hu] at hf'; cases hf'
  have hno : (!y.onFalse) = false → ∀ t ∈ ts, tagHoldsIn h t (ρ i) = false := by
    intro ho
    have hu : u = .fls := hneg (by simpa using ho)
    rcases hrun with ⟨ht', _⟩ | ⟨_, h1⟩
    · rw [hu] at ht'; cases ht'
    · exact h1
  split at hp
  · cases hp
  · rename_i p _
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, hc⟩ | hc
    · split at hc
      · rename_i A hA
        have hs := memberSlice_sound (slice := tagSlice G) (M := fun B => meaning G B (m+1) W (ρ y.target))
          (Q := fun t q => tagHolds t (ρ y.target) = q ∨ protoFree t (ρ y.target) = false)
          (fun hsub ⟨a, ha, hv⟩ => ⟨a, hsub a ha, hv⟩) (fun hB hQ => tagSlice_sound hB hQ)
          (q := !y.onFalse) (ts := ts) (he.2 _ A hA)
          (fun ho => (hyes ho).imp fun t ⟨ht, hq'⟩ => ⟨ht, tagHolds_of_heap hq'⟩)
          (fun ho t ht => tagHolds_of_heap (hno ho t ht))
        -- Where every tag answered `false`, a covered label holds no value.
        have hs' : meaning G (memberSlotSlice G A ts !y.onFalse) (m+1) W (ρ y.target) := by
          unfold memberSlotSlice
          cases hq : (!y.onFalse)
          · rw [hq] at hs
            exact BranchRefinement.uncovered_sound hs (fun t ht => tagHolds_of_heap (hno hq t ht))
          · rw [hq] at hs
            exact hs
        exact PositiveCertificates.acceptedUsing hc _ _ _ hs'
      · cases hc
    · obtain ⟨g, hg, hc⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨ha, ho⟩, hv⟩, hcell⟩, hp'⟩ := hc
      split at hp'
      · rename_i A hA
        have hlink := hl g hg
        simp only [ha, ho, Bool.false_eq_true, ite_false] at hlink
        obtain ⟨flds, c, oid, l, hobj, hlk, hu⟩ := hlink
        have hs := memberSlice_sound (slice := fun B t q => fieldSlice G B g.field t q)
          (M := fun B => meaning G B (m+1) W (ρ g.cell))
          (Q := fun t q => tagHolds t (ρ g.value) = q ∨ protoFree t (ρ g.value) = false)
          (fun hsub ⟨a, ha, hv⟩ => ⟨a, hsub a ha, hv⟩) (fun hB hQ => fieldSlice_sound hB hh hobj hlk hu hQ)
          (q := !y.onFalse) (ts := ts) (he.2 _ A hA)
          (fun ho => (hyes ho).imp fun t ⟨ht, hq'⟩ => ⟨ht, tagHolds_of_heap (hv ▸ hq')⟩)
          (fun ho t ht => tagHolds_of_heap (hv ▸ hno ho t ht))
        -- Where every tag answered `false`, an arm the set covers holds no
        -- object, and one it partly covers at a stable key is its rest.
        have hs' : meaning G (memberFieldSlice G A g.field ts (!y.onFalse) y.type) (m+1) W (ρ g.cell) := by
          unfold memberFieldSlice
          cases hq : (!y.onFalse)
          · rw [hq] at hs
            exact BranchRefinement.uncoveredField_sound hs hh hobj hlk hu
              (fun t ht => tagHolds_of_heap (hv ▸ hno hq t ht))
          · rw [hq] at hs
            exact hs
        rw [← hcell]
        exact PositiveCertificates.acceptedUsing hp' _ _ _ hs'
      · cases hp'


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
  intro k hk U hU r h' u run hu y hy hcond _hneg
  have he' := he.transfer k hk U hU
  have hx' := hx.transfer k hk U hU
  have hf := List.all_eq_true.mp hc y hy
  -- The object's slice, at the run's own level, carried to the reached world.
  have later : ∀ {B : Ty ι} {v}, meaning G B (m+1) W v → meaning G B k U v := fun hv =>
    (meaning_adm G _).mono k _ U hU _ ((meaning_adm G _).down_le (m+1) k hk W _ hv)
  unfold yieldFollows at hf
  simp only [Bool.or_eq_true] at hf
  rcases hf with hm | hf
  · unfold memberFollows at hm
    split at hm
    · rename_i ts i _
      simp only [Bool.and_eq_true] at hm
      obtain ⟨hshape, hm⟩ := hm
      have hval : isVal (ρ i) = true := by
        unfold memberYield at hm
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hm
        obtain ⟨⟨_, A, hA⟩, -⟩ := hm
        exact (meaning_value (he.2 i A hA)).1
      have run' : Steps r h (memberOn ts (ρ i)) h' u := by
        rw [← instantiate_memberOn, ← isMemberOn_sound hshape]
        simpa using run
      exact later (memberYield_sound hm he hh hl (member_run hval run' hu) hcond _hneg)
    · cases hm
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
          if s.receiver = jr.type ∧ s.arguments = jas.map Sequent.type ∧ s.effect.requires = none then
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
    (v : Tm) (h' : Heap) : HeapKnowledge.Holds (HeapExpressionRules.ordinaryOutput k) (push v ρ) h' :=
  ⟨HeapFacts.holds_nil _ _,(HeapKnowledge.shift_holds (v := v) hk).2.1,
    HeapLinks.stable_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.1,
    (HeapKnowledge.shift_holds (v := v) hk).2.2.2.1, HeapKnowledge.elemsHolds_nil _ _,
    HeapKnowledge.envIndices_holds (HeapKnowledge.shift_holds (v := v) hk).2.2.2.2.2 _⟩

/-- Whether a signature's effect keeps the contents of every location a
call starts with on a normal return: the empty footprint, on the receiver's
array store and own locations as well (PROGRAM-TYPING.md, "A call that keeps
the heap"). -/
def keepsHeap (e : Effect) : Bool := e.footprint.le .empty && !e.receiverStore && !e.receiverOwn

/-- The heap facts of a call's entry kept on a normal return of a call at a
promise signature: every one where its effect keeps the heap (`call-keep`),
else those no call changes. -/
def promiseOutput (effect : Effect) (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  if keepsHeap effect then HeapKnowledge.shift k else HeapExpressionRules.ordinaryOutput k

/-- A normal return at an effect keeping the heap returns in an extension of
the heap the call started in. -/
theorem keepsHeap_prefix {e : Effect} (hk : keepsHeap e = true) {r : Tm} {before after : Heap} {v}
    (hp : e.post r before after v) : before.IsPrefix after := by
  simp only [keepsHeap, Bool.and_eq_true, Bool.not_eq_true'] at hk
  exact Footprints.Closed.holds_empty.mp ((CallEffects.Effect.within_holds hp.1 hk.1.2 hk.2).mono hk.1.1)

theorem promiseOutput_holds {effect : Effect} {k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap}
    {r : Tm} {v} (hk : HeapKnowledge.Holds k ρ h) (hp : effect.post r h h' v) :
    HeapKnowledge.Holds (promiseOutput effect k) (push v ρ) h' := by
  unfold promiseOutput
  split
  · rename_i hkeep
    obtain ⟨vs, rfl⟩ := keepsHeap_prefix hkeep hp
    exact HeapKnowledge.shift_holds (HeapKnowledge.alloc_frames vs hk)
  · exact ordinaryOutput_holds hk v h'

/-- What the ordinary output states holds wherever a promise call's output
holds: it keeps less. -/
theorem promiseOutput_ordinary {effect : Effect} {k : HeapKnowledge.Knowledge} {τ : Env} {h : Heap}
    (hk : HeapKnowledge.Holds (promiseOutput effect k) τ h) :
    HeapKnowledge.Holds (HeapExpressionRules.ordinaryOutput k) τ h := by
  unfold promiseOutput at hk
  split at hk
  · exact ⟨HeapFacts.holds_nil _ _, hk.2.1, HeapLinks.stable_holds hk.2.2.1, hk.2.2.2.1,
      HeapKnowledge.elemsHolds_nil _ _, HeapKnowledge.envIndices_holds hk.2.2.2.2.2 _⟩
  · exact hk

/-- **A call at a promise signature** returns where the promise holds: its
callee meets the promise signature it holds beside the one the call is
checked at, at the same receiver and actuals, so the call's own run is one the
promise is about (`CallEffects.call_safe`). The result meets the claim's type,
and the facts kept are those its effect keeps (`promiseOutput`). -/
theorem promiseCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {e : Evidence ι}
    {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {effect a T} {ys : List (Yield ι)}
    (hp : promiseOf G e = some (effect, a, T))
    (ht : checkTreeUsing G images e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    (hy : promiseYields G (claim e).type effect a T ys = true)
    {k ρ n W h} (he : EnvOk G (claim e).context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (fun m U u => meaning G (claim e).type m U u ∧ YieldsOk G ys ρ m U u)
      (fun h' v => HeapKnowledge.Holds (promiseOutput effect k) (push v ρ) h') n W h
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
    exact checkTreeUsing_sound e (ht.2 ⟨e, heq⟩ (by simp)) hcodes hsums
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
  obtain ⟨hrecv, hargsig, hreq⟩ := hsig
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
      (CallEffects.Effect.requires_none hreq _ _)
    have hterm : instantiate 0 ρ (.invoke f rv args) = .invoke (instantiate 0 ρ jf.term)
        (instantiate 0 ρ jr.term) (args.map (instantiate 0 ρ)) := by
      simp [instantiate, instantiateArgs_eq_map, htf, htr]
    rw [hterm]
    have hsel : s.effect = effect := by
      revert hsome
      split <;> (try split) <;> intro hsome <;> simp_all
    refine consequence (fun m U u hu => ?_) (fun h' v hq => promiseOutput_holds hk (hsel ▸ hq)) hs'
    clear hsel
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
        refine ⟨?_, fun y hym hcond _ => ?_⟩
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
        refine ⟨admitsUndef_sound hundefA m U, fun y hym _ _ => ?_⟩
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

/-! ### A call that keeps the heap (PROGRAM-TYPING.md, "A call that keeps the heap")

A call whose selected signature's footprint is within the empty one, its
receiver's store included, returns normally in an extension of the heap it
started in, so every heap fact of its entry still holds there (`call-keep`).
A call at a promise signature keeps them only where the promise signature's
effect keeps the heap too, as its node's check (`checkYields`) requires. -/

/-- Whether an ordinary step's evidence is a call `call-keep` applies to: at
the sequent `j`, at a selected signature keeping the heap, its derivation
checked, and, at a promise signature, that signature's effect keeping the
heap as well. -/
@[nospecialize] def keepsCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && ExpressionEffects.selectedCallWithin .empty p &&
      (match promiseOf G p with | some (effect, _, _) => keepsHeap effect | none => true) &&
      checkTreeUsing G images p codes sums
  | _ => false

theorem keepsCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : keepsCall G images j e codes sums = true) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (HeapKnowledge.shift k) (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold keepsCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hsel⟩, -⟩, ht⟩ := hc
    refine consequence (fun _ _ _ hv => hv) (fun h' v hq => ?_)
      (ExpressionEffects.selectedCall_sound p ht hsel hcodes hsums he hw hh)
    obtain ⟨vs, rfl⟩ := Footprints.Closed.holds_empty.mp hq
    exact HeapKnowledge.shift_holds (HeapKnowledge.alloc_frames vs hk)
  · contradiction

/-! ### A call allocating its result (PROGRAM-TYPING.md, "A call allocating its result")

A call keeping the heap whose signature states `freshObject` returns an object
every own location of which lies past the heap the call started in, while
every contract field of a slot of the call's context lies in it: its result
is separated from those fields, as an allocation's is (`call-fresh`). -/

/-- Whether an ordinary step's evidence is a call `call-fresh` applies to: at
the sequent `j`, its operands values, at a selected signature keeping the heap
and stating a fresh object, its derivation checked. -/
@[nospecialize] def freshCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && ExpressionEffects.selectedOperands p &&
      (match ExpressionEffects.selectedEffect p with
        | some eff => keepsHeap eff && eff.freshObject
        | none => false) &&
      checkTreeUsing G images p codes sums
  | _ => false

/-- The knowledge after a call allocating its result: every fact of the entry,
and the result's separation from the context's contract fields. -/
def freshOutput (G : NormalGraph ι) (Γ : List (Ty ι)) (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  HeapExpressionRules.allocOutput k [] Γ.length (HeapExpressionRules.contractFields G Γ)

/-- A fresh object's own locations lie past the old heap's end; a contract
field of a slot holds a heap value, so it lies below it. -/
theorem freshObject_apart {G : NormalGraph ι} {Γ ρ n W h} {v : Tm}
    (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h) (hv : Footprints.FreshObjectAt h.length v) :
    ∀ s g, (s, g) ∈ HeapExpressionRules.contractFields G Γ →
      HeapSeparation.Apart (push v ρ) 0 none (s + 1) g := by
  intro s g hm l l' hl hl'
  obtain ⟨Ref,hidx,hfo⟩ := HeapExpressionRules.contractFields_mem hm
  obtain ⟨_,flds1,code0,oid0,l1,c1,hl0,hfd1,hlookup,_⟩ :=
    HeapExpressionRules.fieldOperand_sound hfo (he.2 s Ref hidx)
  obtain ⟨u,hu,_⟩ := hh.2 l1 c1 hlookup
  have hlt : l1 < h.length := List.getElem?_eq_some_iff.mp hu |>.1
  obtain ⟨⟨fs, c, oid, rfl⟩, hown⟩ := hv
  have hge : h.length ≤ l := hown l (by simpa [push, HeapSeparation.At, Footprints.ownOf, Footprints.fieldsOf] using hl)
  simp only [push, hl0, HeapSeparation.At, List.mem_singleton, exists_eq_left] at hl'
  have : l' = l1 := Option.some.inj (hl'.symm.trans hfd1)
  omega

theorem freshCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hc : freshCall G images j e codes sums = true) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (freshOutput G j.context k) (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold freshCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hops⟩, hsel⟩, ht⟩ := hc
    split at hsel
    · rename_i eff heff
      simp only [Bool.and_eq_true] at hsel
      obtain ⟨hkeep, hfo⟩ := hsel
      refine consequence (fun _ _ _ hv => hv) (fun h' v hq => ?_)
        (ExpressionEffects.selected_sound p ht hops heff hcodes hsums he hw hh)
      have hfresh := hq.2.2.1 hfo
      obtain ⟨vs, rfl⟩ := keepsHeap_prefix hkeep hq
      have hshift := HeapKnowledge.shift_holds (v := v) (HeapKnowledge.alloc_frames vs hk)
      refine ⟨?_, hshift.2.1, hshift.2.2.1,
        HeapSeparation.allocate_holds hk.2.2.2.1 (freshObject_apart he hh hfresh), hshift.2.2.2.2⟩
      simpa [freshOutput, HeapExpressionRules.allocOutput, HeapKnowledge.shift] using hshift.1
    · cases hsel
  · contradiction

/-! ### A call changing only its receiver's own locations (PROGRAM-TYPING.md, "A call changing only its receiver")

A call at a signature whose footprint is within the empty one on every old
location but its receiver's own ones changes no location a fact names that a
separation fact keeps apart from every own location of the receiver
(`call-own`). -/

/-- The receiver slot of an ordinary step's evidence that `call-own` applies
to: at the sequent `j`, its operands values, at a selected signature within
the empty footprint but on its receiver's own locations, its derivation
checked, its receiver a slot. -/
@[nospecialize] def ownCallChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && ExpressionEffects.selectedOperands p &&
      (match ExpressionEffects.selectedEffect p with
        | some eff => eff.footprint.le .empty && eff.receiverOwn && !eff.receiverStore
        | none => false) &&
      checkTreeUsing G images p codes sums
  | _ => false

/-- The slot a call's receiver is, where it is one. -/
def receiverSlot : Tm → Option Nat
  | .invoke _ (.var i) _ => some i
  | _ => none

@[nospecialize] def ownCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) : Option Nat :=
  if ownCallChecked G images j e codes sums then receiverSlot j.term else none

/-- The facts a call changing only the own locations of the slot `i` keeps:
each cell fact and read link about a field separated from every own location
of `i`, every alias link, every value fact and the separation. -/
def ownKept (k : HeapKnowledge.Knowledge) (i : Nat) : HeapKnowledge.Knowledge :=
  ⟨k.cells.filter (fun f => HeapSeparation.apartAll k.separation i f.slot f.field), k.values,
    k.links.filter (fun g => g.alias || HeapSeparation.apartAll k.separation i g.cell g.field), k.separation, [], []⟩

def ownOutput (k : HeapKnowledge.Knowledge) (i : Nat) : HeapKnowledge.Knowledge :=
  HeapKnowledge.shift (ownKept k i)

/-- A field read gives what it gave before where its location keeps its
contents. -/
theorem readGave_kept {flds field h h' u} (hr : HeapFacts.ReadGave flds field h u)
    (hkeep : ∀ l, flds.lookup field = some l → ∀ v, h[l]? = some v → h'[l]? = some v) :
    HeapFacts.ReadGave flds field h' u := by
  unfold HeapFacts.ReadGave at hr ⊢
  cases hl : flds.lookup field with
  | none => simpa [hl] using hr
  | some l => simp only [hl] at hr ⊢; exact hkeep l hl u hr

theorem ownKept_holds {k : HeapKnowledge.Knowledge} {i : Nat} {ρ : Env} {h h' : Heap}
    (hk : HeapKnowledge.Holds k ρ h)
    (hkeep : ∀ l, l ∉ Footprints.ownOf (ρ i) → ∀ v, h[l]? = some v → h'[l]? = some v) :
    HeapKnowledge.Holds (ownKept k i) ρ h' := by
  have away : ∀ {s g flds c oid l}, HeapSeparation.apartAll k.separation i s g = true →
      ρ s = .objAt flds c oid → flds.lookup g = some l → l ∉ Footprints.ownOf (ρ i) := by
    intro s g flds c oid l ha hs hl hm
    have hat : HeapSeparation.At none (ρ i) l := by
      unfold Footprints.ownOf Footprints.fieldsOf at hm
      unfold HeapSeparation.At
      split at hm <;> simp_all
    exact HeapSeparation.apartAll_sound ha hk.2.2.2.1 hat hs hl rfl
  refine ⟨?_, hk.2.1, ?_, hk.2.2.2.1, HeapKnowledge.elemsHolds_nil _ _, HeapKnowledge.indexHolds_nil _ _⟩
  · intro f hf
    obtain ⟨hf, ha⟩ := List.mem_filter.mp hf
    obtain ⟨flds,c,oid,u,hs,hr,hm⟩ := hk.1 f hf
    exact ⟨flds,c,oid,u,hs,readGave_kept hr (fun l hl v hv => hkeep l (away ha hs hl) v hv),hm⟩
  · intro g hg
    obtain ⟨hg, ha⟩ := List.mem_filter.mp hg
    have hh := hk.2.2.1 g hg
    cases hal : g.alias
    · simp only [hal, Bool.false_or] at ha
      cases ho : g.optional
      · simp only [hal, ho, Bool.false_eq_true, if_false] at hh ⊢
        obtain ⟨flds,c,oid,l,hs,hl,hv⟩ := hh
        exact ⟨flds,c,oid,l,hs,hl,hkeep l (away ha hs hl) _ hv⟩
      · simp only [hal, ho, Bool.false_eq_true, if_false, if_true] at hh ⊢
        obtain ⟨flds,c,oid,hs,hr⟩ := hh
        exact ⟨flds,c,oid,hs,readGave_kept hr (fun l hl v hv => hkeep l (away ha hs hl) v hv)⟩
    · simp only [hal, if_true] at hh ⊢
      exact hh

theorem ownCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)} {i : Nat}
    (hc : ownCall G images j e codes sums = some i) (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (ownOutput k i) (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold ownCall at hc
  split at hc
  · rename_i hcond
    unfold ownCallChecked at hcond
    split at hcond
    · rename_i p
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨hj, hops⟩, hsel⟩, ht⟩ := hcond
      subst hj
      have hterm : ∃ f args, (claim p).term = .invoke f (.var i) args := by
        revert hc
        cases hT : (claim p).term <;> simp only [receiverSlot] <;> intro hc <;> try cases hc
        rename_i f r args
        cases r <;> first | (cases hc; exact ⟨f, args, rfl⟩) | cases hc
      obtain ⟨f, args, hterm⟩ := hterm
      split at hsel
      · rename_i eff heff
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsel
        obtain ⟨⟨hle, hown⟩, -⟩ := hsel
        refine consequence (fun _ _ _ hv => hv) (fun h' v hq => ?_)
          (ExpressionEffects.selected_sound p ht hops heff hcodes hsums he hw hh)
        have hw' := hq.1
        unfold CallEffects.Effect.within at hw'
        simp only [hown, if_true] at hw'
        rw [hterm] at hw'
        simp only [ExpressionEffects.receiverOf, instantiate] at hw'
        have hon := hw'.1.mono hle
        refine HeapKnowledge.shift_holds (ownKept_holds hk fun l hl u hu => ?_)
        obtain ⟨u', hu', hc⟩ := hon.2 l u hl hu
        have : u' = u := by
          simp only [Footprints.Closed.at, Footprints.Closed.empty] at hc
          split at hc <;> simpa [Footprints.Change.Holds] using hc
        rw [← this]; exact hu'
      · cases hsel
    · cases hcond
  · cases hc

/-! ### A call promising its receiver's elements (FOOTPRINTS.md, "The elements fact")

A call keeping the heap whose selected signature promises its receiver's
elements (`elements R`) returns `true` only where every present element of
the array its receiver slot holds satisfies `R`: its output keeps every fact
of its entry and adds that atom, conditional on its result
(`call-elements`). -/

/-- Whether every value of a type is a Boolean. -/
def onlyBool (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with | .boolLit _ => true | _ => false

omit [DecidableEq ι] in
theorem onlyBool_sound {G : NormalGraph ι} {A : Ty ι} {n W v}
    (h : onlyBool G A = true) (hv : meaning G A n W v) : v = .tru ∨ v = .fls := by
  simp only [onlyBool, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c, hc, hv, -⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [PositiveNormalization.semWithArgs]

/-- A safe run whose postcondition holds of each value it returns where the
value meets the result's type. -/
theorem post_with_type {Ξ T : Fam} {Q Q' : Post} (hq : ∀ k W h v, T k W v → Q h v → Q' h v) :
    ∀ {n W h t}, SafePost Ξ T Q n W h t → SafePost Ξ T Q' n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (⟨hv, ht, hq'⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, hq _ _ _ _ ht hq'⟩)
    · exact .inl (.inr hth)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih hs⟩

theorem receiverSlot_term {t : Tm} {x : Nat} (h : receiverSlot t = some x) :
    ∃ f args, t = .invoke f (.var x) args := by
  unfold receiverSlot at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- The derivation a step's evidence carries beside its kind, for the kinds
whose check reads it alone: ordinary, pure, reading and created steps. -/
def stepProof : HeapExpressionRules.StepEvidence ι → Option (Evidence ι)
  | .ordinary p | .pure p | .reading p | .created p => some p
  | _ => none

/-- The receiver slot and predicate of an ordinary step's evidence that
`call-elements` applies to: at the sequent `j`, its operands values, at a
selected signature keeping the heap and promising its receiver's elements,
its derivation checked, its receiver a slot. -/
@[nospecialize] def elementsCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Option (Nat × CallEffects.ElemPred) :=
  match stepProof e with
  | some p =>
    if decide (claim p = j) && ExpressionEffects.selectedOperands p && checkTreeUsing G images p codes sums &&
        onlyBool G j.type then
      match ExpressionEffects.selectedEffect p, receiverSlot j.term with
      | some eff, some x => if keepsHeap eff then eff.elements.map fun R => (x, R) else none
      | _, _ => none
    else none
  | _ => none

/-- The knowledge after a call promising its receiver's elements: every fact
of the entry, and the atom on the receiver's slot, conditional on the result. -/
def elementsOutput (k : HeapKnowledge.Knowledge) (x : Nat) (R : CallEffects.ElemPred) : HeapKnowledge.Knowledge :=
  { HeapKnowledge.shift k with elems := ⟨x + 1, R, some 0, false⟩ :: (HeapKnowledge.shift k).elems }

theorem elementsCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {x : Nat} {R : CallEffects.ElemPred}
    (hc : elementsCall G images j e codes sums = some (x, R)) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    {k : HeapKnowledge.Knowledge} {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (elementsOutput k x R) (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold elementsCall at hc
  split at hc
  · rename_i p _
    by_cases hcond : (decide (claim p = j) && ExpressionEffects.selectedOperands p &&
        checkTreeUsing G images p codes sums && onlyBool G j.type) = true
    · rw [if_pos hcond] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨rfl, hops⟩, ht⟩, hbool⟩ := hcond
      cases hsel : ExpressionEffects.selectedEffect p with
      | none => simp [hsel] at hc
      | some eff =>
        cases hrs : receiverSlot (claim p).term with
        | none => simp [hsel, hrs] at hc
        | some x' =>
          simp only [hsel, hrs] at hc
          by_cases hkeep : keepsHeap eff = true
          · rw [if_pos hkeep] at hc
            obtain ⟨R', hR', hpair⟩ := Option.map_eq_some_iff.mp hc
            simp only [Prod.mk.injEq] at hpair
            obtain ⟨rfl, rfl⟩ := hpair
            obtain ⟨f, args, hterm⟩ := receiverSlot_term hrs
            refine post_with_type (fun m U h' v hT hq => ?_)
              (ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh)
            have hb := onlyBool_sound hbool hT
            obtain ⟨vs, rfl⟩ := keepsHeap_prefix hkeep hq
            have hs := HeapKnowledge.shift_holds (v := v) (HeapKnowledge.alloc_frames vs hk)
            refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, hs.2.2.2.2.2⟩
            intro a ha hcond
            rcases List.mem_cons.mp ha with rfl | ha
            · have hv : v = .tru := by
                have ht := hcond 0 rfl
                simp only [push] at ht
                rcases hb with rfl | rfl
                · rfl
                · simp [tagHolds] at ht
              have hel := hq.2.2.2 _ hR' hv
              rw [hterm] at hel
              simpa [ExpressionEffects.receiverOf, instantiate, push] using hel
            · exact hs.2.2.2.2.1 a ha hcond
          · rw [if_neg hkeep] at hc; cases hc
    · rw [if_neg hcond] at hc; cases hc
  · cases hc

/-! ### A call at a precondition on its receiver's elements

A call whose selected signature requires its receiver's elements to satisfy
`R` is safe where its receiver slot's class has an unconditional atom with a
predicate within `R`: the atom gives the precondition (`call-requires`). -/

/-- Whether the knowledge states, of a slot's class, that its array's present
elements satisfy a predicate within `R`. -/
def atomFor (k : HeapKnowledge.Knowledge) (x : Nat) (R : CallEffects.ElemPred) : Bool :=
  k.elems.any fun a => a.cond.isNone && (HeapLinks.aliases k.links x).contains a.slot && a.pred.le R

theorem atomFor_sound {k : HeapKnowledge.Knowledge} {x R ρ h} (hc : atomFor k x R = true)
    (hk : HeapKnowledge.Holds k ρ h) : CallEffects.ElemsAt R (ρ x) h := by
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.contains_iff_mem] at hm
  obtain ⟨⟨hnone, hal⟩, hle⟩ := hm
  have hat := hk.2.2.2.2.1 a ha fun b hb => by rw [hnone] at hb; cases hb
  rw [HeapLinks.aliases_eq hk.2.2.1 hal] at hat
  exact hat.mono hle

/-- Whether a derivation is a call `call-requires` applies to: the local call
rule at a selected signature stating a precondition, its operands values, its
premises' derivations checked, and the precondition's atom on its receiver
slot. -/
@[nospecialize] def requiresApp (G : NormalGraph ι) (images : InstanceImageCheck G)
    (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Evidence ι → Bool
  | .node j (.app eff) ps =>
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.app eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    match eff.requires, receiverSlot j.term with
    | some R, some x => atomFor k x R
    | _, _ => false
  | _ => false

/-- Such a call, or its subsumption. -/
@[nospecialize] def requiresTree (G : NormalGraph ι) (images : InstanceImageCheck G)
    (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Evidence ι → Bool
  | .node j (.sub c) [p] =>
    decide (LocalUsing G images j (.sub c) [claim p] codes (sums := sums)) && requiresApp G images k codes sums p
  | p => requiresApp G images k codes sums p

theorem requiresApp_sound {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) {eff : Effect}
    (hsel : ExpressionEffects.selectedEffect p = some eff) {ρ n W h} (he : EnvOk G (claim p).context ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G (claim p).type)
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he ⊢
      cases hR : eff'.requires with
      | none => simp [hR] at hreq
      | some R =>
        cases hx : receiverSlot j.term with
        | none => simp [hR, hx] at hreq
        | some x =>
          simp only [hR, hx] at hreq
          obtain ⟨f, args, hterm⟩ := receiverSlot_term hx
          have hq : eff'.Requires (ExpressionEffects.receiverOf (instantiate 0 ρ j.term)) h := by
            intro R' hR'
            rw [hR] at hR'
            cases hR'
            rw [hterm]
            simpa [ExpressionEffects.receiverOf, instantiate] using atomFor_sound hreq hk
          have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
            intro p hm
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
            exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
          have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
              checkScope p.context.length p.term = true := by
            intro p hm
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
            simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
          exact (ExpressionEffects.call_local_sound hl typed values he hw hh hq).post
  | _ => simp [requiresApp] at hc

theorem requiresApp_selected {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' => exact ⟨_, rfl⟩
  | _ => simp [requiresApp] at hc

theorem requiresTree_sound {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresTree G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff ∧ ∀ {ρ n W h}, EnvOk G (claim p).context ρ n W →
    HeapKnowledge.Holds k ρ h → WorldAdm W → HeapOk n W h →
    SafePost (excOf G) (meaning G (claim p).type)
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  by_cases hs : ∃ j c q, p = .node j (.sub c) [q]
  · obtain ⟨j, c, q, rfl⟩ := hs
    simp only [requiresTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, hc⟩ := hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected q hc
    refine ⟨eff, by simpa [ExpressionEffects.selectedEffect] using hsel, fun {ρ n W h} he hk hw hh => ?_⟩
    obtain ⟨hctx, hterm, hsub⟩ := hl
    have ih := requiresApp_sound hcodes hsums q hc hsel (ρ := ρ) (n := n) (W := W) (h := h)
      (by rw [hctx]; exact he) hk hw hh
    rw [hterm] at ih
    exact consequence (fun j W v hv => PositiveCertificates.acceptedUsing hsub j W v hv) (fun _ _ hp => hp) ih
  · have happ : requiresApp G images k codes sums p = true := by
      obtain ⟨j, r, ps⟩ := p
      cases r <;> try (simpa [requiresTree] using hc)
      rcases ps with _ | ⟨q, _ | ⟨q', qs⟩⟩
      · simpa [requiresTree] using hc
      · exact absurd ⟨j, _, q, rfl⟩ hs
      · simpa [requiresTree] using hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected p happ
    exact ⟨eff, hsel, fun he hk hw hh => requiresApp_sound hcodes hsums p happ hsel he hk hw hh⟩

/-- Whether an ordinary step's evidence is a call `call-requires` applies to. -/
@[nospecialize] def requiresCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : HeapKnowledge.Knowledge) (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : Bool :=
  match e with
  | .ordinary p =>
    decide (claim p = j) && requiresTree G images k codes sums p
  | _ => false

/-- The knowledge after a call at a precondition: every fact where its
signature keeps the heap, else those no call changes. -/
def requiresOutput (e : HeapExpressionRules.StepEvidence ι) (k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  match e with
  | .ordinary p => match ExpressionEffects.selectedEffect p with
    | some eff => promiseOutput eff k
    | none => HeapExpressionRules.ordinaryOutput k
  | _ => HeapExpressionRules.ordinaryOutput k

theorem requiresCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)}
    (hc : requiresCall G images j k e codes sums = true) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (fun h' v => HeapKnowledge.Holds (requiresOutput e k) (push v ρ) h') n W h (instantiate 0 ρ j.term) := by
  unfold requiresCall at hc
  split at hc
  · rename_i p
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨rfl, hc⟩ := hc
    obtain ⟨eff, hsel, hs⟩ := requiresTree_sound hcodes hsums p hc
    have hs := hs he hk hw hh
    refine consequence (fun _ _ _ hv => hv) (fun h' v hp => ?_) hs
    simp only [requiresOutput, hsel]
    exact promiseOutput_holds hk hp
  · cases hc

/-! ### A negation of a Boolean slot

`if x then false else true` on the slot `x` steps once, in the heap it starts
in, to the negation of `x`'s Boolean: an atom conditional on `x`'s
truthiness holds conditional on the result's falsiness (`not-elements`). -/

/-- The slot a term negates, where it is `if x then false else true`, the
test of `x` a Boolean's or its truthiness. -/
def negationOf (j : Sequent ι) : Option Nat :=
  match j.term with
  | .ite (.var x) .fls .tru | .ite (.test .truthy (.var x)) .fls .tru =>
    if x < j.context.length then some x else none
  | _ => none

theorem negation_run {Ξ T : Fam} {Q : Post} {v : Tm} (hv : isVal v = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h (.ite v .fls .tru) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧ ((v = .tru ∧ u = .fls) ∨ (v = .fls ∧ u = .tru))) n W h
        (.ite v .fls .tru) := by
  intro n W h hs
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | iteC hr => exact absurd (raises_not_val hr) (by simp [hv])
    · refine .inr ⟨U, h', t', hx, hu, step, hh, ?_⟩
      cases step with
      | iteC s => exact absurd s (value_no_step hv)
      | iteT =>
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, .inl ⟨rfl, rfl⟩⟩)
          · exact absurd (raises_not_val hr) (by simp [isVal])
          · exact absurd step' (value_no_step (by simp [isVal]))
      | iteF =>
        cases n with
        | zero => trivial
        | succ m =>
          rcases hs with (⟨hval, ht, hq⟩ | ⟨u, hr, -⟩) | ⟨U', h'', t'', -, -, step', -, -⟩
          · exact .inl (.inl ⟨hval, ht, hq, rfl, .inr ⟨rfl, rfl⟩⟩)
          · exact absurd (raises_not_val hr) (by simp [isVal])
          · exact absurd step' (value_no_step (by simp [isVal]))

theorem negation_test_run {Ξ T : Fam} {Q : Post} {v : Tm} (hv : isVal v = true) :
    ∀ {n W h}, SafePost Ξ T Q n W h (.ite (.test .truthy v) .fls .tru) →
      SafePost Ξ T (fun h' u => Q h' u ∧ h' = h ∧
        ((tagHolds .truthy v = true ∧ u = .fls) ∨ (tagHolds .truthy v = false ∧ u = .tru))) n W h
        (.ite (.test .truthy v) .fls .tru) := by
  intro n W h hs
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval, -, -⟩ | ⟨u, hr, -⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · simp [isVal] at hval
    · cases hr with
      | iteC hr => cases hr with
        | testC hr => exact absurd (raises_not_val hr) (by simp [hv])
    · cases step with
      | iteC step =>
        cases step with
        | testC s => exact absurd s (value_no_step hv)
        | testV _ =>
          have hb : isVal (if tagHoldsIn h .truthy v then Tm.tru else .fls) = true := by
            split <;> rfl
          have hp : tagHoldsIn h .truthy v = tagHolds .truthy v := tagHoldsIn_of_protoFree (by simp [protoFree])
          refine .inr ⟨U, h, _, hx, hu, .iteC (.testV hv), hh, ?_⟩
          refine HeapObservations.weaken (fun h'' u hq => ⟨hq.1, hq.2.1, ?_⟩) (negation_run hb hs)
          rw [hp] at hq
          cases ht : tagHolds .truthy v
          · rw [ht] at hq
            rcases hq.2.2 with ⟨h1, -⟩ | ⟨-, h2⟩
            · cases h1
            · exact .inr ⟨rfl, h2⟩
          · rw [ht] at hq
            rcases hq.2.2 with ⟨-, h2⟩ | ⟨h1, -⟩
            · exact .inl ⟨rfl, h2⟩
            · cases h1

/-- The atoms on the negated slot's class, restated on the result with the
opposite condition. -/
def negatedAtoms (k : HeapKnowledge.Knowledge) (x : Nat) : List HeapKnowledge.ElemAtom :=
  (k.elems.filter fun a => a.cond.any fun c => (HeapLinks.aliases k.links x).contains c).map fun a =>
    { a with slot := a.slot + 1, cond := some 0, negated := !a.negated }

theorem negatedAtoms_holds {k : HeapKnowledge.Knowledge} {x : Nat} {ρ h u}
    (hk : HeapKnowledge.Holds k ρ h)
    (hu : (tagHolds .truthy (ρ x) = true ∧ u = .fls) ∨ (tagHolds .truthy (ρ x) = false ∧ u = .tru)) :
    HeapKnowledge.ElemsHolds (negatedAtoms k x) (push u ρ) h := by
  intro a ha hc
  obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
  obtain ⟨hbm, hbc⟩ := List.mem_filter.mp hb'
  have hcu := hc 0 rfl
  simp only [push] at hcu
  cases hcb : b.cond with
  | none => rw [hcb] at hbc; simp at hbc
  | some c =>
    rw [hcb] at hbc
    simp only [Option.any_some, List.contains_iff_mem] at hbc
    have hrc : ρ c = ρ x := HeapLinks.aliases_eq hk.2.2.1 hbc
    have := hk.2.2.2.2.1 b hbm fun c' hc' => by
      rw [hcb] at hc'; cases hc'
      rw [hrc]
      rcases hu with ⟨hx, hu⟩ | ⟨hx, hu⟩
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
    simpa [push] using this

/-- The index atoms on the negated slot's class, restated on the result with
the opposite condition: the polarity of the condition flips, the fact stays. -/
def negatedIndices (k : HeapKnowledge.Knowledge) (x : Nat) : List HeapKnowledge.IndexAtom :=
  (k.indices.filter fun a => a.cond.any fun c => (HeapLinks.aliases k.links x).contains c).map fun a =>
    { a with fact := a.fact.map (· + 1), cond := some 0, negated := !a.negated }

theorem negatedIndices_holds {k : HeapKnowledge.Knowledge} {x : Nat} {ρ h u}
    (hk : HeapKnowledge.Holds k ρ h)
    (hu : (tagHolds .truthy (ρ x) = true ∧ u = .fls) ∨ (tagHolds .truthy (ρ x) = false ∧ u = .tru)) :
    HeapKnowledge.IndexHolds (negatedIndices k x) (push u ρ) h := by
  intro a ha hc
  obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
  obtain ⟨hbm, hbc⟩ := List.mem_filter.mp hb'
  have hcu := hc 0 rfl
  simp only [push] at hcu
  cases hcb : b.cond with
  | none => rw [hcb] at hbc; simp at hbc
  | some c =>
    rw [hcb] at hbc
    simp only [Option.any_some, List.contains_iff_mem] at hbc
    have hrc : ρ c = ρ x := HeapLinks.aliases_eq hk.2.2.1 hbc
    have := hk.2.2.2.2.2 b hbm fun c' hc' => by
      rw [hcb] at hc'; cases hc'
      rw [hrc]
      rcases hu with ⟨hx, hu⟩ | ⟨hx, hu⟩
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
      · rw [hu] at hcu; rw [hx]; cases hn : b.negated <;> simp_all [tagHolds]
    exact (HeapKnowledge.IndexFact.holdsAt_map (fun s _ => rfl)).mpr this

theorem negation_bool {u v : Tm} (h : (v = .tru ∧ u = .fls) ∨ (v = .fls ∧ u = .tru)) :
    (tagHolds .truthy v = true ∧ u = .fls) ∨ (tagHolds .truthy v = false ∧ u = .tru) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

end
end Verification.PromiseCalls

namespace Verification.HeapExpressionRules
open ProgramCertificates PositiveGraphs HeapObservations
open PositiveCertificates (InstanceImageCheck)

/-- A checker whose steps negating a Boolean slot restate the atoms
conditional on it with the opposite condition (`PromiseCalls.negationOf`);
every step is otherwise `base`'s. -/
@[nospecialize] def Checker.negatingSlots [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.negationOf j with
    | some x => (base.run j k e codes sums).map fun out =>
        { out with
            elems := out.elems ++ PromiseCalls.negatedAtoms k x
            indices := out.indices ++ PromiseCalls.negatedIndices k x }
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.negationOf j with
    | some x => (base.select j k e codes sums).map fun out =>
        { out with
            elems := out.elems ++ PromiseCalls.negatedAtoms k x
            indices := out.indices ++ PromiseCalls.negatedIndices k x }
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i x hx
      simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, rfl⟩ := hc
      have hs := base.sound hrun hcodes hsums he hk hw hh
      have hterm : (j.term = .ite (.var x) .fls .tru ∨ j.term = .ite (.test .truthy (.var x)) .fls .tru) ∧
          x < j.context.length := by
        unfold PromiseCalls.negationOf at hx
        split at hx
        · rename_i y hy
          split at hx
          · cases hx; exact ⟨.inl hy, by assumption⟩
          · cases hx
        · rename_i y hy
          split at hx
          · cases hx; exact ⟨.inr hy, by assumption⟩
          · cases hx
        · cases hx
      have hxv : isVal (ρ x) = true :=
        (ProgramTyping.meaning_value (he.2 x _ (List.getElem?_eq_getElem hterm.2))).1
      have finish : ∀ h' u, HeapKnowledge.Holds out0 (push u ρ) h' ∧ h' = h ∧
          ((tagHolds .truthy (ρ x) = true ∧ u = .fls) ∨ (tagHolds .truthy (ρ x) = false ∧ u = .tru)) →
          HeapKnowledge.Holds { out0 with
            elems := out0.elems ++ PromiseCalls.negatedAtoms k x
            indices := out0.indices ++ PromiseCalls.negatedIndices k x } (push u ρ) h' := by
        intro h' u hq
        obtain ⟨hq, rfl, hu⟩ := hq
        exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, fun a ha hc => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hq.2.2.2.2.1 a ha hc
          · exact PromiseCalls.negatedAtoms_holds hk hu a ha hc, fun a ha hc => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hq.2.2.2.2.2 a ha hc
          · exact PromiseCalls.negatedIndices_holds hk hu a ha hc⟩
      rcases hterm.1 with ht | ht
      · have hinst : instantiate 0 ρ j.term = .ite (ρ x) .fls .tru := by
          rw [ht]; simp [instantiate]
        rw [hinst] at hs ⊢
        exact HeapObservations.weaken (fun h' u hq =>
          finish h' u ⟨hq.1, hq.2.1, PromiseCalls.negation_bool hq.2.2⟩) (PromiseCalls.negation_run hxv hs)
      · have hinst : instantiate 0 ρ j.term = .ite (.test .truthy (ρ x)) .fls .tru := by
          rw [ht]; simp [instantiate]
        rw [hinst] at hs ⊢
        exact HeapObservations.weaken (fun h' u hq => finish h' u hq) (PromiseCalls.negation_test_run hxv hs)
    · exact base.sound hc hcodes hsums he hk hw hh


/-- A checker whose ordinary steps that are calls keeping the heap keep every
heap fact of their entry (`PromiseCalls.keepsCall`); every other step is
`base`'s. -/
@[nospecialize] def Checker.keepingCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    if PromiseCalls.keepsCall G images j e codes sums then pure (HeapKnowledge.shift k) else base.run j k e codes sums
  select := fun j k e codes sums =>
    if PromiseCalls.keepsCall G images j e codes sums then pure (HeapKnowledge.shift k) else base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i hkeep
      cases hc
      exact PromiseCalls.keepsCall_sound hkeep hcodes hsums he hk hw hh
    · exact base.sound hc hcodes hsums he hk hw hh

/-- A checker whose ordinary steps that are calls keeping the heap and
allocating their result keep every heap fact of their entry and separate the
result from the context's contract fields (`PromiseCalls.freshCall`); every
other step is `base`'s. -/
@[nospecialize] def Checker.allocatingCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    if PromiseCalls.freshCall G images j e codes sums then pure (PromiseCalls.freshOutput G j.context k)
    else base.run j k e codes sums
  select := fun j k e codes sums =>
    if PromiseCalls.freshCall G images j e codes sums then pure (PromiseCalls.freshOutput G j.context k)
    else base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i hfresh
      cases hc
      exact PromiseCalls.freshCall_sound hfresh hcodes hsums he hk hw hh
    · exact base.sound hc hcodes hsums he hk hw hh

/-- A checker whose ordinary steps that are calls changing only their
receiver's own locations keep the heap facts separated from them
(`PromiseCalls.ownCall`); every other step is `base`'s. -/
@[nospecialize] def Checker.keepingOwnCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.ownCall G images j e codes sums with
    | some i => pure (PromiseCalls.ownOutput k i)
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.ownCall G images j e codes sums with
    | some i => pure (PromiseCalls.ownOutput k i)
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i i hown
      cases hc
      exact PromiseCalls.ownCall_sound hown hcodes hsums he hk hw hh
    · exact base.sound hc hcodes hsums he hk hw hh

/-- A checker whose ordinary steps that are calls promising their receiver's
elements add that atom (`PromiseCalls.elementsCall`); every other step is
`base`'s. -/
@[nospecialize] def Checker.elementCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.elementsCall G images j e codes sums with
    | some (x, R) => pure (PromiseCalls.elementsOutput k x R)
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.elementsCall G images j e codes sums with
    | some (x, R) => pure (PromiseCalls.elementsOutput k x R)
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i x R hel
      cases hc
      exact PromiseCalls.elementsCall_sound hel hcodes hsums he hk hw hh
    · exact base.sound hc hcodes hsums he hk hw hh

/-- A checker whose ordinary steps that are calls at a precondition on their
receiver's elements are checked against the entry's atoms
(`PromiseCalls.requiresCall`); every other step is `base`'s. -/
@[nospecialize] def Checker.requiringCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    if PromiseCalls.requiresCall G images j k e codes sums then pure (PromiseCalls.requiresOutput e k)
    else base.run j k e codes sums
  select := fun j k e codes sums =>
    if PromiseCalls.requiresCall G images j k e codes sums then pure (PromiseCalls.requiresOutput e k)
    else base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i hreq
      cases hc
      exact PromiseCalls.requiresCall_sound hreq hcodes hsums he hk hw hh
    · exact base.sound hc hcodes hsums he hk hw hh

/-- The steps' rules, a call keeping the heap keeping every heap fact, a call
allocating its result separating it, a call changing only its receiver's own
locations keeping the facts separated from them, the index atoms a step
states and the write at a checked index (`IndexWrites`), each keeping its
input's stable links. -/
@[nospecialize] def Checker.ordinary [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) : Checker G images :=
  (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.negatingSlots
    |>.indexing.boundedWrites.keepingStable

end Verification.HeapExpressionRules
