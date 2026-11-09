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
          if s.receiver = jr.type ∧ s.arguments = jas.map Sequent.type ∧ s.effect.requires = none ∧
              s.effect.pre = [] then
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
theorem keepsHeap_prefix {e : Effect} (hk : keepsHeap e = true) {r : Tm} {args : List Tm} {before after : Heap} {v}
    (hp : e.post r args before after v) : before.IsPrefix after := by
  simp only [keepsHeap, Bool.and_eq_true, Bool.not_eq_true'] at hk
  exact Footprints.Closed.holds_empty.mp ((CallEffects.Effect.within_holds hp.1 hk.1.2 hk.2).mono hk.1.1)

theorem promiseOutput_holds {effect : Effect} {k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap}
    {r : Tm} {args : List Tm} {v} (hk : HeapKnowledge.Holds k ρ h) (hp : effect.post r args h h' v) :
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
  obtain ⟨hrecv, hargsig, hreq, hpre⟩ := hsig
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
      (CallEffects.Effect.requires_none hreq hpre _ _ _)
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
    k.links.filter (fun g => g.alias || HeapSeparation.apartAll k.separation i g.cell g.field), k.separation, [],
    HeapKnowledge.keptIndices HeapKnowledge.Changes.top (fun s g => HeapSeparation.apartAll k.separation i s (.str g))
      k.indices⟩

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
  refine ⟨?_, hk.2.1, ?_, hk.2.2.2.1, HeapKnowledge.elemsHolds_nil _ _,
    HeapKnowledge.keptIndices_holds hk.2.2.2.2.2
      (HeapKnowledge.Changes.top_holds h h')
      (fun s g fs cd o l v hap hs hl hv => hkeep l (away hap hs hl) v hv)⟩
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
              have hel := hq.2.2.2.1 _ hR' hv
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

/-- The slots a list of terms names, where each is a slot. -/
def varSlots : List Tm → Option (List Nat)
  | [] => some []
  | .var a :: t => (varSlots t).map (a :: ·)
  | _ :: _ => none

theorem varSlots_get {args : List Tm} {as : List Nat} (h : varSlots args = some as) (ρ : Env) :
    as.length = args.length ∧ ∀ q < as.length, (args.map (instantiate 0 ρ)).getD q .undef = ρ (as.getD q 0) := by
  induction args generalizing as with
  | nil => simp only [varSlots, Option.some.injEq] at h; subst h; simp
  | cons t rest ih =>
    cases t <;> simp only [varSlots, Option.map_eq_some_iff, reduceCtorEq] at h
    rename_i a
    obtain ⟨bs, hbs, rfl⟩ := h
    obtain ⟨hl, hg⟩ := ih hbs
    refine ⟨by simp [hl], fun q hq => ?_⟩
    cases q with
    | zero => simp [instantiate]
    | succ q => simpa using hg q (by simpa using hq)

/-- The slots a call's positions hold: its receiver's, then its actuals', each
a slot (`CallEffects.callEnv`'s positions); and whether the receiver is a
slot. A receiver that is no slot, such as the `undefined` of a plain
function's call, holds position `0` at slot `0`, which a precondition then
may not name. -/
def callSlots : Tm → Option (Bool × List Nat)
  | .invoke _ (.var r) args => (varSlots args).map fun as => (true, r :: as)
  | .invoke _ _ args => (varSlots args).map fun as => (false, 0 :: as)
  -- A construction's receiver is `undefined` (`ExpressionEffects.receiverOf`).
  | .construct _ args => (varSlots args).map fun as => (false, 0 :: as)
  | _ => none

theorem callSlots_env {t : Tm} {recv : Bool} {slots : List Nat} (hs : callSlots t = some (recv, slots)) (ρ : Env) :
    ∀ p < slots.length, (p ≠ 0 ∨ recv = true) → PointClaims.mapEnv (some slots) ρ p =
      CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ t))
        (ExpressionEffects.actualsOf (instantiate 0 ρ t)) p := by
  intro p hp hrecv
  cases t <;> simp only [callSlots, reduceCtorEq] at hs
  case construct f args =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs
    obtain ⟨as, has, rfl, rfl⟩ := hs
    cases p with
    | zero => simp at hrecv
    | succ q =>
      obtain ⟨hl, hg⟩ := varSlots_get has ρ
      simp only [List.length_cons] at hp
      simp only [PointClaims.mapEnv, PointClaims.slot, ExpressionEffects.actualsOf, instantiate,
        instantiateArgs_eq_map, CallEffects.callEnv, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
        List.getElem?_cons_succ]
      rw [hg q (by omega)]
      simp [List.getD_eq_getElem?_getD]
  rename_i f r args
  have core : ∀ (as : List Nat), varSlots args = some as → ∀ (y : Nat) (q : Nat), q + 1 < (y :: as).length →
      PointClaims.mapEnv (some (y :: as)) ρ (q + 1) =
        CallEffects.callEnv (ExpressionEffects.receiverOf (instantiate 0 ρ (.invoke f r args)))
          (ExpressionEffects.actualsOf (instantiate 0 ρ (.invoke f r args))) (q + 1) := by
    intro as has y q hq
    obtain ⟨hl, hg⟩ := varSlots_get has ρ
    simp only [List.length_cons] at hq
    simp only [PointClaims.mapEnv, PointClaims.slot, ExpressionEffects.actualsOf, instantiate,
      instantiateArgs_eq_map, CallEffects.callEnv, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
      List.getElem?_cons_succ]
    rw [hg q (by omega)]
    simp [List.getD_eq_getElem?_getD]
  cases r <;> simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs
  case var x =>
    obtain ⟨as, has, -, rfl⟩ := hs
    cases p with
    | zero => simp [PointClaims.mapEnv, PointClaims.slot, ExpressionEffects.receiverOf, instantiate,
        CallEffects.callEnv]
    | succ q => exact core as has x q hp
  all_goals
    obtain ⟨as, has, rfl, rfl⟩ := hs
    cases p with
    | zero => simp at hrecv
    | succ q => exact core as has 0 q hp

/-- Whether a derivation is a call `call-requires` applies to: the local call
rule at a selected signature stating a precondition, its operands values, its
premises' derivations checked; the elements precondition's atom on its
receiver slot, and each fact of the precondition on the call's values
following from the knowledge at the slots its positions hold. -/
def preconditionHolds (k : HeapKnowledge.Knowledge) (eff : Effect) (t : Tm) : Bool :=
  (eff.requires.isSome || !eff.pre.isEmpty) &&
  (match eff.requires with
    | none => true
    | some R => match receiverSlot t with
      | some x => atomFor k x R
      | none => false) &&
  (eff.pre.isEmpty || match callSlots t with
    | some (recv, slots) => eff.pre.all (fun F => F.slots.all fun p => p < slots.length && (p != 0 || recv)) &&
        HeapKnowledge.indicesCheckWith (HeapKnowledge.guardTags k) (HeapLinks.aliases k.links) k.links k.indices
          (eff.pre.map fun F => ⟨F, none, false⟩) (some slots)
    | none => false)

theorem preconditionHolds_sound {k : HeapKnowledge.Knowledge} {eff : Effect} {t : Tm} {ρ h}
    (hc : preconditionHolds k eff t = true) (hk : HeapKnowledge.Holds k ρ h) :
    eff.Requires (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h := by
  simp only [preconditionHolds, Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨-, hreq⟩, hpre⟩ := hc
  refine ⟨fun R hR => ?_, fun F hF => ?_⟩
  · rw [hR] at hreq
    simp only at hreq
    split at hreq
    · rename_i x hx
      obtain ⟨f, args, hterm⟩ := receiverSlot_term hx
      rw [hterm]
      simpa [ExpressionEffects.receiverOf, instantiate] using atomFor_sound hreq hk
    · cases hreq
  · rcases hpre with hnil | hpre
    · simp only [List.isEmpty_iff] at hnil; rw [hnil] at hF; cases hF
    · split at hpre
      · rename_i recv slots hs
        simp only [Bool.and_eq_true, List.all_eq_true] at hpre
        obtain ⟨hin, hchk⟩ := hpre
        have hheld := HeapKnowledge.indicesCheckWith_sound (HeapKnowledge.guardTags_sound hk)
          (fun x y hy => HeapLinks.aliases_eq hk.2.2.1 hy) hk.2.2.1 hchk
          hk.2.2.2.2.2 ⟨F, none, false⟩ (List.mem_map_of_mem hF) (fun b hb => by cases hb)
        refine (HeapKnowledge.IndexFact.holdsAt_congr fun s hs' => ?_).mp hheld
        have hp := hin F hF s hs'
        simp only [decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hp
        exact callSlots_env hs ρ s hp.1 hp.2
      · simp at hpre

@[nospecialize] def requiresApp (G : NormalGraph ι) (images : InstanceImageCheck G)
    (k : HeapKnowledge.Knowledge) (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) :
    Evidence ι → Bool
  | .node j (.app eff) ps =>
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.app eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    preconditionHolds k eff j.term
  -- A construction at a construct signature stating a precondition, alike.
  | .node j (.construct eff) ps =>
    (ps.all fun p => ExpressionEffects.valueTerm (claim p).term && checkScope (claim p).context.length (claim p).term) &&
    decide (LocalUsing G images j (.construct eff) (ps.map claim) codes (sums := sums) (allowRequires := true)) &&
    ps.attach.all (fun p => checkTreeUsing G images p.val codes sums) &&
    preconditionHolds k eff j.term
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
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he ⊢
      have hq := preconditionHolds_sound hreq hk (ρ := ρ)
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
  | construct eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he ⊢
      have hq := preconditionHolds_sound hreq hk (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact (ExpressionEffects.construct_local_requires_sound hl typed values he hw hh hq).post
  | _ => simp [requiresApp] at hc

/-- `call-requires` also bounds the heap a throw leaves, where its signature
states so (`excPost`). -/
theorem requiresApp_sound_exc {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) {eff : Effect}
    (hsel : ExpressionEffects.selectedEffect p = some eff) {ρ n W h} (he : EnvOk G (claim p).context ρ n W)
    (hk : HeapKnowledge.Holds k ρ h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G (claim p).type)
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h)
      (eff.excPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he ⊢
      have hq := preconditionHolds_sound hreq hk (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact ExpressionEffects.call_local_sound hl typed values he hw hh hq
  | construct eff' =>
      simp only [ExpressionEffects.selectedEffect, Option.some.injEq] at hsel
      subst hsel
      simp only [requiresApp, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hvals, hl⟩, ht⟩, hreq⟩ := hc
      simp only [claim] at he ⊢
      have hq := preconditionHolds_sound hreq hk (ρ := ρ)
      have typed : ∀ p ∈ ps.map claim, HasTyUsing G images p.context p.term p.type := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact checkTreeUsing_sound q (List.all_eq_true.mp ht ⟨q, hq⟩ (List.mem_attach _ _)) hcodes hsums
      have values : ∀ p ∈ ps.map claim, ExpressionEffects.valueTerm p.term = true ∧
          checkScope p.context.length p.term = true := by
        intro p hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp hvals q hq
      exact ExpressionEffects.construct_local_requires_sound hl typed values he hw hh hq
  | _ => simp [requiresApp] at hc

theorem requiresApp_selected {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (p : Evidence ι) (hc : requiresApp G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff := by
  obtain ⟨j, r, ps⟩ := p
  cases r with
  | app eff' => exact ⟨_, rfl⟩
  | construct eff' => exact ⟨_, rfl⟩
  | _ => simp [requiresApp] at hc

theorem requiresTree_sound {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresTree G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff ∧ ∀ {ρ n W h}, EnvOk G (claim p).context ρ n W →
    HeapKnowledge.Holds k ρ h → WorldAdm W → HeapOk n W h →
    SafePost (excOf G) (meaning G (claim p).type)
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h) n W h
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

theorem requiresTree_sound_exc {G : NormalGraph ι} {images : InstanceImageCheck G}
    {k : HeapKnowledge.Knowledge} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (p : Evidence ι) (hc : requiresTree G images k codes sums p = true) :
    ∃ eff, ExpressionEffects.selectedEffect p = some eff ∧ ∀ {ρ n W h}, EnvOk G (claim p).context ρ n W →
    HeapKnowledge.Holds k ρ h → WorldAdm W → HeapOk n W h →
    SafePostExc (excOf G) (meaning G (claim p).type)
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ (claim p).term)) h)
      (eff.excPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim p).term)) h) n W h
      (instantiate 0 ρ (claim p).term) := by
  by_cases hs : ∃ j c q, p = .node j (.sub c) [q]
  · obtain ⟨j, c, q, rfl⟩ := hs
    simp only [requiresTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, hc⟩ := hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected q hc
    refine ⟨eff, by simpa [ExpressionEffects.selectedEffect] using hsel, fun {ρ n W h} he hk hw hh => ?_⟩
    obtain ⟨hctx, hterm, hsub⟩ := hl
    have ih := requiresApp_sound_exc hcodes hsums q hc hsel (ρ := ρ) (n := n) (W := W) (h := h)
      (by rw [hctx]; exact he) hk hw hh
    rw [hterm] at ih
    exact SafePostExc.consequence_below' (fun _ _ _ _ hv => hv)
      (fun j _ W v hv => PositiveCertificates.acceptedUsing hsub j W v hv) (fun _ _ hp => hp) (fun _ hp => hp) ih
  · have happ : requiresApp G images k codes sums p = true := by
      obtain ⟨j, r, ps⟩ := p
      cases r <;> try (simpa [requiresTree] using hc)
      rcases ps with _ | ⟨q, _ | ⟨q', qs⟩⟩
      · simpa [requiresTree] using hc
      · exact absurd ⟨j, _, q, rfl⟩ hs
      · simpa [requiresTree] using hc
    obtain ⟨eff, hsel⟩ := requiresApp_selected p happ
    exact ⟨eff, hsel, fun he hk hw hh => requiresApp_sound_exc hcodes hsums p happ hsel he hk hw hh⟩

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

/-! ### A call stating a postcondition (PROGRAM-TYPING.md, "Reads below the length")

A call whose selected signature states a postcondition (`Effect.ensures`)
returns normally in a heap where each holds at the return's positions: the
result, and the call's receiver and actuals. Renamed to the slots after the
return, the result's slot `0` and each position's slot one higher, each fact
naming slots alone is an atom of the knowledge after the call (`call-ensures`). -/

/-- The slot after a return that a return's position names, where a slot holds
it: `0` the result; `p + 1` the call's position `p`, held by the slot `slots`
gives it, one higher past the result; a receiver that is no slot holds none. -/
def ensuresSlot (recv : Bool) (slots : List Nat) : Nat → Option Nat
  | 0 => some 0
  | p + 1 => if p < slots.length ∧ (p ≠ 0 ∨ recv = true) then some (PointClaims.slot (some slots) p + 1) else none

/-- The atoms a normal return of the call `t` at `eff` states, at the slots
after the return: each result fact every position of which a slot holds,
renamed (`call-ensures`). -/
def ensuresAtoms (eff : Effect) (t : Tm) : List HeapKnowledge.IndexAtom :=
  match callSlots t with
  | some (recv, slots) => HeapKnowledge.mapIndices (ensuresSlot recv slots) (eff.ensures.map fun F => { fact := F })
  | none => []

theorem ensuresAtoms_holds {eff : Effect} {t : Tm} {ρ : Env} {h' : Heap} {v : Tm}
    (hp : ∀ F ∈ eff.ensures, F.HoldsAt (CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h') :
    HeapKnowledge.IndexHolds (ensuresAtoms eff t) (push v ρ) h' := by
  unfold ensuresAtoms
  split
  · rename_i recv slots hs
    refine HeapKnowledge.mapIndices_holds (ρ := CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t))) (fun s t' hst => ?_) ?_
    · cases s with
      | zero =>
        simp only [ensuresSlot, Option.some.injEq] at hst
        subst hst
        rfl
      | succ p =>
        simp only [ensuresSlot] at hst
        split at hst
        · rename_i hc
          simp only [Option.some.injEq] at hst
          subst hst
          have he := callSlots_env hs ρ p hc.1 hc.2
          simp only [PointClaims.mapEnv] at he
          simp only [push, CallEffects.ensuresEnv, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          exact he
        · cases hst
    · intro a ha _
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
      exact hp F hF
  · exact HeapKnowledge.indexHolds_nil _ _

/-- The change of a call growing its receiver's store (`ReceiverGrows`):
no object or number altered, every store grown. -/
def growChanges : HeapKnowledge.Changes := ⟨false, false, .grow⟩

theorem receiverGrows_changes {r : Tm} {h h' : Heap} (hg : CallEffects.ReceiverGrows r h h') :
    growChanges.Holds h h' := by
  refine ⟨fun l v hv ha => ?_, fun hs => by simp [growChanges] at hs, fun _ l ls hls => ?_⟩
  · rcases hg l v hv with hk | ⟨-, ls, ls', rfl, -⟩
    · exact hk
    · simp [growChanges, HeapKnowledge.Changes.alters] at ha
  · rcases hg l _ hls with hk | ⟨-, ls₀, ls', he, hls', hle, hmax⟩
    · exact ⟨ls, hk, Nat.le_refl _, id⟩
    · cases he; exact ⟨ls', hls', hle.length_le, fun _ => hmax⟩

/-- The locations a call growing the receiver slot `i`'s store keeps beside
every object and number: each field of a slot a separation fact keeps apart
from every own location of `i`, or from `i`'s store field, in either
orientation. -/
def growFirst (k : HeapKnowledge.Knowledge) (t : Tm) : Nat → String → Bool :=
  match receiverSlot t with
  | some i => fun s g => HeapSeparation.apartAll k.separation i s (.str g) ||
      HeapSeparation.apart k.separation i arrayStoreKey s (.str g) ||
      (g == "[]" && IndexWrites.apartFrom k i s)
  | none => fun _ _ => false

theorem growFirst_kept {k : HeapKnowledge.Knowledge} {t : Tm} {ρ : Env} {h h' : Heap}
    (hk : HeapKnowledge.Holds k ρ h)
    (hg : CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h') :
    HeapKnowledge.FirstKept (growFirst k t) ρ h h' := by
  intro s g fs cd o l v hf hs hl hv
  cases hi : receiverSlot t with
  | none => simp [growFirst, hi] at hf
  | some i =>
    simp only [growFirst, hi, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨f, args, rfl⟩ := receiverSlot_term hi
    rcases hg l v hv with hk' | ⟨hst, -⟩
    · exact hk'
    · simp only [ExpressionEffects.receiverOf, instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero] at hst
      rcases hf with (hf | hf) | ⟨rfl, hf⟩
      case inl.inr =>
        -- A separation fact keeps the receiver's store field apart from the
        -- slot's field.
        cases hr : ρ i with
        | objAt flds' c' o' =>
          rw [hr] at hst
          exact absurd rfl (HeapSeparation.apart_sound hf hk.2.2.2.1 hr hst hs hl)
        | _ => rw [hr] at hst; simp [Footprints.storeOf, Footprints.fieldsOf] at hst
      case inr =>
        -- A region fact keeps the receiver's store cell apart from the
        -- store cell of the slot's array.
        obtain ⟨sa, xs, sb, ys, hra, hrb, hsep⟩ := IndexWrites.apartFrom_sound hf hk
        have hss : Footprints.storeOf (ρ s) = some l := by
          simpa [hs, Footprints.storeOf, Footprints.fieldsOf, arrayStoreKey] using hl
        rw [HeapKnowledge.regionOf_store hra hst] at hsep
        rw [HeapKnowledge.regionOf_store hrb hss] at hsep
        exact absurd rfl (hsep l (.inl rfl) l (.inl rfl))
      have hat : HeapSeparation.At none (ρ i) l := by
        cases hr : ρ i with
        | objAt flds' c' o' =>
          rw [hr] at hst
          simp only [HeapSeparation.At]
          exact Footprints.lookup_mem_snd hst
        | _ => rw [hr] at hst; simp [Footprints.storeOf, Footprints.fieldsOf] at hst
      exact absurd rfl (HeapSeparation.apartAll_sound hf hk.2.2.2.1 hat hs hl)

/-- The heap-reading atoms of a call's entry its footprint keeps, renamed past
the result (`Changes.ofClosed`, ARITHMETIC.md, "Linear facts"): with
`receiverGrows`, those `growChanges` keeps, a field apart from the receiver's
own locations kept besides (`growFirst`); none where its signature keeps the
heap, whose output keeps every atom (`call-keep`), or excepts its receiver's
store or own locations. -/
def effectKept (views : Nat → String → Bool) (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  if eff.receiverGrows then
    HeapKnowledge.shiftIndices (HeapKnowledge.keptIndices growChanges (growFirst k t)
      (k.indices.filter fun a => !a.fact.envOnly))
  else if keepsHeap eff || eff.receiverStore || eff.receiverOwn then [] else
  match eff.elementWrite with
  | some w => HeapKnowledge.shiftIndices (HeapKnowledge.keptIndicesWith w.changes (fun _ _ => false) views
      (k.indices.filter fun a => !a.fact.envOnly))
  | none =>
    HeapKnowledge.shiftIndices (HeapKnowledge.keptIndicesWith (HeapKnowledge.Changes.ofClosed eff.footprint)
      (fun _ _ => false) views (k.indices.filter fun a => !a.fact.envOnly))

theorem effectKept_holds {views : Nat → String → Bool} {eff : Effect} {t : Tm} {k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    (hk : HeapKnowledge.Holds k ρ h) (hw : eff.within (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hg : eff.receiverGrows = true →
      CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hew : ∀ w, eff.elementWrite = some w → w.Holds (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h')
    (hv : HeapKnowledge.ViewsKept views ρ h h') :
    HeapKnowledge.IndexHolds (effectKept views eff t k) (push v ρ) h' := by
  unfold effectKept
  split
  · rename_i hgr
    have hg := hg hgr
    exact HeapKnowledge.shiftIndices_holds (HeapKnowledge.keptIndices_holds
      (fun a ha hcd => hk.2.2.2.2.2 a (List.mem_filter.mp ha).1 hcd)
      (receiverGrows_changes hg) (growFirst_kept hk hg))
  · split
    · exact HeapKnowledge.indexHolds_nil _ _
    · rename_i hc
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
      obtain ⟨⟨-, hs⟩, ho⟩ := hc
      split
      · rename_i w hwr
        exact HeapKnowledge.shiftIndices_holds (HeapKnowledge.keptIndicesWith_holds
          (fun a ha hcd => hk.2.2.2.2.2 a (List.mem_filter.mp ha).1 hcd) (hew w hwr).1 HeapKnowledge.firstKept_none hv)
      · exact HeapKnowledge.shiftIndices_holds (HeapKnowledge.keptIndicesWith_holds
          (fun a ha hcd => hk.2.2.2.2.2 a (List.mem_filter.mp ha).1 hcd)
          (HeapKnowledge.Changes.ofClosed_holds (CallEffects.Effect.within_holds hw hs ho)) HeapKnowledge.firstKept_none hv)

/-! ### Quantified facts across a growth (ARITHMETIC.md, "Quantified clauses") -/

open HeapKnowledge in
/-- What a body variable denotes at an index a growth keeps: the index and
the element there, each the same, and each term kept or grown as the change
allows. -/
theorem boundValue_grown {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {r : Tm}
    {ls ls' : List (Option Nat)} (i : Nat)
    (hg : CallEffects.ReceiverGrows r h h') (hf : FirstKept first ρ h h') (hp : ls <+: ls') :
    (∀ x n, x.keptBy growChanges first = true → boundValue ρ h ls i x = some n →
      boundValue ρ h' ls' i x = some n) ∧
    (∀ x n, x.grownBy growChanges first = true → boundValue ρ h ls i x = some n →
      ∃ n', boundValue ρ h' ls' i x = some n' ∧ n ≤ n') := by
  have hc := receiverGrows_changes hg
  refine ⟨fun x n hk hx => ?_, fun x n hgx hx => ?_⟩
  · cases x with
    | index => exact hx
    | project _ _ | offset _ => simp [Bound.keptBy] at hk
    | free t => exact termValue_kept hc hf hk hx
    | elem =>
      simp only [boundValue, elementInt] at hx ⊢
      obtain ⟨t, rfl⟩ := hp
      split at hx
      · rename_i l hl
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1, hl]
        simp only [Option.bind_eq_some_iff] at hx ⊢
        obtain ⟨w, hw, hwn⟩ := hx
        rcases hg l w hw with hk' | ⟨-, ls0, -, rfl, -⟩
        · exact ⟨w, hk', hwn⟩
        · simp [intValue] at hwn
      · cases hx
  · cases x with
    | index | elem | project _ _ | offset _ => simp [Bound.grownBy] at hgx
    | free t => exact termValue_grown hc hf hgx hx

open HeapKnowledge in
/-- **A growth keeps a quantified fact whose bound and body it keeps**
(`every-grow`): the array its path reads is the same object, whose store is
the receiver's, extended with its old elements at their indices, or one the
growth keeps. -/
theorem every_grown {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {r : Tm}
    (hg : CallEffects.ReceiverGrows r h h') (hf : FirstKept first ρ h h')
    {s : Nat} {p : List String} {st : Term} {body : List (LinearClause Bound)}
    (hst : st.keptBy growChanges first = true) (hb : body.all (bodyKeptBy growChanges first) = true)
    (hF : (IndexFact.every s p st body).HoldsAt ρ h) : (IndexFact.every s p st body).HoldsAt ρ h' := by
  obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
  have hc := receiverGrows_changes hg
  have hwa : growChanges.alters w = false := by
    cases w <;> simp_all [elementsOf, Footprints.storeOf, Footprints.fieldsOf, growChanges, Changes.alters]
  obtain ⟨ls', hls', hp⟩ : ∃ ls', h'[sto]? = some (.arr ls') ∧ ls <+: ls' := by
    rcases hg sto _ hls with hk | ⟨-, ls0, ls', he, hls', hp, -⟩
    · exact ⟨ls, hk, List.prefix_refl ls⟩
    · cases he; exact ⟨ls', hls', hp⟩
  refine ⟨w, sto, ls', n, readPath_kept hc p (ρ s) w hw (Or.inr hwa) (fun _ => rfl), hsto, hls',
    termValue_kept hc hf hst hn, fun i hi F hF => ?_⟩
  obtain ⟨hk, hgr⟩ := boundValue_grown i hg hf hp
  exact LinearClause.holdsAt_monotone hk hgr (List.all_eq_true.mp hb F hF) (hall i hi F hF)

/-- What a body variable of a quantified fact over the slot `i`'s array
denotes at the value of the slot `a` appended to it: the index its old
length, the element the slot's value, a term itself. -/
def appendTerm (i a : Nat) : HeapKnowledge.Bound → HeapKnowledge.Term
  | .index => .length i
  | .elem => .value a
  | .offset _ => .value a
  | .project k p => ⟨k, a, p⟩
  | .free t => t

open HeapKnowledge in
/-- **An append extends a quantified fact over the receiver's array by the
appended value** (`every-push`): where the slot `x`'s value, a safe integer,
is appended to the slot `i`'s array, the fact over its whole length holds
after it where each body fact holds of the value at the old length, and the
growth keeps each body fact. -/
theorem every_appended {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {i x : Nat}
    (hg : CallEffects.ReceiverGrows (ρ i) h h') (ha : CallEffects.ReceiverAppends (ρ i) [ρ x] h h')
    (hf : FirstKept first ρ h h') (hx : (intValue (ρ x)).isSome)
    {body : List (LinearClause Bound)} (hb : body.all (bodyKeptBy growChanges first) = true)
    (hnew : ∀ F ∈ body, F.HoldsAt (fun b => termValue ρ h (appendTerm i x b)))
    (hF : (IndexFact.every i [] (.length i) body).HoldsAt ρ h) :
    (IndexFact.every i [] (.length i) body).HoldsAt ρ h' := by
  obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
  simp only [readPath, Option.some.injEq] at hw
  subst hw
  simp only [termValue_length] at hn
  obtain ⟨sto2, ls2, hs2, hls2, rfl, -⟩ := lengthOf_store hn
  rw [elementsOf_store hs2] at hsto
  cases hsto
  rw [hls2] at hls
  cases hls
  have hvx : isVal (ρ x) = true := by
    obtain ⟨b, hb, -⟩ := intValue_safe (Option.get_mem hx)
    rw [hb]; rfl
  obtain ⟨ls', hls', hlen, hel⟩ := ha (by simpa using hvx) sto ls hs2 hls2
  obtain ⟨l, hl, hlv, -⟩ := hel 0 (ρ x) rfl
  obtain ⟨hp, hmax⟩ : ls <+: ls' ∧ ls'.length ≤ maxArrayLength := by
    rcases hg sto _ hls2 with hk | ⟨-, ls0, ls1, he, hls1, hp, hm⟩
    · rw [hk] at hls'; cases hls'; simp at hlen
    · cases he; rw [hls1] at hls'; cases hls'; exact ⟨hp, hm⟩
  refine ⟨ρ i, sto, ls', ls'.length, rfl, elementsOf_store hs2, hls', ?_, fun j hj F hF => ?_⟩
  · simp only [termValue_length]; exact lengthOf_of_store hs2 hls' hmax
  obtain ⟨hk, hgr⟩ := boundValue_grown j hg hf hp
  have hbF := List.all_eq_true.mp hb F hF
  by_cases hj' : j < ls.length
  · exact LinearClause.holdsAt_monotone hk hgr hbF (hall j (by exact_mod_cast hj') F hF)
  · have hjl : j = ls.length := by simp only [List.length_singleton] at hlen; omega
    subst hjl
    have hc := receiverGrows_changes hg
    refine LinearClause.holdsAt_monotone (val := fun b => termValue ρ h (appendTerm i x b)) (fun y n hky hy => ?_)
      (fun y n hgy hy => ?_) hbF (hnew F hF)
    · cases y with
      | index =>
        simp only [appendTerm, termValue_length, hn, Option.some.injEq] at hy
        rw [← hy]; rfl
      | elem =>
        simp only [appendTerm, termValue_value] at hy
        simp only [Nat.add_zero] at hl
        simp only [boundValue, elementInt, hl, hlv, Option.bind_some, hy]
      | project _ _ | offset _ => simp [Bound.keptBy] at hky
      | free t => exact termValue_kept hc hf hky hy
    · cases y with
      | index | elem | project _ _ | offset _ => simp [Bound.grownBy] at hgy
      | free t => exact termValue_grown hc hf hgy hy

open HeapKnowledge in
/-- Whether the atoms `as` state a body fact of the value of the slot `a`
appended to the slot `i`'s array: the fact with the index read as the
array's old length and the element as the slot's value, each of its terms
but that length defined. -/
def appendedBody (as : List IndexAtom) (i a : Nat) : LinearClause Bound → Bool
  | .either _ _ => false
  | .atom F => match F.mapVars (some ∘ appendTerm i a) with
    | some G => G.vars.all (fun t => t == Term.length i || termDefined as t) && entailsKnown as G
    | none => false

open HeapKnowledge in
theorem appendedBody_sound {as : List IndexAtom} {ρ : Env} {h : Heap} {i a : Nat}
    (he : IndexHolds as ρ h) (hlen : (termValue ρ h (Term.length i)).isSome) {F : LinearClause Bound}
    (hF : appendedBody as i a F = true) : F.HoldsAt (fun b => termValue ρ h (appendTerm i a b)) := by
  cases F with
  | either A B => cases hF
  | atom F =>
    simp only [appendedBody] at hF
    cases hG : F.mapVars (some ∘ appendTerm i a) with
    | some G =>
      rw [hG] at hF
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hF
      obtain ⟨hd, hent⟩ := hF
      refine (factAt_mapVars (val' := termValue ρ h) hG fun y _ t ht => ?_).mp
        ⟨fun t ht => ?_, entailsKnown_sound he hent⟩
      · simp only [Function.comp_apply, Option.some.injEq] at ht
        rw [← ht]
      · rcases hd t ht with rfl | hdt
        · exact hlen
        · exact termDefined_sound he hdt
    | none => simp [hG] at hF

open HeapKnowledge in
/-- Whether a call growing its receiver's store keeps a quantified atom of
its entry `k`: each body fact kept by the growth (`bodyKeptBy`), and its
bound kept (`every-grow`) or, for the call `x.push(a)` of one actual a safe
integer, the fact over `x`'s whole array, each body fact stated of the value
at the old length (`every-push`). -/
def everyGrown (k : Knowledge) (t : Tm) (a : IndexAtom) : Bool :=
  match a.fact with
  | .every s p st body =>
    body.all (bodyKeptBy growChanges (growFirst k t)) &&
      (st.keptBy growChanges (growFirst k t) ||
        match t with
        | .invoke _ (.var i) [.var x] => s == i && p.isEmpty && st == Term.length i && intSlot k.indices x &&
            body.all (appendedBody k.indices i x)
        | _ => false)
  | _ => false

/-- The quantified atoms of a call's entry `k` its growth of its receiver's
store keeps or extends (`everyGrown`), renamed past the result; none of a call
growing nothing. -/
def appendKept (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  if eff.receiverGrows then HeapKnowledge.shiftIndices (k.indices.filter (everyGrown k t)) else []

open HeapKnowledge in
theorem appendKept_holds {eff : Effect} {t : Tm} {k : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    (hk : Holds k ρ h)
    (hg : eff.receiverGrows = true →
      CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h' ∧
      CallEffects.ReceiverAppends (ExpressionEffects.receiverOf (instantiate 0 ρ t))
        (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h') :
    IndexHolds (appendKept eff t k) (push v ρ) h' := by
  unfold appendKept
  split
  · rename_i hgr
    obtain ⟨hgrow, happ⟩ := hg hgr
    have hf := growFirst_kept hk hgrow
    refine shiftIndices_holds fun a ha hcd => ?_
    obtain ⟨ha, hkept⟩ := List.mem_filter.mp ha
    have hF := hk.2.2.2.2.2 a ha hcd
    unfold everyGrown at hkept
    split at hkept
    · rename_i s p st body hfa
      rw [hfa] at hF ⊢
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hkept
      obtain ⟨hb, hst | hpush⟩ := hkept
      · exact every_grown hgrow hf hst hb hF
      · split at hpush
        · rename_i f i x
          simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hpush
          obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hx⟩, hbody⟩ := hpush
          simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate, instantiateArgs,
            Nat.not_lt_zero, if_false, Nat.sub_zero] at hgrow happ hf
          have hlen : (termValue ρ h (Term.length s)).isSome := by
            obtain ⟨w, sto, ls, n, -, -, -, hn, -⟩ := hF
            rw [hn]; rfl
          exact every_appended hgrow happ hf (intSlot_sound hk.2.2.2.2.2 hx) hb
            (fun F hF' => appendedBody_sound hk.2.2.2.2.2 hlen (List.all_eq_true.mp hbody F hF')) hF
        · simp at hpush
    · cases hkept
  · exact indexHolds_nil _ _

open HeapKnowledge in
/-- Exact length on a normal append of value actuals. -/
theorem appended_length {ρ : Env} {h h' : Heap} {i : Nat} {args : List Tm} {n : Int}
    (hg : CallEffects.ReceiverGrows (ρ i) h h')
    (ha : CallEffects.ReceiverAppends (ρ i) args h h')
    (hv : ∀ a ∈ args, isVal a = true) (hn : termValue ρ h (.length i) = some n) :
    termValue ρ h' (.length i) = some (n + args.length) := by
  simp only [termValue_length] at hn ⊢
  obtain ⟨s, ls, hs, hls, rfl, hm⟩ := lengthOf_store hn
  obtain ⟨ls', hls', hlen, -⟩ := ha hv s ls hs hls
  have hm' : ls'.length ≤ maxArrayLength := by
    rcases hg s _ hls with hk | ⟨-, ls0, ls1, he, hls1, -, hmax⟩
    · rw [hk] at hls'; cases hls'; exact hm
    · cases he; rw [hls1] at hls'; cases hls'; exact hmax
  have hl := lengthOf_of_store hs hls' hm'
  simpa [hlen] using hl

open HeapKnowledge in
/-- The change of a term: the receiver's length grows by the actual count. -/
def appendDelta (i count : Nat) (t : Term) : Int :=
  if t == Term.length i then count else 0

open HeapKnowledge in
def appendFact (i count : Nat) : Linear.Fact Term → Linear.Fact Term
  | .le F d => .le F (d + Linear.Form.eval (appendDelta i count) F)
  | .ne F d => .ne F (d + Linear.Form.eval (appendDelta i count) F)

open HeapKnowledge in
/-- A linear fact translated by the exact change of its terms. -/
theorem append_fact_holds {i count : Nat} {ρ : Env} {h h' : Heap} {F : Linear.Fact Term}
    (terms : ∀ t ∈ F.vars, ∀ n, termValue ρ h t = some n →
      termValue ρ h' t = some (n + appendDelta i count t))
    (hF : (IndexFact.linear F).HoldsAt ρ h) :
    (IndexFact.linear (appendFact i count F)).HoldsAt ρ h' := by
  obtain ⟨hd, hF⟩ := hF
  have hd' : ∀ t ∈ F.vars, (termValue ρ h' t).isSome := by
    intro t ht
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd t ht)
    simp [terms t ht n hn]
  have eval : ∀ G : Linear.Form Term, (∀ t ∈ G.map (·.1), t ∈ F.vars) →
      Linear.Form.eval (termValuation ρ h') G =
        Linear.Form.eval (termValuation ρ h) G + Linear.Form.eval (appendDelta i count) G := by
    intro G
    induction G with
    | nil => intro _; simp [Linear.Form.eval]
    | cons tc G ih =>
      obtain ⟨t,c⟩ := tc
      intro hm
      have ht := hm t (by simp)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd t ht)
      have hn' := terms t ht n hn
      have hi := ih (fun t ht => hm t (by simp [ht]))
      simp only [Linear.Form.eval, termValuation, hn, hn', Option.getD_some, Int.mul_add, hi]
      omega
  cases F with
  | le G d =>
    refine ⟨hd', ?_⟩
    have he := eval G (fun _ ht => ht)
    simp only [appendFact, Linear.Fact.Holds] at hF ⊢
    omega
  | ne G d =>
    refine ⟨hd', ?_⟩
    have he := eval G (fun _ ht => ht)
    simp only [appendFact, Linear.Fact.Holds] at hF ⊢
    omega


open HeapKnowledge in
def linearAppended (i count : Nat) (first : Nat → String → Bool) (a : IndexAtom) : Option IndexAtom :=
  match a.cond, a.fact with
  | none, .linear F =>
    if F.vars.all (fun t => t == Term.length i || t.keptBy growChanges first) then
      some { fact := .linear (appendFact i count F) }
    else none
  | _, _ => none

open HeapKnowledge in
def linearAppendKept (n : Nat) (eff : Effect) (t : Tm) (k : Knowledge) : List IndexAtom :=
  match t with
  | .invoke _ (.var i) args =>
    if eff.receiverGrows && IndexWrites.appendSlots n args then
      shiftIndices (k.indices.filterMap (linearAppended i args.length (growFirst k t)) ++
        if termDefined k.indices (.length i) then
          [{ fact := .linear (.le [(.length i, -1)] (-(args.length : Int))) }] else []) else []
  | _ => []

open HeapKnowledge in
theorem linearAppendKept_holds {n : Nat} {eff : Effect} {t : Tm} {k : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    (hv : ∀ i, i < n → isVal (ρ i) = true) (hk : Holds k ρ h)
    (hg : eff.receiverGrows = true →
      CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h' ∧
      CallEffects.ReceiverAppends (ExpressionEffects.receiverOf (instantiate 0 ρ t))
        (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h') :
    IndexHolds (linearAppendKept n eff t k) (push v ρ) h' := by
  unfold linearAppendKept
  split
  · rename_i f i args
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨he, hs⟩ := hc
      obtain ⟨hgrow, happ⟩ := hg he
      have hf := growFirst_kept hk hgrow
      simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate, Nat.not_lt_zero,
        if_false, Nat.sub_zero] at hgrow happ
      refine shiftIndices_holds fun a ha _ => ?_
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
        unfold linearAppended at hab
        split at hab
        · rename_i F hcond hfact
          split at hab
          · rename_i hvars
            cases hab
            apply append_fact_holds (fun t ht m hm => ?_)
              (by simpa [hfact] using hk.2.2.2.2.2 b hb (by simp [hcond]))
            rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hvars t ht) with heq | hkeep
            · have heq : t = Term.length i := of_decide_eq_true heq
              subst t
              have hl := appended_length hgrow happ (IndexWrites.appendSlots_values hv hs) hm
              simpa [appendDelta, instantiateArgs_eq_map] using hl
            · by_cases heq : t = Term.length i
              · subst t
                have hl := appended_length hgrow happ (IndexWrites.appendSlots_values hv hs) hm
                simpa [appendDelta, instantiateArgs_eq_map] using hl
              · simpa [appendDelta, heq] using termValue_kept (receiverGrows_changes hgrow) hf hkeep hm
          · cases hab
        · cases hab
      · split at ha
        · rename_i hd
          simp only [List.mem_singleton] at ha
          subst ha
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (termDefined_sound hk.2.2.2.2.2 hd)
          have hl := appended_length hgrow happ (IndexWrites.appendSlots_values hv hs) hm
          have hm0 : 0 ≤ m := by
            obtain ⟨_, ls, _, _, rfl, _⟩ := lengthOf_store hm
            omega
          simp only [instantiateArgs_eq_map, List.length_map] at hl
          have hv' : termValuation ρ h' (.length i) = m + args.length := by simp [termValuation, hl]
          refine ⟨?_, ?_⟩
          · intro t ht
            simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_singleton] at ht
            subst ht
            simp [hl]
          · simp only [Linear.Fact.Holds, Linear.Form.eval, hv']
            omega
        · cases ha
    · exact indexHolds_nil _ _
  · exact indexHolds_nil _ _

/-! ### Quantified facts across a typed array's element write (ARITHMETIC.md, "Quantified clauses") -/

/-- The change of a typed array's element write: stores keep their lengths,
nothing else changes. -/
def writeChanges : HeapKnowledge.Changes := CallEffects.ElementWrite.changes .exact

open HeapKnowledge in
/-- Whether the atoms `as` state a body fact of the value of the slot `x`
written at the index the slot `i` holds: the fact with the index read as `i`
and the element as `x`, each term defined and kept by the write. -/
def writtenBody (as : List IndexAtom) (i x : Nat) : LinearClause Bound → Bool
  | .either _ _ => false
  | .atom F => (F.vars.all fun v => match v with | .offset _ => false | _ => true) &&
    match F.mapVars (some ∘ Bound.inst i x) with
    | some G => G.vars.all (fun t => termDefined as t && t.keptBy writeChanges (fun _ _ => false)) && entailsKnown as G
    | none => false

open HeapKnowledge in
/-- Whether an exact write `b[i] = x` of a typed array keeps a quantified
atom of its entry `k` (`every-write`): over the view of `b`'s class, its path
empty, its bound and body kept by the write, and the index at or past the
bound, or each body fact stated of `x` at `i`. -/
def everyWritten (k : Knowledge) (b i x : Nat) (a : IndexAtom) : Bool :=
  match a.fact with
  | .every s [] st body =>
    (s == b || (HeapLinks.aliases k.links b).contains s) &&
      st.keptBy writeChanges (fun _ _ => false) && body.all (bodyKeptBy writeChanges (fun _ _ => false)) &&
      intSlot k.indices i &&
      (entailsKnown k.indices (.le [(st, 1), (.value i, -1)] 0) || body.all (writtenBody k.indices i x))
  | _ => false

open HeapKnowledge in
/-- A prefix ending at a known term after the written index. The old prefix
covers every smaller index, and the written value satisfies the body. -/
def writtenPrefix (k : Knowledge) (b i x : Nat) (a : IndexAtom) (next : Term) : Option IndexAtom :=
  match a.fact with
  | .every s [] st body =>
    if (s == b || (HeapLinks.aliases k.links b).contains s) &&
        termDefined k.indices next && next.keptBy writeChanges (fun _ _ => false) &&
        body.all (bodyKeptBy writeChanges (fun _ _ => false)) &&
        entailsKnown k.indices (.le [(next, 1), (.value i, -1)] 1) &&
        entailsKnown k.indices (.le [(.value i, 1), (st, -1)] 0) &&
        body.all (writtenBody k.indices i x)
    then some { a with fact := .every s [] next body } else none
  | _ => none

/-- The quantified atoms of a call's entry `k` an exact element write keeps
(`everyWritten`), renamed past the result; none of any other call. -/
def writeKept (eff : Effect) (t : Tm) (k : HeapKnowledge.Knowledge) : List HeapKnowledge.IndexAtom :=
  match eff.elementWrite, t with
  | some .exact, .invoke _ _ [.var b, .var i, .var x] =>
    let i := HeapKnowledge.pick (HeapLinks.aliases k.links) (HeapKnowledge.intSlot k.indices) i
    let x := HeapKnowledge.pick (HeapLinks.aliases k.links) (HeapKnowledge.intSlot k.indices) x
    HeapKnowledge.shiftIndices (k.indices.filter (everyWritten k b i x) ++
      (k.indices.filter fun a => match a.fact with | .every _ [] _ _ => true | _ => false).flatMap fun a =>
        (HeapKnowledge.definedTerms k.indices).eraseDups.filterMap fun next =>
          if HeapKnowledge.entailsKnown k.indices (.le [(.value i, 1), (next, -1)] (-1))
          then writtenPrefix k b i x a next else none)
  | _, _ => []

open HeapKnowledge in
/-- **An exact element write keeps a quantified fact over its view**
(`every-write`): each element at another index is the same location, holding
the same number; the element at the index is the written value, which meets
the body or lies past the bound. -/
theorem every_written {ρ : Env} {h h' : Heap} {b i x s : Nat} {st : Term} {body : List (LinearClause Bound)}
    {as : List IndexAtom} (he : IndexHolds as ρ h) (hs : ρ s = ρ b)
    (hc : writeChanges.Holds h h') (hx : CallEffects.ExactWrite [ρ b, ρ i, ρ x] h h')
    (hst : st.keptBy writeChanges (fun _ _ => false) = true)
    (hb : body.all (bodyKeptBy writeChanges (fun _ _ => false)) = true)
    (hnew : entailsKnown as (.le [(st, 1), (.value i, -1)] 0) = true ∨ body.all (writtenBody as i x) = true)
    (hF : (IndexFact.every s [] st body).HoldsAt ρ h) : (IndexFact.every s [] st body).HoldsAt ρ h' := by
  obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
  simp only [readPath, Option.some.injEq] at hw
  subst hw
  obtain ⟨ls', kb, i0, hls', hkb, hi0, hlt, hj, l, hl, hlv⟩ := hx sto ls (by simpa [hs] using hsto) hls
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hkb hlv
  have hki : intValue (ρ i) = some (i0 : Int) := by rw [hkb]; exact intValue_num hi0
  have hn' := termValue_kept hc firstKept_none hst hn
  refine ⟨ρ s, sto, ls', n, rfl, hsto, hls', hn', fun j hj' F hF => ?_⟩
  have hbF := List.all_eq_true.mp hb F hF
  by_cases hji : j = i0
  · subst hji
    rcases hnew with hent | hbody
    · have := entailsKnown_sound he hent
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hn, termValue_value, hki,
        Option.getD_some] at this
      omega
    · have hwb := List.all_eq_true.mp hbody F hF
      cases F with
      | either A B => cases hwb
      | atom F =>
        simp only [writtenBody, Bool.and_eq_true] at hwb
        obtain ⟨hvalid, hwb⟩ := hwb
        cases hG : F.mapVars (some ∘ Bound.inst i x) with
        | some G =>
          rw [hG] at hwb
          simp only [Bool.and_eq_true, List.all_eq_true] at hwb
          obtain ⟨hd, hent⟩ := hwb
          have hG0 : (IndexFact.linear G).HoldsAt ρ h :=
            ⟨fun t ht => termDefined_sound he (hd t ht).1, entailsKnown_sound he hent⟩
          have hG1 := IndexFact.holdsAt_kept hc firstKept_none
            (by simp only [IndexFact.keptBy, Bool.or_eq_true]; exact .inl (List.all_eq_true.mpr fun t ht => (hd t ht).2))
            hG0
          refine (factAt_mapVars (val' := termValue ρ h') hG fun y hy t ht => ?_).mp hG1
          simp only [Function.comp_apply, Option.some.injEq] at ht
          subst ht
          cases y with
          | index => simp only [Bound.inst, termValue_value, hki, boundValue]
          | elem => simp only [Bound.inst, termValue_value, boundValue, elementInt, hl, hlv, Option.bind_some]
          | offset d => have := List.all_eq_true.mp hvalid (.offset d) hy; simp at this
          | project k p => simp only [Bound.inst, boundValue, hl, hlv, Option.bind_some, termValue]
          | free t => rfl
        | none => simp [hG] at hwb
  · refine LinearClause.holdsAt_monotone (fun y m hky hy => ?_) (fun y m hgy hy => ?_) hbF (hall j hj' F hF)
    · cases y with
      | index => exact hy
      | elem =>
        simp only [boundValue, elementInt, hj j hji] at hy ⊢
        split at hy
        · rename_i l' hl'
          obtain ⟨u, hu, hum⟩ := Option.bind_eq_some_iff.mp hy
          obtain ⟨bu, rfl, -⟩ := intValue_safe hum
          simp only [hc.1 l' _ hu (by simp [writeChanges, CallEffects.ElementWrite.changes, Changes.alters]),
            Option.bind_some, hum]
        · cases hy
      | project _ _ | offset _ => simp [Bound.keptBy] at hky
      | free t => exact termValue_kept hc firstKept_none hky hy
    · cases y with
      | index | elem | project _ _ | offset _ => simp [Bound.grownBy] at hgy
      | free t => simp [Bound.grownBy, Term.grownBy, writeChanges, CallEffects.ElementWrite.changes] at hgy

open HeapKnowledge in
/-- **An exact element write establishes a prefix through its index**
Every target index other than the written index belongs to the old prefix;
the written index holds the value checked against the body. -/
theorem every_written_prefix {ρ : Env} {h h' : Heap} {b i x s : Nat} {st next : Term} {body : List (LinearClause Bound)}
    {as : List IndexAtom} (he : IndexHolds as ρ h) (hs : ρ s = ρ b)
    (hc : writeChanges.Holds h h') (hx : CallEffects.ExactWrite [ρ b, ρ i, ρ x] h h')
    (hnext : termDefined as next = true)
    (hcover : entailsKnown as (.le [(next, 1), (.value i, -1)] 1) = true)
    (hstart : entailsKnown as (.le [(.value i, 1), (st, -1)] 0) = true)
    (hst : next.keptBy writeChanges (fun _ _ => false) = true)
    (hb : body.all (bodyKeptBy writeChanges (fun _ _ => false)) = true)
    (hbody : body.all (writtenBody as i x) = true)
    (hF : (IndexFact.every s [] st body).HoldsAt ρ h) : (IndexFact.every s [] next body).HoldsAt ρ h' := by
  obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
  simp only [readPath, Option.some.injEq] at hw
  subst hw
  obtain ⟨ls', kb, i0, hls', hkb, hi0, hlt, hj, l, hl, hlv⟩ := hx sto ls (by simpa [hs] using hsto) hls
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hkb hlv
  have hki : intValue (ρ i) = some (i0 : Int) := by rw [hkb]; exact intValue_num hi0
  obtain ⟨n', hn0⟩ := Option.isSome_iff_exists.mp (termDefined_sound he hnext)
  have hn' := termValue_kept hc firstKept_none hst hn0
  have hcoverage := entailsKnown_sound he hcover
  have hbegin := entailsKnown_sound he hstart
  simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hn0, hn, termValue_value, hki,
    Option.getD_some] at hcoverage hbegin
  refine ⟨ρ s, sto, ls', n', rfl, hsto, hls', hn', fun j hj' F hF => ?_⟩
  have hbF := List.all_eq_true.mp hb F hF
  by_cases hji : j = i0
  · subst hji
    have hwb := List.all_eq_true.mp hbody F hF
    cases F with
    | either A B => cases hwb
    | atom F =>
      simp only [writtenBody, Bool.and_eq_true] at hwb
      obtain ⟨hvalid, hwb⟩ := hwb
      cases hG : F.mapVars (some ∘ Bound.inst i x) with
      | some G =>
        rw [hG] at hwb
        simp only [Bool.and_eq_true, List.all_eq_true] at hwb
        obtain ⟨hd, hent⟩ := hwb
        have hG0 : (IndexFact.linear G).HoldsAt ρ h :=
          ⟨fun t ht => termDefined_sound he (hd t ht).1, entailsKnown_sound he hent⟩
        have hG1 := IndexFact.holdsAt_kept hc firstKept_none
          (by simp only [IndexFact.keptBy, Bool.or_eq_true]; exact .inl (List.all_eq_true.mpr fun t ht => (hd t ht).2))
          hG0
        refine (factAt_mapVars (val' := termValue ρ h') hG fun y hy t ht => ?_).mp hG1
        simp only [Function.comp_apply, Option.some.injEq] at ht
        subst ht
        cases y with
        | index => simp only [Bound.inst, termValue_value, hki, boundValue]
        | elem => simp only [Bound.inst, termValue_value, boundValue, elementInt, hl, hlv, Option.bind_some]
        | offset d => have := List.all_eq_true.mp hvalid (.offset d) hy; simp at this
        | project k p => simp only [Bound.inst, boundValue, hl, hlv, Option.bind_some, termValue]
        | free t => rfl
      | none => simp [hG] at hwb
  · refine LinearClause.holdsAt_monotone (fun y m hky hy => ?_) (fun y m hgy hy => ?_) hbF (hall j (by omega) F hF)
    · cases y with
      | index => exact hy
      | elem =>
        simp only [boundValue, elementInt, hj j hji] at hy ⊢
        split at hy
        · rename_i l' hl'
          obtain ⟨u, hu, hum⟩ := Option.bind_eq_some_iff.mp hy
          obtain ⟨bu, rfl, -⟩ := intValue_safe hum
          simp only [hc.1 l' _ hu (by simp [writeChanges, CallEffects.ElementWrite.changes, Changes.alters]),
            Option.bind_some, hum]
        · cases hy
      | project _ _ | offset _ => simp [Bound.keptBy] at hky
      | free t => exact termValue_kept hc firstKept_none hky hy
    · cases y with
      | index | elem | project _ _ | offset _ => simp [Bound.grownBy] at hgy
      | free t => simp [Bound.grownBy, Term.grownBy, writeChanges, CallEffects.ElementWrite.changes] at hgy

open HeapKnowledge in
theorem writeKept_holds {eff : Effect} {t : Tm} {k : Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    (hk : Holds k ρ h)
    (hew : ∀ w, eff.elementWrite = some w → w.Holds (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h') :
    IndexHolds (writeKept eff t k) (push v ρ) h' := by
  unfold writeKept
  split
  · rename_i f r b i x hw
    obtain ⟨hc, hx⟩ := hew _ hw
    have hx := hx rfl
    simp only [ExpressionEffects.actualsOf, instantiate, instantiateArgs, Nat.not_lt_zero, if_false,
      Nat.sub_zero] at hx
    have hi := pick_eq (fun a b hab => HeapLinks.aliases_eq hk.2.2.1 hab)
      (p := intSlot k.indices) i
    have hv := pick_eq (fun a b hab => HeapLinks.aliases_eq hk.2.2.1 hab)
      (p := intSlot k.indices) x
    have hx' : CallEffects.ExactWrite [ρ b,
        ρ (pick (HeapLinks.aliases k.links) (intSlot k.indices) i),
        ρ (pick (HeapLinks.aliases k.links) (intSlot k.indices) x)] h h' := by
      simpa only [hi, hv] using hx
    clear hx
    have hx := hx'
    refine shiftIndices_holds fun a ha hcd => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨ha, hkept⟩ := List.mem_filter.mp ha
      have hF := hk.2.2.2.2.2 a ha hcd
      unfold everyWritten at hkept
      split at hkept
      · rename_i s st body hfa
        rw [hfa] at hF ⊢
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hkept
        obtain ⟨⟨⟨⟨hcls, hst⟩, hb⟩, -⟩, hnew⟩ := hkept
        have hs : ρ s = ρ b := by
          rcases hcls with rfl | hm
          · rfl
          · exact HeapLinks.aliases_eq hk.2.2.1 hm
        exact every_written hk.2.2.2.2.2 hs hc hx hst hb hnew hF
      · cases hkept
    · obtain ⟨a0, ha0, ha⟩ := List.mem_flatMap.mp ha
      have ha0 := (List.mem_filter.mp ha0).1
      obtain ⟨next, -, hnext⟩ := List.mem_filterMap.mp ha
      split at hnext <;> try contradiction
      unfold writtenPrefix at hnext
      split at hnext
      · rename_i s st body hfact
        split at hnext
        · rename_i hcheck
          cases hnext
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hcheck
          obtain ⟨⟨⟨⟨⟨⟨hcls, hd⟩, hst⟩, hb⟩, hcover⟩, hstart⟩, hbody⟩ := hcheck
          have hs : ρ s = ρ b := by
            rcases hcls with rfl | hm
            · rfl
            · exact HeapLinks.aliases_eq hk.2.2.1 hm
          have hF := hk.2.2.2.2.2 a0 ha0 hcd
          rw [hfact] at hF
          exact every_written_prefix hk.2.2.2.2.2 hs hc hx hd hcover hstart hst hb hbody hF
        · cases hnext
      · cases hnext
  · exact indexHolds_nil _ _

/-- Knowledge with a call's result-fact atoms added, the atoms of its entry
`k0` its footprint keeps (`effectKept`) and the quantified atoms its growth
of its receiver's store keeps or extends (`appendKept`), then the instances
of quantified facts the element reads among them state (`withElements`). -/
def withEnsures (views : Nat → String → Bool) (n : Nat) (eff : Effect) (t : Tm) (k0 k : HeapKnowledge.Knowledge) : HeapKnowledge.Knowledge :=
  HeapKnowledge.withElements
    { k with indices := k.indices ++ ensuresAtoms eff t ++ effectKept views eff t k0 ++ appendKept eff t k0 ++
        writeKept eff t k0 ++ linearAppendKept n eff t k0 }

theorem withEnsures_holds {views : Nat → String → Bool} {n : Nat} {eff : Effect} {t : Tm} {k0 k : HeapKnowledge.Knowledge} {ρ : Env} {h h' : Heap} {v : Tm}
    (hv : ∀ i, i < n → isVal (ρ i) = true)
    (hk : HeapKnowledge.Holds k (push v ρ) h') (hk0 : HeapKnowledge.Holds k0 ρ h)
    (hw : eff.within (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h')
    (hp : ∀ F ∈ eff.ensures, F.HoldsAt (CallEffects.ensuresEnv v (ExpressionEffects.receiverOf (instantiate 0 ρ t))
      (ExpressionEffects.actualsOf (instantiate 0 ρ t))) h')
    (hg : eff.receiverGrows = true →
      CallEffects.ReceiverGrows (ExpressionEffects.receiverOf (instantiate 0 ρ t)) h h' ∧
      CallEffects.ReceiverAppends (ExpressionEffects.receiverOf (instantiate 0 ρ t))
        (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h')
    (hew : ∀ w, eff.elementWrite = some w → w.Holds (ExpressionEffects.actualsOf (instantiate 0 ρ t)) h h')
    (hviews : HeapKnowledge.ViewsKept views ρ h h') :
    HeapKnowledge.Holds (withEnsures views n eff t k0 k) (push v ρ) h' := HeapKnowledge.withElements_holds
  ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => by
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · exact hk.2.2.2.2.2 a ha hc
            · exact ensuresAtoms_holds hp a ha hc
          · exact effectKept_holds hk0 hw (fun hgr => (hg hgr).1) hew hviews a ha hc
        · exact appendKept_holds hk0 hg a ha hc
      · exact writeKept_holds hk0 hew a ha hc
    · exact linearAppendKept_holds hv hk0 hg a ha hc⟩

/-- Knowledge with the region facts a call growing its receiver's store keeps
(`IndexWrites.grownRegions`) added, renamed past the result; none of a call
growing nothing. -/
def withGrown (eff : Effect) (out : HeapKnowledge.Knowledge) (kept : List HeapKnowledge.IndexAtom) :
    HeapKnowledge.Knowledge :=
  if eff.receiverGrows then { out with indices := out.indices ++ HeapKnowledge.shiftIndices kept } else out

theorem withGrown_holds {eff : Effect} {out : HeapKnowledge.Knowledge} {kept : List HeapKnowledge.IndexAtom}
    {ρ : Env} {h' : Heap} {v : Tm} (ho : HeapKnowledge.Holds out (push v ρ) h')
    (hk : eff.receiverGrows = true → HeapKnowledge.IndexHolds kept ρ h') :
    HeapKnowledge.Holds (withGrown eff out kept) (push v ρ) h' := by
  unfold withGrown
  split
  · rename_i hg
    exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, ho.2.2.2.2.1,
      IndexWrites.indexHolds_cat ho.2.2.2.2.2 (HeapKnowledge.shiftIndices_holds (hk hg))⟩
  · exact ho

/-- The selected signature of an ordinary step's evidence that `call-ensures`
applies to: at the sequent `j`, a call checked as `selected_sound` or as
`call-requires` admits it, at a selected signature stating a postcondition. -/
@[nospecialize] def ensuresCall (G : NormalGraph ι) (images : InstanceImageCheck G) (j : Sequent ι)
    (k : HeapKnowledge.Knowledge) (e : HeapExpressionRules.StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : Option Effect :=
  match e with
  | .ordinary p =>
    if decide (claim p = j) && (ExpressionEffects.selectedOperands p && checkTreeUsing G images p codes sums ||
        requiresTree G images k codes sums p) then
      match ExpressionEffects.selectedEffect p with
      | some eff => if eff.ensures.isEmpty && (effectKept (HeapExpressionRules.writeViews G j.context) eff j.term k).isEmpty && (appendKept eff j.term k).isEmpty &&
          (writeKept eff j.term k).isEmpty &&
          (linearAppendKept j.context.length eff j.term k).isEmpty then none else some eff
      | none => none
    else none
  | _ => none

/-- **`call-ensures`**: such a call's normal return meets its selected
signature's postcondition at its receiver and actuals, its `ensures` facts
included. -/
theorem ensuresCall_sound {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k : HeapKnowledge.Knowledge} {e : HeapExpressionRules.StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {eff : Effect}
    (hc : ensuresCall G images j k e codes sums = some eff) (hcodes : CodesSound G codes)
    (hsums : SummariesSound G images sums)
    {ρ n W h} (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (excOf G) (meaning G j.type)
      (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ j.term))
        (ExpressionEffects.actualsOf (instantiate 0 ρ j.term)) h) n W h (instantiate 0 ρ j.term) := by
  unfold ensuresCall at hc
  split at hc
  · rename_i p
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨rfl, hcheck⟩ := hcond
      cases hsel : ExpressionEffects.selectedEffect p with
      | none => simp [hsel] at hc
      | some eff' =>
        simp only [hsel] at hc
        split at hc
        · cases hc
        · cases hc
          rcases hcheck with ⟨hops, ht⟩ | hreq
          · exact ExpressionEffects.selected_sound p ht hops hsel hcodes hsums he hw hh
          · obtain ⟨eff'', hsel', hs⟩ := requiresTree_sound hcodes hsums p hreq
            rw [hsel] at hsel'
            cases hsel'
            exact hs he hk hw hh
    · cases hc
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

/-- A checker whose ordinary steps that are calls stating a postcondition add
their atoms to what `base` gives the step (`PromiseCalls.ensuresCall`); every
other step is `base`'s. -/
@[nospecialize] def Checker.ensuringCalls [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (base : Checker G images) : Checker G images where
  run := fun j k e codes sums =>
    match PromiseCalls.ensuresCall G images j k e codes sums with
    | some eff => (base.run j k e codes sums).map fun out => PromiseCalls.withGrown eff
        (PromiseCalls.withEnsures (HeapExpressionRules.writeViews G j.context) j.context.length eff j.term k out) (IndexWrites.grownRegions G j.context k j.term)
    | none => base.run j k e codes sums
  select := fun j k e codes sums =>
    match PromiseCalls.ensuresCall G images j k e codes sums with
    | some eff => (base.select j k e codes sums).map fun out => PromiseCalls.withGrown eff
        (PromiseCalls.withEnsures (HeapExpressionRules.writeViews G j.context) j.context.length eff j.term k out) (IndexWrites.grownRegions G j.context k j.term)
    | none => base.select j k e codes sums
  sound := by
    intro j k e out codes sums hc hcodes hsums ρ n W h he hk hw hh
    split at hc
    · rename_i eff hens
      simp only [CheckResult.map, Option.map_eq_some_iff] at hc
      obtain ⟨out0, hrun, rfl⟩ := hc
      cases n with
      | zero => trivial
      | succ n =>
      have hs := base.sound hrun hcodes hsums he hk hw hh
      have hp := PromiseCalls.ensuresCall_sound hens hcodes hsums he hk hw hh
      exact HeapObservations.weaken (fun h' v hq => PromiseCalls.withGrown_holds
        (PromiseCalls.withEnsures_holds (fun i hi => (ProgramTyping.meaning_value (he.2 i _ (List.getElem?_eq_getElem hi))).1) hq.1.1 hk hq.1.2.1 hq.1.2.2.2.2.2.1 hq.1.2.2.2.2.2.2.1 hq.1.2.2.2.2.2.2.2 hq.2)
        (fun hgr => IndexWrites.grownRegions_holds he hh hk (hq.1.2.2.2.2.2.2.1 hgr).1 (hq.1.2.2.2.2.2.2.1 hgr).2))
        (HeapExpressionRules.viewFields_frame he hh
          (HeapObservations.cross_upto (n + 1) (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh hs hp))
    · exact base.sound hc hcodes hsums he hk hw hh

/-- The steps' rules, a call keeping the heap keeping every heap fact, a call
allocating its result separating it, a call changing only its receiver's own
locations keeping the facts separated from them, a call stating a postcondition
adding their atoms, the index atoms a step states and the write at a checked
index (`IndexWrites`), each keeping its input's stable links. -/
@[nospecialize] def Checker.ordinary [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) : Checker G images :=
  (Checker.steps G images).keepingCalls.keepingOwnCalls.allocatingCalls.requiringCalls.elementCalls.ensuringCalls
    |>.negatingSlots.indexing.boundedWrites.keepingStable

end Verification.HeapExpressionRules
