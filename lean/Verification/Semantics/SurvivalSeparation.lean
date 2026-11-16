import Verification.Semantics.Survival
import Verification.Semantics.HeapKnowledge

/-! # Separation queries from knowledge

The separation query a state's knowledge answers (FOOTPRINTS.md, "Separation
queries") is the one disjointness check (`SepEvidence.query`,
`Semantics/SeparationEvidence.lean`) of the evidence the knowledge holds: its
links, which read a path up to aliases and read links; the separations its
unconditional facts state, a spine separation of two paths and a region
fact of two arrays; and the separations its allocations state
(`HeapSeparation`). The query is built from the prestate's knowledge and is
sound where that knowledge holds, at a well-formed state
(`knowledgeQuery_sound`). -/
namespace Verification.Footprints
open HeapKnowledge

/-! ## Spine separations the knowledge states -/

/-- The sites a separation fact names, when it names two. -/
def SepFact.sites : SepFact → Option ((Nat × List String) × (Nat × List String))
  | .spines a b | .arrays a b => some (a, b)
  | .locs .. => none

/-- The separations an unconditional fact states: a spine separation
($`\pi \mathrel{\#} \pi'`$), a region fact ($`\mathrm{apart}(x, y)`$), and
either guarded by a slot's value being a guard's tag where one of its paths
starts at that slot: there it reads no object, so it selects no location. -/
def factSeps (ls : HeapLinks.Links) : IndexFact → List SepFact
  | .spineApart a p b q => [.spines (a, p) (b, q)]
  | .apart a b => [.arrays (a, []) (b, [])]
  | .guarded g [] _ B => (factSeps ls B).filter fun e => match e.sites with
    | some (a, b) => (HeapLinks.aliases ls g).contains a.1 || (HeapLinks.aliases ls g).contains b.1
    | none => false
  | _ => []

/-- A guard's tag is no object: a path from it reads the tag itself. -/
private theorem tag_reads {t : GuardTag} {h : Heap} {p : List String} {u : Val}
    (hu : readPath h t.val p = some u) : u = t.val := by
  cases p with
  | nil => simp only [readPath, Option.some.injEq] at hu; exact hu.symm
  | cons f q => cases t <;> simp [GuardTag.val, readPath] at hu

private theorem tag_spine (t : GuardTag) : spineOf t.val = none := by
  cases t <;> simp [GuardTag.val, spineOf, fieldsOf]

private theorem tag_array {t : GuardTag} {h : Heap} {l : Nat} (ha : ArrayPart h t.val l) : False := by
  rcases ha with ha | ha <;> cases t <;>
    simp [GuardTag.val, elementsOf, spineCells, entriesAt, descriptorSpine, fieldsOf] at ha

theorem factSeps_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) :
    ∀ (F : IndexFact), F.HoldsAt ε ρ h → ∀ e ∈ factSeps ls F, e.Holds ρ h := by
  intro F
  induction F with
  | spineApart a p b q =>
    intro hF e he
    simp only [factSeps, List.mem_singleton] at he
    subst he
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    intro u' w' l hu' hw' hsu hsw
    rw [hu] at hu'; cases hu'
    rw [hw] at hw'; cases hw'
    exact hne l l hsu hsw rfl
  | apart a b =>
    intro hF e he
    simp only [factSeps, List.mem_singleton] at he
    subst he
    intro u w l hu hw hpu hpw hul hwl
    simp only [readPath, Option.some.injEq] at hu hw
    subst hu; subst hw
    exact regionsApart_arrays hF hpu hpw hul hwl
  | guarded g p tag B ih =>
    intro hF e he
    cases p with
    | cons _ _ => simp [factSeps] at he
    | nil =>
      simp only [factSeps, List.mem_filter] at he
      obtain ⟨he, hroot⟩ := he
      obtain ⟨v, hv, hor⟩ := hF
      simp only [readGuard, Option.some.injEq] at hv
      rcases hor with htag | hB
      · have tagAt : ∀ {z : Nat}, z ∈ HeapLinks.aliases ls g → ∀ {q : List String} {u : Val},
            readPath h (ρ z) q = some u → u = tag.val := by
          intro z hz q u hu
          rw [HeapLinks.aliases_eq hl hz, hv, htag] at hu; exact tag_reads hu
        cases e with
        | spines a b =>
          simp only [SepFact.sites, Bool.or_eq_true, List.contains_iff_mem] at hroot
          intro u w l hu hw hsu hsw
          rcases hroot with hr | hr
          · rw [tagAt hr hu, tag_spine] at hsu; cases hsu
          · rw [tagAt hr hw, tag_spine] at hsw; cases hsw
        | arrays a b =>
          simp only [SepFact.sites, Bool.or_eq_true, List.contains_iff_mem] at hroot
          intro u w l hu hw _ _ hul hwl
          rcases hroot with hr | hr
          · rw [tagAt hr hu] at hul; exact tag_array hul
          · rw [tagAt hr hw] at hwl; exact tag_array hwl
        | locs => simp [SepFact.sites] at hroot
      · exact ih hB e he
  | _ => intro _ e he; simp [factSeps] at he

/-- The separations of a state's unconditional facts. -/
def knowledgeSeps (k : Knowledge) : List SepFact :=
  k.indices.flatMap fun a => if a.cond.isNone then factSeps k.links a.fact else []

theorem knowledgeSeps_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ε ρ h) :
    ∀ e ∈ knowledgeSeps k, e.Holds ρ h := by
  intro e he
  simp only [knowledgeSeps, List.mem_flatMap] at he
  obtain ⟨a, ha, he⟩ := he
  split at he
  · rename_i hn
    have hF := hk.2.2.2.2.2 a ha fun b hb => by simp only [Option.isNone_iff_eq_none] at hn; rw [hn] at hb; cases hb
    exact factSeps_holds hk.2.2.1 a.fact hF e he
  · cases he

/-! ## The query -/

/-- **The separation evidence a state's knowledge holds**: its links, the
separations of its unconditional facts, and those of its allocations
(`HeapSeparation`). -/
def knowledgeEvidence (k : Knowledge) : SepEvidence :=
  { links := k.links, facts := knowledgeSeps k ++ separationFacts k.separation }

theorem knowledgeEvidence_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ε ρ h) :
    (knowledgeEvidence k).Holds id ρ h := by
  refine ⟨fun _ _ _ _ hc => by simp [knowledgeEvidence] at hc,
    ⟨fun _ _ hc => by simp [knowledgeEvidence] at hc, fun _ _ hc => by simp [knowledgeEvidence] at hc⟩,
    fun _ _ hij => hij, hk.2.2.1, fun e he => ?_⟩
  simp only [knowledgeEvidence, List.mem_append] at he
  rcases he with he | he
  · exact knowledgeSeps_holds hk e he
  · exact separationFacts_holds hk.2.2.2.1 e he

/-- **The query a state's knowledge answers**: the one disjointness check
of its separation evidence. -/
def knowledgeQuery (k : Knowledge) : SepQuery := (knowledgeEvidence k).query

/-- **The knowledge's query is sound** wherever the knowledge holds, at a
heap meeting its world with valid roots. -/
theorem knowledgeQuery_sound {k : Knowledge} {ρ : Env} {h : Heap} {n : Nat} {W : WorldT n}
    (hk : HeapKnowledge.Holds k ε ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ) :
    (knowledgeQuery k).Sound ρ h :=
  SepEvidence.query_sound (knowledgeEvidence_holds hk) hok hρ

/-- **Every pair the bounds separate, the knowledge's query separates.** -/
theorem knowledgeQuery_bound (k : Knowledge) {r s : Region} (hd : boundQuery.disjoint r s = true) :
    (knowledgeQuery k).disjoint r s = true :=
  SepEvidence.query_of_bound _ hd

/-- **Every pair of spine sites an unconditional fact separates, the
knowledge's query separates**: a spine separation, or a region fact, whose
sites are the two regions' spine sites, through the links. -/
theorem knowledgeQuery_spines (k : Knowledge) {e : SepFact} (he : e ∈ knowledgeSeps k) {r s : Region}
    {x y : Nat × List String} (hx : spineSite r = some x) (hy : spineSite s = some y)
    (hm : e.sites.any fun ab =>
      sameSite k.links (pathViews k.links x.1 x.2) (pathViews k.links ab.1.1 ab.1.2) &&
      sameSite k.links (pathViews k.links y.1 y.2) (pathViews k.links ab.2.1 ab.2.2)) :
    (knowledgeQuery k).disjoint r s = true := by
  refine SepEvidence.query_fact _ (f := e) (by simp [knowledgeEvidence, he]) ?_
  cases e with
  | spines a b => simpa [SepEvidence.byFact, hx, hy, knowledgeEvidence, SepFact.sites] using hm
  | arrays a b =>
    simpa [SepEvidence.byFact, arraySite_of_spineSite hx, arraySite_of_spineSite hy, knowledgeEvidence,
      SepFact.sites] using hm
  | locs => simp [SepFact.sites] at hm

end Verification.Footprints

namespace Verification.Footprints

/-! ## An effect at the caller's slots -/

/-- A region read at a callee's positions, at the caller's slots: a
position `σ` maps to a slot is that slot, a position it maps to none
widens to every location. -/
def Region.renameM (σ : Nat → Option Nat) : Region → Region
  | .field x k => match σ x with | some y => .field y k | none => .all
  | .fields x => match σ x with | some y => .fields y | none => .all
  | .cells x => match σ x with | some y => .cells y | none => .all
  | .path x p k => match σ x with | some y => .path y p k | none => .all
  | .pathFields x p => match σ x with | some y => .pathFields y p | none => .all
  | .pathCells x p => match σ x with | some y => .pathCells y p | none => .all
  | .cls c => .cls c
  | .all => .all
  | .cell b => .cell b
  | .inCls r c => .inCls (r.renameM σ) c
  | .spine x p => match σ x with | some y => .spine y p | none => .all

theorem Region.mem_renameM {σ : Nat → Option Nat} {ρ env : Env} {h : Heap} {l : Nat}
    (hσ : ∀ i j, σ i = some j → ρ j = env i) :
    ∀ r : Region, r.mem env h l = true → (r.renameM σ).mem ρ h l = true := by
  intro r
  induction r with
  | inCls r c ih =>
    intro hm
    simp only [Region.renameM, Region.mem, Bool.and_eq_true] at hm ⊢
    exact ⟨ih hm.1, hm.2⟩
  | cls | all | cell => intro hm; exact hm
  | _ =>
    intro hm
    simp only [Region.renameM]
    split
    · rename_i y hy; simpa [Region.mem, hσ _ _ hy] using hm
    · rfl

/-- A footprint read at a callee's positions, at the caller's slots. -/
def Footprint.renameM (σ : Nat → Option Nat) (Φ : Footprint) : Footprint :=
  Φ.map fun e => (e.1.renameM σ, e.2)

/-- **The effect at the caller's slots bounds the call**: a call meeting a
footprint at its positions meets the renamed footprint at the caller's
environment, where each position mapped to a slot holds that slot's value. -/
theorem Post.renameM {Φ : Footprint} {σ : Nat → Option Nat} {ρ env : Env} {h h' : Heap}
    (hσ : ∀ i j, σ i = some j → ρ j = env i) (hp : Post Φ env h h') : Post (Φ.renameM σ) ρ h h' := by
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with h | ⟨e, he, hm, hh⟩
  · exact .inl h
  · exact .inr ⟨(e.1.renameM σ, e.2), List.mem_map.mpr ⟨e, he, rfl⟩, Region.mem_renameM hσ e.1 hm, hh⟩

end Verification.Footprints

namespace Verification.Footprints

/-- **A footprint's class entries as they act on their class**: on a
selector of spine categories alone `init` and `scalar` are `keep`, on one of
the value category alone `grow` is `scalar` (`Change.onSpine`,
`Change.onValue`); a selector of both kinds keeps its change. -/
def Footprint.byClass (Φ : Footprint) : Footprint := Φ.map fun e => match e.1 with
  | .cls c => if !c.value then (e.1, e.2.onSpine)
      else if !c.array && !c.view then (e.1, e.2.onValue) else e
  | _ => e

/-- A transition within a footprint is within its class entries' action on
their class. -/
theorem Post.byClass {Φ : Footprint} {ρ : Env} {h h' : Heap} (hp : Post Φ ρ h h') : Post Φ.byClass ρ h h' := by
  refine ⟨hp.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with h | ⟨e, he, hm, hh⟩
  · exact .inl h
  · obtain ⟨r, δ⟩ := e
    refine .inr ⟨_, List.mem_map.mpr ⟨(r, δ), he, rfl⟩, ?_⟩
    cases r with
    | cls c =>
      have hsel : c.selects v = true := by simpa [Region.mem, hv] using hm
      simp only
      by_cases hcv : c.value = false
      · simp only [hcv, Bool.not_false, if_true]
        have harr : isArr v = true := Selector.selects_noValue hcv hsel
        refine ⟨hm, ?_⟩
        cases δ <;> simp only [Change.onSpine]
        · exact hh
        · exact hh.init_isArr harr
        · exact hh.scalar_isArr harr
        · exact hh
        · exact hh
      · simp only [Bool.not_eq_false] at hcv
        simp only [hcv, Bool.not_true, Bool.false_eq_true, if_false]
        split
        · rename_i hst
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hst
          have harr : isArr v = false := Selector.selects_valueOnly hst.1 hst.2 hsel
          refine ⟨hm, ?_⟩
          cases δ <;> simp only [Change.onValue]
          all_goals first | exact hh | exact hh.grow_value harr
        · exact ⟨hm, hh⟩
    | _ => exact ⟨hm, hh⟩

end Verification.Footprints
