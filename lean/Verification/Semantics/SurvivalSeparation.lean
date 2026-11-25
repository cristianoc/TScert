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
  | .guarded g [] t B => if t.isPositive then (factSeps ls B).filter fun e => match e.sites with
    | some (a, b) => (HeapLinks.aliases ls g).contains a.1 || (HeapLinks.aliases ls g).contains b.1
    | none => false
    else []
  | _ => []

/-- A positive guard's tag is no object: a path from a value meeting it reads that value itself. -/
private theorem tag_reads {t : GuardTag} {h : Heap} {p : List String} {v u : Val}
    (hp : t.isPositive = true) (ht : t.holds v) (hu : readPath h v p = some u) : u = v := by
  cases p with
  | nil => simp only [readPath, Option.some.injEq] at hu; exact hu.symm
  | cons f q =>
    cases t <;> simp_all [GuardTag.isPositive, GuardTag.holds, readPath]

private theorem tag_spine {t : GuardTag} {v : Val} (hp : t.isPositive = true) (ht : t.holds v) :
    spineOf v = none := by
  cases t <;> simp_all [GuardTag.isPositive, GuardTag.holds, spineOf, fieldsOf]

private theorem tag_array {t : GuardTag} {h : Heap} {v : Val} {l : Nat}
    (hp : t.isPositive = true) (ht : t.holds v) (ha : ArrayPart h v l) : False := by
  rcases ha with ha | ha <;> cases t <;>
    simp_all [GuardTag.isPositive, GuardTag.holds, elementsOf, spineCells, entriesAt, descriptorSpine, fieldsOf]

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
      simp only [factSeps] at he
      split at he
      · rename_i hpos
        simp only [List.mem_filter] at he
        obtain ⟨he, hroot⟩ := he
        obtain ⟨v, hv, hor⟩ := hF
        simp only [readGuard, Option.some.injEq] at hv
        rcases hor with htag | hB
        · have tagAt : ∀ {z : Nat}, z ∈ HeapLinks.aliases ls g → ∀ {q : List String} {u : Val},
              readPath h (ρ z) q = some u → u = v := by
            intro z hz q u hu
            rw [HeapLinks.aliases_eq hl hz, hv] at hu; exact tag_reads hpos htag hu
          cases e with
          | spines a b =>
            simp only [SepFact.sites, Bool.or_eq_true, List.contains_iff_mem] at hroot
            intro u w l hu hw hsu hsw
            rcases hroot with hr | hr
            · rw [tagAt hr hu, tag_spine hpos htag] at hsu; cases hsu
            · rw [tagAt hr hw, tag_spine hpos htag] at hsw; cases hsw
          | arrays a b =>
            simp only [SepFact.sites, Bool.or_eq_true, List.contains_iff_mem] at hroot
            intro u w l hu hw _ _ hul hwl
            rcases hroot with hr | hr
            · rw [tagAt hr hu] at hul; exact tag_array hpos htag hul
            · rw [tagAt hr hw] at hwl; exact tag_array hpos htag hwl
          | locs => simp [SepFact.sites] at hroot
        · exact ih hB e he
      · cases he
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
  refine ⟨noClassEvidence_ok ρ h,
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

/-! ## Guarded separation queries and survival -/

/-- The separations an unconditional fact states under slot guards `gs`
assumed not to hold (`∀ (g, t) ∈ gs, ¬t.holds (ρ g)`): a spine separation,
a region fact, a positively guarded separation on a path root, or any
separation guarded by a slot guard in `gs`. -/
def factSepsUnder (ls : HeapLinks.Links) (gs : List (Nat × GuardTag)) : IndexFact → List SepFact
  | .spineApart a p b q => [.spines (a, p) (b, q)]
  | .apart a b => [.arrays (a, []) (b, [])]
  | .guarded g [] t B =>
    if gs.contains (g, t) then factSepsUnder ls gs B
    else if t.isPositive then (factSepsUnder ls gs B).filter fun e => match e.sites with
      | some (a, b) => (HeapLinks.aliases ls g).contains a.1 || (HeapLinks.aliases ls g).contains b.1
      | none => false
    else []
  | _ => []

theorem factSepsUnder_holds {ls : HeapLinks.Links} {gs : List (Nat × GuardTag)} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (hgs : ∀ g ∈ gs, ¬g.2.holds (ρ g.1)) :
    ∀ (F : IndexFact), F.HoldsAt ε ρ h → ∀ e ∈ factSepsUnder ls gs F, e.Holds ρ h := by
  intro F
  induction F with
  | spineApart a p b q =>
    intro hF e he
    simp only [factSepsUnder, List.mem_singleton] at he
    subst he
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    intro u' w' l hu' hw' hsu hsw
    rw [hu] at hu'; cases hu'
    rw [hw] at hw'; cases hw'
    exact hne l l hsu hsw rfl
  | apart a b =>
    intro hF e he
    simp only [factSepsUnder, List.mem_singleton] at he
    subst he
    intro u w l hu hw hpu hpw hul hwl
    simp only [readPath, Option.some.injEq] at hu hw
    subst hu; subst hw
    exact regionsApart_arrays hF hpu hpw hul hwl
  | guarded g p tag B ih =>
    intro hF e he
    cases p with
    | cons _ _ => simp [factSepsUnder] at he
    | nil =>
      simp only [factSepsUnder] at he
      obtain ⟨v, hv, hor⟩ := hF
      simp only [readGuard, Option.some.injEq] at hv
      split at he
      · rename_i hmem
        have hnt : ¬tag.holds (ρ g) := hgs (g, tag) (List.contains_iff_mem.mp hmem)
        exact ih (hor.resolve_left (by rw [← hv]; exact hnt)) e he
      · split at he
        · rename_i hpos
          simp only [List.mem_filter] at he
          obtain ⟨he, hroot⟩ := he
          rcases hor with htag | hB
          · have tagAt : ∀ {z : Nat}, z ∈ HeapLinks.aliases ls g → ∀ {q : List String} {u : Val},
                readPath h (ρ z) q = some u → u = v := by
              intro z hz q u hu
              rw [HeapLinks.aliases_eq hl hz, hv] at hu; exact tag_reads hpos htag hu
            cases e with
            | spines a b =>
              simp only [SepFact.sites, Bool.or_eq_true, List.contains_iff_mem] at hroot
              intro u w l hu hw hsu hsw
              rcases hroot with hr | hr
              · rw [tagAt hr hu, tag_spine hpos htag] at hsu; cases hsu
              · rw [tagAt hr hw, tag_spine hpos htag] at hsw; cases hsw
            | arrays a b =>
              simp only [SepFact.sites, Bool.or_eq_true, List.contains_iff_mem] at hroot
              intro u w l hu hw _ _ hul hwl
              rcases hroot with hr | hr
              · rw [tagAt hr hu] at hul; exact tag_array hpos htag hul
              · rw [tagAt hr hw] at hwl; exact tag_array hpos htag hwl
            | locs => simp [SepFact.sites] at hroot
          · exact ih hB e he
        · cases he
  | _ => intro _ e he; simp [factSepsUnder] at he

/-- The separations of a state's unconditional facts under discharged slot guards `gs`. -/
def knowledgeSepsUnder (k : Knowledge) (gs : List (Nat × GuardTag)) : List SepFact :=
  k.indices.flatMap fun a => if a.cond.isNone then factSepsUnder k.links gs a.fact else []

theorem knowledgeSepsUnder_holds {k : Knowledge} {gs : List (Nat × GuardTag)} {ρ : Env} {h : Heap}
    (hk : HeapKnowledge.Holds k ε ρ h) (hgs : ∀ g ∈ gs, ¬g.2.holds (ρ g.1)) :
    ∀ e ∈ knowledgeSepsUnder k gs, e.Holds ρ h := by
  intro e he
  simp only [knowledgeSepsUnder, List.mem_flatMap] at he
  obtain ⟨a, ha, he⟩ := he
  split at he
  · rename_i hn
    have hF := hk.2.2.2.2.2 a ha fun b hb => by simp only [Option.isNone_iff_eq_none] at hn; rw [hn] at hb; cases hb
    exact factSepsUnder_holds hk.2.2.1 hgs a.fact hF e he
  · cases he

/-- The separation evidence a state's knowledge holds under discharged slot guards `gs`. -/
def knowledgeEvidenceUnder (k : Knowledge) (gs : List (Nat × GuardTag)) : SepEvidence :=
  { links := k.links, facts := knowledgeSepsUnder k gs ++ separationFacts k.separation }

theorem knowledgeEvidenceUnder_holds {k : Knowledge} {gs : List (Nat × GuardTag)} {ρ : Env} {h : Heap}
    (hk : HeapKnowledge.Holds k ε ρ h) (hgs : ∀ g ∈ gs, ¬g.2.holds (ρ g.1)) :
    (knowledgeEvidenceUnder k gs).Holds id ρ h := by
  refine ⟨noClassEvidence_ok ρ h,
    ⟨fun _ _ hc => by simp [knowledgeEvidenceUnder] at hc, fun _ _ hc => by simp [knowledgeEvidenceUnder] at hc⟩,
    fun _ _ hij => hij, hk.2.2.1, fun e he => ?_⟩
  simp only [knowledgeEvidenceUnder, List.mem_append] at he
  rcases he with he | he
  · exact knowledgeSepsUnder_holds hk hgs e he
  · exact separationFacts_holds hk.2.2.2.1 e he

/-- The query a state's knowledge answers under discharged slot guards `gs`. -/
def knowledgeQueryUnder (k : Knowledge) (gs : List (Nat × GuardTag)) : SepQuery :=
  (knowledgeEvidenceUnder k gs).query

theorem knowledgeQueryUnder_sound {k : Knowledge} {gs : List (Nat × GuardTag)} {ρ : Env} {h : Heap}
    {n : Nat} {W : WorldT n} (hk : HeapKnowledge.Holds k ε ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ)
    (hgs : ∀ g ∈ gs, ¬g.2.holds (ρ g.1)) :
    (knowledgeQueryUnder k gs).Sound ρ h :=
  SepEvidence.query_sound (knowledgeEvidenceUnder_holds hk hgs) hok hρ

/-- **Guarded survival check**: peels leading slot guards `(s, t)` into the
separation query's discharged guards `gs`, then checks `F.keeps` under
`knowledgeQueryUnder k gs`. -/
def _root_.Verification.HeapKnowledge.IndexFact.keepsUnder (k : Knowledge) (c : ReadContext) (Φ : Footprint)
    (gs : List (Nat × GuardTag)) : IndexFact → Bool
  | .guarded s [] t B => B.keepsUnder k c Φ ((s, t) :: gs)
  | F => F.keeps (knowledgeQueryUnder k gs) c Φ

/-- **Guarded survival is sound**: a fact `keepsUnder` keeps holds after every
transition within `Φ` meeting `c`, from a prestate where `k` holds. -/
theorem IndexFact.keepsUnder_sound {k : Knowledge} {c : ReadContext} {Φ : Footprint} {ρ : Env} {h h' : Heap}
    {n : Nat} {W : WorldT n} (hk : HeapKnowledge.Holds k ε ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ)
    (hp : Post Φ ρ h h') (hc : c.Holds ρ h h') :
    ∀ (F : IndexFact) (gs : List (Nat × GuardTag)),
      (∀ g ∈ gs, ¬g.2.holds (ρ g.1)) →
      F.keepsUnder k c Φ gs = true → F.HoldsAt ε ρ h → F.HoldsAt ε ρ h' := by
  intro F
  induction F with
  | guarded s p t B ih =>
    cases p with
    | nil =>
      intro gs hgs hkeep hF
      obtain ⟨v, hv, hor⟩ := hF
      simp only [readGuard, Option.some.injEq] at hv
      subst hv
      refine ⟨ρ s, rfl, ?_⟩
      by_cases ht : t.holds (ρ s)
      · exact .inl ht
      · refine .inr (ih ((s, t) :: gs) ?_ hkeep (hor.resolve_left ht))
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ht
        · exact hgs g hg
    | cons _ _ =>
      intro gs hgs hkeep hF
      exact IndexFact.keeps_sound hkeep (knowledgeQueryUnder_sound hk hok hρ hgs) hp hc hF
  | _ =>
    intro gs hgs hkeep hF
    exact IndexFact.keeps_sound hkeep (knowledgeQueryUnder_sound hk hok hρ hgs) hp hc hF

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
  | .spine x p => match σ x with | some y => .spine y p | none => .all
  | .elemSpines x p => match σ x with | some y => .elemSpines y p | none => .all

theorem Region.mem_renameM {σ : Nat → Option Nat} {ρ env : Env} {h : Heap} {l : Nat}
    (hσ : ∀ i j, σ i = some j → ρ j = env i) (hl : l < h.length) :
    ∀ r : Region, r.mem env h l = true → (r.renameM σ).mem ρ h l = true := by
  intro r
  cases r with
  | cls | all => intro hm; exact hm
  | _ =>
    intro hm
    simp only [Region.renameM]
    split
    · rename_i y hy; simpa [Region.mem, hσ _ _ hy] using hm
    · simpa [Region.mem] using hl

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
  · exact .inr ⟨(e.1.renameM σ, e.2), List.mem_map.mpr ⟨e, he, rfl⟩, Region.mem_renameM hσ (List.getElem?_eq_some_iff.mp hv).1 e.1 hm, hh⟩

end Verification.Footprints

namespace Verification.Footprints

/-- **A footprint's class entries as they act on their class**: on a
selector of spine categories alone `init` and `scalar` are `keep`, on one of
the value category alone `extend` and `grow` are `scalar` (`Change.onSpine`,
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
      · simp only [hcv, Bool.not_false, ite_true]
        have harr : isArr v = true := Selector.selects_noValue hcv hsel
        refine ⟨hm, ?_⟩
        cases δ <;> simp only [Change.onSpine]
        · exact hh
        · exact hh.init_isArr harr
        · exact hh.scalar_isArr harr
        · exact hh
        · exact hh
        · exact hh
      · simp only [Bool.not_eq_false] at hcv
        simp only [hcv, Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · rename_i hst
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hst
          have harr : isArr v = false := Selector.selects_valueOnly hst.1 hst.2 hsel
          refine ⟨hm, ?_⟩
          cases δ <;> simp only [Change.onValue]
          all_goals first | exact hh | exact hh.grow_value harr | exact hh.extend_value harr
        · exact ⟨hm, hh⟩
    | _ => exact ⟨hm, hh⟩

end Verification.Footprints

/-! ## The knowledge of the empty support

The facts of a state's knowledge whose support is empty (the note, §5,
"Supports of the atoms"; its Derivations, "The modality": an assertion over
variables alone is invariant): its slots' values (`FactKind.value`), its
alias links (`FactKind.link` of an alias), its index facts reading the
environment alone (`IndexFact.envOnly`), whose produced support is empty, the
entry state fixed (`IndexFact.support?_envOnly`), and its separation facts
(`HeapSeparation`: the field locations of two objects differ). The note's
assertion language has no form for the separation facts; they read no heap,
an object's field locations being fixed (the note, (T3)). The tolerant frame
at the empty support (`frame_nil`) keeps each through every transition. -/

namespace Verification.Footprints
open HeapKnowledge

variable {ε : EntryState}

/-- A term reading the environment alone has the empty support. -/
private theorem term_support_envOnly (c : ReadContext) (δ : Change) {t : Term} (ht : t.envOnly = true) :
    t.support c δ = [] := by
  obtain ⟨k, s, p, a⟩ := t
  cases a
  · simp only [Term.envOnly, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.isEmpty_iff] at ht
    obtain ⟨rfl | rfl, rfl⟩ := ht <;> rfl
  · rfl

private theorem produceSupport_envOnly (c : ReadContext) :
    ∀ (F : IndexFact), F.envOnly = true → ∃ ev, F.produceSupport c = some ([], ev) := by
  intro F
  induction F with
  | index _ | int _ | pastSafe _ | same _ _ => intro _; exact ⟨_, rfl⟩
  | linear F =>
    intro hF
    have hv : ∀ t ∈ F.vars, t.envOnly = true := fun t ht =>
      List.all_eq_true.mp (by simpa only [IndexFact.envOnly] using hF) t ht
    refine ⟨.linear, ?_⟩
    simp only [IndexFact.produceSupport, Option.some.injEq, Prod.mk.injEq, and_true]
    cases F with
    | le G d =>
      simp only [linearSupport, List.flatMap_eq_nil_iff]
      exact fun p hp => term_support_envOnly c _ (hv p.1 (List.mem_map_of_mem hp))
    | ne G d =>
      simp only [linearSupport, List.flatMap_eq_nil_iff]
      exact fun p hp => term_support_envOnly c _ (hv p.1 (List.mem_map_of_mem hp))
  | either A B ihA ihB =>
    intro hF
    simp only [IndexFact.envOnly, Bool.and_eq_true] at hF
    obtain ⟨a, ha⟩ := ihA hF.1
    obtain ⟨b, hb⟩ := ihB hF.2
    exact ⟨.either [] a [] b, by simp [IndexFact.produceSupport, ha, hb]⟩
  | guarded s p tag B ih =>
    intro hF
    simp only [IndexFact.envOnly, Bool.and_eq_true, List.isEmpty_iff] at hF
    obtain ⟨rfl, hB⟩ := hF
    obtain ⟨b, hb⟩ := ih hB
    exact ⟨.guarded [] b, by simp [IndexFact.produceSupport, hb, pathReads]⟩
  | spineApart a p b q =>
    intro hF
    simp only [IndexFact.envOnly, Bool.and_eq_true, List.isEmpty_iff] at hF
    obtain ⟨rfl, rfl⟩ := hF
    exact ⟨.spineApart, by simp [IndexFact.produceSupport, pathReads]⟩
  | _ => intro hF; simp [IndexFact.envOnly] at hF

/-- **An index fact reading the environment alone has the empty support**,
in every context. -/
theorem IndexFact.support?_envOnly (c : ReadContext) {F : IndexFact} (hF : F.envOnly = true) :
    F.support? c = some [] := by
  obtain ⟨ev, h⟩ := produceSupport_envOnly c F hF
  simp [IndexFact.support?, h]

/-- The empty context holds of every transition. -/
theorem ReadContext.empty_holds (ρ : Env) (h h' : Heap) : ({} : ReadContext).Holds ρ h h' :=
  And.intro (fun _ _ _ _ _ _ _ hs => nomatch hs) (fun _ _ _ _ ha => nomatch ha)

/-- **An index fact reading the environment alone holds in every heap**: the
tolerant frame at its empty support (`support?_envOnly`, `frame_nil`). -/
theorem _root_.Verification.HeapKnowledge.IndexFact.holdsAt_envOnly {F : IndexFact} {ρ : Env} {h : Heap}
    (henv : F.envOnly = true) (hF : F.HoldsAt ε ρ h) (h' : Heap) : F.HoldsAt ε ρ h' :=
  frame_nil (D := heaps) (m := 0) (IndexFact.support?_supports {} F (IndexFact.support?_envOnly {} henv)) trivial
    (ReadContext.empty_holds ρ h h') hF

theorem _root_.Verification.HeapKnowledge.envIndices_holds {as : List IndexAtom} {ρ h}
    (he : IndexHolds ε as ρ h) (h' : Heap) : IndexHolds ε (envIndices as) ρ h' := by
  intro a ha hc
  obtain ⟨ha, henv⟩ := List.mem_filter.mp ha
  exact HeapKnowledge.IndexFact.holdsAt_envOnly henv (he a ha hc) h'

/-- **Alias links hold in every heap**: an alias link's support is empty
(`FactKind.link`), the tolerant frame at it. -/
theorem stableLinks_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hh : HeapLinks.Holds ls ρ h) (h' : Heap) :
    HeapLinks.Holds (HeapLinks.stable ls) ρ h' := by
  intro g hg
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hg
  have hs : Supports (fun _ _ _ => True) (FactKind.link g).Holds [] := by
    simpa [FactKind.support, ha] using (FactKind.link g).supports
  exact frame_nil (D := heaps) (m := 0) hs trivial trivial
    (fun g' hg' => by rw [List.mem_singleton.mp hg']; exact hh g hm) g (List.mem_singleton_self _)

/-- **The knowledge of the empty support**: the slots' values, the alias
links, the separation facts and the index facts reading the environment
alone. -/
def _root_.Verification.HeapKnowledge.Knowledge.heapFree (k : Knowledge) : Knowledge :=
  ⟨[], k.values, HeapLinks.stable k.links, k.separation, [], envIndices k.indices⟩

/-- **The knowledge of the empty support has the empty support** (each part's
is empty: `FactKind.value`, `stableLinks_holds`, `holdsAt_envOnly`; the
separation facts read no heap). -/
theorem heapFree_supports (k : Knowledge) :
    Supports (fun _ _ _ => True) (fun ρ h => HeapKnowledge.Holds k.heapFree ε ρ h) [] := by
  refine Supports.intro fun ρ h h' _ hk _ => ⟨HeapFacts.holds_nil _ _, hk.2.1, ?_, hk.2.2.2.1,
    elemsHolds_nil _ _, ?_⟩
  · intro g hg
    have := stableLinks_holds hk.2.2.1 h' g (List.mem_filter.mpr ⟨hg, (List.mem_filter.mp hg).2⟩)
    exact this
  · intro a ha hc
    exact HeapKnowledge.IndexFact.holdsAt_envOnly (List.mem_filter.mp ha).2 (hk.2.2.2.2.2 a ha hc) h'

/-- The knowledge of the empty support is part of the knowledge, at the same
state. -/
theorem heapFree_le {k : Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ε ρ h) :
    HeapKnowledge.Holds k.heapFree ε ρ h :=
  ⟨HeapFacts.holds_nil _ _, hk.2.1, fun g hg => hk.2.2.1 g (List.mem_filter.mp hg).1, hk.2.2.2.1,
    elemsHolds_nil _ _, fun a ha => hk.2.2.2.2.2 a (List.mem_filter.mp ha).1⟩

/-- **The knowledge of the empty support holds after every transition**: the
tolerant frame at the empty support (`heapFree_supports`, `frame_nil`). -/
theorem heapFree_frame {k : Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ε ρ h) (h' : Heap) :
    HeapKnowledge.Holds k.heapFree ε ρ h' :=
  frame_nil (D := heaps) (m := 0) (heapFree_supports (ε := ε) k) trivial trivial (heapFree_le hk)

/-! ## The support `all`

The note, §5, Definition "Supports of the atoms", its last paragraph: every
assertion without a modality has the support
$`\mathrm{all} = \{\mathsf{val}{:}\,\mathsf{keep},\ \mathsf{st}{:}\,\mathsf{keep}\}`$,
the closed footprint `Closed.empty`: it reads the valuation, the mark and
locations below the heap's length (W3), which a transition keeping every one
of them keeps. The empty effect respects it, so a step whose normal effect is
empty keeps every fact by it. -/

/-- **The empty effect respects every support**: its every entry is at
`keep`, which every change tolerates. -/
theorem respects_empty (q : SepQuery) (S : Footprint) : respects q S Closed.empty.fp = true := by
  simp only [respects, List.all_eq_true]
  intro ⟨r, δ⟩ _ f hf
  simp only [Closed.fp, Closed.empty, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> cases δ <;> rfl

/-- **Every represented fact has the support `all`**: where `all` is
supported the heap only grows (`Closed.empty_of_supported`), and every fact
holds after an extension of the heap (`HeapKnowledge.alloc_frames`). -/
theorem knowledge_supports_all (k : Knowledge) :
    Supports (fun _ _ _ => True) (fun ρ h => HeapKnowledge.Holds k ε ρ h) Closed.empty.fp :=
  Supports.intro fun _ _ _ _ hk hs => by
    obtain ⟨vs, rfl⟩ := Closed.holds_empty.mp (Closed.empty_of_supported hs)
    exact HeapKnowledge.alloc_frames vs hk

/-- **The tolerant frame at the empty effect**: every fact, by the support
`all`, which the empty effect respects (`respects_empty`). -/
theorem knowledge_frame_empty {k : Knowledge} {ρ : Env} {h h' : Heap} (hk : HeapKnowledge.Holds k ε ρ h)
    (hp : Closed.empty.Holds h h') : HeapKnowledge.Holds k ε ρ h' :=
  Footprints.frame_step (D := heaps) (m := 0) (knowledge_supports_all k) (respects_empty .empty _)
    (SepQuery.empty_sound ρ h) (Closed.post_iff.mpr (Closed.holds_iff.mp hp)) trivial trivial hk


end Verification.Footprints
