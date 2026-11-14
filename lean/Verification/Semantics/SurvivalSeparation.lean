import Verification.Semantics.Survival
import Verification.Semantics.HeapKnowledge

/-! # Separation queries from knowledge

The separation query a state's knowledge answers (FOOTPRINTS.md, "Separation
queries"): two regions are disjoint by class, or each selects the store of
the value a path reads, and an unconditional fact of the knowledge states
those two values' stores different. A path is read up to the knowledge's
alias links and read links (`pathViews`): every view of it reads the same
value. The query is built from the prestate's knowledge and is sound where
that knowledge holds (`knowledgeQuery_sound`). -/
namespace Verification.Footprints
open HeapKnowledge

/-! ## Disjointness by class -/

/-- Locations of a region whose contents are of one class, against the
locations of another class. -/
def classQuery : SepQuery := ⟨fun r s => match r, s with
  | .inCls _ c, .cls c' => c != c'
  | .cls c', .inCls _ c => c != c'
  | _, _ => false⟩

private theorem cls_disjoint {c c' : Cls} (hne : c ≠ c') {v : Val} (h₁ : c.has v = true)
    (h₂ : c'.has v = true) : False := by
  cases c <;> cases c' <;> simp_all [Cls.has]

theorem classQuery_sound (ρ : Env) (h : Heap) : classQuery.Sound ρ h := by
  intro r s l hd hr hs
  have key : ∀ {r c c'}, c ≠ c' → (Region.inCls r c).mem ρ h l = true → (Region.cls c').mem ρ h l = true → False := by
    intro r c c' hne hr hs
    simp only [Region.mem, Bool.and_eq_true] at hr hs
    obtain ⟨-, hr⟩ := hr
    split at hr
    · rename_i v hv; rw [hv] at hs; exact cls_disjoint hne hr hs
    · cases hr
  cases r <;> cases s <;> simp only [classQuery, Bool.false_eq_true, bne_iff_ne, ne_eq] at hd
  all_goals first | exact key hd hr hs | exact key hd hs hr

/-! ## Views of a path -/

/-- The paths that read what the path `p` from slot `x` reads, by the
knowledge's links: the path itself, and for a first field `f` that a
non-optional read link from an alias of `x` reads into a slot `y`, the views
of the rest from `y`. -/
def pathViews (ls : HeapLinks.Links) : Nat → List String → List (Nat × List String)
  | x, [] => [(x, [])]
  | x, f :: q => (x, f :: q) :: ls.flatMap fun g =>
      if !g.alias && !g.optional && g.field == .str f && (HeapLinks.aliases ls x).contains g.cell
      then pathViews ls g.value q else []

/-- **Every view of a path reads what it reads.** -/
theorem pathViews_read {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) :
    ∀ (p : List String) (x : Nat) {z : Nat} {r : List String}, (z, r) ∈ pathViews ls x p →
      readPath h (ρ z) r = readPath h (ρ x) p := by
  intro p
  induction p with
  | nil => intro x z r hm; simp only [pathViews, List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm; rfl
  | cons f q ih =>
    intro x z r hm
    simp only [pathViews, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨g, hg, hm⟩
    · rfl
    · split at hm
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hc
        obtain ⟨⟨⟨ha, ho⟩, hf⟩, hal⟩ := hc
        rw [ih g.value hm]
        have hx : ρ g.cell = ρ x := HeapLinks.aliases_eq hl hal
        have hlink := hl g hg
        simp only [ha, ho, Bool.false_eq_true, if_false] at hlink
        obtain ⟨flds, c, oid, l, hobj, hlook, hv⟩ := hlink
        rw [← hx, hobj]
        simp only [readPath]
        rw [hf] at hlook
        simp [hlook, hv]
      · cases hm

/-- Two paths name the same site where a view of one is a view of the other
up to an alias of its root. -/
def sameSite (ls : HeapLinks.Links) (X A : List (Nat × List String)) : Bool :=
  X.any fun x => A.any fun a => x.2 == a.2 && (HeapLinks.aliases ls x.1).contains a.1

theorem sameSite_read {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {x a : Nat} {p q : List String} (hs : sameSite ls (pathViews ls x p) (pathViews ls a q) = true) :
    readPath h (ρ x) p = readPath h (ρ a) q := by
  obtain ⟨⟨z, r⟩, hz, hm⟩ := List.any_eq_true.mp hs
  obtain ⟨⟨w, r'⟩, hw, hm⟩ := List.any_eq_true.mp hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hm
  obtain ⟨rfl, hal⟩ := hm
  rw [← pathViews_read hl p x hz, ← pathViews_read hl q a hw, HeapLinks.aliases_eq hl hal]

/-! ## Store separations the knowledge states -/

/-- A separation the knowledge states: the stores of the values the two
paths read differ, or one of the paths selects no store. -/
structure StoreSep where
  a : Nat × List String
  b : Nat × List String

/-- The two paths' values hold different stores. -/
def StoreSep.Holds (e : StoreSep) (ρ : Env) (h : Heap) : Prop :=
  ∀ u w l, readPath h (ρ e.a.1) e.a.2 = some u → readPath h (ρ e.b.1) e.b.2 = some w →
    storeOf u = some l → storeOf w = some l → False

/-- The separations an unconditional fact states: a store separation, a
region fact (its two values' stores), and either guarded by a slot's value
being a guard's tag where one of its paths starts at that slot: there it
reads no object, so it selects no store. -/
def factSeps (ls : HeapLinks.Links) : IndexFact → List StoreSep
  | .storeApart a p b q => [⟨(a, p), (b, q)⟩]
  | .apart a b => [⟨(a, []), (b, [])⟩]
  | .guarded g [] _ B => (factSeps ls B).filter fun e =>
      (HeapLinks.aliases ls g).contains e.a.1 || (HeapLinks.aliases ls g).contains e.b.1
  | _ => []

private theorem tag_reads_none {t : GuardTag} {h : Heap} {p : List String} {u : Val} {l : Nat}
    (hu : readPath h t.val p = some u) (hl : storeOf u = some l) : False := by
  cases p with
  | nil =>
    simp only [readPath, Option.some.injEq] at hu
    subst hu
    cases t <;> simp [GuardTag.val, storeOf, fieldsOf] at hl
  | cons f q => cases t <;> simp [GuardTag.val, readPath] at hu

theorem factSeps_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) :
    ∀ (F : IndexFact), F.HoldsAt ε ρ h → ∀ e ∈ factSeps ls F, e.Holds ρ h := by
  intro F
  induction F with
  | storeApart a p b q =>
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
    intro u w l hu hw hsu hsw
    simp only [readPath, Option.some.injEq] at hu hw
    subst hu; subst hw
    exact regionsApart_stores hF l l hsu hsw rfl
  | guarded g p tag B ih =>
    intro hF e he
    cases p with
    | cons _ _ => simp [factSeps] at he
    | nil =>
      simp only [factSeps, List.mem_filter, Bool.or_eq_true, List.contains_iff_mem] at he
      obtain ⟨he, hroot⟩ := he
      obtain ⟨v, hv, hor⟩ := hF
      simp only [readGuard, Option.some.injEq] at hv
      rcases hor with htag | hB
      · intro u w l hu hw hsu hsw
        rcases hroot with hr | hr
        · rw [HeapLinks.aliases_eq hl hr, hv, htag] at hu; exact tag_reads_none hu hsu
        · rw [HeapLinks.aliases_eq hl hr, hv, htag] at hw; exact tag_reads_none hw hsw
      · exact ih hB e he
  | _ => intro _ e he; simp [factSeps] at he

/-- The separations of a state's unconditional facts. -/
def knowledgeSeps (k : Knowledge) : List StoreSep :=
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

/-- The store site a region selects within: the store of the value a path
reads. -/
def storeSite : Region → Option (Nat × List String)
  | .path x p k => if k == arrayStoreKey then some (x, p) else none
  | .field x k => if k == arrayStoreKey then some (x, []) else none
  | .inCls r _ => storeSite r
  | _ => none

theorem storeSite_mem {ρ : Env} {h : Heap} {l : Nat} :
    ∀ {r : Region} {x : Nat} {p : List String}, storeSite r = some (x, p) → r.mem ρ h l = true →
      ∃ u, readPath h (ρ x) p = some u ∧ storeOf u = some l := by
  intro r
  induction r with
  | path y q k =>
    intro x p hs hm
    simp only [storeSite] at hs
    split at hs
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [beq_iff_eq] at hk
      subst hk
      simp only [Region.mem] at hm
      split at hm
      · rename_i u hu; exact ⟨u, hu, by simpa [storeOf] using hm⟩
      · cases hm
    · cases hs
  | field y k =>
    intro x p hs hm
    simp only [storeSite] at hs
    split at hs
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [beq_iff_eq] at hk
      subst hk
      exact ⟨_, rfl, by simpa [Region.mem, storeOf] using hm⟩
    · cases hs
  | inCls r c ih =>
    intro x p hs hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hs hm.1
  | _ => intro x p hs; simp [storeSite] at hs

/-- Two store sites the separations place apart, either way round. -/
def sitesApart (ls : HeapLinks.Links) (seps : List StoreSep) (x y : Nat × List String) : Bool :=
  let X := pathViews ls x.1 x.2
  let Y := pathViews ls y.1 y.2
  seps.any fun e =>
    (sameSite ls X (pathViews ls e.a.1 e.a.2) && sameSite ls Y (pathViews ls e.b.1 e.b.2)) ||
    (sameSite ls X (pathViews ls e.b.1 e.b.2) && sameSite ls Y (pathViews ls e.a.1 e.a.2))

/-- **The query a state's knowledge answers**: by class, or by a store
separation between the two regions' store sites. -/
def knowledgeQuery (k : Knowledge) : SepQuery :=
  let seps := knowledgeSeps k
  classQuery.or ⟨fun r s => match storeSite r, storeSite s with
    | some x, some y => sitesApart k.links seps x y
    | _, _ => false⟩

/-- **The knowledge's query is sound** wherever the knowledge holds. -/
theorem knowledgeQuery_sound {k : Knowledge} {ρ : Env} {h : Heap} (hk : HeapKnowledge.Holds k ε ρ h) :
    (knowledgeQuery k).Sound ρ h := by
  refine SepQuery.or_sound (classQuery_sound ρ h) ?_
  intro r s l hd hr hs
  simp only at hd
  split at hd
  · rename_i x y hx hy
    obtain ⟨u, hu, hul⟩ := storeSite_mem hx hr
    obtain ⟨w, hw, hwl⟩ := storeSite_mem hy hs
    obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hd
    have hl := hk.2.2.1
    have hsep := knowledgeSeps_holds hk e he
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sameSite_read hl h1] at hu; rw [sameSite_read hl h2] at hw
      exact hsep u w l hu hw hul hwl
    · rw [sameSite_read hl h1] at hu; rw [sameSite_read hl h2] at hw
      exact hsep w u l hw hu hwl hul
  · cases hd

end Verification.Footprints

namespace Verification.Footprints

/-! ## An effect at the caller's slots -/

/-- A region read at a callee's positions, at the caller's slots: a
position `σ` maps to a slot is that slot, a position it maps to none
widens to every location. -/
def Region.renameM (σ : Nat → Option Nat) : Region → Region
  | .field x k => match σ x with | some y => .field y k | none => .all
  | .own x => match σ x with | some y => .own y | none => .all
  | .elems x => match σ x with | some y => .elems y | none => .all
  | .path x p k => match σ x with | some y => .path y p k | none => .all
  | .pathOwn x p => match σ x with | some y => .pathOwn y p | none => .all
  | .pathElems x p => match σ x with | some y => .pathElems y p | none => .all
  | .cls c => .cls c
  | .all => .all
  | .cell b => .cell b
  | .inCls r c => .inCls (r.renameM σ) c

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
