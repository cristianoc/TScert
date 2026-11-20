import Verification.Semantics.RegionBounds
import Verification.Semantics.FootprintProvenance
import Verification.Semantics.HeapSeparation
import Verification.Semantics.IndexFacts

/-! # Separation evidence and the one disjointness check

Two regions are disjoint for the respect check (the note *Tolerant frames*,
§3, Definition "Derivations", last paragraph) when no kind of location
belongs to both, or when a separation at hand says so: $`\pi \mathrel{\#}
\pi'`$ for the spines of two array paths, $`\mathrm{apart}(x, y)`$ for
$`x[*]`$ and $`y[*]`$, and $`\mathrm{fresh}(r)`$ for $`r`$ and any region of
locations below the mark.

**Separation evidence** (`SepEvidence`) is what a state's knowledge holds
of these: class evidence of fields, which narrows a field region's bound
(`SepEvidence.bound`); provenance stamps against marks (`fresh`); links,
which make two paths read the same value (`pathViews`, `sameSite`); and a
list of separation facts (`SepFact`): two paths' spines differ, two paths'
arrays are apart, two field locations differ. Its one query
(`SepEvidence.query`) answers by the bounds of the two regions, by
freshness, or by a separation fact whose two sites are those of the two
regions, either way round. It is sound at a well-formed state where the
evidence holds (`SepEvidence.query_sound`). -/
namespace Verification.Footprints
open HeapKnowledge

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

/-- The slots holding what the path `p` from slot `z` reads: each slot an
empty view of the path names, and its aliases. -/
def slotsOf (ls : HeapLinks.Links) (z : Nat) (p : List String) : List Nat :=
  (pathViews ls z p).flatMap fun v => if v.2.isEmpty then HeapLinks.aliases ls v.1 else []

theorem slotsOf_read {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {z x : Nat} {p : List String} (hx : x ∈ slotsOf ls z p) : readPath h (ρ z) p = some (ρ x) := by
  obtain ⟨⟨w, r⟩, hv, hx⟩ := List.mem_flatMap.mp hx
  split at hx
  · rename_i he
    simp only [List.isEmpty_iff] at he
    subst he
    rw [← pathViews_read hl p z hv, HeapLinks.aliases_eq hl hx]
    rfl
  · cases hx

/-! ## Sites of a region -/

/-- The spine site a region selects within: the `[]` slot of the value a
path reads. -/
def spineSite : Region → Option (Nat × List String)
  | .path x p k => if k == arraySpineKey then some (x, p) else none
  | .field x k => if k == arraySpineKey then some (x, []) else none
  | .inCls r _ => spineSite r
  | _ => none

theorem spineSite_mem {ρ : Env} {h : Heap} {l : Nat} :
    ∀ {r : Region} {x : Nat} {p : List String}, spineSite r = some (x, p) → r.mem ρ h l = true →
      ∃ u, readPath h (ρ x) p = some u ∧ spineOf u = some l := by
  intro r
  induction r with
  | path y q k =>
    intro x p hs hm
    simp only [spineSite] at hs
    split at hs
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [beq_iff_eq] at hk
      subst hk
      simp only [Region.mem] at hm
      split at hm
      · rename_i u hu; exact ⟨u, hu, by simpa [spineOf] using hm⟩
      · cases hm
    · cases hs
  | field y k =>
    intro x p hs hm
    simp only [spineSite] at hs
    split at hs
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [beq_iff_eq] at hk
      subst hk
      exact ⟨_, rfl, by simpa [Region.mem, spineOf] using hm⟩
    · cases hs
  | inCls r c ih =>
    intro x p hs hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hs hm.1
  | _ => intro x p hs; simp [spineSite] at hs

/-- The locations of the array a value is: the spine it selects and the
cells its spines list (`Region.spine`, `Region.cells`). -/
def ArrayPart (h : Heap) (u : Val) (l : Nat) : Prop :=
  elementsOf u = some l ∨ some l ∈ spineCells h u

/-- The array site a region selects within: the spine or the cells of the
value a path reads. -/
def arraySite : Region → Option (Nat × List String)
  | .path x p k => if k == arraySpineKey then some (x, p) else none
  | .field x k => if k == arraySpineKey then some (x, []) else none
  | .spine x p => some (x, p)
  | .cells x => some (x, [])
  | .pathCells x p => some (x, p)
  | .inCls r _ => arraySite r
  | _ => none

/-- The `[]` slot of a value is the spine it selects. -/
theorem elementsOf_of_spineOf {u : Val} {l : Nat} (hs : spineOf u = some l) : elementsOf u = some l := by
  cases u with
  | objAt fs c i => simp only [spineOf, fieldsOf] at hs; simp [elementsOf, hs]
  | _ => simp [spineOf, fieldsOf] at hs

/-- A spine site is an array site. -/
theorem arraySite_of_spineSite : ∀ {r : Region} {x : Nat × List String}, spineSite r = some x → arraySite r = some x
  | .path _ _ _, _, h => by simpa [spineSite, arraySite] using h
  | .field _ _, _, h => by simpa [spineSite, arraySite] using h
  | .inCls r _, _, h => arraySite_of_spineSite (r := r) h
  | .fields _, _, h | .cells _, _, h | .cls _, _, h | .all, _, h | .pathFields _ _, _, h
  | .pathCells _ _, _, h | .spine _ _, _, h => by simp [spineSite] at h

theorem arraySite_mem {ρ : Env} {h : Heap} {l : Nat} :
    ∀ {r : Region} {x : Nat} {p : List String}, arraySite r = some (x, p) → r.mem ρ h l = true →
      ∃ u, readPath h (ρ x) p = some u ∧ ArrayPart h u l := by
  intro r
  induction r with
  | path y q k =>
    intro x p hs hm
    have hsp : spineSite (.path y q k) = some (x, p) := by simpa [spineSite, arraySite] using hs
    obtain ⟨u, hu, hl⟩ := spineSite_mem hsp hm
    exact ⟨u, hu, .inl (elementsOf_of_spineOf hl)⟩
  | field y k =>
    intro x p hs hm
    have hsp : spineSite (.field y k) = some (x, p) := by simpa [spineSite, arraySite] using hs
    obtain ⟨u, hu, hl⟩ := spineSite_mem hsp hm
    exact ⟨u, hu, .inl (elementsOf_of_spineOf hl)⟩
  | spine y q =>
    intro x p hs hm
    simp only [arraySite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Region.mem] at hm
    split at hm
    · rename_i u hu; exact ⟨u, hu, .inl (by simpa using hm)⟩
    · cases hm
  | cells y =>
    intro x p hs hm
    simp only [arraySite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, rfl, .inr (by simpa [Region.mem] using hm)⟩
  | pathCells y q =>
    intro x p hs hm
    simp only [arraySite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Region.mem] at hm
    split at hm
    · rename_i u hu; exact ⟨u, hu, .inr (by simpa using hm)⟩
    · cases hm
  | inCls r c ih =>
    intro x p hs hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hs hm.1
  | _ => intro x p hs; simp [arraySite] at hs

/-- The fields site a region selects within: the value a path reads, and
the key of its field (`none`: every own location). -/
def fieldSite : Region → Option ((Nat × List String) × Option PropKey)
  | .field x k => some ((x, []), some k)
  | .path x p k => some ((x, p), some k)
  | .fields x => some ((x, []), none)
  | .pathFields x p => some ((x, p), none)
  | .inCls r _ => fieldSite r
  | _ => none

/-- A location of a value's field at `k`, or of its field locations at
`none`. -/
def FieldAt (v : Val) : Option PropKey → Nat → Prop
  | some k, l => (fieldsOf v).lookup k = some l
  | none, l => l ∈ fieldLocs v

theorem FieldAt.own {v : Val} {o : Option PropKey} {l : Nat} (h : FieldAt v o l) :
    l ∈ (fieldsOf v).map Prod.snd := by
  cases o with
  | none => exact fieldLocs_own h
  | some k => exact lookup_mem_snd h

theorem fieldSite_mem {ρ : Env} {h : Heap} {l : Nat} :
    ∀ {r : Region} {x : Nat} {p : List String} {o : Option PropKey}, fieldSite r = some ((x, p), o) →
      r.mem ρ h l = true → ∃ v, readPath h (ρ x) p = some v ∧ FieldAt v o l := by
  intro r
  induction r with
  | field y k =>
    intro x p o hs hm
    simp only [fieldSite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
    exact ⟨_, rfl, by simpa [Region.mem, FieldAt] using hm⟩
  | fields y =>
    intro x p o hs hm
    simp only [fieldSite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
    exact ⟨_, rfl, by simpa [Region.mem, FieldAt] using hm⟩
  | path y q k =>
    intro x p o hs hm
    simp only [fieldSite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
    simp only [Region.mem] at hm
    split at hm
    · rename_i v hv; exact ⟨v, hv, by simpa [FieldAt] using hm⟩
    · cases hm
  | pathFields y q =>
    intro x p o hs hm
    simp only [fieldSite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
    simp only [Region.mem] at hm
    split at hm
    · rename_i v hv; exact ⟨v, hv, by simpa [FieldAt] using hm⟩
    · cases hm
  | inCls r c ih =>
    intro x p o hs hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hs hm.1
  | _ => intro x p o hs; simp [fieldSite] at hs

/-! ## Separation facts -/

/-- A separation a state's knowledge states. -/
inductive SepFact where
  /-- $`\pi \mathrel{\#} \pi'`$: the `[]` slots of the values the two paths
  read are different locations. -/
  | spines (a b : Nat × List String)
  /-- $`\mathrm{apart}(x, y)`$: the arrays the two paths read share no
  location, spine or cell (`RegionsApart`). -/
  | arrays (a b : Nat × List String)
  /-- The fields `F` of slot `x` (every own location where `none`) and the
  field `g` of slot `y` are different locations (`HeapSeparation.Apart`). -/
  | locs (x : Nat) (F : Option (List PropKey)) (y : Nat) (g : PropKey)
  deriving DecidableEq, Repr

/-- No value holds both a `[]` slot and a view spine: what valid
references give (`RefOk` of a view). -/
def Plain (u : Val) : Prop := spineOf u = none ∨ descriptorSpine u = none

def SepFact.Holds (ρ : Env) (h : Heap) : SepFact → Prop
  | .spines a b => ∀ u w l, readPath h (ρ a.1) a.2 = some u → readPath h (ρ b.1) b.2 = some w →
      spineOf u = some l → spineOf w = some l → False
  | .arrays a b => ∀ u w l, readPath h (ρ a.1) a.2 = some u → readPath h (ρ b.1) b.2 = some w →
      Plain u → Plain w → ArrayPart h u l → ArrayPart h w l → False
  | .locs x F y g => HeapSeparation.Apart ρ x F y g

/-- A value with valid references is plain. -/
theorem plain_of_refs {n : Nat} {W : WorldT n} {u : Val} (hu : RefsOk W u) : Plain u := by
  cases u with
  | objAt fs c i =>
    cases c with
    | view s f m =>
      have hmem : Ref.view s f m (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view s f m) i) := by
        simp [refs]
      have hp := (hu _ hmem).1
      left
      simpa [spineOf, fieldsOf] using hp
    | _ => right; rfl
  | _ => right; rfl

/-- The locations of a plain value's array lie in its region. -/
theorem regionOf_arrayPart {h : Heap} {u : Val} {s : Option Nat} {xs : List (Option Nat)}
    (hr : RegionOf h u s xs) (hp : Plain u) {l : Nat} (hl : ArrayPart h u l) : InRegion s xs l := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨st, rfl, hst, hx⟩
  · rcases hl with hl | hl
    · simp [elementsOf] at hl
    · simp [spineCells, entriesAt, descriptorSpine, fieldsOf] at hl
  · have hd : descriptorSpine u = none := by
      rcases hp with hp | hp
      · rw [hst] at hp; cases hp
      · exact hp
    rcases hl with hl | hl
    · rw [elementsOf_of_spineOf hst] at hl; cases hl; exact .inl rfl
    · simp only [spineCells, spineOf_lookup hst, hd, entriesAt, hx, Option.bind_some, spineEntries,
        Option.getD_some, List.append_nil] at hl
      exact .inr hl

/-- **Apart arrays share no location** of their spines or cells. -/
theorem regionsApart_arrays {h : Heap} {u w : Val} (ha : RegionsApart h u w) (hu : Plain u) (hw : Plain w)
    {l : Nat} (hl : ArrayPart h u l) (hl' : ArrayPart h w l) : False := by
  obtain ⟨sa, xs, sb, ys, hra, hrb, hne⟩ := ha
  exact hne l (regionOf_arrayPart hra hu hl) l (regionOf_arrayPart hrb hw hl') rfl

/-- The separation facts of an allocation's separation
(`HeapSeparation.Separation`): each fact's fields against each listed field
of each partner, at the slots its levels name. -/
def separationFacts (S : HeapSeparation.Separation) : List SepFact :=
  S.facts.flatMap fun a => a.partners.flatMap fun p => p.2.map fun g =>
    .locs (S.depth - 1 - a.slot) a.fields (S.depth - 1 - p.1) g

theorem separationFacts_holds {S : HeapSeparation.Separation} {ρ : Env} {h : Heap}
    (hS : HeapSeparation.Holds S ρ) : ∀ f ∈ separationFacts S, f.Holds ρ h := by
  intro f hf
  simp only [separationFacts, List.mem_flatMap, List.mem_map] at hf
  obtain ⟨a, ha, p, hp, g, hg, rfl⟩ := hf
  exact ((hS a ha).2 p hp).2 g hg

/-! ## Evidence -/

/-- **Separation evidence**: class evidence of fields, provenance stamps
against marks and the typed fields they cover, links, and separation
facts. -/
structure SepEvidence where
  cl : ClassEvidence := fun _ _ => none
  stamps : Stamps := ⟨fun _ => none, fun _ => none⟩
  typed : Nat → List PropKey := fun _ => []
  links : HeapLinks.Links := []
  facts : List SepFact := []

def SepEvidence.Holds (E : SepEvidence) (μ : Nat → Nat) (ρ : Env) (h : Heap) : Prop :=
  ClassOk E.cl ρ h ∧ StampsHold E.stamps E.typed μ ρ ∧ (∀ i j, i ≤ j → μ i ≤ μ j) ∧
    HeapLinks.Holds E.links ρ h ∧ ∀ f ∈ E.facts, f.Holds ρ h

/-- **A region's bound under the evidence**: a field's bound narrowed to
the classes of the category its class evidence gives (`Region.bound`
otherwise). -/
def SepEvidence.bound (E : SepEvidence) : Region → RoleSet
  | .field x k => match E.cl x k with
    | some c => (slotBound k).inter c.roles
    | none => slotBound k
  | .inCls r c => (E.bound r).inter c.roles
  | r => r.bound

theorem SepEvidence.bound_sound {E : SepEvidence} {μ : Nat → Nat} {n : Nat} {W : WorldT n} {h : Heap}
    {ρ : Env} (hE : E.Holds μ ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ) :
    ∀ (r : Region) {l : Nat}, l < h.length → r.mem ρ h l = true →
      ∃ role, roleAt W l = some role ∧ (E.bound r).contains role.cls = true := by
  intro r
  induction r with
  | field x k =>
    intro l hl hm
    obtain ⟨role, hr, hb⟩ := Region.bound_sound hok hρ (.field x k) hl hm
    simp only [SepEvidence.bound]
    split
    · rename_i c hc
      have hcls := hE.1 x k c l hc (by simpa [Region.mem] using hm) hl
      simp only [Region.mem] at hcls
      split at hcls
      · rename_i v hv
        obtain ⟨role', hr', hc'⟩ := selects_bound hok hv hcls
        rw [hr] at hr'; cases hr'
        exact ⟨role, hr, by simp [Region.bound] at hb; simp [hb, hc']⟩
      · cases hcls
    · exact ⟨role, hr, hb⟩
  | inCls r c ih =>
    intro l hl hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    obtain ⟨role, hr, hb⟩ := ih hl hm.1
    have hc := hm.2
    split at hc
    · rename_i v hv
      obtain ⟨role', hr', hc'⟩ := selects_bound hok hv hc
      rw [hr] at hr'; cases hr'
      exact ⟨role, hr, by simp [SepEvidence.bound, hb, hc']⟩
    · cases hc
  | _ =>
    intro l hl hm
    exact Region.bound_sound hok hρ _ hl hm

/-- Whether a fact separates `r` from `s`, its first site `r`'s and its
second `s`'s, each read through the links. -/
def SepEvidence.byFact (E : SepEvidence) (r s : Region) : SepFact → Bool
  | .spines a b => match spineSite r, spineSite s with
    | some x, some y => sameSite E.links (pathViews E.links x.1 x.2) (pathViews E.links a.1 a.2) &&
        sameSite E.links (pathViews E.links y.1 y.2) (pathViews E.links b.1 b.2)
    | _, _ => false
  | .arrays a b => match arraySite r, arraySite s with
    | some x, some y => sameSite E.links (pathViews E.links x.1 x.2) (pathViews E.links a.1 a.2) &&
        sameSite E.links (pathViews E.links y.1 y.2) (pathViews E.links b.1 b.2)
    | _, _ => false
  | .locs x F y g => match fieldSite r, fieldSite s with
    | some (sx, o), some (sy, some g') =>
      (slotsOf E.links sx.1 sx.2).contains x && (match o with
        | some k => HeapSeparation.covers F k
        | none => F.isNone) &&
      (slotsOf E.links sy.1 sy.2).contains y && g' == g
    | _, _ => false

/-- $`\mathrm{fresh}(r)`$: every own location of the value `r` reads lies at
or above a mark at or above the one a typed field `s` selects lies below. -/
def SepEvidence.fresh (E : SepEvidence) (r s : Region) : Bool :=
  match fieldSite r, fieldSite s with
  | some (sx, _), some (sy, some k) =>
    (slotsOf E.links sx.1 sx.2).any fun x => (slotsOf E.links sy.1 sy.2).any fun y =>
      (E.typed y).contains k && match E.stamps.after x, E.stamps.before y with
        | some m, some m' => decide (m' ≤ m)
        | _, _ => false
  | _, _ => false

/-- **The one disjointness check**: by the regions' bounds under the
evidence or their keys (`Region.keysApart`), by freshness, or by a
separation fact, either way round. -/
def SepEvidence.query (E : SepEvidence) : SepQuery :=
  ⟨fun r s => (((E.bound r).inter (E.bound s)).isEmpty || r.keysApart s) || E.fresh r s || E.fresh s r ||
    E.facts.any fun f => E.byFact r s f || E.byFact s r f⟩

theorem SepEvidence.byFact_sound {E : SepEvidence} {μ : Nat → Nat} {n : Nat} {W : WorldT n} {h : Heap}
    {ρ : Env} (hE : E.Holds μ ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ) {f : SepFact} (hf : f ∈ E.facts)
    {r s : Region} (hb : E.byFact r s f = true) {l : Nat} (hr : r.mem ρ h l = true)
    (hs : s.mem ρ h l = true) : False := by
  have hl := hE.2.2.2.1
  have hF := hE.2.2.2.2 f hf
  cases f with
  | spines a b =>
    simp only [SepEvidence.byFact] at hb
    split at hb
    · rename_i x y hx hy
      simp only [Bool.and_eq_true] at hb
      obtain ⟨u, hu, hul⟩ := spineSite_mem hx hr
      obtain ⟨w, hw, hwl⟩ := spineSite_mem hy hs
      rw [sameSite_read hl hb.1] at hu; rw [sameSite_read hl hb.2] at hw
      exact hF u w l hu hw hul hwl
    · cases hb
  | arrays a b =>
    simp only [SepEvidence.byFact] at hb
    split at hb
    · rename_i x y hx hy
      simp only [Bool.and_eq_true] at hb
      obtain ⟨u, hu, hul⟩ := arraySite_mem hx hr
      obtain ⟨w, hw, hwl⟩ := arraySite_mem hy hs
      have hpu := plain_of_refs (readPath_refs hok x.2 (hρ x.1) hu)
      have hpw := plain_of_refs (readPath_refs hok y.2 (hρ y.1) hw)
      rw [sameSite_read hl hb.1] at hu; rw [sameSite_read hl hb.2] at hw
      exact hF u w l hu hw hpu hpw hul hwl
    · cases hb
  | locs x F y g =>
    simp only [SepEvidence.byFact] at hb
    split at hb
    · rename_i sx o sy g' hx hy
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hb
      obtain ⟨⟨⟨hxs, hcov⟩, hys⟩, rfl⟩ := hb
      obtain ⟨v, hv, hvl⟩ := fieldSite_mem hx hr
      obtain ⟨v', hv', hvl'⟩ := fieldSite_mem hy hs
      rw [slotsOf_read hl hxs] at hv; cases hv
      rw [slotsOf_read hl hys] at hv'; cases hv'
      cases hρx : ρ x with
      | objAt flds c oid =>
        cases hρy : ρ y with
        | objAt flds' c' oid' =>
          rw [hρy] at hvl'
          have hat' : HeapSeparation.At (some [g']) (ρ y) l := by
            rw [hρy]; exact HeapSeparation.at_lookup (by simpa [FieldAt, fieldsOf] using hvl')
          have hat : HeapSeparation.At F (ρ x) l := by
            rw [hρx] at hvl ⊢
            cases o with
            | some k =>
              exact HeapSeparation.at_of_single hcov (HeapSeparation.at_lookup (by simpa [FieldAt, fieldsOf] using hvl))
            | none =>
              simp only [Option.isNone_iff_eq_none] at hcov
              subst hcov
              simpa [HeapSeparation.At, fieldsOf] using fieldLocs_own (v := .objAt flds c oid) hvl
          exact hF l l hat hat' rfl
        | _ => rw [hρy] at hvl'; simp [FieldAt, fieldsOf] at hvl'
      | _ => rw [hρx] at hvl; have := hvl.own; simp [fieldsOf] at this
    · cases hb

theorem SepEvidence.fresh_sound {E : SepEvidence} {μ : Nat → Nat} {h : Heap} {ρ : Env}
    (hE : E.Holds μ ρ h) {r s : Region} (hb : E.fresh r s = true) {l : Nat} (hr : r.mem ρ h l = true)
    (hs : s.mem ρ h l = true) : False := by
  have hl := hE.2.2.2.1
  simp only [SepEvidence.fresh] at hb
  split at hb
  · rename_i sx o sy k hx hy
    obtain ⟨x, hxs, hb⟩ := List.any_eq_true.mp hb
    obtain ⟨y, hys, hb⟩ := List.any_eq_true.mp hb
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hb
    obtain ⟨hk, hm⟩ := hb
    obtain ⟨v, hv, hvl⟩ := fieldSite_mem hx hr
    obtain ⟨v', hv', hvl'⟩ := fieldSite_mem hy hs
    rw [slotsOf_read hl hxs] at hv; cases hv
    rw [slotsOf_read hl hys] at hv'; cases hv'
    cases ha : E.stamps.after x with
    | none => simp [ha] at hm
    | some m =>
      cases hb' : E.stamps.before y with
      | none => simp [ha, hb'] at hm
      | some m' =>
        simp only [ha, hb', decide_eq_true_eq] at hm
        have h₁ := hE.2.1.1 x m ha l hvl.own
        have h₂ := hE.2.1.2 y m' hb' k hk l hvl'
        have h₃ := hE.2.2.1 m' m hm
        omega
  · cases hb

/-- **The one disjointness check is sound** at a heap meeting its world
with valid roots, where the evidence holds. -/
theorem SepEvidence.query_sound {E : SepEvidence} {μ : Nat → Nat} {n : Nat} {W : WorldT n} {h : Heap}
    {ρ : Env} (hE : E.Holds μ ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ) : E.query.Sound ρ h := by
  intro r s l hl hd hr hs
  simp only [SepEvidence.query, Bool.or_eq_true] at hd
  rcases hd with (((hd | hd) | hd) | hd) | hd
  · obtain ⟨role, hrole, hb⟩ := E.bound_sound hE hok hρ r hl hr
    obtain ⟨role', hrole', hb'⟩ := E.bound_sound hE hok hρ s hl hs
    rw [hrole] at hrole'; cases hrole'
    rw [RoleSet.inter_isEmpty hd hb] at hb'
    cases hb'
  · exact Region.apart_of_keys hok hρ hd hr hs
  · exact SepEvidence.fresh_sound hE hd hr hs
  · exact SepEvidence.fresh_sound hE hd hs hr
  · obtain ⟨f, hf, hb⟩ := List.any_eq_true.mp hd
    simp only [Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact SepEvidence.byFact_sound hE hok hρ hf hb hr hs
    · exact SepEvidence.byFact_sound hE hok hρ hf hb hs hr

/-! ## The check answers every pair its parts answer -/

theorem RoleSet.inter_comm (a b : RoleSet) : a.inter b = b.inter a := by
  rcases a with ⟨_, _, _, _, _, _⟩; rcases b with ⟨_, _, _, _, _, _⟩
  simp [RoleSet.inter, Bool.and_comm]

/-- The check is symmetric. -/
theorem SepEvidence.query_symm (E : SepEvidence) (r s : Region) :
    E.query.disjoint r s = E.query.disjoint s r := by
  simp only [SepEvidence.query, RoleSet.inter_comm (E.bound r), Region.keysApart_symm r s]
  cases ((E.bound s).inter (E.bound r)).isEmpty <;> cases s.keysApart r <;> cases E.fresh r s <;>
    cases E.fresh s r <;> simp [Bool.or_comm]

/-- A region's bound under the evidence is within its bound. -/
theorem SepEvidence.bound_le (E : SepEvidence) :
    ∀ (r : Region) (c : RoleClass), (E.bound r).contains c = true → r.bound.contains c = true := by
  intro r
  induction r with
  | field x k =>
    intro c hc
    simp only [SepEvidence.bound] at hc
    split at hc
    · simp only [RoleSet.contains_inter, Bool.and_eq_true] at hc; exact hc.1
    · exact hc
  | inCls r c' ih =>
    intro c hc
    simp only [SepEvidence.bound, RoleSet.contains_inter, Bool.and_eq_true] at hc
    simp only [Region.bound, RoleSet.contains_inter, Bool.and_eq_true]
    exact ⟨ih c hc.1, hc.2⟩
  | _ => intro c hc; exact hc

/-- **Every pair the bounds separate, the check separates**
(`boundQuery`). -/
theorem SepEvidence.query_of_bound (E : SepEvidence) {r s : Region}
    (hd : boundQuery.disjoint r s = true) : E.query.disjoint r s = true := by
  simp only [boundQuery, Bool.or_eq_true] at hd
  rcases hd with hd | hd
  case inr => simp [SepEvidence.query, hd]
  have : ((E.bound r).inter (E.bound s)).isEmpty = true := by
    refine RoleSet.isEmpty_iff.mpr fun c => ?_
    have h0 := RoleSet.isEmpty_iff.mp hd c
    simp only [RoleSet.contains_inter] at h0 ⊢
    cases hr : (E.bound r).contains c
    · simp
    · cases hs : (E.bound s).contains c
      · simp
      · simp [E.bound_le r c hr, E.bound_le s c hs] at h0
  simp [SepEvidence.query, this]

/-- **A part of a region in a class is separated from whatever the region
is.** -/
theorem SepEvidence.query_inCls_left (E : SepEvidence) {r s : Region} (c : Selector)
    (hd : E.query.disjoint r s = true) : E.query.disjoint (.inCls r c) s = true := by
  simp only [SepEvidence.query, Bool.or_eq_true] at hd ⊢
  have hb : ∀ c', (E.bound (.inCls r c)).contains c' = true → (E.bound r).contains c' = true := by
    intro c' h; simp only [SepEvidence.bound, RoleSet.contains_inter, Bool.and_eq_true] at h; exact h.1
  rcases hd with (((hd | hd) | hd) | hd) | hd
  · left; left; left; left
    refine RoleSet.isEmpty_iff.mpr fun c' => ?_
    have h0 := RoleSet.isEmpty_iff.mp hd c'
    simp only [RoleSet.contains_inter] at h0 ⊢
    cases hr : (E.bound (.inCls r c)).contains c'
    · simp
    · simp only [hb c' hr, Bool.true_and] at h0; simp [h0]
  · left; left; left; right; simpa [Region.keysApart, Region.key?] using hd
  · left; left; right; simpa [SepEvidence.fresh, fieldSite] using hd
  · left; right; simpa [SepEvidence.fresh, fieldSite] using hd
  · right
    obtain ⟨f, hf, hm⟩ := List.any_eq_true.mp hd
    refine List.any_eq_true.mpr ⟨f, hf, ?_⟩
    cases f <;> simpa [SepEvidence.byFact, spineSite, arraySite, fieldSite] using hm

/-- A field whose class evidence is a class disjoint from `c` is
separated from every region bounded by `c`'s classes: `cls c`, the part of
a region in `c`, a module cell where `c` is the values. -/
theorem SepEvidence.query_field_class (E : SepEvidence) {x : Nat} {k : PropKey} {c c' : Selector}
    (hc : E.cl x k = some c') (hd : c'.disjoint c = true) {s : Region}
    (hs : ∀ cl, (E.bound s).contains cl = true → c.roles.contains cl = true) :
    E.query.disjoint (.field x k) s = true := by
  have h0 := (Selector.roles_inter_isEmpty c' c).trans hd
  have : ((E.bound (.field x k)).inter (E.bound s)).isEmpty = true := by
    refine RoleSet.isEmpty_iff.mpr fun cl => ?_
    have h1 := RoleSet.isEmpty_iff.mp h0 cl
    simp only [SepEvidence.bound, hc, RoleSet.contains_inter] at h1 ⊢
    cases h2 : (E.bound s).contains cl
    · simp
    · simp only [hs cl h2, Bool.and_true] at h1; simp [h1]
  simp [SepEvidence.query, this]

/-- A fact the evidence lists separates its two sites. -/
theorem SepEvidence.query_fact (E : SepEvidence) {f : SepFact} (hf : f ∈ E.facts) {r s : Region}
    (hb : E.byFact r s f = true) : E.query.disjoint r s = true := by
  simp only [SepEvidence.query, Bool.or_eq_true]
  right
  exact List.any_eq_true.mpr ⟨f, hf, by simp [hb]⟩


/-! ## Each separation a field class, a stamp or a listed fact gives

Every pair the case table of the stability check separated, the check
separates: a field against a region in a disjoint class
(`query_field_class`), a part in a class (`query_inCls_left`,
`query_of_bound` with `boundQuery_inCls_cls`), fresh own locations against
an older typed field (`query_fresh`), two listed distinct fields
(`query_locs`), a path's spine against a slot's (`query_spines`), and the
cells of a path, element cells by their bound, against a spine field or a
class other than the values (`query_pathCells_field`,
`query_pathCells_cls`). -/

theorem slotsOf_self (ls : HeapLinks.Links) (x : Nat) : x ∈ slotsOf ls x [] := by
  simp [slotsOf, pathViews, HeapLinks.aliases]

theorem sameSite_self (ls : HeapLinks.Links) (x : Nat) (p : List String) :
    sameSite ls (pathViews ls x p) (pathViews ls x p) = true := by
  have hx : (x, p) ∈ pathViews ls x p := by cases p <;> simp [pathViews]
  refine List.any_eq_true.mpr ⟨(x, p), hx, List.any_eq_true.mpr ⟨(x, p), hx, ?_⟩⟩
  simp [HeapLinks.aliases]

theorem SepEvidence.query_fresh (E : SepEvidence) {x y : Nat} {k' : PropKey} {m m' : Nat}
    (ha : E.stamps.after x = some m) (hb : E.stamps.before y = some m') (hk : k' ∈ E.typed y)
    (hm : m' ≤ m) {r : Region} (hr : r = .fields x ∨ ∃ k, r = .field x k) :
    E.query.disjoint r (.field y k') = true := by
  have hf : E.fresh r (.field y k') = true := by
    have hfr : ∃ o, fieldSite r = some ((x, []), o) := by
      rcases hr with rfl | ⟨k, rfl⟩
      · exact ⟨none, rfl⟩
      · exact ⟨some k, rfl⟩
    obtain ⟨o, ho⟩ := hfr
    simp only [SepEvidence.fresh, ho, fieldSite]
    refine List.any_eq_true.mpr ⟨x, slotsOf_self _ _, List.any_eq_true.mpr ⟨y, slotsOf_self _ _, ?_⟩⟩
    simp [ha, hb, hk, hm]
  simp [SepEvidence.query, hf]

theorem SepEvidence.query_locs (E : SepEvidence) {x y : Nat} {k k' : PropKey}
    (hf : SepFact.locs x (some [k]) y k' ∈ E.facts) : E.query.disjoint (.field x k) (.field y k') = true :=
  E.query_fact hf (by simp [SepEvidence.byFact, fieldSite, slotsOf_self, HeapSeparation.covers])

theorem SepEvidence.query_spines (E : SepEvidence) {x y : Nat} {p : List String}
    (hf : SepFact.spines (x, p) (y, []) ∈ E.facts) :
    E.query.disjoint (.path x p arraySpineKey) (.field y arraySpineKey) = true :=
  E.query_fact hf (by simp [SepEvidence.byFact, spineSite, sameSite_self])

theorem SepEvidence.query_pathCells_field (E : SepEvidence) (x : Nat) (p : List String) {y : Nat}
    {k : PropKey} (hc : E.cl y k = some .spines) : E.query.disjoint (.pathCells x p) (.field y k) = true := by
  have := (E.query_field_class (s := .pathCells x p) hc (c := .values) rfl
    (fun cl h => by revert h; cases cl <;> simp [SepEvidence.bound, Region.bound, RoleSet.contains, RoleSet.elems,
      Selector.roles, RoleSet.ofCategories, Selector.has]))
  rwa [E.query_symm]

theorem SepEvidence.query_pathCells_cls (E : SepEvidence) (x : Nat) (p : List String) {c : Selector}
    (hd : Selector.values.disjoint c = true) : E.query.disjoint (.pathCells x p) (.cls c) = true := by
  refine E.query_of_bound (boundQuery_of_isEmpty (RoleSet.isEmpty_iff.mpr fun cl => ?_))
  rcases c with ⟨v, a, w⟩
  simp only [Selector.disjoint, Selector.values] at hd
  cases v <;> simp at hd
  cases cl <;> simp [Region.bound, RoleSet.contains, RoleSet.inter, RoleSet.elems, Selector.roles,
    RoleSet.ofCategories, Selector.has]

end Verification.Footprints
