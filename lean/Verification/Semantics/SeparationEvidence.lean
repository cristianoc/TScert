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
        simp only [ha, ho, Bool.false_eq_true, ite_false] at hlink
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
  | _ => none

/-- A site whose spine a region selects: a `[]` slot (`spineSite`) or a
selected spine (`.spine x p`, which on a non-view is its `[]` slot and on a
view selects a view spine, disjoint from every `[]` slot). -/
def selectedSpineSite : Region → Option (Nat × List String)
  | .path x p k => if k == arraySpineKey then some (x, p) else none
  | .field x k => if k == arraySpineKey then some (x, []) else none
  | .spine x p => some (x, p)
  | _ => none

theorem spineSite_mem {ρ : Env} {h : Heap} {l : Nat} :
    ∀ {r : Region} {x : Nat} {p : List String}, spineSite r = some (x, p) → r.mem ρ h l = true →
      ∃ u, readPath h (ρ x) p = some u ∧ spineOf u = some l := by
  intro r
  cases r with
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
  | _ => intro x p hs; simp [spineSite] at hs

theorem spineSite_role {n : Nat} {W : WorldT n} {ρ : Env} {h : Heap} {l : Nat}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) {r : Region} {x : Nat} {p : List String}
    (hs : spineSite r = some (x, p)) (hm : r.mem ρ h l = true) :
    roleAt W l = some (.spine .array) := by
  obtain ⟨u, hu, hsp⟩ := spineSite_mem hs hm
  have hsr := slotRole_of_refs (readPath_refs hok p (hρ x) hu) (k := arraySpineKey) (l := l) (by simpa [spineOf] using hsp)
  rcases hr : roleAt W l with _ | role
  · rw [hr] at hsr; cases hsr
  · rw [hr] at hsr
    cases role with
    | spine f => cases f with
      | array => rfl
      | view => simp [SlotRole] at hsr
    | _ => simp [SlotRole] at hsr

theorem selectedSpineSite_array_mem {n : Nat} {W : WorldT n} {ρ : Env} {h : Heap} {l : Nat}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) (hrole : roleAt W l = some (.spine .array)) :
    ∀ {r : Region} {x : Nat} {p : List String}, selectedSpineSite r = some (x, p) → r.mem ρ h l = true →
      ∃ u, readPath h (ρ x) p = some u ∧ spineOf u = some l := by
  intro r
  cases r with
  | path y q k =>
    intro x p hs hm
    exact spineSite_mem (by simpa [selectedSpineSite, spineSite] using hs) hm
  | field y k =>
    intro x p hs hm
    exact spineSite_mem (by simpa [selectedSpineSite, spineSite] using hs) hm
  | spine y q =>
    intro x p hs hm
    simp only [selectedSpineSite, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Region.mem] at hm
    split at hm
    · rename_i u hu
      have href := readPath_refs hok q (hρ y) hu
      cases u with
      | objAt fs c i =>
        simp only [elementsOf, beq_iff_eq] at hm
        cases hk : fs.lookup arraySpineKey with
        | some s =>
          rw [hk] at hm; cases hm
          exact ⟨.objAt fs c i, hu, by simpa [spineOf, fieldsOf] using hk⟩
        | none =>
          rw [hk] at hm
          cases c with
          | view s f m =>
            cases hm
            have hmem : Ref.view l f m (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view l f m) i) := by
              simp [refs]
            have hvr : roleAt W l = some (.spine (.view f m)) := (href _ hmem).2
            rw [hrole] at hvr; cases hvr
          | _ => simp at hm
      | _ => simp [elementsOf] at hm
    · cases hm
  | _ => intro x p hs; simp [selectedSpineSite] at hs

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
  | .fields _, _, h | .cells _, _, h | .cls _, _, h | .all, _, h | .pathFields _ _, _, h
  | .pathCells _ _, _, h | .spine _ _, _, h | .elemSpines _ _, _, h => by simp [spineSite] at h

theorem arraySite_mem {ρ : Env} {h : Heap} {l : Nat} :
    ∀ {r : Region} {x : Nat} {p : List String}, arraySite r = some (x, p) → r.mem ρ h l = true →
      ∃ u, readPath h (ρ x) p = some u ∧ ArrayPart h u l := by
  intro r
  cases r with
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
  | _ => intro x p hs; simp [arraySite] at hs

/-- The fields site a region selects within: the value a path reads, and
the key of its field (`none`: every own location). -/
def fieldSite : Region → Option ((Nat × List String) × Option PropKey)
  | .field x k => some ((x, []), some k)
  | .path x p k => some ((x, p), some k)
  | .fields x => some ((x, []), none)
  | .pathFields x p => some ((x, p), none)
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
  cases r with
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
  /-- The spine of path `a` is distinct from the spine of every element stored
  in path `b` (`PathElemSpinesApart`). -/
  | elemSpines (a b : Nat × List String)
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
  | .elemSpines a b => ∀ u w l, readPath h (ρ a.1) a.2 = some u → readPath h (ρ b.1) b.2 = some w →
      Plain w → spineOf u = some l →
      ∀ c, some c ∈ spineCells h w → ∀ e, h[c]? = some e → spineOf e = some l → False
  | .locs x F y g => HeapSeparation.Apart ρ x F y g

theorem spineCells_of_plain {h : Heap} {w : Val} (hp : Plain w) {c : Nat}
    (hc : some c ∈ spineCells h w) :
    ∃ st ls, elementsOf w = some st ∧ h[st]?.bind spineEntries = some ls ∧ some c ∈ ls := by
  simp only [spineCells, List.mem_append] at hc
  rcases hc with hc | hc
  · cases hl : (fieldsOf w).lookup arraySpineKey with
    | none => rw [hl] at hc; simp [entriesAt] at hc
    | some st =>
      rw [hl] at hc; simp only [entriesAt] at hc
      cases hls : h[st]?.bind spineEntries with
      | none => rw [hls] at hc; simp at hc
      | some ls =>
        rw [hls] at hc
        have hsp : spineOf w = some st := by cases w <;> simp_all [spineOf, fieldsOf]
        exact ⟨st, ls, elementsOf_of_spineOf hsp, hls, by simpa using hc⟩
  · cases hd : descriptorSpine w with
    | none => rw [hd] at hc; simp [entriesAt] at hc
    | some st =>
      have hsp : spineOf w = none := hp.resolve_right (by rw [hd]; simp)
      rw [hd] at hc; simp only [entriesAt] at hc
      cases hls : h[st]?.bind spineEntries with
      | none => rw [hls] at hc; simp at hc
      | some ls =>
        rw [hls] at hc
        have hel : elementsOf w = some st := by
          cases w with
          | objAt fs cd oid =>
            simp only [spineOf, fieldsOf] at hsp
            cases cd with
            | view s' _ _ =>
              simp only [descriptorSpine, Option.some.injEq] at hd; subst hd
              simp [elementsOf, hsp]
            | _ => simp [descriptorSpine] at hd
          | _ => simp [descriptorSpine] at hd
        exact ⟨st, ls, hel, hls, by simpa using hc⟩

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
  cl : ClassEvidence := noClassEvidence
  stamps : Stamps := ⟨fun _ => none, fun _ => none⟩
  typed : Nat → List PropKey := fun _ => []
  links : HeapLinks.Links := []
  facts : List SepFact := []

def SepEvidence.Holds (E : SepEvidence) (μ : Nat → Nat) (ρ : Env) (h : Heap) : Prop :=
  ClassOk E.cl ρ h ∧ StampsHold E.stamps E.typed μ ρ ∧ (∀ i j, i ≤ j → μ i ≤ μ j) ∧
    HeapLinks.Holds E.links ρ h ∧ ∀ f ∈ E.facts, f.Holds ρ h

/-- **A region's bound under the evidence**: narrowed to the kinds of the
category its class evidence gives (`Region.bound` otherwise). -/
def SepEvidence.bound (E : SepEvidence) (r : Region) : KindSet :=
  match E.cl r with
  | some c => r.bound.inter c.kinds
  | none => r.bound

theorem SepEvidence.bound_sound {E : SepEvidence} {μ : Nat → Nat} {n : Nat} {W : WorldT n} {h : Heap}
    {ρ : Env} (hE : E.Holds μ ρ h) (hok : HeapOk n W h) (hρ : RootsOk W ρ) :
    ∀ (r : Region) {l : Nat}, l < h.length → r.mem ρ h l = true →
      ∃ role, roleAt W l = some role ∧ (E.bound r).contains role.kind = true := by
  intro r l hl hm
  obtain ⟨role, hr, hb⟩ := Region.bound_sound hok hρ r hl hm
  simp only [SepEvidence.bound]
  split
  · rename_i c hc
    have hcls := hE.1 r c l hc hm hl
    simp only [Region.mem] at hcls
    split at hcls
    · rename_i v hv
      obtain ⟨role', hr', hc'⟩ := selects_bound hok hv hcls
      rw [hr] at hr'; cases hr'
      exact ⟨role, hr, by simp [hb, hc']⟩
    · cases hcls
  · exact ⟨role, hr, hb⟩

/-- Whether a fact separates `r` from `s`, its first site `r`'s and its
second `s`'s, each read through the links. -/
def SepEvidence.byFact (E : SepEvidence) (r s : Region) : SepFact → Bool
  | .spines a b =>
    let pair (x y : Nat × List String) : Bool :=
      sameSite E.links (pathViews E.links x.1 x.2) (pathViews E.links a.1 a.2) &&
        sameSite E.links (pathViews E.links y.1 y.2) (pathViews E.links b.1 b.2)
    match spineSite r, spineSite s with
    | some x, some y => pair x y
    | some x, none => match selectedSpineSite s with
      | some y => pair x y
      | none => false
    | none, some y => match selectedSpineSite r with
      | some x => pair x y
      | none => false
    | none, none => false
  | .arrays a b => match arraySite r, arraySite s with
    | some x, some y => sameSite E.links (pathViews E.links x.1 x.2) (pathViews E.links a.1 a.2) &&
        sameSite E.links (pathViews E.links y.1 y.2) (pathViews E.links b.1 b.2)
    | _, _ => false
  | .elemSpines a b => match spineSite r, s with
    | some x, .elemSpines y q =>
        sameSite E.links (pathViews E.links x.1 x.2) (pathViews E.links a.1 a.2) &&
        sameSite E.links (pathViews E.links y q) (pathViews E.links b.1 b.2)
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
    · rename_i x hx _
      split at hb
      · rename_i y hy
        simp only [Bool.and_eq_true] at hb
        obtain ⟨u, hu, hul⟩ := spineSite_mem hx hr
        have hrole := spineSite_role hok hρ hx hr
        obtain ⟨w, hw, hwl⟩ := selectedSpineSite_array_mem hok hρ hrole hy hs
        rw [sameSite_read hl hb.1] at hu; rw [sameSite_read hl hb.2] at hw
        exact hF u w l hu hw hul hwl
      · cases hb
    · rename_i y _ hy
      split at hb
      · rename_i x hx
        simp only [Bool.and_eq_true] at hb
        have hrole := spineSite_role hok hρ hy hs
        obtain ⟨u, hu, hul⟩ := selectedSpineSite_array_mem hok hρ hrole hx hr
        obtain ⟨w, hw, hwl⟩ := spineSite_mem hy hs
        rw [sameSite_read hl hb.1] at hu; rw [sameSite_read hl hb.2] at hw
        exact hF u w l hu hw hul hwl
      · cases hb
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
  | elemSpines a b =>
    simp only [SepEvidence.byFact] at hb
    split at hb
    · rename_i x y q hx
      simp only [Bool.and_eq_true] at hb
      obtain ⟨u, hu, hul⟩ := spineSite_mem hx hr
      simp only [Region.mem] at hs
      cases hw : readPath h (ρ y) q with
      | none => rw [hw] at hs; cases hs
      | some w =>
        rw [hw] at hs
        simp only [List.any_eq_true] at hs
        obtain ⟨o, ho, hm⟩ := hs
        cases o with
        | none => cases hm
        | some c =>
          dsimp only at hm
          cases he : h[c]? with
          | none => rw [he] at hm; cases hm
          | some e =>
            rw [he] at hm
            simp only [beq_iff_eq] at hm
            have hpw := plain_of_refs (readPath_refs hok q (hρ y) hw)
            rw [sameSite_read hl hb.1] at hu; rw [sameSite_read hl hb.2] at hw
            exact hF u w l hu hw hpw hul c ho e he (by simpa [spineOf] using hm)
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
    rw [KindSet.inter_isEmpty hd hb] at hb'
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

/-- The check is symmetric. -/
theorem SepEvidence.query_symm (E : SepEvidence) (r s : Region) :
    E.query.disjoint r s = E.query.disjoint s r := by
  simp only [SepEvidence.query, KindSet.inter_comm (E.bound r), Region.keysApart_symm r s]
  cases ((E.bound s).inter (E.bound r)).isEmpty <;> cases s.keysApart r <;> cases E.fresh r s <;>
    cases E.fresh s r <;> simp [Bool.or_comm]

/-- A region's bound under the evidence is within its bound. -/
theorem SepEvidence.bound_le (E : SepEvidence) :
    ∀ (r : Region) (k : Kind), (E.bound r).contains k = true → r.bound.contains k = true := by
  intro r k hk
  simp only [SepEvidence.bound] at hk
  split at hk
  · simp only [KindSet.contains_inter, Bool.and_eq_true] at hk; exact hk.1
  · exact hk

/-- **Every pair the bounds separate, the check separates**
(`boundQuery`). -/
theorem SepEvidence.query_of_bound (E : SepEvidence) {r s : Region}
    (hd : boundQuery.disjoint r s = true) : E.query.disjoint r s = true := by
  simp only [boundQuery, Bool.or_eq_true] at hd
  rcases hd with hd | hd
  case inr => simp [SepEvidence.query, hd]
  have : ((E.bound r).inter (E.bound s)).isEmpty = true := by
    refine KindSet.isEmpty_iff.mpr fun k => ?_
    have h0 := KindSet.isEmpty_iff.mp hd k
    simp only [KindSet.contains_inter] at h0 ⊢
    cases hr : (E.bound r).contains k
    · simp
    · cases hs : (E.bound s).contains k
      · simp
      · simp [E.bound_le r k hr, E.bound_le s k hs] at h0
  simp [SepEvidence.query, this]

/-- A region whose class evidence is a class disjoint from `c` is separated
from every region bounded by `c`'s kinds: `cls c`, a field or cell where
`c` is the values. -/
theorem SepEvidence.query_region_class (E : SepEvidence) {r : Region} {c c' : Selector}
    (hc : E.cl r = some c') (hd : c'.disjoint c = true) {s : Region}
    (hs : ∀ kd, (E.bound s).contains kd = true → c.kinds.contains kd = true) :
    E.query.disjoint r s = true := by
  have h0 := (Selector.kinds_inter_isEmpty c' c).trans hd
  have : ((E.bound r).inter (E.bound s)).isEmpty = true := by
    refine KindSet.isEmpty_iff.mpr fun kd => ?_
    have h1 := KindSet.isEmpty_iff.mp h0 kd
    simp only [KindSet.contains_inter] at h1 ⊢
    cases h2 : (E.bound s).contains kd
    · simp
    · simp only [SepEvidence.bound, hc, KindSet.contains_inter]
      simp only [hs kd h2, Bool.and_true] at h1
      simp [h1]
  simp [SepEvidence.query, this]

/-- A fact the evidence lists separates its two sites. -/
theorem SepEvidence.query_fact (E : SepEvidence) {f : SepFact} (hf : f ∈ E.facts) {r s : Region}
    (hb : E.byFact r s f = true) : E.query.disjoint r s = true := by
  simp only [SepEvidence.query, Bool.or_eq_true]
  right
  exact List.any_eq_true.mpr ⟨f, hf, by simp [hb]⟩


/-! ## Each separation a class, a stamp or a listed fact gives

Every pair the case table of the stability check separated, the check
separates: a region against one in a disjoint class
(`query_region_class`, `query_of_bound` with `boundQuery_cats_cls`), fresh
own locations against an older typed field (`query_fresh`), two listed
distinct fields (`query_locs`), a path's spine against a slot's
(`query_spines`), and the cells of a path, element cells by their bound,
against a spine field or a class other than the values
(`query_pathCells_field`, `query_pathCells_cls`). -/

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
    have hfy : fieldSite (.field y k') = some ((y, []), some k') := rfl
    simp only [SepEvidence.fresh, ho, hfy]
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
    {k : PropKey} (hc : E.cl (.field y k) = some .spines) : E.query.disjoint (.pathCells x p) (.field y k) = true := by
  have := (E.query_region_class (s := .pathCells x p) hc (c := .values) rfl
    (fun kd h => by
      have hb := E.bound_le (.pathCells x p) kd h
      cases kd <;> simp [Region.bound, KindSet.contains, KindSet.elems,
        Selector.kinds, KindSet.ofCategories, Selector.has] at hb ⊢))
  rwa [E.query_symm]

theorem SepEvidence.query_pathCells_cls (E : SepEvidence) (x : Nat) (p : List String) {c : Selector}
    (hd : Selector.values.disjoint c = true) : E.query.disjoint (.pathCells x p) (.cls c) = true := by
  refine E.query_of_bound (boundQuery_of_isEmpty (KindSet.isEmpty_iff.mpr fun kd => ?_))
  rcases c with ⟨v, a, w⟩
  simp only [Selector.disjoint, Selector.values] at hd
  cases v <;> simp at hd
  cases kd <;> simp [Region.bound, KindSet.contains, KindSet.inter, KindSet.elems, Selector.kinds,
    KindSet.ofCategories, Selector.has]

/-! ## Pre-indexed separation query (`@[csimp]` replacement for `SepEvidence.query`) -/

/-- Hash map indexing non-alias, non-optional string read links by `(cell, field)`. -/
def pathViewsReads (ls : HeapLinks.Links) : Std.HashMap (Nat × String) (List Nat) :=
  ls.reverse.foldl (fun m g =>
    if !g.alias && !g.optional then match g.field with
    | .str f => m.insert (g.cell, f) (g.value :: m.getD (g.cell, f) [])
    | .sym _ => m
    else m) {}

private theorem pathViewsReads_mem (ls : HeapLinks.Links) (c : Nat) (f : String) (v : Nat) :
    v ∈ (pathViewsReads ls).getD (c, f) [] ↔
      ∃ g ∈ ls, g.alias = false ∧ g.optional = false ∧ g.field = .str f ∧ g.cell = c ∧ g.value = v := by
  unfold pathViewsReads
  have hgo : ∀ (xs : HeapLinks.Links) (m : Std.HashMap (Nat × String) (List Nat)),
      v ∈ (xs.foldl (fun m g =>
        if !g.alias && !g.optional then match g.field with
        | .str f' => m.insert (g.cell, f') (g.value :: m.getD (g.cell, f') [])
        | .sym _ => m
        else m) m).getD (c, f) [] ↔
      (∃ g ∈ xs, g.alias = false ∧ g.optional = false ∧ g.field = .str f ∧ g.cell = c ∧ g.value = v) ∨
        v ∈ m.getD (c, f) [] := by
    intro xs
    induction xs with
    | nil => intro m; simp
    | cons g xs ih =>
      intro m
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih]
      constructor
      · intro h
        rcases h with ⟨g', hg', hrest⟩ | hm
        · exact .inl ⟨g', .inr hg', hrest⟩
        · by_cases hao : (!g.alias && !g.optional) = true
          · simp only [hao, ↓reduceIte] at hm
            cases hgf : g.field with
            | sym _ => rw [hgf] at hm; exact .inr hm
            | str f' =>
              rw [hgf] at hm; dsimp only at hm
              rw [Std.HashMap.getD_insert] at hm
              split at hm
              · rename_i heq
                simp only [beq_iff_eq, Prod.mk.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                rcases List.mem_cons.mp hm with rfl | hm'
                · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hao
                  exact .inl ⟨g, .inl rfl, hao.1, hao.2, hgf, rfl, rfl⟩
                · exact .inr hm'
              · exact .inr hm
          · simp only [hao, Bool.false_eq_true, ↓reduceIte] at hm; exact .inr hm
      · intro h
        rcases h with ⟨g', rfl | hg', ha, ho, hgf, rfl, rfl⟩ | hm
        · right
          have hao : (!g'.alias && !g'.optional) = true := by simp [ha, ho]
          simp only [hao, ↓reduceIte, hgf]
          rw [Std.HashMap.getD_insert]
          simp
        · exact .inl ⟨g', hg', ha, ho, hgf, rfl, rfl⟩
        · right
          by_cases hao : (!g.alias && !g.optional) = true
          · simp only [hao, ↓reduceIte]
            cases hgf : g.field with
            | sym _ => exact hm
            | str f' =>
              dsimp only
              rw [Std.HashMap.getD_insert]
              split
              · rename_i heq
                simp only [beq_iff_eq, Prod.mk.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                exact List.mem_cons_of_mem _ hm
              · exact hm
          · simp only [hao, Bool.false_eq_true, ↓reduceIte]; exact hm
  have h := hgo ls.reverse {}
  simp only [Std.HashMap.getD_empty, List.not_mem_nil, or_false] at h
  rw [h]
  constructor <;> (rintro ⟨g, hg, hr⟩; exact ⟨g, by simpa using hg, hr⟩)

/-- Indexed `pathViews` using precomputed `aliasesMap` and `pathViewsReads`. -/
def pathViewsIdx (am : Std.HashMap Nat (List Nat)) (reads : Std.HashMap (Nat × String) (List Nat)) :
    Nat → List String → List (Nat × List String)
  | x, [] => [(x, [])]
  | x, f :: q => (x, f :: q) :: (HeapLinks.aliasesOf am x).flatMap fun c =>
      (reads.getD (c, f) []).flatMap fun v => pathViewsIdx am reads v q

private theorem pathViewsIdx_mem_iff (ls : HeapLinks.Links) :
    ∀ (p : List String) (x : Nat) (z : Nat × List String),
      z ∈ pathViewsIdx (HeapLinks.aliasesMap ls) (pathViewsReads ls) x p ↔ z ∈ pathViews ls x p := by
  intro p
  induction p with
  | nil => intro x z; simp [pathViewsIdx, pathViews]
  | cons f q ih =>
    intro x z
    simp only [pathViewsIdx, pathViews, List.mem_cons, List.mem_flatMap]
    constructor
    · rintro (rfl | ⟨c, hc, v, hv, hz⟩)
      · exact .inl rfl
      · rw [HeapLinks.aliasesOf_eq_aliases] at hc
        obtain ⟨g, hg, ha, ho, hgf, rfl, rfl⟩ := (pathViewsReads_mem ls c f v).mp hv
        right
        refine ⟨g, hg, ?_⟩
        have hcond : ((!g.alias && !g.optional) && (g.field == .str f) && (HeapLinks.aliases ls x).contains g.cell) = true := by
          simp [ha, ho, hgf, hc]
        simp only [hcond, ↓reduceIte]
        exact (ih g.value z).mp hz
    · rintro (rfl | ⟨g, hg, hz⟩)
      · exact .inl rfl
      · split at hz
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hcond
          obtain ⟨⟨⟨ha, ho⟩, hgf⟩, hc⟩ := hcond
          right
          refine ⟨g.cell, by rw [HeapLinks.aliasesOf_eq_aliases]; exact hc, g.value, ?_, (ih g.value z).mpr hz⟩
          exact (pathViewsReads_mem ls g.cell f g.value).mpr ⟨g, hg, ha, ho, hgf, rfl, rfl⟩
        · cases hz

def sameSiteIdx (am : Std.HashMap Nat (List Nat)) (X A : List (Nat × List String)) : Bool :=
  X.any fun x => A.any fun a => x.2 == a.2 && (HeapLinks.aliasesOf am x.1).contains a.1

private theorem sameSiteIdx_eq (ls : HeapLinks.Links) {X X' A A' : List (Nat × List String)}
    (hX : ∀ z, z ∈ X' ↔ z ∈ X) (hA : ∀ z, z ∈ A' ↔ z ∈ A) :
    sameSiteIdx (HeapLinks.aliasesMap ls) X' A' = sameSite ls X A := by
  apply Bool.eq_iff_iff.mpr
  simp only [sameSiteIdx, sameSite, List.any_eq_true, Bool.and_eq_true, HeapLinks.aliasesOf_eq_aliases]
  constructor
  · rintro ⟨x, hx, a, ha, h⟩; exact ⟨x, (hX x).mp hx, a, (hA a).mp ha, h⟩
  · rintro ⟨x, hx, a, ha, h⟩; exact ⟨x, (hX x).mpr hx, a, (hA a).mpr ha, h⟩

def slotsOfIdx (am : Std.HashMap Nat (List Nat)) (reads : Std.HashMap (Nat × String) (List Nat))
    (z : Nat) (p : List String) : List Nat :=
  (pathViewsIdx am reads z p).flatMap fun v => if v.2.isEmpty then HeapLinks.aliasesOf am v.1 else []

private theorem slotsOfIdx_mem_iff (ls : HeapLinks.Links) (z : Nat) (p : List String) (y : Nat) :
    y ∈ slotsOfIdx (HeapLinks.aliasesMap ls) (pathViewsReads ls) z p ↔ y ∈ slotsOf ls z p := by
  simp only [slotsOfIdx, slotsOf, List.mem_flatMap, HeapLinks.aliasesOf_eq_aliases]
  constructor
  · rintro ⟨v, hv, hy⟩; exact ⟨v, (pathViewsIdx_mem_iff ls p z v).mp hv, hy⟩
  · rintro ⟨v, hv, hy⟩; exact ⟨v, (pathViewsIdx_mem_iff ls p z v).mpr hv, hy⟩

/-- Multi-field pre-indexed separation evidence built once per `SepEvidence.query`. -/
structure SepIndex where
  aliases : Std.HashMap Nat (List Nat)
  reads : Std.HashMap (Nat × String) (List Nat)
  spines : List (List (Nat × List String) × List (Nat × List String))
  arrays : List (List (Nat × List String) × List (Nat × List String))
  elemSpines : List (List (Nat × List String) × List (Nat × List String))
  locs : Std.HashMap PropKey (List (Nat × Option (List PropKey) × Nat))

def SepIndex.ofEvidence (E : SepEvidence) : SepIndex :=
  let aliases := HeapLinks.aliasesMap E.links
  let reads := pathViewsReads E.links
  let spines := E.facts.filterMap fun
    | .spines a b => some (pathViewsIdx aliases reads a.1 a.2, pathViewsIdx aliases reads b.1 b.2)
    | _ => none
  let arrays := E.facts.filterMap fun
    | .arrays a b => some (pathViewsIdx aliases reads a.1 a.2, pathViewsIdx aliases reads b.1 b.2)
    | _ => none
  let elemSpines := E.facts.filterMap fun
    | .elemSpines a b => some (pathViewsIdx aliases reads a.1 a.2, pathViewsIdx aliases reads b.1 b.2)
    | _ => none
  let locs : Std.HashMap PropKey (List (Nat × Option (List PropKey) × Nat)) :=
    E.facts.foldl (fun m f => match f with
      | .locs x F y g => m.insert g ((x, F, y) :: m.getD g [])
      | _ => m) {}
  { aliases, reads, spines, arrays, elemSpines, locs }

private theorem SepIndex_locs_mem (facts : List SepFact) (g : PropKey) (e : Nat × Option (List PropKey) × Nat) :
    e ∈ (facts.foldl (fun (m : Std.HashMap PropKey (List (Nat × Option (List PropKey) × Nat))) f => match f with
      | .locs x F y g' => m.insert g' ((x, F, y) :: m.getD g' [])
      | _ => m) {}).getD g [] ↔
      SepFact.locs e.1 e.2.1 e.2.2 g ∈ facts := by
  have hgo : ∀ (xs : List SepFact) (m : Std.HashMap PropKey (List (Nat × Option (List PropKey) × Nat))),
      e ∈ (xs.foldl (fun m f => match f with
        | .locs x F y g' => m.insert g' ((x, F, y) :: m.getD g' [])
        | _ => m) m).getD g [] ↔
      SepFact.locs e.1 e.2.1 e.2.2 g ∈ xs ∨ e ∈ m.getD g [] := by
    intro xs
    induction xs with
    | nil => intro m; simp
    | cons f xs ih =>
      intro m
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih]
      cases f with
      | spines _ _ | arrays _ _ | elemSpines _ _ =>
        simp
      | locs x F y g' =>
        dsimp only
        rw [Std.HashMap.getD_insert]
        by_cases hg : g' == g
        · simp only [hg, ↓reduceIte, List.mem_cons]
          have hge : g' = g := beq_iff_eq.mp hg
          subst hge
          rcases e with ⟨e1, e2, e3⟩
          simp only [Prod.mk.injEq, SepFact.locs.injEq, and_true]
          constructor
          · rintro (h | (h | h))
            · exact .inl (.inr h)
            · exact .inl (.inl h)
            · exact .inr h
          · rintro ((h | h) | h)
            · exact .inr (.inl h)
            · exact .inl h
            · exact .inr (.inr h)
        · simp only [hg, Bool.false_eq_true, ↓reduceIte]
          have hne : g ≠ g' := fun h => hg (beq_iff_eq.mpr h.symm)
          constructor
          · rintro (h | h)
            · exact .inl (.inr h)
            · exact .inr h
          · rintro ((h | h) | h)
            · cases h; exact (hne rfl).elim
            · exact .inl h
            · exact .inr h
  simpa using hgo facts {}

def SepIndex.fresh (idx : SepIndex) (E : SepEvidence) (r s : Region) : Bool :=
  match fieldSite r, fieldSite s with
  | some (sx, _), some (sy, some k) =>
    let xs := slotsOfIdx idx.aliases idx.reads sx.1 sx.2
    let ys := slotsOfIdx idx.aliases idx.reads sy.1 sy.2
    xs.any fun x => ys.any fun y =>
      (E.typed y).contains k && match E.stamps.after x, E.stamps.before y with
        | some m, some m' => decide (m' ≤ m)
        | _, _ => false
  | _, _ => false

private theorem SepIndex.fresh_eq (E : SepEvidence) (r s : Region) :
    (SepIndex.ofEvidence E).fresh E r s = E.fresh r s := by
  unfold SepIndex.fresh SepEvidence.fresh
  cases fieldSite r with
  | none => rfl
  | some p =>
    rcases p with ⟨sx, ox⟩
    cases fieldSite s with
    | none => rfl
    | some q =>
      rcases q with ⟨sy, oy⟩
      cases oy with
      | none => rfl
      | some k =>
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, SepIndex.ofEvidence]
        constructor
        · rintro ⟨x, hx, y, hy, h⟩
          exact ⟨x, (slotsOfIdx_mem_iff E.links sx.1 sx.2 x).mp hx, y, (slotsOfIdx_mem_iff E.links sy.1 sy.2 y).mp hy, h⟩
        · rintro ⟨x, hx, y, hy, h⟩
          exact ⟨x, (slotsOfIdx_mem_iff E.links sx.1 sx.2 x).mpr hx, y, (slotsOfIdx_mem_iff E.links sy.1 sy.2 y).mpr hy, h⟩

def SepIndex.byFacts (idx : SepIndex) (r s : Region) : Bool :=
  (if idx.spines.isEmpty then false else
    let pair? : Option ((Nat × List String) × (Nat × List String)) :=
      match spineSite r, spineSite s with
      | some x, some y => some (x, y)
      | some x, none => (selectedSpineSite s).map (x, ·)
      | none, some y => (selectedSpineSite r).map (·, y)
      | none, none => none
    match pair? with
    | some (x, y) =>
      let vx := pathViewsIdx idx.aliases idx.reads x.1 x.2
      let vy := pathViewsIdx idx.aliases idx.reads y.1 y.2
      idx.spines.any fun (va, vb) => sameSiteIdx idx.aliases vx va && sameSiteIdx idx.aliases vy vb
    | none => false) ||
  (if idx.arrays.isEmpty then false else
    match arraySite r, arraySite s with
    | some x, some y =>
      let vx := pathViewsIdx idx.aliases idx.reads x.1 x.2
      let vy := pathViewsIdx idx.aliases idx.reads y.1 y.2
      idx.arrays.any fun (va, vb) => sameSiteIdx idx.aliases vx va && sameSiteIdx idx.aliases vy vb
    | _, _ => false) ||
  (if idx.elemSpines.isEmpty then false else
    match spineSite r, s with
    | some x, .elemSpines y q =>
      let vx := pathViewsIdx idx.aliases idx.reads x.1 x.2
      let vy := pathViewsIdx idx.aliases idx.reads y q
      idx.elemSpines.any fun (va, vb) => sameSiteIdx idx.aliases vx va && sameSiteIdx idx.aliases vy vb
    | _, _ => false) ||
  (match fieldSite r, fieldSite s with
    | some (sx, o), some (sy, some g') =>
      let entries := idx.locs.getD g' []
      if entries.isEmpty then false else
      let xs := slotsOfIdx idx.aliases idx.reads sx.1 sx.2
      let ys := slotsOfIdx idx.aliases idx.reads sy.1 sy.2
      entries.any fun (x, F, y) =>
        xs.contains x && (match o with | some k => HeapSeparation.covers F k | none => F.isNone) && ys.contains y
    | _, _ => false)

private theorem SepIndex.byFacts_eq (E : SepEvidence) (r s : Region) :
    (SepIndex.ofEvidence E).byFacts r s = E.facts.any (E.byFact r s ·) := by
  apply Bool.eq_iff_iff.mpr
  let idx := SepIndex.ofEvidence E
  have hes : (if idx.elemSpines.isEmpty then false else
      match spineSite r, s with
      | some x, .elemSpines y q =>
        let vx := pathViewsIdx idx.aliases idx.reads x.1 x.2
        let vy := pathViewsIdx idx.aliases idx.reads y q
        idx.elemSpines.any fun (va, vb) => sameSiteIdx idx.aliases vx va && sameSiteIdx idx.aliases vy vb
      | _, _ => false) = true ↔ ∃ a b, SepFact.elemSpines a b ∈ E.facts ∧ E.byFact r s (.elemSpines a b) = true := by
    constructor
    · intro h
      split at h
      · cases h
      · split at h
        · rename_i x y q hx
          obtain ⟨⟨va, vb⟩, hmem, hss⟩ := List.any_eq_true.mp h
          obtain ⟨f, hf, hfm⟩ := List.mem_filterMap.mp hmem
          cases f with
          | elemSpines a b =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hfm
            obtain ⟨rfl, rfl⟩ := hfm
            refine ⟨a, b, hf, ?_⟩
            simp only [SepEvidence.byFact, hx]
            simpa [idx, SepIndex.ofEvidence, sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)] using hss
          | spines _ _ | arrays _ _ | locs _ _ _ _ => simp at hfm
        · cases h
    · rintro ⟨a, b, hf, hb⟩
      have hmem : (pathViewsIdx idx.aliases idx.reads a.1 a.2, pathViewsIdx idx.aliases idx.reads b.1 b.2) ∈ idx.elemSpines :=
        List.mem_filterMap.mpr ⟨.elemSpines a b, hf, rfl⟩
      have hne : idx.elemSpines.isEmpty = false := by cases h : idx.elemSpines with | nil => rw [h] at hmem; cases hmem | cons _ _ => rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      simp only [SepEvidence.byFact] at hb
      split at hb
      · refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
        simpa [idx, SepIndex.ofEvidence, sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)] using hb
      · cases hb
  have hsp : (if idx.spines.isEmpty then false else
      match (match spineSite r, spineSite s with
        | some x, some y => some (x, y)
        | some x, none => (selectedSpineSite s).map (x, ·)
        | none, some y => (selectedSpineSite r).map (·, y)
        | none, none => none) with
      | some (x, y) =>
        let vx := pathViewsIdx idx.aliases idx.reads x.1 x.2
        let vy := pathViewsIdx idx.aliases idx.reads y.1 y.2
        idx.spines.any fun (va, vb) => sameSiteIdx idx.aliases vx va && sameSiteIdx idx.aliases vy vb
      | none => false) = true ↔ ∃ a b, SepFact.spines a b ∈ E.facts ∧ E.byFact r s (.spines a b) = true := by
    have hmatch : ∀ a b,
        (match (match spineSite r, spineSite s with
          | some x, some y => some (x, y)
          | some x, none => (selectedSpineSite s).map (x, ·)
          | none, some y => (selectedSpineSite r).map (·, y)
          | none, none => none) with
        | some (x, y) =>
          sameSiteIdx idx.aliases (pathViewsIdx idx.aliases idx.reads x.1 x.2) (pathViewsIdx idx.aliases idx.reads a.1 a.2) &&
          sameSiteIdx idx.aliases (pathViewsIdx idx.aliases idx.reads y.1 y.2) (pathViewsIdx idx.aliases idx.reads b.1 b.2)
        | none => false) = E.byFact r s (.spines a b) := by
      intro a b
      simp only [SepEvidence.byFact, idx, SepIndex.ofEvidence]
      cases spineSite r <;> cases spineSite s
      · rfl
      · cases selectedSpineSite r <;> simp [sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)]
      · cases selectedSpineSite s <;> simp [sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)]
      · simp [sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)]
    constructor
    · intro h
      split at h
      · cases h
      · split at h
        · rename_i x y hpair
          obtain ⟨⟨va, vb⟩, hmem, hss⟩ := List.any_eq_true.mp h
          obtain ⟨f, hf, hfm⟩ := List.mem_filterMap.mp hmem
          cases f with
          | spines a b =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hfm
            obtain ⟨rfl, rfl⟩ := hfm
            refine ⟨a, b, hf, ?_⟩
            rw [← hmatch a b, hpair]
            exact hss
          | arrays _ _ | elemSpines _ _ | locs _ _ _ _ => simp at hfm
        · cases h
    · rintro ⟨a, b, hf, hb⟩
      have hmem : (pathViewsIdx idx.aliases idx.reads a.1 a.2, pathViewsIdx idx.aliases idx.reads b.1 b.2) ∈ idx.spines :=
        List.mem_filterMap.mpr ⟨.spines a b, hf, rfl⟩
      have hne : idx.spines.isEmpty = false := by cases h : idx.spines with | nil => rw [h] at hmem; cases hmem | cons _ _ => rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [← hmatch a b] at hb
      split at hb
      · exact List.any_eq_true.mpr ⟨_, hmem, hb⟩
      · cases hb
  have harr : (if idx.arrays.isEmpty then false else
      match arraySite r, arraySite s with
      | some x, some y =>
        let vx := pathViewsIdx idx.aliases idx.reads x.1 x.2
        let vy := pathViewsIdx idx.aliases idx.reads y.1 y.2
        idx.arrays.any fun (va, vb) => sameSiteIdx idx.aliases vx va && sameSiteIdx idx.aliases vy vb
      | _, _ => false) = true ↔ ∃ a b, SepFact.arrays a b ∈ E.facts ∧ E.byFact r s (.arrays a b) = true := by
    constructor
    · intro h
      split at h
      · cases h
      · split at h
        · rename_i x y hx hy
          obtain ⟨⟨va, vb⟩, hmem, hss⟩ := List.any_eq_true.mp h
          obtain ⟨f, hf, hfm⟩ := List.mem_filterMap.mp hmem
          cases f with
          | arrays a b =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hfm
            obtain ⟨rfl, rfl⟩ := hfm
            refine ⟨a, b, hf, ?_⟩
            simp only [SepEvidence.byFact, hx, hy]
            simpa [idx, SepIndex.ofEvidence, sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)] using hss
          | spines _ _ | elemSpines _ _ | locs _ _ _ _ => simp at hfm
        · cases h
    · rintro ⟨a, b, hf, hb⟩
      have hmem : (pathViewsIdx idx.aliases idx.reads a.1 a.2, pathViewsIdx idx.aliases idx.reads b.1 b.2) ∈ idx.arrays :=
        List.mem_filterMap.mpr ⟨.arrays a b, hf, rfl⟩
      have hne : idx.arrays.isEmpty = false := by cases h : idx.arrays with | nil => rw [h] at hmem; cases hmem | cons _ _ => rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      simp only [SepEvidence.byFact] at hb
      split at hb
      · refine List.any_eq_true.mpr ⟨_, hmem, ?_⟩
        simpa [idx, SepIndex.ofEvidence, sameSiteIdx_eq E.links (pathViewsIdx_mem_iff E.links _ _) (pathViewsIdx_mem_iff E.links _ _)] using hb
      · cases hb
  have hloc : (match fieldSite r, fieldSite s with
      | some (sx, o), some (sy, some g') =>
        let entries := idx.locs.getD g' []
        if entries.isEmpty then false else
        let xs := slotsOfIdx idx.aliases idx.reads sx.1 sx.2
        let ys := slotsOfIdx idx.aliases idx.reads sy.1 sy.2
        entries.any fun (x, F, y) =>
          xs.contains x && (match o with | some k => HeapSeparation.covers F k | none => F.isNone) && ys.contains y
      | _, _ => false) = true ↔ ∃ x F y g, SepFact.locs x F y g ∈ E.facts ∧ E.byFact r s (.locs x F y g) = true := by
    constructor
    · intro h
      split at h
      · rename_i sx o sy g' hx hy
        dsimp only at h
        split at h
        · cases h
        · obtain ⟨⟨x, F, y⟩, hmem, hb⟩ := List.any_eq_true.mp h
          have hf : SepFact.locs x F y g' ∈ E.facts := (SepIndex_locs_mem E.facts g' (x, F, y)).mp hmem
          refine ⟨x, F, y, g', hf, ?_⟩
          simp only [SepEvidence.byFact, hx, hy, beq_self_eq_true, Bool.and_true]
          simp only [Bool.and_eq_true, List.contains_iff_mem] at hb ⊢
          exact ⟨⟨(slotsOfIdx_mem_iff E.links sx.1 sx.2 x).mp hb.1.1, hb.1.2⟩,
            (slotsOfIdx_mem_iff E.links sy.1 sy.2 y).mp hb.2⟩
      · cases h
    · rintro ⟨x, F, y, g, hf, hb⟩
      simp only [SepEvidence.byFact] at hb
      split at hb
      · rename_i sx o sy g' hx hy
        simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hb
        obtain ⟨⟨⟨hxs, hcov⟩, hys⟩, rfl⟩ := hb
        have hmem : (x, F, y) ∈ idx.locs.getD g' [] := (SepIndex_locs_mem E.facts g' (x, F, y)).mpr hf
        have hne2 : (idx.locs.getD g' []).isEmpty = false := by
          cases h : idx.locs.getD g' [] with | nil => rw [h] at hmem; cases hmem | cons _ _ => rfl
        simp only [hne2, Bool.false_eq_true, ↓reduceIte]
        refine List.any_eq_true.mpr ⟨(x, F, y), hmem, ?_⟩
        simp only [Bool.and_eq_true, List.contains_iff_mem]
        exact ⟨⟨(slotsOfIdx_mem_iff E.links sx.1 sx.2 x).mpr hxs, hcov⟩,
          (slotsOfIdx_mem_iff E.links sy.1 sy.2 y).mpr hys⟩
      · cases hb
  change idx.byFacts r s = true ↔ E.facts.any (E.byFact r s ·) = true
  unfold SepIndex.byFacts
  simp only [Bool.or_eq_true]
  constructor
  · rintro (((h1 | h2) | h3) | h4)
    · obtain ⟨a, b, hf, hb⟩ := hsp.mp h1; exact List.any_eq_true.mpr ⟨_, hf, hb⟩
    · obtain ⟨a, b, hf, hb⟩ := harr.mp h2; exact List.any_eq_true.mpr ⟨_, hf, hb⟩
    · obtain ⟨a, b, hf, hb⟩ := hes.mp h3; exact List.any_eq_true.mpr ⟨_, hf, hb⟩
    · obtain ⟨x, F, y, g, hf, hb⟩ := hloc.mp h4; exact List.any_eq_true.mpr ⟨_, hf, hb⟩
  · intro h
    obtain ⟨f, hf, hb⟩ := List.any_eq_true.mp h
    cases f with
    | spines a b => exact .inl (.inl (.inl (hsp.mpr ⟨a, b, hf, hb⟩)))
    | arrays a b => exact .inl (.inl (.inr (harr.mpr ⟨a, b, hf, hb⟩)))
    | elemSpines a b => exact .inl (.inr (hes.mpr ⟨a, b, hf, hb⟩))
    | locs x F y g => exact .inr (hloc.mpr ⟨x, F, y, g, hf, hb⟩)

def SepEvidence.queryFast (E : SepEvidence) : SepQuery :=
  let idx := SepIndex.ofEvidence E
  ⟨fun r s =>
    (((E.bound r).inter (E.bound s)).isEmpty || r.keysApart s) ||
    idx.fresh E r s || idx.fresh E s r ||
    idx.byFacts r s || idx.byFacts s r⟩

@[csimp] theorem SepEvidence.query_eq_fast : @SepEvidence.query = @SepEvidence.queryFast := by
  funext E
  simp only [SepEvidence.query, SepEvidence.queryFast]
  congr 1
  funext r s
  simp only [SepIndex.fresh_eq, SepIndex.byFacts_eq]
  have hany : (E.facts.any fun f => E.byFact r s f || E.byFact s r f) =
      (E.facts.any (E.byFact r s ·) || E.facts.any (E.byFact s r ·)) := by
    induction E.facts with
    | nil => rfl
    | cons f fs ih =>
      simp only [List.any_cons, ih]
      cases E.byFact r s f <;> cases E.byFact s r f <;> cases fs.any (E.byFact r s ·) <;>
        cases fs.any (E.byFact s r ·) <;> rfl
  rw [hany]
  cases (((E.bound r).inter (E.bound s)).isEmpty || r.keysApart s) <;>
    cases E.fresh r s <;> cases E.fresh s r <;> cases E.facts.any (E.byFact r s ·) <;>
    cases E.facts.any (E.byFact s r ·) <;> rfl

end Verification.Footprints
