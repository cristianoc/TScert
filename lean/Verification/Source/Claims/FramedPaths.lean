import Verification.Paper.TolerantFrames.ReadOnlyCallFrame

/-! # Paths of field reads and the locations they read

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Milestone 2: the protected
reading", the decision and the theorem chain's step 5). A slot of a
request's run holds a copy of an argument's value or the value a path of
field reads gives from it; a region rooted at that slot reads further
locations. Both are stated over the locations they read, each found in a
value it holds, by a *step*: the field of a key (`Region.field 0 k`) or
the spine a value selects (`Region.spine 0 []`).

- **A read of a key** (`ReadKey`): the calculus's `readAt` on an object,
  its own field, or the key read from the prototype its `[[proto]]` field
  holds, or `undefined` where neither is present (`Step.readField`,
  `Step.readProto`, `Step.readMissing`); `KeyLoc` names each location it
  reads, with the value holding it and the step.
- **A path of reads** (`Reads`, `ReadsAt`): the reads of a list of keys in
  order, and the locations they read.
- **The locations a region's membership reads** (`RegionReadsAt`): those
  of its path of own fields (`HeapKnowledge.readPath`), and the spine of
  the value its cells are read from.
- **What they reach** (`ValReach`, `reads_reach`, `region_reach`): each
  value a read gives, and each location of a region whose read locations
  hold what they held, is reached from the value read from.
- **Unchanged locations give the same reads** (`readKey_congr`,
  `reads_congr`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-! ## Reads of keys and paths -/

/-- **A read of the key `f` from a value**, at a heap: an object's own
field's contents, the read from its prototype where it has none, or
`undefined` where it has neither (`Step.readField`, `Step.readProto`,
`Step.readMissing`). -/
inductive ReadKey (h : Heap) (f : PropKey) : Val → Val → Prop where
  | own {fs : List (PropKey × Nat)} {c : CallCode} {o l : Nat} {u : Val} :
      fs.lookup f = some l → h[l]? = some u → ReadKey h f (.objAt fs c o) u
  | proto {fs : List (PropKey × Nat)} {c : CallCode} {o l : Nat} {p u : Val} :
      fs.lookup f = none → fs.lookup CallArguments.protoField = some l → h[l]? = some p → ReadKey h f p u →
      ReadKey h f (.objAt fs c o) u
  | missing {fs : List (PropKey × Nat)} {c : CallCode} {o : Nat} :
      fs.lookup f = none → fs.lookup CallArguments.protoField = none → ReadKey h f (.objAt fs c o) .undef

/-- **A location a read of `f` reads**, in the value `w` holding it, by the
step `q`: the own field read, the `[[proto]]` field followed, and those of
the read from the prototype. -/
inductive KeyLoc (h : Heap) (f : PropKey) : Val → Nat → Val → Region → Prop where
  | own {fs : List (PropKey × Nat)} {c : CallCode} {o l : Nat} :
      fs.lookup f = some l → KeyLoc h f (.objAt fs c o) l (.objAt fs c o) (.field 0 f)
  | proto {fs : List (PropKey × Nat)} {c : CallCode} {o l : Nat} :
      fs.lookup f = none → fs.lookup CallArguments.protoField = some l →
      KeyLoc h f (.objAt fs c o) l (.objAt fs c o) (.field 0 CallArguments.protoField)
  | next {fs : List (PropKey × Nat)} {c : CallCode} {o l l' : Nat} {p w : Val} {q : Region} :
      fs.lookup f = none → fs.lookup CallArguments.protoField = some l → h[l]? = some p → KeyLoc h f p l' w q →
      KeyLoc h f (.objAt fs c o) l' w q

/-- **A path of reads**: the reads of the keys `π`, in order. -/
inductive Reads (h : Heap) : Val → List PropKey → Val → Prop where
  | nil (v : Val) : Reads h v [] v
  | cons {v w u : Val} {f : PropKey} {π : List PropKey} : ReadKey h f v w → Reads h w π u → Reads h v (f :: π) u

/-- **A location a path of reads reads**, in the value holding it, by its
step. -/
inductive ReadsAt (h : Heap) : Val → List PropKey → Nat → Val → Region → Prop where
  | here {v w : Val} {f : PropKey} {π : List PropKey} {l : Nat} {q : Region} :
      KeyLoc h f v l w q → ReadsAt h v (f :: π) l w q
  | there {v m w : Val} {f : PropKey} {π : List PropKey} {l : Nat} {q : Region} :
      ReadKey h f v m → ReadsAt h m π l w q → ReadsAt h v (f :: π) l w q

/-- **The steps of a read of `f`**: its own field and its `[[proto]]`
field. -/
def keySteps (f : PropKey) : List Region := [.field 0 f, .field 0 CallArguments.protoField]

/-- The steps of a path of reads. -/
def pathSteps (π : List PropKey) : List Region := π.flatMap keySteps

/-! ## Paths from paths -/

/-- **A path continues from the contents of the location it reaches**
(proved, by induction on the first path). -/
theorem follows_append {ofC : ComponentTag → Bool} {h : Heap} :
    ∀ {v : Val} {π₁ : List Label} {l : Nat} {w : Val} {π₂ : List Label} {m : Nat},
      Follows ofC h v π₁ l → h[l]? = some w → Follows ofC h w π₂ m → Follows ofC h v (π₁ ++ π₂) m
  | _, [], _, _, _, _, hf, _, _ => hf.elim
  | _, [_], _, _, [], _, _, _, hf₂ => hf₂.elim
  | _, [_], _, _, _ :: _, _, hf, hw, hf₂ => ⟨_, .inl ⟨_, hf, hw⟩, hf₂⟩
  | _, _ :: _ :: _, _, _, _, _, ⟨v₀, hs, hf⟩, hw, hf₂ => ⟨v₀, hs, follows_append hf hw hf₂⟩

/-- A location reached from a value reached is reached (proved). -/
theorem ValReach.reaches {ofC : ComponentTag → Bool} {h : Heap} {v w : Val} (hw : ValReach ofC h v w) {m : Nat}
    (hm : Reaches ofC h w m) : Reaches ofC h v m := by
  rcases hw with rfl | ⟨π, l, hf, hl⟩
  · exact hm
  · obtain ⟨π', hf'⟩ := hm
    exact ⟨_, follows_append hf hl hf'⟩

/-- A value the contents of a location reached from a value reached holds
is reached (proved). -/
theorem ValReach.step {ofC : ComponentTag → Bool} {h : Heap} {v w u : Val} (hw : ValReach ofC h v w) {a : Label}
    {l : Nat} (hn : next w a = some l) (hl : h[l]? = some u) : ValReach ofC h v u := by
  obtain ⟨π, hf⟩ := hw.reaches (m := l) ⟨[a], hn⟩
  exact .inr ⟨π, l, hf, hl⟩

theorem next_field {fs : List (PropKey × Nat)} {c : CallCode} {o : Nat} {k : PropKey} {l : Nat}
    (h : fs.lookup k = some l) : next (.objAt fs c o) (.key k) = some l := by
  simpa [next, fieldsOf] using h

/-! ## What reads reach -/

/-- **A read's value is reached, or `undefined`** (proved, by induction on
the read). -/
theorem readKey_reach {ofC : ComponentTag → Bool} {h : Heap} {f : PropKey} :
    ∀ {v u : Val}, ReadKey h f v u → ∀ {v₀ : Val}, ValReach ofC h v₀ v → ValReach ofC h v₀ u ∨ u = .undef
  | _, _, .own hl hu, _, hv => .inl (hv.step (next_field hl) hu)
  | _, _, .proto _ hp hpv hr, _, hv => readKey_reach hr (hv.step (next_field hp) hpv)
  | _, _, .missing _ _, _, _ => .inr rfl

/-- **A path's value is reached, or `undefined`** (proved). -/
theorem reads_reach {ofC : ComponentTag → Bool} {h : Heap} :
    ∀ {v π u : _}, Reads h v π u → ∀ {v₀ : Val}, ValReach ofC h v₀ v → ValReach ofC h v₀ u ∨ u = .undef
  | _, _, _, .nil _, _, hv => .inl hv
  | _, _, _, .cons hk hr, _, hv => by
    rcases readKey_reach hk hv with hw | rfl
    · exact reads_reach hr hw
    · cases hr with
      | nil => exact .inr rfl
      | cons hk' _ => cases hk'

/-- **A location a read reads is in a value reached, by a step of the
read's key** (proved). -/
theorem keyLoc_reach {ofC : ComponentTag → Bool} {h : Heap} {f : PropKey} :
    ∀ {v : Val} {l : Nat} {w : Val} {q : Region}, KeyLoc h f v l w q → ∀ {v₀ : Val}, ValReach ofC h v₀ v →
      ValReach ofC h v₀ w ∧ q ∈ keySteps f ∧ q.mem (fun _ => w) h l = true
  | _, _, _, _, .own hl, _, hv => ⟨hv, by simp [keySteps], by simp [Region.mem, fieldsOf, hl]⟩
  | _, _, _, _, .proto _ hp, _, hv => ⟨hv, by simp [keySteps], by simp [Region.mem, fieldsOf, hp]⟩
  | _, _, _, _, .next _ hp hpv hk, _, hv => keyLoc_reach hk (hv.step (next_field hp) hpv)

/-- **A location a path of reads reads is in a value reached, by a step of
the path** (proved). -/
theorem readsAt_reach {ofC : ComponentTag → Bool} {h : Heap} :
    ∀ {v : Val} {π : List PropKey} {l : Nat} {w : Val} {q : Region}, ReadsAt h v π l w q → ∀ {v₀ : Val},
      ValReach ofC h v₀ v → ValReach ofC h v₀ w ∧ q ∈ pathSteps π ∧ q.mem (fun _ => w) h l = true
  | _, f :: π, _, _, _, .here hk, _, hv => by
    obtain ⟨hw, hq, hm⟩ := keyLoc_reach hk hv
    exact ⟨hw, List.mem_flatMap.mpr ⟨f, List.mem_cons_self .., hq⟩, hm⟩
  | _, f :: π, _, _, _, .there hk hr, _, hv => by
    rcases readKey_reach (ofC := ofC) hk hv with hm | rfl
    · obtain ⟨hw, hq, hmm⟩ := readsAt_reach hr hm
      exact ⟨hw, List.mem_flatMap.mpr (by
        obtain ⟨g, hg, hq'⟩ := List.mem_flatMap.mp hq
        exact ⟨g, List.mem_cons_of_mem _ hg, hq'⟩), hmm⟩
    · cases hr with
      | here hk' => cases hk'
      | there hk' _ => cases hk'

/-! ## Unchanged locations give the same reads -/

/-- **A read at a heap agreeing on the locations it reads at another is
that heap's read** (proved, by induction on the read). -/
theorem readKey_congr {h₀ h₁ : Heap} {f : PropKey} :
    ∀ {v u : Val}, ReadKey h₁ f v u → (∀ l w q, KeyLoc h₀ f v l w q → h₁[l]? = h₀[l]?) → ReadKey h₀ f v u
  | _, _, .own hl hu, hk => .own hl (by rw [← hk _ _ _ (.own hl)]; exact hu)
  | _, _, .proto hn hp hpv hr, hk =>
    have hpv₀ : h₀[_]? = some _ := by rw [← hk _ _ _ (.proto hn hp)]; exact hpv
    .proto hn hp hpv₀ (readKey_congr hr fun l w q hl => hk l w q (.next hn hp hpv₀ hl))
  | _, _, .missing hn hp, _ => .missing hn hp

/-- A read is functional (proved). -/
theorem readKey_det {h : Heap} {f : PropKey} :
    ∀ {v u u' : Val}, ReadKey h f v u → ReadKey h f v u' → u = u'
  | _, _, _, .own hl hu, .own hl' hu' => by rw [hl] at hl'; cases hl'; rw [hu] at hu'; cases hu'; rfl
  | _, _, _, .own hl _, .proto hn _ _ _ => by rw [hl] at hn; cases hn
  | _, _, _, .own hl _, .missing hn _ => by rw [hl] at hn; cases hn
  | _, _, _, .proto hn _ _ _, .own hl _ => by rw [hl] at hn; cases hn
  | _, _, _, .proto _ hp hpv hr, .proto _ hp' hpv' hr' => by
    rw [hp] at hp'; cases hp'; rw [hpv] at hpv'; cases hpv'; exact readKey_det hr hr'
  | _, _, _, .proto _ hp _ _, .missing _ hp' => by rw [hp] at hp'; cases hp'
  | _, _, _, .missing hn _, .own hl _ => by rw [hl] at hn; cases hn
  | _, _, _, .missing _ hp, .proto _ hp' _ _ => by rw [hp] at hp'; cases hp'
  | _, _, _, .missing _ _, .missing _ _ => rfl

/-- **A path of reads at a heap agreeing on the locations it reads at
another is that heap's** (proved). -/
theorem reads_congr {h₀ h₁ : Heap} :
    ∀ {v π u : _}, Reads h₁ v π u → (∀ l w q, ReadsAt h₀ v π l w q → h₁[l]? = h₀[l]?) → Reads h₀ v π u
  | _, _, _, .nil _, _ => .nil _
  | _, _, _, .cons hk hr, hp => by
    have hk₀ := readKey_congr hk fun l w q hl => hp l w q (.here hl)
    exact .cons hk₀ (reads_congr hr fun l w q hl => hp l w q (.there hk₀ hl))

/-- **A path of reads extended by a read** (proved). -/
theorem reads_snoc {h : Heap} :
    ∀ {v π m u : _} {f : PropKey}, Reads h v π m → ReadKey h f m u → Reads h v (π ++ [f]) u
  | _, _, _, _, _, .nil _, hk => .cons hk (.nil _)
  | _, _, _, _, _, .cons hk' hr, hk => .cons hk' (reads_snoc hr hk)

/-- **The locations a path extended by a read reads**: those of the path,
and those of the read from its value (proved). -/
theorem readsAt_snoc {h : Heap} :
    ∀ {v π m : _} {f : PropKey}, Reads h v π m → ∀ {l w q}, ReadsAt h v (π ++ [f]) l w q →
      ReadsAt h v π l w q ∨ KeyLoc h f m l w q
  | _, _, _, _, .nil _, _, _, _, .here hk => .inr hk
  | _, _, _, _, .nil _, _, _, _, .there _ hr => by cases hr
  | _, _, _, _, .cons hk' hr, _, _, _, .here hk => .inl (.here hk)
  | _, _, _, _, .cons hk' hr, _, _, _, .there hk'' hr' => by
    rw [readKey_det hk'' hk'] at hr'
    rcases readsAt_snoc hr hr' with h₁ | h₂
    · exact .inl (.there hk' h₁)
    · exact .inr h₂

/-- **The locations a path reads are read by its extensions** (proved). -/
theorem readsAt_append {h : Heap} :
    ∀ {v : Val} {π : List PropKey} {l : Nat} {w : Val} {q : Region} (π' : List PropKey),
      ReadsAt h v π l w q → ReadsAt h v (π ++ π') l w q
  | _, _ :: _, _, _, _, _, .here hk => .here hk
  | _, _ :: _, _, _, _, π', .there hk hr => .there hk (readsAt_append π' hr)

/-- **A path extended by a read reads the locations of the read from its
value** (proved). -/
theorem readsAt_of_keyLoc {h : Heap} {f : PropKey} :
    ∀ {v π m : _}, Reads h v π m → ∀ {l w q}, KeyLoc h f m l w q → ReadsAt h v (π ++ [f]) l w q
  | _, _, _, .nil _, _, _, _, hk => .here hk
  | _, _, _, .cons hk' hr, _, _, _, hk => .there hk' (readsAt_of_keyLoc hr hk)

/-! ## The locations a region's membership reads -/

/-- **The slot a region is read from**: that of a field, a path, a spine or
cells of a slot's value; none for a region of every location of a class,
of every location, or of a value's fields by enumeration. -/
def regionSlot : Region → Option Nat
  | .field x _ | .path x _ _ | .spine x _ | .cells x | .pathCells x _ => some x
  | .inCls r _ => regionSlot r
  | .fields _ | .pathFields _ _ | .cls _ | .all => none

/-- The steps of a path of own fields. -/
def ownSteps (p : List String) : List Region := p.map fun f => .field 0 (.str f)

/-- The steps of the spine a value's cells are read from: its `[]` field
and the spine its descriptor names. -/
def spineSteps : List Region := [.field 0 arraySpineKey, .spine 0 []]

/-- **The steps of the locations a region's membership reads**
(`regionReads`): its path's own fields, and for cells the spine they are
read from. -/
def regionSteps : Region → List Region
  | .path _ p _ | .spine _ p => ownSteps p
  | .cells _ => spineSteps
  | .pathCells _ p => ownSteps p ++ spineSteps
  | .inCls r _ => regionSteps r
  | .field _ _ | .fields _ | .pathFields _ _ | .cls _ | .all => []

/-- **A location a path of own fields reads**, in the value holding it, by
its step (`HeapKnowledge.readPath`). -/
inductive OwnAt (h : Heap) : Val → List String → Nat → Val → Region → Prop where
  | here {fs : List (PropKey × Nat)} {c : CallCode} {o l : Nat} {f : String} {p : List String} :
      fs.lookup (.str f) = some l → OwnAt h (.objAt fs c o) (f :: p) l (.objAt fs c o) (.field 0 (.str f))
  | there {fs : List (PropKey × Nat)} {c : CallCode} {o l l' : Nat} {f : String} {p : List String} {v w : Val}
      {q : Region} :
      fs.lookup (.str f) = some l → h[l]? = some v → OwnAt h v p l' w q → OwnAt h (.objAt fs c o) (f :: p) l' w q

/-- **A spine location the cells of a value are read from**: its `[]`
field, or the spine its descriptor names. -/
def SpineAt (u : Val) (l : Nat) (w : Val) (q : Region) : Prop :=
  w = u ∧ ((q = .field 0 arraySpineKey ∧ (fieldsOf u).lookup arraySpineKey = some l) ∨
    (q = .spine 0 [] ∧ HeapKnowledge.descriptorSpine u = some l))

/-- **A location a region's membership reads** from the value `u` of its
slot, in the value holding it, by its step. -/
def RegionReadsAt (h : Heap) : Region → Val → Nat → Val → Region → Prop
  | .path _ p _, u, l, w, q | .spine _ p, u, l, w, q => OwnAt h u p l w q
  | .cells _, u, l, w, q => SpineAt u l w q
  | .pathCells _ p, u, l, w, q =>
    OwnAt h u p l w q ∨ ∃ v, HeapKnowledge.readPath h u p = some v ∧ SpineAt v l w q
  | .inCls r _, u, l, w, q => RegionReadsAt h r u l w q
  | .field _ _, _, _, _, _ | .fields _, _, _, _, _ | .pathFields _ _, _, _, _, _ | .cls _, _, _, _, _
  | .all, _, _, _, _ => False

/-- **A path of own fields at a heap agreeing on the locations it reads at
another is that heap's** (proved), and its value is reached. -/
theorem readPath_congr {ofC : ComponentTag → Bool} {h₀ h₁ : Heap} :
    ∀ {p : List String} {v : Val} {u : Val}, HeapKnowledge.readPath h₁ v p = some u →
      (∀ l w q, OwnAt h₀ v p l w q → h₁[l]? = h₀[l]?) →
      HeapKnowledge.readPath h₀ v p = some u ∧ ∀ {v₀ : Val}, ValReach ofC h₀ v₀ v → ValReach ofC h₀ v₀ u := by
  intro p
  induction p with
  | nil =>
    intro v u hr _
    simp only [HeapKnowledge.readPath, Option.some.injEq] at hr; subst hr
    exact ⟨rfl, fun h => h⟩
  | cons f p ih =>
    intro v u hr hk
    cases v with
    | objAt fs c o =>
      simp only [HeapKnowledge.readPath] at hr
      split at hr
      · rename_i l hl
        split at hr
        · rename_i w hv
          have hv₀ : h₀[l]? = some w := by rw [← hk _ _ _ (.here hl)]; exact hv
          obtain ⟨hr₀, hreach⟩ := ih hr fun l' w' q hl' => hk l' w' q (.there hl hv₀ hl')
          exact ⟨by simp only [HeapKnowledge.readPath, hl, hv₀]; exact hr₀,
            fun hv' => hreach (hv'.step (a := .key (.str f)) (next_field hl) hv₀)⟩
        · cases hr
      · cases hr
    | _ => simp [HeapKnowledge.readPath] at hr

/-- **A location a path of own fields reads is in a value reached, by a
step of the path** (proved). -/
theorem ownAt_reach {ofC : ComponentTag → Bool} {h : Heap} :
    ∀ {v : Val} {p : List String} {l : Nat} {w : Val} {q : Region}, OwnAt h v p l w q → ∀ {v₀ : Val},
      ValReach ofC h v₀ v → ValReach ofC h v₀ w ∧ q ∈ ownSteps p ∧ q.mem (fun _ => w) h l = true
  | _, _, _, _, _, .here hl, _, hv => ⟨hv, by simp [ownSteps], by simp [Region.mem, fieldsOf, hl]⟩
  | _, _ :: _, _, _, _, .there hl hlv ho, _, hv => by
    obtain ⟨hw, hq, hm⟩ := ownAt_reach ho (hv.step (a := .key (.str _)) (next_field hl) hlv)
    exact ⟨hw, List.mem_cons_of_mem _ hq, hm⟩

/-- **The cells of a value at a heap agreeing on its spines with another are
reached there** (proved): each is a cell of the spine its `[]` field or
its descriptor names. -/
theorem spineCells_reach {ofC : ComponentTag → Bool} {h₀ h₁ : Heap} {v : Val}
    (hk : ∀ l w q, SpineAt v l w q → h₁[l]? = h₀[l]?) {m : Nat} (hm : (spineCells h₁ v).contains (some m) = true) :
    Reaches ofC h₀ v m := by
  have key : ∀ (o : Option Nat) (a : Label), next v a = o → (∀ s, o = some s → h₁[s]? = h₀[s]?) →
      some m ∈ entriesAt h₁ o → Reaches ofC h₀ v m := by
    intro o a ho hs hl
    cases o with
    | none => simp [entriesAt] at hl
    | some s =>
      simp only [entriesAt] at hl
      rw [hs s rfl] at hl
      cases hsv : h₀[s]? with
      | none => simp [hsv] at hl
      | some sp =>
        rw [hsv] at hl
        cases he : spineEntries sp with
        | none => simp [he] at hl
        | some ls =>
          simp only [he, Option.bind_some, Option.getD_some] at hl
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hl
          have hn : next sp (.cell i) = some m := by simp [next, he, hi]
          exact ⟨[a, .cell i], ⟨sp, .inl ⟨s, ho, hsv⟩, hn⟩⟩
  simp only [spineCells, List.contains_iff_mem, List.mem_append] at hm
  rcases hm with h1 | h2
  · exact key _ (.key arraySpineKey) (by simp [next]) (fun s hs => hk s v _ ⟨rfl, .inl ⟨rfl, hs⟩⟩) h1
  · exact key _ .view (by simp [next]) (fun s hs => hk s v _ ⟨rfl, .inr ⟨rfl, hs⟩⟩) h2

/-- **A location of a region at a heap agreeing with another on the
locations its membership reads there is reached from its slot's value
there** (proved, by cases on the region): a field of the slot's value, of
the value its path reads, its spine, or a cell of that spine. -/
theorem region_reach {ofC : ComponentTag → Bool} {h₀ h₁ : Heap} {ρ : Env} :
    ∀ {r : Region} {x : Nat}, regionSlot r = some x → (∀ l w q, RegionReadsAt h₀ r (ρ x) l w q → h₁[l]? = h₀[l]?) →
      ∀ {m : Nat}, r.mem ρ h₁ m = true → Reaches ofC h₀ (ρ x) m := by
  intro r
  induction r with
  | field y k =>
    intro x hx _ m hm
    simp only [regionSlot, Option.some.injEq] at hx; subst hx
    simp only [Region.mem, beq_iff_eq] at hm
    exact ⟨[.key k], by simpa [Follows, next] using hm⟩
  | path y p k =>
    intro x hx hk m hm
    simp only [regionSlot, Option.some.injEq] at hx; subst hx
    simp only [Region.mem] at hm
    split at hm
    · rename_i u hu
      obtain ⟨-, hreach⟩ := readPath_congr (ofC := ofC) hu fun l w q ho => hk l w q ho
      exact (hreach (.inl rfl)).reaches ⟨[.key k], by simpa [Follows, next] using hm⟩
    · cases hm
  | spine y p =>
    intro x hx hk m hm
    simp only [regionSlot, Option.some.injEq] at hx; subst hx
    simp only [Region.mem] at hm
    split at hm
    · rename_i u hu
      obtain ⟨-, hreach⟩ := readPath_congr (ofC := ofC) hu fun l w q ho => hk l w q ho
      exact (hreach (.inl rfl)).reaches (leaves_elements (by simpa using hm)).reaches
    · cases hm
  | cells y =>
    intro x hx hk m hm
    simp only [regionSlot, Option.some.injEq] at hx; subst hx
    exact spineCells_reach (fun l w q hs => hk l w q hs) hm
  | pathCells y p =>
    intro x hx hk m hm
    simp only [regionSlot, Option.some.injEq] at hx; subst hx
    simp only [Region.mem] at hm
    split at hm
    · rename_i u hu
      obtain ⟨hu₀, hreach⟩ := readPath_congr (ofC := ofC) hu fun l w q ho => hk l w q (.inl ho)
      exact (hreach (.inl rfl)).reaches (spineCells_reach (fun l w q hs => hk l w q (.inr ⟨u, hu₀, hs⟩)) hm)
    · cases hm
  | inCls r c ih =>
    intro x hx hk m hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hx hk hm.1
  | fields _ => intro _ hx; simp [regionSlot] at hx
  | pathFields _ _ => intro _ hx; simp [regionSlot] at hx
  | cls _ => intro _ hx; simp [regionSlot] at hx
  | all => intro _ hx; simp [regionSlot] at hx

/-- **A spine location the cells of a value with valid references are read
from is in the value, by its step** (proved): a view's descriptor names its
spine only where it owns no `[]` field (`RefOk` of a view). -/
theorem spineAt_mem {k : Nat} {W : WorldT k} {h : Heap} {u w : Val} {l : Nat} {q : Region} (hv : RefsOk W w)
    (hs : SpineAt u l w q) : q ∈ spineSteps ∧ q.mem (fun _ => w) h l = true := by
  obtain ⟨rfl, (⟨rfl, hl⟩ | ⟨rfl, hl⟩)⟩ := hs
  · exact ⟨by simp [spineSteps], by simp [Region.mem, hl]⟩
  · refine ⟨by simp [spineSteps], ?_⟩
    cases w with
    | objAt fs c o =>
      cases c with
      | view s f n =>
        simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hl; subst hl
        have hmem : Ref.view s f n (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view s f n) o) := by
          simp [refs]
        have hplain := (hv _ hmem).1
        cases hk : fs.lookup arraySpineKey with
        | some _ => rw [hk] at hplain; cases hplain
        | none => simp [Region.mem, HeapKnowledge.readPath, HeapKnowledge.elementsOf, hk]
      | _ => simp [HeapKnowledge.descriptorSpine] at hl
    | _ => simp [HeapKnowledge.descriptorSpine] at hl

/-- **A location a region's membership reads is in a value reached, by a
step of the region** (proved), where the values reached have valid
references. -/
theorem regionReadsAt_reach {ofC : ComponentTag → Bool} {k : Nat} {W : WorldT k} {h : Heap} :
    ∀ {r : Region} {u : Val} {l : Nat} {w : Val} {q : Region}, RegionReadsAt h r u l w q →
      (∀ v, ValReach ofC h u v → RefsOk W v) →
      ValReach ofC h u w ∧ q ∈ regionSteps r ∧ q.mem (fun _ => w) h l = true := by
  intro r
  induction r with
  | path _ p _ | spine _ p =>
    intro u l w q hr _
    obtain ⟨hw, hq, hm⟩ := ownAt_reach hr (.inl rfl)
    exact ⟨hw, by simpa [regionSteps] using hq, hm⟩
  | cells _ =>
    intro u l w q hr hv
    have hw : w = u := hr.1
    obtain ⟨hq, hm⟩ := spineAt_mem (h := h) (hv w (by rw [hw]; exact .inl rfl)) hr
    exact ⟨by rw [hw]; exact .inl rfl, by simpa [regionSteps] using hq, hm⟩
  | pathCells _ p =>
    intro u l w q hr hv
    rcases hr with ho | ⟨v, hp, hs⟩
    · obtain ⟨hw, hq, hm⟩ := ownAt_reach ho (.inl rfl)
      exact ⟨hw, by simp [regionSteps, hq], hm⟩
    · have hreach := (readPath_congr (ofC := ofC) (h₀ := h) (h₁ := h) hp fun _ _ _ _ => rfl).2 (.inl rfl)
      have hw : w = v := hs.1
      obtain ⟨hq, hm⟩ := spineAt_mem (h := h) (hv w (by rw [hw]; exact hreach)) hs
      exact ⟨by rw [hw]; exact hreach, by simp [regionSteps, hq], hm⟩
  | inCls r _ ih =>
    intro u l w q hr hv
    obtain ⟨hw, hq, hm⟩ := ih hr hv
    exact ⟨hw, by simpa [regionSteps] using hq, hm⟩
  | field _ _ | fields _ | pathFields _ _ | cls _ | all => intro _ _ _ _ hr; cases hr

end Verification.TolerantFrames.ReadOnly
