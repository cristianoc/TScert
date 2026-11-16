import Verification.Semantics.TolerantFramesCells
import Verification.Semantics.FootprintRebase
import Verification.Semantics.AssertionScopes

/-! # Parity assertions

The assertion language of the note "Tolerant frames"
(`docs/drafts/tolerant-frames-note/note.tex`, §4 "The assertion language"),
represented as the design `docs/drafts/parity-interfaces.md` states it (I4,
"Assertion representation"): one acyclic arena of nodes, each reference
naming an earlier node, and boxes referring to their body.

An assertion is read at a name valuation `η`, an entry mark `m` and an
indexed state `s` (`TolerantFrames.IndexedHeap`): the note's triple
`ρ, m, h ⊨ F`. Atoms read `η` and the heap only. A logical variable bound by
`existsValue` is slot `0` of the valuation its body is read at (`push`); the
outer slots shift by one.

The modality reads one definition of the effect semantics, `EffectAction`,
and the lemmas stated beside it (§ "The effect action"): the role-aware
action of the shared foundation replaces that one section. -/
namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

/-! ## The effect action

The one place the parity modules read the meaning of an effect. Every
modal statement goes through `EffectAction` and the lemmas after it, and
every support through `SupportedBy`. -/

/-- **A transition within a support** (the note, §5, "Support"):
`Footprints.Supported` at the two states' heaps. -/
abbrev SupportedBy (S : Footprint) (η : Env) (s s' : IndexedHeap) : Prop :=
  Footprints.Supported S η s.h s'.h

/-- A region read without the name valuation: classes, every location and
their intersections with a class. -/
def regionEnvFree : Region → Bool
  | .cls _ | .all => true
  | .inCls r _ => regionEnvFree r
  | _ => false

/-- An effect every region of which is read without the name valuation. -/
def effectEnvFree (Φ : Footprint) : Bool := Φ.all fun e => regionEnvFree e.1

/-- **An ordinary array spine stays one** along every admissible
transition: its contents keep their category, an array spine
(`Admissible.contentsCategory`). -/
theorem _root_.Verification.TolerantFrames.Admissible.arraySpine {s s' : IndexedHeap} (ha : Admissible s s')
    {l : Nat} {xs : List (Option Nat)} (hl : s.h[l]? = some (.arr xs)) : ∃ ys, s'.h[l]? = some (.arr ys) := by
  have hl' : l < s'.h.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hl).1 ha.length_le
  obtain ⟨u, hu⟩ : ∃ u, s'.h[l]? = some u := ⟨_, List.getElem?_eq_getElem hl'⟩
  have hc := ha.contentsCategory hl hu
  cases u <;> simp [contentsCategory] at hc
  exact ⟨_, hu⟩

theorem viewCells_ordinary {h : Heap} {v : Val} {s : Nat} (hs : spineOf v = some s) : viewCells h v = none := by
  simp [viewCells, hs]

section Action
variable {Φ : Footprint} {η η' : Env} {s s' s'' : IndexedHeap}

theorem EffectAction.refl (Φ : Footprint) (η : Env) (s : IndexedHeap) : EffectAction Φ η s s :=
  TolerantFrames.Action.refl Φ η s

private theorem region_mem_envFree {r : Region} (hr : regionEnvFree r = true) (hp : Heap) (l : Nat) :
    r.mem η hp l = r.mem η' hp l := by
  induction r with
  | inCls r _ ih => simp only [Region.mem, ih hr]
  | cls _ => rfl
  | all => rfl
  | _ => simp [regionEnvFree] at hr

/-- An effect read without the name valuation acts alike at every valuation. -/
theorem EffectAction.envFree (hΦ : effectEnvFree Φ = true) (h : EffectAction Φ η s s') :
    EffectAction Φ η' s s' := by
  refine ⟨h.1, h.2.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := h.2.2 l v hv
  refine ⟨v', hv', ha.imp_right fun ⟨e, he, hm, hc⟩ => ⟨e, he, ?_, hc⟩⟩
  have := List.all_eq_true.mp hΦ e he
  rw [← region_mem_envFree this]; exact hm

/-- A closed effect's action is transitive (`TolerantFrames.closed_rigid`):
the note's rigidity, §4, law (e). -/
theorem EffectAction.closed_trans (c : Footprints.Closed) (h₁ : EffectAction c.fp η s s')
    (h₂ : EffectAction c.fp η s' s'') : EffectAction c.fp η s s'' :=
  closed_rigid c η s s' s'' h₁ h₂

/-- Inclusion of closed effects includes their actions
(`TolerantFrames.action_le_closed`): the note's `Φ ⊑ Ψ`, §4, law (c). -/
theorem EffectAction.closed_mono {a b : Footprints.Closed} (hle : a.le b = true) (h : EffectAction a.fp η s s') :
    EffectAction b.fp η s s' :=
  action_le_closed hle h

/-- Entrywise region inclusion includes the actions (`Footprints.Post.mono`,
`Region.sub_mem`), read with no class claim on fields. -/
theorem EffectAction.regions_mono {Ψ : Footprint} (hle : Footprint.le (fun _ _ => none) Φ Ψ = true)
    (ha : EffectAction Φ η s s') : EffectAction Ψ η s s' :=
  ⟨ha.1, Post.mono hle (fun _ _ _ _ hc => by cases hc) ha.2⟩

/-- **An effect whose regions read the same locations at both states of a
first action composes with a second** (the note, §3, "Order, top,
rigidity"): two actions in sequence are one. The changes of two entries
meeting at a location compose within the larger of the two
(`Change.Holds.seq`, `Change.max_cases`). -/
theorem EffectAction.trans_stable
    (hst : ∀ e ∈ Φ, ∀ l, l < s.h.length → e.1.mem η s'.h l = e.1.mem η s.h l)
    (h₁ : EffectAction Φ η s s') (h₂ : EffectAction Φ η s' s'') : EffectAction Φ η s s'' := by
  refine ⟨h₁.1.trans h₂.1, Nat.le_trans h₁.2.1 h₂.2.1, fun l v₀ hv₀ => ?_⟩
  have hl : l < s.h.length := (List.getElem?_eq_some_iff.mp hv₀).1
  have hb : s.h.length ≤ s'.h.length := h₁.2.1
  obtain ⟨v₁, hv₁, a₁⟩ := h₁.2.2 l v₀ hv₀
  obtain ⟨v₂, hv₂, a₂⟩ := h₂.2.2 l v₁ hv₁
  refine ⟨v₂, hv₂, ?_⟩
  rcases a₁ with rfl | ⟨e₁, he₁, hm₁, hh₁⟩
  · rcases a₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inl rfl
    · refine .inr ⟨e₂, he₂, by rw [← hst e₂ he₂ l hl]; exact hm₂, hh₂.lower hb⟩
  · rcases a₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inr ⟨e₁, he₁, hm₁, hh₁⟩
    · have hseq := Change.Holds.seq hb hh₁ hh₂
      rcases Change.max_cases e₁.2 e₂.2 with hmx | hmx
      · rw [hmx] at hseq; exact .inr ⟨e₁, he₁, hm₁, hseq⟩
      · rw [hmx] at hseq; exact .inr ⟨e₂, he₂, by rw [← hst e₂ he₂ l hl]; exact hm₂, hseq⟩

/-- A region reading the same locations at every state an admissible
transition reaches, given the paths it reads at `paths`: classes (their
locations keep their category), every location, module cells, a variable's
own fields, and a selected spine or field at a path whose read is fixed. A
spine's cells (`cells`, `pathCells`) are not: a spine may come to list other
cells (the note, §3, "Not rigid"). -/
def stableRegion (paths : List (Nat × List String)) : Region → Bool
  | .cls _ | .all | .field _ _ | .fields _ => true
  | .inCls r _ => stableRegion paths r
  | .spine x p | .path x p _ | .pathFields x p => paths.contains (x, p)
  | .cells _ | .pathCells _ _ => false

theorem region_mem_stable {paths : List (Nat × List String)} (ha : Admissible s s')
    (hp : ∀ xp ∈ paths, readPath s'.h (η xp.1) xp.2 = readPath s.h (η xp.1) xp.2) :
    ∀ {r : Region}, stableRegion paths r = true → ∀ l, l < s.h.length → r.mem η s'.h l = r.mem η s.h l
  | .cls c, _, l, hl => ha.cls_mem hl η c
  | .all, _, _, _ => rfl
  | .field _ _, _, _, _ => rfl
  | .fields _, _, _, _ => rfl
  | .inCls r c, h, l, hl => by
    have := region_mem_stable ha hp (r := r) h l hl
    have hc := ha.cls_mem hl η c
    simp only [Region.mem] at hc ⊢
    rw [this, hc]
  | .spine x p, h, _, _ => by
    simp only [stableRegion, List.contains_iff_mem] at h
    simp only [Region.mem, hp _ h]
  | .path x p _, h, _, _ => by
    simp only [stableRegion, List.contains_iff_mem] at h
    simp only [Region.mem, hp _ h]
  | .pathFields x p, h, _, _ => by
    simp only [stableRegion, List.contains_iff_mem] at h
    simp only [Region.mem, hp _ h]
  | .cells _, h, _, _ => by simp [stableRegion] at h
  | .pathCells _ _, h, _, _ => by simp [stableRegion] at h

/-- The category class a region's locations lie in at every well-formed
state, whatever the valuation: a class, a module cell (values), and a
spine's listed cells (values: element cells hold no spine,
`HeapCategories.cells`). -/
def regionClass : Region → Option Selector
  | .cls a | .inCls _ a => some a
  | .cells _ | .pathCells _ _ => some .values
  | _ => none

theorem spineCells_values {s : IndexedHeap} {v : Val} {l : Nat}
    (hm : (spineCells s.h v).contains (some l) = true) : (Region.cls .values).mem η s.h l = true := by
  simp only [spineCells, List.contains_iff_mem, List.mem_append] at hm
  have key : ∀ o : Option Nat, some l ∈ entriesAt s.h o → (Region.cls .values).mem η s.h l = true := by
    intro o ho
    cases o with
    | none => simp [entriesAt] at ho
    | some st =>
      simp only [entriesAt] at ho
      cases he : s.h[st]?.bind spineEntries with
      | none => rw [he] at ho; simp at ho
      | some ls =>
        rw [he] at ho
        simp only [Option.getD_some] at ho
        obtain ⟨-, hlt⟩ := s.ok.entries_cells he ho
        obtain ⟨u, hu⟩ : ∃ u, s.h[l]? = some u := ⟨_, List.getElem?_eq_getElem hlt⟩
        have hna := (Footprints.HeapOk.categories s.ok).cells st ls l u he ho hu
        simp only [Region.mem, hu, Selector.selects]
        cases u <;> simp_all [isArr, contentsCategory, Selector.has]
  rcases hm with hm | hm
  · exact key _ hm
  · exact key _ hm

theorem regionClass_sound {s : IndexedHeap} {r : Region} {a : Selector} (hr : regionClass r = some a) {l : Nat}
    (hm : r.mem η s.h l = true) : (Region.cls a).mem η s.h l = true := by
  cases r with
  | cls c => cases hr; exact hm
  | inCls r c =>
    cases hr
    simp only [Region.mem, Bool.and_eq_true] at hm ⊢
    exact hm.2
  | cells x => cases hr; exact spineCells_values hm
  | pathCells x p =>
    cases hr
    simp only [Region.mem] at hm
    split at hm
    · exact spineCells_values hm
    · cases hm
  | _ => cases hr

end Action

/-! ## Paths and witnesses -/

namespace Path

/-- The current term of kind `k` read at the end of the path. -/
def term (k : Term.Kind) (p : Path) : Term := Term.now k p.root p.fields

@[simp] theorem term_atEntry (k : Term.Kind) (p : Path) : (p.term k).atEntry = false := rfl

/-- A path's term denotes what its kind reads of the value the path reads. -/
theorem termAt_term (η : Env) (h : Heap) (k : Term.Kind) (p : Path) :
    termAt η h (p.term k) = (p.read η h).bind (kindValue h k) := rfl

end Path

/-! ## Atoms -/

/-- A variable of a scalar body (I4, "ScalarBody"): the bound index, the
element's scalar value, the element's string length, or a logical scalar
parameter (a slot's own safe integer). The note's `every(z, t, φ)`, §4,
"Atoms": `φ` over scalars. -/
def scalarBound : Bound → Bool
  | .index | .elem => true
  | .project .strLength [] => true
  | .free t => !t.atEntry && t.kind == .value && t.path.isEmpty
  | _ => false

/-- A scalar body: every variable of every clause is scalar. -/
def scalarBody (body : List (LinearClause Bound)) : Bool :=
  body.all fun F => F.vars.all scalarBound

/-- The terms an atom names. -/
def Atom.terms : Atom → List Term
  | .linear F => F.vars
  | .dense _ n => [n]
  | .every _ n body => n :: body.flatMap fun F => F.vars.filterMap fun
      | .free t => some t
      | _ => none
  | .element _ t _ => [t]
  | .defined t => [t]
  | _ => []

/-- Every term of an atom reads the current state: a single-state assertion
names no entry term (I4: `Term.old` belongs to two-state posts), and its
quantified bodies are scalar. -/
def Atom.wellFormed (a : Atom) : Bool :=
  a.terms.all (fun t => !t.atEntry) && match a with
    | .every _ _ body => scalarBody body
    | _ => true

/-- An atom whose truth depends on the name valuation alone: each path it
reads is a variable, and each term a variable's own safe integer or string
length. -/
def Atom.envOnly : Atom → Bool
  | .linear F => F.vars.all fun t => (t.envOnly || (t.kind == .view && t.path.isEmpty)) && !t.atEntry
  | .equal p w => p.fields.isEmpty && match w with
    | .path q => q.fields.isEmpty
    | .literal _ => true
  | .contents p _ => p.fields.isEmpty
  | .defined t => (t.envOnly || (t.kind == .view && t.path.isEmpty)) && !t.atEntry
  | .safeInt p => p.fields.isEmpty
  | .pastSafe p => p.fields.isEmpty
  | _ => false

private theorem termAt_envOnly {η : Env} {h h' : Heap} {t : Term}
    (ht : (t.envOnly || (t.kind == .view && t.path.isEmpty)) = true) (he : t.atEntry = false) :
    termAt η h t = termAt η h' t := by
  rcases Bool.or_eq_true _ _ |>.mp ht with ht | ht
  · have := termValue_envOnly (ε := ⟨η, h⟩) (ρ := η) (h := h) (h' := h') ht
    rwa [termValue_now he, termValue_now he] at this
  · simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ht
    simp only [termAt, ht.2, readPath, Option.bind_some, ht.1, kindValue]

/-- **An atom reading the name valuation alone holds in every heap.** -/
theorem Atom.holds_envOnly {a : Atom} (ha : a.envOnly = true) {η : Env} {h h' : Heap} :
    a.Holds η h ↔ a.Holds η h' := by
  cases a with
  | linear F =>
    have he : ∀ t ∈ F.vars, termAt η h' t = termAt η h t := fun t ht => by
      have := List.all_eq_true.mp ha t ht
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact termAt_envOnly this.1 this.2
    exact ⟨fun hf => factAt_congr he hf, fun hf => factAt_congr (fun t ht => (he t ht).symm) hf⟩
  | equal p w =>
    simp only [Atom.envOnly, Bool.and_eq_true, List.isEmpty_iff] at ha
    obtain ⟨hp, hw⟩ := ha
    have hw' : w.value η h = w.value η h' := by
      cases w with
      | path q => simp only [List.isEmpty_iff] at hw; exact Path.read_heap hw
      | literal _ => rfl
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') hp, hw']
  | contents p R =>
    simp only [Atom.envOnly, List.isEmpty_iff] at ha
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') ha]
  | defined t =>
    simp only [Atom.envOnly, Bool.and_eq_true, Bool.not_eq_true'] at ha
    simp only [Atom.Holds, termAt_envOnly (h := h) (h' := h') ha.1 ha.2]
  | safeInt p =>
    simp only [Atom.envOnly, List.isEmpty_iff] at ha
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') ha]
  | pastSafe p =>
    simp only [Atom.envOnly, List.isEmpty_iff] at ha
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') ha]
  | _ => simp [Atom.envOnly] at ha

/-! ## Separation and freshness -/

/-- An ordinary array's cells, as the region `π[∗]` selects them
(`spineCells`), are its spine's listing. -/
theorem ArraySpine.cells {h : Heap} {u : Val} {s : Nat} {xs : List (Option Nat)} (ha : ArraySpine h u s xs) :
    spineCells h u = xs := by
  obtain ⟨hs, hd, hx⟩ := ha
  have hs' : (fieldsOf u).lookup arraySpineKey = some s := hs
  simp [spineCells, entriesAt, hs', hd, hx, spineEntries]

/-- **The cells of two ordinary arrays are disjoint as regions exactly where
their spine listings are** (the note's `apart` and the regions `π[∗]`). -/
theorem cells_disjoint_iff {h : Heap} {u w : Val} {s t : Nat} {xs ys : List (Option Nat)}
    (hu : ArraySpine h u s xs) (hw : ArraySpine h w t ys) :
    (∀ l, some l ∈ spineCells h u → some l ∉ spineCells h w) ↔ (∀ l, some l ∈ xs → some l ∉ ys) := by
  rw [hu.cells, hw.cells]

/-! ## The arena

The arena, its nodes and their satisfaction (`satNode`, `Sat`) are defined
in `TwoStateFormulas`, below the callable guarantees. -/

/-! ## Invariant assertions -/

/-- **Checked invariance** (the note, §4, "Invariant assertions": `F ⊢ □_⊤ F`):
`true`, `false`, atoms reading the name valuation alone, separation of
variables, freshness of a variable, a box of `⊤`, and the connectives over
invariant assertions. -/
def invNode (nodes : Array AssertionNode) (i : Nat) : Bool :=
  match nodes[i]? with
  | some .truth | some .falsity => true
  | some (.atom a) => a.envOnly
  | some (.and l r) | some (.guarded l r) =>
    (if _ : l.index < i then invNode nodes l.index else false) &&
      (if _ : r.index < i then invNode nodes r.index else false)
  | some (.existsValue b) => if _ : b.index < i then invNode nodes b.index else false
  | some (.separated p q) => p.fields.isEmpty && q.fields.isEmpty
  | some (.fresh p) => p.fields.isEmpty
  | some (.box Φ _) => Φ == topEffect
  | _ => false
termination_by i

/-- **Checked invariance is invariance.** -/
theorem invNode_sound (nodes : Array AssertionNode) :
    ∀ i, invNode nodes i = true → Invariant (satNode nodes i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi η m s s' ha hs
  rw [invNode] at hi
  rw [satNode] at hs ⊢
  split at hi
  · rename_i hn; rw [hn] at hs ⊢; exact hs
  · rename_i hn; rw [hn] at hs; exact hs.elim
  · rename_i a hn
    rw [hn] at hs ⊢
    exact (Atom.holds_envOnly hi).mp hs
  · rename_i l r hn
    rw [hn] at hs ⊢
    simp only [Bool.and_eq_true] at hi
    obtain ⟨hl, hr⟩ := hi
    refine ⟨?_, ?_⟩
    · split at hl
      · rename_i hli; simp only [hli, dite_true] at hs ⊢; exact ih _ hli hl η m s s' ha hs.1
      · cases hl
    · split at hr
      · rename_i hri; simp only [hri, dite_true] at hs ⊢; exact ih _ hri hr η m s s' ha hs.2
      · cases hr
  · rename_i l r hn
    rw [hn] at hs ⊢
    simp only [Bool.and_eq_true] at hi
    obtain ⟨hl, hr⟩ := hi
    rcases hs with hs | hs
    · refine .inl ?_
      split at hl
      · rename_i hli; simp only [hli, dite_true] at hs ⊢; exact ih _ hli hl η m s s' ha hs
      · cases hl
    · refine .inr ?_
      split at hr
      · rename_i hri; simp only [hri, dite_true] at hs ⊢; exact ih _ hri hr η m s s' ha hs
      · cases hr
  · rename_i b hn
    rw [hn] at hs ⊢
    split at hi
    · rename_i hbi
      obtain ⟨v, hv⟩ := hs
      simp only [hbi, dite_true] at hv
      exact ⟨v, by simp only [hbi, dite_true]; exact ih _ hbi hi _ m s s' ha hv⟩
    · cases hi
  · rename_i p q hn
    rw [hn] at hs ⊢
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hi
    obtain ⟨u, w, a, b, xs, ys, hu, hw, ⟨hsa, hda, hxa⟩, ⟨hsb, hdb, hyb⟩, hne⟩ := hs
    obtain ⟨xs', hx'⟩ := ha.arraySpine hxa
    obtain ⟨ys', hy'⟩ := ha.arraySpine hyb
    exact ⟨u, w, a, b, xs', ys', by rw [Path.read_heap hi.1]; exact hu, by rw [Path.read_heap hi.2]; exact hw,
      ⟨hsa, hda, hx'⟩, ⟨hsb, hdb, hy'⟩, hne⟩
  · rename_i p hn
    rw [hn] at hs ⊢
    simp only [List.isEmpty_iff] at hi
    obtain ⟨v, hv, hf⟩ := hs
    exact ⟨v, by rw [Path.read_heap hi]; exact hv, hf⟩
  · rename_i Φ b hn
    rw [hn] at hs ⊢
    simp only [beq_iff_eq] at hi
    subst hi
    intro s'' ha'
    exact hs s'' (EffectAction.top (ha.trans ha'.admissible))
  · cases hi

/-! ## Validity -/

/-- The references of a node precede it. -/
def AssertionNode.refsBelow (i : Nat) : AssertionNode → Bool
  | .and l r | .guarded l r => decide (l.index < i) && decide (r.index < i)
  | .existsValue b | .box _ b => decide (b.index < i)
  | _ => true

/-- **A well-formed node** (I4, `AssertionArena.Valid`): its references
precede it, its atoms read the current state with scalar quantified bodies,
and a guard has checked invariance. -/
def AssertionNode.wellFormed (nodes : Array AssertionNode) (i : Nat) (n : AssertionNode) : Bool :=
  n.refsBelow i && match n with
    | .atom a => a.wellFormed
    | .guarded g _ => invNode nodes g.index
    | _ => true

/-- Every node of the arena is well formed. -/
def AssertionArena.Valid (arena : AssertionArena) : Prop :=
  ∀ (i : Nat) (n : AssertionNode), arena.nodes[i]? = some n → n.wellFormed arena.nodes i = true

/-- The executable check of validity. -/
def AssertionArena.check (arena : AssertionArena) : Bool :=
  (List.range arena.nodes.size).all fun i => match arena.nodes[i]? with
    | some n => n.wellFormed arena.nodes i
    | none => true

theorem AssertionArena.check_valid {arena : AssertionArena} (hc : arena.check = true) : arena.Valid := by
  intro i n hn
  have hi : i < arena.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
  have := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simpa only [hn] using this

theorem AssertionArena.Valid.refs {arena : AssertionArena} (hv : arena.Valid) {i : Nat} {n : AssertionNode}
    (hn : arena.nodes[i]? = some n) : n.refsBelow i = true := by
  have := hv i n hn
  simp only [AssertionNode.wellFormed, Bool.and_eq_true] at this
  exact this.1

/-! ## Interpretation lemmas -/

section Interpretation
variable {arena : AssertionArena} {η : Env} {m : Nat} {s : IndexedHeap} {a : AssertionRef}

theorem sat_truth (hn : arena.nodes[a.index]? = some .truth) : Sat arena η m s a := by
  unfold Sat; rw [satNode, hn]; trivial

theorem sat_falsity (hn : arena.nodes[a.index]? = some .falsity) : ¬ Sat arena η m s a := by
  unfold Sat; rw [satNode, hn]; exact id

theorem sat_atom {x : Atom} (hn : arena.nodes[a.index]? = some (.atom x)) :
    Sat arena η m s a ↔ x.Holds η s.h := by
  unfold Sat; rw [satNode, hn]

theorem sat_and {l r : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.and l r)) :
    Sat arena η m s a ↔ Sat arena η m s l ∧ Sat arena η m s r := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, Bool.and_eq_true, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb.1, hb.2, dite_true]

theorem sat_guarded {g b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.guarded g b)) :
    Sat arena η m s a ↔ Sat arena η m s g ∨ Sat arena η m s b := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, Bool.and_eq_true, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb.1, hb.2, dite_true]

theorem sat_exists {b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.existsValue b)) :
    Sat arena η m s a ↔ ∃ v : Val, Sat arena (push v η) m s b := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb, dite_true]

theorem sat_separated {p q : Path} (hn : arena.nodes[a.index]? = some (.separated p q)) :
    Sat arena η m s a ↔ Separated η s.h p q := by
  unfold Sat; rw [satNode, hn]

theorem sat_apart {p q : Path} (hn : arena.nodes[a.index]? = some (.apart p q)) :
    Sat arena η m s a ↔ Apart η s.h p q := by
  unfold Sat; rw [satNode, hn]

theorem sat_fresh {p : Path} (hn : arena.nodes[a.index]? = some (.fresh p)) :
    Sat arena η m s a ↔ FreshPath η m s.h p := by
  unfold Sat; rw [satNode, hn]

theorem sat_box {Φ : Footprint} {b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.box Φ b)) :
    Sat arena η m s a ↔ ∀ s', EffectAction Φ η s s' → Sat arena η m s' b := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb, dite_true]

/-- **A box is the note's modality**: `Sat` of `box Φ A` is `TolerantFrames.Box`
of `A`'s satisfaction, through `EffectAction`. -/
theorem sat_box_iff_Box {Φ : Footprint} {b : AssertionRef} (hv : arena.Valid)
    (hn : arena.nodes[a.index]? = some (.box Φ b)) :
    Sat arena η m s a ↔ Box Φ (fun η m s => Sat arena η m s b) η m s :=
  sat_box hv hn

/-- A guard of a valid arena is invariant. -/
theorem guard_invariant {g b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.guarded g b)) :
    Invariant (fun η m s => Sat arena η m s g) := by
  have := hv _ _ hn
  simp only [AssertionNode.wellFormed, Bool.and_eq_true] at this
  exact invNode_sound arena.nodes g.index this.2

/-- **Definedness**: a linear atom defines each of its terms. -/
theorem sat_linear_defined {F : Linear.Fact Term} (hn : arena.nodes[a.index]? = some (.atom (.linear F)))
    (hs : Sat arena η m s a) : ∀ t ∈ F.vars, (termAt η s.h t).isSome :=
  ((sat_atom hn).mp hs).1

/-- An assertion's satisfaction reads the state's heap and the entry mark
alone: two states with one heap satisfy the same atoms. -/
theorem atom_heap {x : Atom} {s' : IndexedHeap} (hh : s.h = s'.h) : x.Holds η s.h ↔ x.Holds η s'.h := by
  rw [hh]

end Interpretation

end Verification.Parity
