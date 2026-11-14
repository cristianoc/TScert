import Verification.Semantics.ClosedFootprints

/-! # Rebasing a step's frame to the invocation's entry

A step's frame is read at the step's own positions `σ`, in the heap the step
starts in. The enclosing invocation's frame is read at its entry values
`ρ₀`, in its entry heap `h₀`. **Rebasing** maps each region of the step to
regions of the entry by checked evidence: a position's value is the value an
entry path reads (`link`), and a path read from it at the step's heap reads
the same value at the entry heap (`agree`). A class region and a cell are
read in themselves. A store at a position's path whose location, where it
has one, is at or above the entry heap's length (`fresh`, `FreshIfStore`) is
no entry location and rebases to none. A field at a nonempty path widens to
its key's class and element cells to the value class, by the step heap's
contents categories (`HeapCategories`); a field of a position's own value
and own locations without evidence become `all`. `Post.compose_at` composes an entry
frame so far with the step's frame through it: the one composition of a
body's steps (FOOTPRINTS.md, "Argument-path store regions"). -/
namespace Verification.Footprints

/-- Resolving a concatenated path is resolving its suffix from the prefix's value. -/
theorem readPath_append (h : Heap) (x : Val) (p q : List String) :
    HeapKnowledge.readPath h x (p ++ q) =
      (HeapKnowledge.readPath h x p).bind (fun v => HeapKnowledge.readPath h v q) := by
  induction p generalizing x with
  | nil => rfl
  | cons f p ih =>
    cases x <;> simp only [List.cons_append, HeapKnowledge.readPath, Option.bind_none]
    rename_i fs code oid
    split
    · split
      · exact ih _
      · rfl
    · rfl

/-! ## Categories of a well-formed heap

The class a location's contents have follows from the reference to it: a
field location holds contents of its key's class (`keyClass`, the array
store key's location holds an array store), a store's listed cell holds no
store, and a typed array's descriptor names a view store. On a
well-formed heap these hold of every value the heap holds (`HeapCategories`,
`HeapOk.categories`), so of every value read at a nonempty path; a value at
an empty path is a position's own, whose references the heap does not
vouch for. -/

/-- The class a field key demands of its location's contents: an array
store for the array store key, a value otherwise (`SlotRole`). -/
def keyClass (k : PropKey) : Selector :=
  if k = arrayStoreKey then .arrays else .values

/-- **Contents categories of a heap's own values**: each field location of
a value the heap holds has contents of its key's class, each cell a store
of the heap lists (`storeEntries`) holds no store, and the store a typed
array's descriptor names holds a view store. -/
structure HeapCategories (h : Heap) : Prop where
  fields : ∀ (l₀ : Nat) (v : Val) (k : PropKey) (l : Nat) (u : Val), h[l₀]? = some v →
    (fieldsOf v).lookup k = some l → h[l]? = some u → (keyClass k).selects u = true
  cells : ∀ (s : Nat) (ls : List (Option Nat)) (l : Nat) (u : Val), h[s]?.bind storeEntries = some ls →
    some l ∈ ls → h[l]? = some u → isArr u = false
  views : ∀ (l₀ : Nat) (fs : List (PropKey × Nat)) (i s : Nat) (f : ViewFormat) (n : Nat) (u : Val),
    h[l₀]? = some (.viewAt fs i s f n) → h[s]? = some u → Selector.views.selects u = true

/-- A well-formed heap's contents have valid references. -/
theorem HeapOk.contents_refs {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {l : Nat} {v : Val}
    (hv : h[l]? = some v) : RefsOk W v := by
  have hl : l < (roles W).length := by
    have := (List.getElem?_eq_some_iff.mp hv).1
    rw [hok.1.1] at this; simpa using this
  obtain ⟨u, hu, -, hr⟩ := hok.2 l (roles W)[l] (List.getElem?_eq_getElem hl)
  rw [hv] at hu; cases hu
  exact hr

/-- A valid value's field location has the role its key demands. -/
theorem slotRole_of_refs {k' : Nat} {W : WorldT k'} {v : Val} (hr : RefsOk W v) {k : PropKey} {l : Nat}
    (hl : (fieldsOf v).lookup k = some l) : SlotRole k (roleAt W l) := by
  cases v <;> simp only [fieldsOf, List.lookup_nil, reduceCtorEq] at hl
  rename_i fs c i
  have hmem : Ref.slot k l ∈ objRefs fs i := by
    simp only [objRefs, List.mem_cons, List.mem_map, reduceCtorEq, false_or]
    have hkl : (k, l) ∈ fs := by
      clear hr
      induction fs with
      | nil => simp at hl
      | cons p fs ih =>
        rcases p with ⟨k', l'⟩
        by_cases hk : k = k'
        · subst hk; simp [List.lookup] at hl; subst hl; simp
        · have : fs.lookup k = some l := by
            simpa [List.lookup, show (k == k') = false from by simpa using hk] using hl
          simp [ih this]
    exact ⟨(k, l), hkl, rfl⟩
  have hin : Ref.slot k l ∈ refs (.objAt fs c i) := by
    cases c <;> simp only [refs, List.mem_append] <;> simp [hmem]
  simpa [RefOk] using hr _ hin

/-- **A well-formed heap's categories.** -/
theorem HeapOk.categories {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) : HeapCategories h where
  fields l₀ v k l u hv hl hu := by
    have hs := slotRole_of_refs (HeapOk.contents_refs hok hv) hl
    cases hr : roleAt W l with
    | none => rw [hr] at hs; cases hs
    | some r =>
      rw [hr] at hs
      obtain ⟨u', hu', hc, -⟩ := hok.2 l r hr
      rw [hu] at hu'; cases hu'
      unfold keyClass
      cases r with
      | store f =>
        cases f with
        | array =>
          obtain ⟨ls, rfl⟩ := hc; simp [SlotRole] at hs
          simp [hs, Selector.selects, Selector.arrays, Selector.has, contentsCategory]
        | view N => simp [SlotRole] at hs
      | field | cell =>
        simp only [SlotRole] at hs
        simp only [hs, if_false]
        cases u <;> simp_all [Cat, isSourceVal, Selector.selects, Selector.values, Selector.has, contentsCategory]
      | elem | identity => simp [SlotRole] at hs
  cells s ls l u hs hl hu := by
    obtain ⟨hr, -⟩ := hok.entries_cells hs hl
    obtain ⟨u', hu', hc, -⟩ := hok.2 l .elem hr
    rw [hu] at hu'; cases hu'
    cases u <;> simp_all [Cat, isSourceVal, isArr]
  views l₀ fs i s f n u hv hu := by
    have hr := HeapOk.contents_refs hok hv
    have hin : Ref.view s f n (fs.lookup arrayStoreKey).isNone ∈ refs (.viewAt fs i s f n) := by
      simp [refs]
    have hrole : roleAt W s = some (.store (.view f n)) := (hr _ hin).2
    obtain ⟨u', hu', hc, -⟩ := hok.2 s _ hrole
    rw [hu] at hu'; cases hu'
    obtain ⟨cs, rfl, -⟩ := hc
    rfl

/-- A read at a nonempty path is the contents of a heap location. -/
theorem readPath_contents {h : Heap} : ∀ {p : List String} {x v : Val}, p ≠ [] →
    HeapKnowledge.readPath h x p = some v → ∃ l : Nat, h[l]? = some v := by
  intro p
  induction p with
  | nil => intro _ _ hp; exact absurd rfl hp
  | cons f p ih =>
    intro x v _ hr
    cases x <;> simp only [HeapKnowledge.readPath, reduceCtorEq] at hr
    split at hr
    · rename_i l _
      split at hr
      · rename_i u hu
        cases p with
        | nil => simp only [HeapKnowledge.readPath, Option.some.injEq] at hr; subst hr; exact ⟨l, hu⟩
        | cons g q => exact ih (by simp) hr
      · cases hr
    · cases hr

/-- The cells a value's store lists hold no store. -/
theorem HeapCategories.elems {h : Heap} (hc : HeapCategories h) {v : Val} {l : Nat} {u : Val}
    (hm : some l ∈ storeElems h v) (hu : h[l]? = some u) : isArr u = false := by
  have entries : ∀ o, some l ∈ entriesAt h o → isArr u = false := by
    intro o ho
    cases o with
    | none => simp [entriesAt] at ho
    | some s =>
      simp only [entriesAt] at ho
      cases ht : h[s]?.bind storeEntries with
      | none => rw [ht] at ho; simp at ho
      | some ls => rw [ht] at ho; exact hc.cells s ls l u ht ho hu
  rcases List.mem_append.mp hm with hm | hm
  · exact entries _ hm
  · exact entries _ hm

/-! ## Rebasing -/

/-- The evidence of a rebasing: for a step position, the entry position and
path whose read at the entry heap is its value; the step position's paths
whose read at the step's heap is its read at the entry heap; and the
positions and paths whose value's store, where it has one, is fresh. -/
structure RebaseEvidence where
  link : Nat → Option (Nat × List String)
  agree : Nat → List String → Bool
  fresh : Nat → List String → Bool := fun _ _ => false

/-- **Selected-location freshness of a store slot**: where the value has a
`[]` slot, its location is at least `b`. It reads no heap; a value with no
such slot (`null`, a number, an object of no store field) meets it. -/
def FreshIfStore (b : Nat) (v : Tm) : Prop :=
  ∀ s, (fieldsOf v).lookup arrayStoreKey = some s → b ≤ s

theorem FreshAt.ifStore {b : Nat} {v : Tm} (h : FreshAt b v) : FreshIfStore b v := by
  obtain ⟨s, hs, hle⟩ := h
  intro s' hs'
  rw [storeOf_lookup hs] at hs'
  cases hs'
  exact hle

/-- The evidence holds of the step's positions `σ` at heap `h`, against the
entry values `ρ₀` at the entry heap `h₀`; and the step's heap has its
contents categories. -/
structure RebaseOk (ev : RebaseEvidence) (σ ρ₀ : Env) (h₀ h : Heap) : Prop where
  link : ∀ s x q, ev.link s = some (x, q) → HeapKnowledge.readPath h₀ (ρ₀ x) q = some (σ s)
  agree : ∀ s p, ev.agree s p = true → ∀ v, HeapKnowledge.readPath h (σ s) p = some v →
    HeapKnowledge.readPath h₀ (σ s) p = some v
  fresh : ∀ s p, ev.fresh s p = true → ∀ v, HeapKnowledge.readPath h (σ s) p = some v →
    FreshIfStore h₀.length v
  categories : HeapCategories h

/-- A region selecting the store at a path of a position, where the
evidence states that store fresh, at any path depth. -/
def RebaseEvidence.freshPath (ev : RebaseEvidence) (s : Nat) (p : List String) (k : PropKey) : Bool :=
  k == arrayStoreKey && ev.fresh s p

/-- A fresh path's store selects no location of the entry heap. -/
theorem RebaseOk.fresh_path {ev σ ρ₀ h₀ h} (hk : RebaseOk ev σ ρ₀ h₀ h) {s p k l}
    (hf : ev.freshPath s p k = true) (hm : (Region.path s p k).mem σ h l = true) : h₀.length ≤ l := by
  simp only [RebaseEvidence.freshPath, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨rfl, hf⟩ := hf
  simp only [Region.mem] at hm
  split at hm
  · rename_i v hv
    exact hk.fresh s p hf v hv l (by simpa using hm)
  · cases hm

/-- Whether a step position's path is read at the entry heap as at the
step's: the empty path always. -/
def RebaseEvidence.reads (ev : RebaseEvidence) (s : Nat) (p : List String) : Bool :=
  p.isEmpty || ev.agree s p

/-- A path read from a linked position, where it agrees, as a path from the
entry position. -/
def RebaseEvidence.path (ev : RebaseEvidence) (s : Nat) (p : List String) : Option (Nat × List String) :=
  if ev.reads s p then (ev.link s).map fun (x, q) => (x, q ++ p) else none

/-- **Rebasing** a region read at the step's positions and heap into regions
read at the entry's (the note, §6, rebasing): a class region and a cell to
themselves; a field or own locations at a path the evidence links to the
entry, to that entry path; a fresh selected store to none; a field at a
nonempty path otherwise to its key's class; element cells to the value
class; a field of a position's own value without a link, and own locations
without one, to `all`. -/
def rebase (ev : RebaseEvidence) : Region → List Region
  | .field s k => if ev.freshPath s [] k then [] else match ev.path s [] with
    | some (x, q) => [.path x q k]
    | none => [.all]
  | .own s => match ev.path s [] with
    | some (x, q) => [.pathOwn x q]
    | none => [.all]
  | .path s p k => if ev.freshPath s p k then [] else match ev.path s p with
    | some (x, q) => [.path x q k]
    | none => if p.isEmpty then [.all] else [.cls (keyClass k)]
  | .pathOwn s p => match ev.path s p with
    | some (x, q) => [.pathOwn x q]
    | none => [.all]
  | .cls c => [.cls c]
  | .cell b => [.cell b]
  | .inCls r c => (rebase ev r).map (·.inCls c)
  | .elems _ => [.cls .values]
  | .pathElems _ _ => [.cls .values]
  | .all => [.all]
  | .store s p => match ev.path s p with
    | some (x, q) => [.store x q]
    | none => [.all]

def rebaseAll (ev : RebaseEvidence) (Ψ : Footprint) : Footprint :=
  Ψ.flatMap fun e => (rebase ev e.1).map (·, e.2)

/-- A path the evidence rebases reads, at the entry heap from the entry
position, the value it reads at the step's heap from the step position. -/
theorem RebaseOk.path {ev σ ρ₀ h₀ h} (hk : RebaseOk ev σ ρ₀ h₀ h) {s p x q v}
    (he : ev.path s p = some (x, q)) (hv : HeapKnowledge.readPath h (σ s) p = some v) :
    HeapKnowledge.readPath h₀ (ρ₀ x) q = some v := by
  unfold RebaseEvidence.path at he
  split at he
  · rename_i hr
    cases hl : ev.link s with
    | none => rw [hl] at he; cases he
    | some xq =>
      obtain ⟨x', q'⟩ := xq
      rw [hl] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h₀v : HeapKnowledge.readPath h₀ (σ s) p = some v := by
        simp only [RebaseEvidence.reads, Bool.or_eq_true, List.isEmpty_iff] at hr
        rcases hr with rfl | hr
        · simpa [HeapKnowledge.readPath] using hv
        · exact hk.agree s p hr v hv
      rw [readPath_append, hk.link s x' q' hl]
      simpa using h₀v
  · cases he

/-- **Fresh-store erasure erases the store's own location only**: a
selected store's cells, old or fresh, rebase to the value class, and a class
region, the all-views one among them, to itself, whatever the evidence
states fresh. Only a `[]` field location the evidence states fresh is
erased. -/
theorem rebase_erases_store_only (ev : RebaseEvidence) (s : Nat) (p : List String) (c : Selector) :
    rebase ev (.elems s) = [.cls .values] ∧ rebase ev (.pathElems s p) = [.cls .values] ∧
      rebase ev (.cls c) = [.cls c] ∧ ∀ k, rebase ev (.path s p k) = [] → k = arrayStoreKey := by
  refine ⟨rfl, rfl, rfl, fun k hk => ?_⟩
  by_cases hf : ev.freshPath s p k = true
  · simp only [RebaseEvidence.freshPath, Bool.and_eq_true, beq_iff_eq] at hf
    exact hf.1
  · simp only [rebase, hf, Bool.false_eq_true, if_false] at hk
    split at hk
    · cases hk
    · split at hk <;> cases hk

/-- A location of the step's heap in a class region by its contents is in
it at the entry heap, or an entry of the first action at `any` covers it. -/
private theorem class_back {Φp ρ₀ h₀ h l} (hp : Post Φp ρ₀ h₀ h) (hl : l < h₀.length) {c : Selector}
    {u : Val} (hu : h[l]? = some u) (hc : c.selects u = true) :
    (∃ s ∈ [Region.cls c], s.mem ρ₀ h₀ l = true) ∨ ∃ e ∈ Φp, e.1.mem ρ₀ h₀ l = true ∧ e.2 = .any := by
  rcases cls_back (ρ := ρ₀) hp hl (c := c) (by simp [Region.mem, hu, hc]) with h | h
  · exact .inl ⟨.cls c, List.mem_singleton_self _, h⟩
  · exact .inr h

theorem rebase_sound {Φp ρ₀ σ h₀ h ev l} (hp : Post Φp ρ₀ h₀ h) (hk : RebaseOk ev σ ρ₀ h₀ h)
    (hl : l < h₀.length) :
    ∀ {r : Region}, r.mem σ h l = true →
    (∃ s ∈ rebase ev r, s.mem ρ₀ h₀ l = true) ∨ ∃ e ∈ Φp, e.1.mem ρ₀ h₀ l = true ∧ e.2 = .any := by
  have hlh : l < h.length := Nat.lt_of_lt_of_le hl hp.1
  obtain ⟨u, hu⟩ : ∃ u, h[l]? = some u := ⟨h[l], List.getElem?_eq_getElem hlh⟩
  intro r
  induction r with
  | field s k =>
    intro hm
    by_cases hf : ev.freshPath s [] k = true
    · have := hk.fresh_path hf (by simpa using hm)
      omega
    simp only [Bool.not_eq_true] at hf
    cases he : ev.path s [] with
    | none => exact .inl ⟨.all, by simp [rebase, he, hf], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.path x q k, by simp [rebase, he, hf], ?_⟩
      simp only [Region.mem, hk.path he (show HeapKnowledge.readPath h (σ s) [] = some (σ s) from rfl)]
      simpa [Region.mem] using hm
  | own s =>
    intro hm
    cases he : ev.path s [] with
    | none => exact .inl ⟨.all, by simp [rebase, he], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.pathOwn x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem, hk.path he (show HeapKnowledge.readPath h (σ s) [] = some (σ s) from rfl)]
      simpa [Region.mem] using hm
  | path s p k =>
    intro hm
    have hf : ev.freshPath s p k = false := by
      cases hfs : ev.freshPath s p k
      · rfl
      · have := hk.fresh_path hfs hm
        omega
    cases he : ev.path s p with
    | none =>
      by_cases hp0 : p.isEmpty = true
      · exact .inl ⟨.all, by simp [rebase, he, hf, hp0], rfl⟩
      · have hne : p ≠ [] := by simpa using hp0
        simp only [Region.mem] at hm
        split at hm
        · rename_i v hv
          obtain ⟨l₀, hl₀⟩ := readPath_contents hne hv
          have hsel := hk.categories.fields l₀ v k l u hl₀ (by simpa using hm) hu
          have hr : rebase ev (.path s p k) = [.cls (keyClass k)] := by
            simp [rebase, he, hf, show p.isEmpty = false from by simpa using hp0]
          rw [hr]
          exact class_back hp hl hu hsel
        · cases hm
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.path x q k, by simp [rebase, he, hf], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm
  | pathOwn s p =>
    intro hm
    cases he : ev.path s p with
    | none => exact .inl ⟨.all, by simp [rebase, he], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.pathOwn x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm
  | cls c =>
    intro hm
    rcases cls_back (ρ := ρ₀) hp hl (by simpa [Region.mem] using hm) with h | h
    · exact .inl ⟨.cls c, by simp [rebase], h⟩
    · exact .inr h
  | cell b =>
    intro hm
    have hv : (Region.cls .values).mem ρ₀ h l = true := by simpa [Region.mem] using hm
    rcases cls_back hp hl hv with h | h
    · exact .inl ⟨.cell b, by simp [rebase], by simpa [Region.mem] using h⟩
    · exact .inr h
  | inCls r c ih =>
    intro hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    have hc : (Region.cls c).mem ρ₀ h l = true := by simpa [Region.mem] using hm.2
    rcases ih hm.1 with ⟨s, hs, hsm⟩ | h
    · rcases cls_back hp hl hc with hc₀ | h
      · refine .inl ⟨s.inCls c, by simp only [rebase]; exact List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
        simp only [Region.mem, Bool.and_eq_true]
        exact ⟨hsm, by simpa [Region.mem] using hc₀⟩
      · exact .inr h
    · exact .inr h
  | elems s =>
    intro hm
    have harr := hk.categories.elems (by simpa [Region.mem] using hm) hu
    exact class_back hp hl hu (by rw [Selector.selects_values, harr]; rfl)
  | pathElems s p =>
    intro hm
    simp only [Region.mem] at hm
    split at hm
    · have harr := hk.categories.elems (by simpa using hm) hu
      exact class_back hp hl hu (by rw [Selector.selects_values, harr]; rfl)
    · cases hm
  | all => intro _; exact .inl ⟨.all, by simp [rebase], rfl⟩
  | store s p =>
    intro hm
    cases he : ev.path s p with
    | none => exact .inl ⟨.all, by simp [rebase, he], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.store x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm

/-- **Composition at the step's positions.** An entry frame so far, a step's
frame at its own positions and heap, the rebasing evidence, and an inclusion
justified by class evidence valid at the entry heap give the next entry
frame. With `σ = ρ₀` and the identity link it is `Post.compose` at a step
reading no path. -/
theorem Post.compose_at {Φp Ψ Φq : Footprint} {cl ρ₀ σ h₀ h h' ev}
    (hp : Post Φp ρ₀ h₀ h) (hn : Post Ψ σ h h') (hk : RebaseOk ev σ ρ₀ h₀ h)
    (hle : Footprint.le cl (Φp ++ rebaseAll ev Ψ) Φq = true) (hc : ClassOk cl ρ₀ h₀) :
    Post Φq ρ₀ h₀ h' := by
  refine ⟨Nat.le_trans hp.1 hn.1, fun l v₀ hv₀ => ?_⟩
  have hl := (List.getElem?_eq_some_iff.mp hv₀).1
  have hb : h₀.length ≤ h.length := hp.1
  obtain ⟨v₁, hv₁, ha₁⟩ := hp.2 l v₀ hv₀
  obtain ⟨v₂, hv₂, ha₂⟩ := hn.2 l v₁ hv₁
  refine ⟨v₂, hv₂, Allowed.mono hle hc hl ?_⟩
  have viaAny : ∀ e ∈ Φp, e.1.mem ρ₀ h₀ l = true → e.2 = .any →
      Allowed (Φp ++ rebaseAll ev Ψ) ρ₀ h₀ l v₀ v₂ := fun e hm hem hany =>
    .inr ⟨e, List.mem_append_left _ hm, hem, by rw [hany]; trivial⟩
  have stepEntry : ∀ e ∈ Ψ, e.1.mem σ h l = true →
      (∃ s, (s, e.2) ∈ rebaseAll ev Ψ ∧ s.mem ρ₀ h₀ l = true) ∨
        ∃ e' ∈ Φp, e'.1.mem ρ₀ h₀ l = true ∧ e'.2 = .any := by
    intro e hem hm
    rcases rebase_sound hp hk hl hm with ⟨s, hs, hsm⟩ | h
    · exact .inl ⟨s, List.mem_flatMap.mpr ⟨e, hem, List.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsm⟩
    · exact .inr h
  rcases ha₁ with rfl | ⟨e₁, he₁, hm₁, hh₁⟩
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inl rfl
    · rcases stepEntry e₂ he₂ hm₂ with ⟨s, hs, hsm⟩ | ⟨e', he', hm', hany⟩
      · exact .inr ⟨(s, e₂.2), List.mem_append_right _ hs, hsm, hh₂.lower hb⟩
      · exact viaAny e' he' hm' hany
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, hh₁⟩
    · rcases stepEntry e₂ he₂ hm₂ with ⟨s, hs, hsm⟩ | ⟨e', he', hm', hany⟩
      · have hseq := hh₁.seq hb hh₂
        rcases Change.max_cases e₁.2 e₂.2 with hmax | hmax
        · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, by rw [← hmax]; exact hseq⟩
        · exact .inr ⟨(s, e₂.2), List.mem_append_right _ hs, hsm, by rw [← hmax]; exact hseq⟩
      · exact viaAny e' he' hm' hany

end Verification.Footprints
