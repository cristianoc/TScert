import Verification.Types.Types
/-!
# Heaps and their invariant

The world says what a location is for; the heap says what it holds. `HeapOk`
relates them in two parts: every declared location holds a value meeting its
contract, at every level below the current one, with the world truncated to
that level (`HeapMeets`); and every location holds contents of the shape its
role demands (`Shaped`), a structural part unindexed by the level, so it holds
at every budget, zero included.

Membership in a contract never inspects the heap, only the world: a write
cannot disturb any claim, so preservation reduces to a local check at the
location written -- the contract and the role's shape there -- and allocation
preserves the invariant provided the world's contracts are admissible, which is
a property of the contracts and not of any one type constructor.
-/
namespace Verification

/-- The contract part of satisfaction. -/
def HeapMeets (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  h.length = (toList W).length ∧
    ∀ l c, lookup W l = some c →
      ∃ v, h[l]? = some v ∧ ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v

/-- **Heap satisfaction**: both parts of each entry. -/
def HeapOk (n : Nat) (W : WorldT n) (h : Heap) : Prop := HeapMeets n W h ∧ Shaped W h

theorem HeapMeets_trunc (n : Nat) (W : WorldT (n + 1)) (h : Heap)
    (hok : HeapMeets (n + 1) W h) : HeapMeets n (trunc n (Nat.le_succ n) W) h := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simpa using hlen, ?_⟩
  intro l c hl
  obtain ⟨d, hd, rfl⟩ := lookup_trunc_inv (Nat.le_succ n) W l c hl
  obtain ⟨v, hv, hmem⟩ := hall l d hd
  refine ⟨v, hv, fun j hj => ?_⟩
  rw [trunc_trunc]
  exact hmem j (by omega)

/-- Heap satisfaction survives dropping a level, with the world truncated. -/
theorem HeapOk_trunc (n : Nat) (W : WorldT (n + 1)) (h : Heap)
    (hok : HeapOk (n + 1) W h) : HeapOk n (trunc n (Nat.le_succ n) W) h :=
  ⟨HeapMeets_trunc n W h hok.1, Shaped_trunc _ hok.2⟩

/-- At positive level, a stable location holds its single value. -/
theorem HeapOk.stable_value {n : Nat} {W : WorldT n} {h : Heap}
    {l : Nat} {c : Ctr n} {v : Val} (hh : HeapOk n W h)
    (hn : 0 < n) (hl : lookup W l = some c) (hc : CtrStable c v) :
    h[l]? = some v := by
  obtain ⟨u, hu, hm⟩ := hh.1.2 l c hl
  have he := hc 0 hn (trunc 0 (Nat.zero_le n) W) u (hm 0 hn)
  simpa [he] using hu

/-! ## Kinds are disjoint and partition the domain -/

/-- The locations of kind `k`: `K_W(k)`. -/
def K {n : Nat} (W : WorldT n) (k : Kind) (l : Nat) : Prop := kindAt W l = some k

/-- **Kinds are disjoint.** -/
theorem kinds_disjoint {n : Nat} (W : WorldT n) {k k' : Kind} (hne : k ≠ k') (l : Nat) :
    ¬ (K W k l ∧ K W k' l) := by
  rintro ⟨h1, h2⟩
  simp only [K] at h1 h2
  rw [h1] at h2; cases h2; exact hne rfl

theorem roleAt_lt {n} {W : WorldT n} {l : Nat} {r : Role} (h : roleAt W l = some r) :
    l < (entries W).length := by
  have := (List.getElem?_eq_some_iff.mp h).1; simpa using this

theorem roleAt_some {n} {W : WorldT n} {l : Nat} (h : l < (entries W).length) :
    ∃ r, roleAt W l = some r :=
  ⟨_, List.getElem?_eq_getElem (by simpa using h)⟩

theorem Cat_store_iff {r : Role} {ls : List (Option Nat)} (h : Cat r (.arr ls)) : r.kind = .store := by
  cases r with
  | field | cell | elem => simp [Cat, isSourceVal] at h
  | identity => simp [Cat] at h
  | store f => rfl

theorem RefsOk_arr {n} {W : WorldT n} {ls : List (Option Nat)} (h : RefsOk W (.arr ls)) :
    ∀ l, some l ∈ ls → K W .elem l := by
  intro l hl
  have := h (.elem l) (by
    simp only [refs, storeRefs]; exact List.mem_filterMap.mpr ⟨some l, hl, rfl⟩)
  simp [RefOk] at this; simp [K, kindAt, this, Role.kind]

/-- **Kinds partition a well-formed heap's domain**: each location has
exactly one kind; a location is a store location exactly when it holds a
store; and every store lists element cells only, which are locations of the
heap. -/
theorem HeapOk.kinds {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) :
    (∀ l, l < h.length → ∃ k, K W k l ∧ ∀ k', K W k' l → k' = k) ∧
    (∀ l, K W .store l ↔ ∃ ls, h[l]? = some (Tm.arr ls)) ∧
    (∀ (s : Nat) (ls : List (Option Nat)), h[s]? = some (Tm.arr ls) →
      ∀ l, some l ∈ ls → K W .elem l ∧ l < h.length) := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  have store_of : ∀ (s : Nat) (ls : List (Option Nat)), h[s]? = some (Tm.arr ls) → ∃ r, roleAt W s = some r ∧ Shape W r (.arr ls) := by
    intro s ls hs
    have hlt : s < (entries W).length := by
      have := (List.getElem?_eq_some_iff.mp hs).1; omega
    obtain ⟨r, hr⟩ := roleAt_some hlt
    obtain ⟨u, hu, hsh⟩ := hok.2 s r hr
    rw [hs] at hu; cases hu
    exact ⟨r, hr, hsh⟩
  refine ⟨fun l hl => ?_, fun l => ⟨fun hk => ?_, fun ⟨ls, hs⟩ => ?_⟩, fun s ls hs l hl => ?_⟩
  · obtain ⟨r, hr⟩ := roleAt_some (show l < (entries W).length by omega)
    refine ⟨r.kind, by simp [K, kindAt, hr], fun k' hk' => ?_⟩
    simp [K, kindAt, hr] at hk'; exact hk'.symm
  · simp only [K, kindAt, Option.map_eq_some_iff] at hk
    obtain ⟨r, hr, hk⟩ := hk
    obtain ⟨u, hu, hc, -⟩ := hok.2 l r hr
    cases r with
    | store f =>
      cases f with
      | array => obtain ⟨ls, rfl⟩ := hc; exact ⟨ls, hu⟩
      | view N => obtain ⟨ls, rfl, -⟩ := hc; exact ⟨ls, hu⟩
    | _ => simp [Role.kind] at hk
  · obtain ⟨r, hr, hsh⟩ := store_of l ls hs
    simp [K, kindAt, hr, Cat_store_iff hsh.1]
  · obtain ⟨r, hr, hsh⟩ := store_of s ls hs
    have he := RefsOk_arr hsh.2 l hl
    refine ⟨he, ?_⟩
    simp only [K, kindAt, Option.map_eq_some_iff] at he
    obtain ⟨r', hr', -⟩ := he
    have := roleAt_lt hr'; omega

/-! ## What kinded satisfaction excludes -/

/-- **Allocated cells**: every cell a store of a well-formed heap lists is an
element cell of the world and a location of the heap. The budget is any,
zero included. -/
theorem HeapOk.store_cells {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {s : Nat}
    {ls : List (Option Nat)} (hs : h[s]? = some (Tm.arr ls)) {l : Nat} (hl : some l ∈ ls) :
    roleAt W l = some .elem ∧ l < h.length := by
  have hk := (HeapOk.kinds hok).2.2 s ls hs l hl
  refine ⟨?_, hk.2⟩
  have hk1 := hk.1
  simp only [K, kindAt, Option.map_eq_some_iff] at hk1
  obtain ⟨r, hr, hk'⟩ := hk1
  cases r <;> first | exact hr | simp [Role.kind] at hk'

theorem RefsOk_arr_iff {k : Nat} {W : WorldT k} {ls : List (Option Nat)} :
    RefsOk W (.arr ls) ↔ ∀ l, some l ∈ ls → roleAt W l = some .elem := by
  constructor
  · intro h l hl
    have := h (.elem l) (by simp only [refs, storeRefs]; exact List.mem_filterMap.mpr ⟨some l, hl, rfl⟩)
    simpa [RefOk] using this
  · intro h r hr
    simp only [refs, storeRefs, List.mem_filterMap] at hr
    obtain ⟨o, ho, hro⟩ := hr
    cases o with
    | none => cases hro
    | some l => cases hro; exact h l ho

/-- A store listing only cells another valid store lists is valid. -/
theorem RefsOk_arr_of_subset {k : Nat} {W : WorldT k} {ls ls' : List (Option Nat)}
    (hsub : ∀ l, some l ∈ ls' → some l ∈ ls) (h : RefsOk W (.arr ls)) : RefsOk W (.arr ls') :=
  RefsOk_arr_iff.mpr fun l hl => RefsOk_arr_iff.mp h l (hsub l hl)

/-! ## Writing one location -/

/-- **Structural satisfaction survives a write of contents of the target's
role's shape.** -/
theorem Shaped_set {k : Nat} {W : WorldT k} {h : Heap} {l : Nat} {r : Role} {v : Val}
    (hsh : Shaped W h) (hr : roleAt W l = some r) (hv : Shape W r v) : Shaped W (h.set l v) := by
  intro l' r' hr'
  by_cases he : l' = l
  · subst he
    rw [hr] at hr'; cases hr'
    obtain ⟨u, hu, -⟩ := hsh l' r hr
    have hlt : l' < h.length := (List.getElem?_eq_some_iff.mp hu).1
    exact ⟨v, by simp [hlt], hv⟩
  · obtain ⟨u, hu, hs⟩ := hsh l' r' hr'
    exact ⟨u, by rw [List.getElem?_set_ne (Ne.symm he)]; exact hu, hs⟩

/-- **Kinded `write_sound`**: a write meeting the location's contract and its
role's shape preserves both parts of satisfaction. -/
theorem write_sound (n : Nat) (W : WorldT n) (h : Heap) (l : Nat) (c : Ctr n) (r : Role) (v : Val)
    (hok : HeapOk n W h) (hl : lookup W l = some c) (hr : roleAt W l = some r)
    (hv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v)
    (hs : Shape W r v) : HeapOk n W (h.set l v) := by
  obtain ⟨⟨hlen, hall⟩, hsh⟩ := hok
  refine ⟨⟨by simpa using hlen, fun k d hk => ?_⟩, Shaped_set hsh hr hs⟩
  by_cases hkl : k = l
  · subst hkl
    rw [hl] at hk; cases hk
    obtain ⟨u, hu, -⟩ := hall k c hl
    have hlt : k < h.length := (List.getElem?_eq_some_iff.mp hu).1
    exact ⟨v, by simp [hlt], hv⟩
  · obtain ⟨w, hw, hmem⟩ := hall k d hk
    exact ⟨w, by rwa [List.getElem?_set_ne (fun hc => hkl hc.symm)], hmem⟩


/-! ## Appending entries -/

theorem roleAt_appendWs_lt {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : l < (entries W).length) : roleAt (appendWs W es) l = roleAt W l := by
  simp only [roleAt, roles, entries_appendWs, List.map_append]
  rw [List.getElem?_append_left (by simpa using hl)]

theorem lookup_appendWs_lt {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : l < (entries W).length) : lookup (appendWs W es) l = lookup W l := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_left (by simpa using hl)]

theorem lookup_appendWs_ge {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat} :
    lookup (appendWs W es) ((entries W).length + i) = (es.map Prod.snd)[i]? := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem roleAt_appendWs' {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat} :
    roleAt (appendWs W es) ((entries W).length + i) = (es.map Prod.fst)[i]? := by
  rw [roleAt_appendWs_ge W es (by omega)]
  simp

/-- **Structural satisfaction survives appending locations** whose contents
have the shapes their new roles demand in the extended world. -/
theorem Shaped_appendWs {k : Nat} {W : WorldT k} {h : Heap} {es : List (Role × Ctr k)}
    {vs : List Val} (hlen : h.length = (entries W).length) (hsh : Shaped W h)
    (hnew : ∀ (i : Nat) (r : Role) (v : Val), (es.map Prod.fst)[i]? = some r → vs[i]? = some v → Shape (appendWs W es) r v)
    (hes : es.length = vs.length) :
    Shaped (appendWs W es) (h ++ vs) := by
  intro l r hr
  by_cases hl : l < (entries W).length
  · rw [roleAt_appendWs_lt W es hl] at hr
    obtain ⟨u, hu, hs⟩ := hsh l r hr
    exact ⟨u, by rw [List.getElem?_append_left (by omega)]; exact hu,
      Shape_mono (WExt_appendWs W es) hs⟩
  · obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    rw [roleAt_appendWs'] at hr
    have hi : i < vs.length := by
      have := (List.getElem?_eq_some_iff.mp hr).1; simp at this; omega
    refine ⟨vs[i], by rw [List.getElem?_append_right (by omega)]; simp [hlen, hi], ?_⟩
    exact hnew i r _ hr (List.getElem?_eq_getElem hi)

/-- **The contract part survives appending locations** whose contents meet
their admissible contracts: `heap_allocs` of `Semantics/Heaps.lean` for any
appended entries. -/
theorem HeapMeets_appendWs {n : Nat} {W : WorldT n} {h : Heap} {es : List (Role × Ctr n)}
    {vs : List Val} (hok : HeapMeets n W h) (hadm : WorldAdm W) (hcadm : ∀ e ∈ es, CtrAdm e.2)
    (hes : es.length = vs.length)
    (hv : ∀ (i : Nat) (c : Ctr n) (v : Val), (es.map Prod.snd)[i]? = some c → vs[i]? = some v →
      ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v) :
    HeapMeets n (appendWs W es) (h ++ vs) := by
  obtain ⟨hlen, hall⟩ := hok
  have hlen' : h.length = (entries W).length := by simpa using hlen
  refine ⟨by simp [hlen', hes], fun l c hl => ?_⟩
  have hxt : ∀ (j : Nat) (hj : j < n),
      WExt (trunc j (Nat.le_of_lt hj) W) (trunc j (Nat.le_of_lt hj) (appendWs W es)) :=
    fun j hj => WExt_trunc (Nat.le_of_lt hj) (WExt_appendWs W es)
  by_cases hlt : l < (entries W).length
  · rw [lookup_appendWs_lt W es hlt] at hl
    obtain ⟨v, hv', hm⟩ := hall l c hl
    exact ⟨v, by rw [List.getElem?_append_left (by omega)]; exact hv',
      fun j hj => (hadm l c hl).1 j hj _ _ (hxt j hj) v (hm j hj)⟩
  · obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    rw [lookup_appendWs_ge] at hl
    have hi : i < vs.length := by
      have := (List.getElem?_eq_some_iff.mp hl).1; simp at this; omega
    have hce : ∃ e ∈ es, e.2 = c := by
      have := List.mem_of_getElem? hl; simpa using this
    obtain ⟨e, he, rfl⟩ := hce
    refine ⟨vs[i], by rw [List.getElem?_append_right (by omega)]; simp [hlen', hi], fun j hj => ?_⟩
    exact (hcadm e he).1 j hj _ _ (hxt j hj) _ (hv i e.2 _ hl (List.getElem?_eq_getElem hi) j hj)

/-- **Kinded allocation**: both parts of satisfaction survive appending
locations whose contents meet their contracts and have their roles' shapes. -/
theorem HeapOk_appendWs {n : Nat} {W : WorldT n} {h : Heap} {es : List (Role × Ctr n)}
    {vs : List Val} (hok : HeapOk n W h) (hadm : WorldAdm W) (hcadm : ∀ e ∈ es, CtrAdm e.2)
    (hes : es.length = vs.length)
    (hv : ∀ (i : Nat) (c : Ctr n) (v : Val), (es.map Prod.snd)[i]? = some c → vs[i]? = some v →
      ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v)
    (hnew : ∀ (i : Nat) (r : Role) (v : Val), (es.map Prod.fst)[i]? = some r → vs[i]? = some v → Shape (appendWs W es) r v) :
    HeapOk n (appendWs W es) (h ++ vs) :=
  ⟨HeapMeets_appendWs hok.1 hadm hcadm hes hv,
    Shaped_appendWs (by simpa using hok.1.1) hok.2 hnew hes⟩

/-! ## Objects -/


/-- **Every location of a well-formed heap holds contents with valid
references.** -/
theorem HeapOk.refs_at {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {l : Nat} {v : Val}
    (hv : h[l]? = some v) : RefsOk W v := by
  have hlt : l < (entries W).length := by
    have := (List.getElem?_eq_some_iff.mp hv).1; have := hok.1.1; simp at this; omega
  obtain ⟨r, hr⟩ := roleAt_some hlt
  obtain ⟨u, hu, -, hs⟩ := hok.2 l r hr
  rw [hv] at hu; cases hu; exact hs

/-- **A fresh error object's allocation**: one identity location holding
`null`. The extended heap is well-formed and the thrown object's references
are valid. -/
theorem HeapOk.error {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) (hadm : WorldAdm W) :
    WorldAdm (appendW W .identity (fun _ _ _ u => u = .nul)) ∧
      HeapOk n (appendW W .identity (fun _ _ _ u => u = .nul)) (h ++ [.nul]) ∧
      RefsOk (appendW W .identity (fun _ _ _ u => u = .nul)) (.throw (thrownError h.length)) := by
  have hcadm : CtrAdm (fun _ _ _ u => u = .nul : Ctr n) :=
    ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => by rw [show _ = Tm.nul from h]; rfl⟩
  have hlen : h.length = (entries W).length := by have := hok.1.1; simpa using this
  have hA : appendW W .identity (fun _ _ _ u => u = .nul) = appendWs W [(.identity, fun _ _ _ u => u = .nul)] := rfl
  refine ⟨WorldAdm_append hadm hcadm, ⟨?_, ?_⟩, ?_⟩
  · rw [hA]
    exact HeapMeets_appendWs hok.1 hadm (by simpa using hcadm) rfl (fun i c v hc hv j hj => by
      obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
      simp at hc hv; subst hc hv; rfl)
  · rw [hA]
    refine Shaped_appendWs hlen hok.2 (fun i r v hr hv => ?_) rfl
    obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    simp at hr hv; subst hr hv
    exact ⟨rfl, fun _ hr => by simp [refs] at hr⟩
  · intro r hr
    simp only [refs, thrownError, objRefs, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · show roleAt _ _ = _
      rw [hA, hlen, show (entries W).length = (entries W).length + 0 from rfl, roleAt_appendWs']; rfl
    · exact ⟨fun m hm => by simp at hm, fun e he => by simp at he, fun e he => by simp at he⟩

/-- **Elements read from a well-formed heap have valid references.** -/
theorem HeapOk.readElems_refs {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs → ∀ v ∈ vs, RefsOk W v
  | [], vs, hr => by simp [readElems] at hr; subst hr; simp
  | none :: ls, vs, hr => by
    simp only [readElems, Option.map_eq_some_iff] at hr
    obtain ⟨ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact RefsOk_undef
    · exact hok.readElems_refs hws v hv
  | some l :: ls, vs, hr => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨w, hw, ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hok.refs_at hw
    · exact hok.readElems_refs hws v hv

end Verification
