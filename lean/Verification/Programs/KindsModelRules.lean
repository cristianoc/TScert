import Verification.Programs.TolerantFramesModelRules
import Verification.Semantics.KindsContracts
/-!
# The note's (View) and Alloc over well-formed states, and a view write

The rules of `Programs/TolerantFramesModelRules.lean` that carry a premise of
the world there, stated over the well-formed states of
`Semantics/KindsStates.lean`, where the premise is part of the state:

- **(View)**: a linear fact whose current terms are slots' integers and
  typed-array lengths holds after every admissible transition (`view_box`);
  the two heaps of that module's `view_not_invariant` are no admissible
  transition between states validating the view (`view_change_excluded`);
- **Alloc**: the allocated array is fresh, empty and apart from every array
  of the well-formed heap it was allocated in (`alloc_post`), and the heap
  after the allocation is well-formed with the array valid (`alloc_wellformed`).

A view-element write (`ViewWrite`) between two concrete well-formed heaps
changes the stores of two views over the written bytes, exact for the
designated one, and keeps an ordinary array's store (`viewWrite_overlap`).
-/
namespace Verification.Kinds
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints
open Verification.TolerantFrames (allocated viewObj viewObj_length oneBits oneBits_safe)

/-! ## (View) -/

/-- **(View)**: a linear fact whose current terms are slots' integers and
typed-array lengths holds after every admissible transition; its entry
terms, of any kind and path, read the entry state. -/
theorem view_box {F : Linear.Fact HeapKnowledge.Term} {ρ : Env} {m : Nat} {s : State ρ}
    (hv : ∀ t ∈ F.vars, t.atEntry = false → t.path = [] ∧ (t.kind = .value ∨ t.kind = .view))
    (hF : (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) :
    Box Footprints.Closed.top.fp
      (fun ρ _ s => (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s.h) ρ m s := by
  intro s' ha
  show (HeapKnowledge.IndexFact.linear F).HoldsAt ε ρ s'.h
  have he : ∀ t ∈ F.vars, HeapKnowledge.termValue ε ρ s'.h t = HeapKnowledge.termValue ε ρ s.h t := by
    intro t ht
    obtain ⟨k, slot, p, e⟩ := t
    cases e
    case true => exact HeapKnowledge.termValue_entry_invariant rfl
    obtain ⟨hp, hk⟩ := hv _ ht rfl
    simp only at hp hk
    subst hp
    rcases hk with rfl | rfl
    · rfl
    · simp only [HeapKnowledge.termValue_nil, HeapKnowledge.kindValue]
      exact viewLengthOf_kept (s.roots slot) ha.1
  obtain ⟨hd, hh⟩ := hF
  refine ⟨fun t ht => by rw [he t ht]; exact hd t ht, ?_⟩
  refine (Linear.Fact.holds_congr fun t ht => ?_).mpr hh
  simp only [HeapKnowledge.termValuation, he t ht]

/-- **No admissible transition changes a valid view's length**: from a state
validating the typed array `viewObj` whose heap gives it the length 1, no
admissible transition reaches the heap giving it the length 2. -/
theorem view_change_excluded {s s' : IndexedHeap} (ha : Admissible s s') (hv : RefsOk s.W viewObj)
    (h₁ : s.h = [.nul, .num oneBits, .nul]) : s'.h ≠ [.nul, .num (bitsOfNat 2), .nul] := by
  intro h₂
  have two : SafeIntegers.SafeInt (bitsOfNat 2) 2 := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
  have hk := viewLengthOf_kept hv ha
  rw [h₁, h₂, viewObj_length oneBits_safe (by decide), viewObj_length two (by decide)] at hk
  cases hk

/-! ## Alloc -/

/-- **Alloc**: the array allocated in a well-formed heap is fresh against
it, has length 0, and is apart, at the heap after the allocation, from every
value whose store is a store of the entry heap. -/
theorem alloc_post {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) :
    FreshAt h.length (allocated h) ∧
      HeapKnowledge.lengthOf (h ++ [.arr []] ++ [.nul]) (allocated h) = some 0 ∧
      ∀ (u : Val) (sy : Nat) (ys : List (Option Nat)), storeOf u = some sy → h[sy]? = some (.arr ys) →
        HeapKnowledge.RegionsApart (h ++ [.arr []] ++ [.nul]) (allocated h) u :=
  let ⟨hf, hl, ha⟩ := TolerantFrames.alloc_post h
  ⟨hf, hl, fun u sy ys hs hy => ha u sy ys hs hy (hok.elementsBelow hy)⟩

/-- **The allocation keeps the heap well-formed.** The rule gives the store
slot the role of an array store and the identity its own, with contracts
`c` and `cid` that survive allocation and admit the empty store and `null`;
the allocated array's references are valid in the extended world. -/
theorem alloc_wellformed {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) (hadm : WorldAdm W)
    {c cid : Ctr n} (hc : CtrAdm c) (hcid : CtrAdm cid)
    (hcv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) (.arr []))
    (hiv : ∀ (j : Nat) (hj : j < n), cid j hj (trunc j (Nat.le_of_lt hj) W) .nul) :
    HeapOk n (appendWs W (objectEntries [.store .array] [c] cid)) (h ++ [.arr []] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.store .array] [c] cid)) (allocated h) := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  obtain ⟨hsh, href⟩ := arrayObject_shaped (ls := []) c cid hlen hok.2 (fun _ hr => by simp [refs, storeRefs] at hr)
  refine ⟨⟨?_, hsh⟩, href⟩
  rw [List.append_assoc]
  refine HeapMeets_appendWs hok.1 hadm (fun e he => ?_) rfl (fun i d v hd hv => ?_)
  · simp only [objectEntries, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hc
    · exact hcid
  · match i with
    | 0 => simp [objectEntries] at hd hv; subst hd hv; exact hcv
    | 1 => simp [objectEntries] at hd hv; subst hd hv; exact hiv
    | i + 2 => simp [objectEntries] at hd

/-! ## A view-element write over two overlapping views -/

/-- A contract admitting every machine value. -/
def anyCtr {k : Nat} : Ctr k := fun _ _ _ v => isVal v = true

/-- The world giving each location its listed role and a contract admitting
every machine value. -/
def roleWorld {k : Nat} (rs : List Role) : WorldT k := ofEntries (rs.map fun r => (r, anyCtr))

@[simp] theorem roleAt_roleWorld {k : Nat} (rs : List Role) (l : Nat) :
    roleAt (roleWorld (k := k) rs) l = rs[l]? := by
  simp [roleAt, roles, roleWorld, Function.comp_def]

theorem roleWorld_meets {k : Nat} {rs : List Role} {h : Heap} (hl : h.length = rs.length)
    (hv : ∀ v ∈ h, isVal v = true) : HeapMeets k (roleWorld rs) h := by
  refine ⟨by simp [roleWorld, hl], fun l c hc => ?_⟩
  simp only [lookup, toList, roleWorld, entries_ofEntries, List.map_map, List.getElem?_map,
    Option.map_eq_some_iff, Function.comp_apply] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  have hlt : l < h.length := by have := (List.getElem?_eq_some_iff.mp hr).1; omega
  exact ⟨h[l], List.getElem?_eq_getElem hlt, fun _ _ => hv _ (List.getElem_mem hlt)⟩

theorem roleWorld_ext {k : Nat} (rs tail : List Role) :
    WExt (roleWorld (k := k) rs) (roleWorld (rs ++ tail)) :=
  ⟨tail.map fun r => (r, anyCtr), by simp [roleWorld]⟩

/-- The roles of the entry heap: two view stores of length 1, their two
element cells, an ordinary array's store and its element cell. -/
def overlapRoles : List Role :=
  [.store (.view 1), .store (.view 1), .elem, .elem, .store .array, .elem]

/-- Two views over the same bytes (stores at 0 and 1) and an ordinary array
(store at 4). -/
def overlapBefore : Heap := [.arr [some 2], .arr [some 3], .num 0, .num 0, .arr [some 5], .num 0]

/-- After a write of `oneBits` at index 0 through the first view: both view
stores list fresh cells holding the written value. -/
def overlapAfter : Heap :=
  [.arr [some 6], .arr [some 7], .num 0, .num 0, .arr [some 5], .num 0, .num oneBits, .num oneBits]

/-- The designated view: a host object whose element store is at 0. -/
def overlapView : Val := .objAt [(hostKey, 8), (viewElementsKey, 0)] .absent 9

theorem overlapBefore_ok (n : Nat) : HeapOk n (roleWorld overlapRoles) overlapBefore := by
  refine ⟨roleWorld_meets rfl (by simp [overlapBefore, isVal]), fun l r hr => ?_⟩
  rw [roleAt_roleWorld] at hr
  rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;> subst hr <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
      | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [overlapRoles])
      | exact fun _ hm => by simp [refs] at hm
      | simp [Cat, isSourceVal]

theorem overlapAfter_ok (n : Nat) :
    HeapOk n (roleWorld (overlapRoles ++ [.elem, .elem])) overlapAfter := by
  refine ⟨roleWorld_meets rfl (by simp [overlapAfter, isVal]), fun l r hr => ?_⟩
  rw [roleAt_roleWorld] at hr
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;> subst hr <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
      | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [overlapRoles])
      | exact fun _ hm => by simp [refs] at hm
      | simp [Cat, isSourceVal]

/-- **A view-element write changes two overlapping views' stores and keeps
an ordinary array's.** Between the two well-formed heaps, at every budget,
the exact write through the first view holds: both view stores (locations 0
and 1) change, the designated one at the written index alone, and the
ordinary array's store (location 4) is kept. -/
theorem viewWrite_overlap (n : Nat) :
    HeapOk n (roleWorld overlapRoles) overlapBefore ∧
      ViewWriteOf .exact [overlapView, .num 0, .num oneBits] (roleWorld (k := n) overlapRoles)
        overlapBefore (roleWorld (k := n) (overlapRoles ++ [.elem, .elem])) overlapAfter ∧
      overlapAfter[0]? ≠ overlapBefore[0]? ∧ overlapAfter[1]? ≠ overlapBefore[1]? ∧
      roleAt (roleWorld (k := n) overlapRoles) 4 = some (.store .array) ∧
      overlapAfter[4]? = overlapBefore[4]? := by
  refine ⟨overlapBefore_ok n, ⟨⟨Nat.le_refl n, by rw [trunc_id]; exact roleWorld_ext _ _,
    overlapAfter_ok n, fun l r hr hne => ?_, fun l N ls ls' hr hl hl' c hc => ?_⟩, fun _ => ?_⟩,
    by simp [overlapAfter, overlapBefore], by simp [overlapAfter, overlapBefore],
    by simp [overlapRoles], rfl⟩
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;> subst hr <;>
      first | rfl | exact absurd rfl (hne 1)
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;>
      simp [overlapAfter] at hl' <;> subst hl' <;> simp at hc <;> subst hc <;>
      exact .inr (by simp [overlapBefore])
  · intro s ls hs hls
    have h0 : SafeIntegers.SafeInt (0 : UInt64) (0 : Int) := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
    have he : HeapKnowledge.elementsOf overlapView = some 0 := by decide
    have hg : ([overlapView, Tm.num 0, Tm.num oneBits] : List Tm).getD 0 .undef = overlapView := rfl
    rw [hg, he] at hs
    cases hs
    have hls' : ls = [some 2] := by simpa [overlapBefore] using hls.symm
    subst hls'
    refine ⟨[some 6], 0, 0, rfl, rfl, h0, by simp, fun j hj => ?_, 6, rfl, rfl⟩
    rcases j with _ | j
    · exact absurd rfl hj
    · simp


/-! ## A representative initial host world

A world with every role a builtin heap holds: a typed array (its view store
of length 1, its element cell, its length metadata with a singleton
contract, its host slot and its identity), an ordinary array (its store, its
element cell, its identity) and an object (a property and its identity).
The heap meets it at every budget with all three objects valid, and the
exact view-element write through the typed array inhabits the repaired
contract (`ViewWriteOf`) from it, keeping the ordinary array's store and
every other location. -/

/-- A contract admitting the single value `1`, the typed array's length. -/
def oneCtr {k : Nat} : Ctr k := fun _ _ _ v => v = .num (bitsOfNat 1)

/-- The roles and contracts of the initial host world, by location. -/
def hostEntries {k : Nat} : List (Role × Ctr k) :=
  [(.store (.view 1), anyCtr), (.elem, anyCtr), (.field, oneCtr), (.field, anyCtr), (.identity, anyCtr),
   (.store .array, anyCtr), (.elem, anyCtr), (.identity, anyCtr), (.field, anyCtr), (.identity, anyCtr)]

def hostWorld {k : Nat} : WorldT k := ofEntries hostEntries

/-- The world after the write: the fresh element cell appended. -/
def hostWorld' {k : Nat} : WorldT k := ofEntries (hostEntries ++ [(.elem, anyCtr)])

def hostBefore : Heap :=
  [.arr [some 1], .num 0, .num (bitsOfNat 1), .nul, .nul, .arr [some 6], .num 0, .nul, .str "x", .nul]

/-- After writing `1` at index 0 through the typed array: its view store
lists a fresh cell holding the value. -/
def hostAfter : Heap :=
  [.arr [some 10], .num 0, .num (bitsOfNat 1), .nul, .nul, .arr [some 6], .num 0, .nul, .str "x", .nul,
   .num oneBits]

/-- The typed array: a host object holding its length and its view store. -/
def hostView : Val := .objAt [(hostKey, 3), (viewLengthKey, 2), (viewElementsKey, 0)] .absent 4
/-- The ordinary array. -/
def hostArray : Val := .objAt [(arrayStoreKey, 5)] .absent 7
/-- The object with one property. -/
def hostObject : Val := .objAt [("p", 8)] .absent 9

theorem entries_meets {k : Nat} {es : List (Role × Ctr k)} {h : Heap} (hl : h.length = es.length)
    (hv : ∀ (i : Nat) (e : Role × Ctr k) (v : Val), es[i]? = some e → h[i]? = some v →
      ∀ (j : Nat) (hj : j < k) (W : WorldT j), e.2 j hj W v) : HeapMeets k (ofEntries es) h := by
  refine ⟨by simp [toList, hl], fun l c hc => ?_⟩
  simp only [lookup, toList, entries_ofEntries, List.getElem?_map, Option.map_eq_some_iff] at hc
  obtain ⟨e, he, rfl⟩ := hc
  have hlt : l < h.length := by have := (List.getElem?_eq_some_iff.mp he).1; omega
  exact ⟨h[l], List.getElem?_eq_getElem hlt, fun j hj => hv l e _ he (List.getElem?_eq_getElem hlt) j hj _⟩

@[simp] theorem roleAt_ofEntries {k : Nat} (es : List (Role × Ctr k)) (l : Nat) :
    roleAt (ofEntries es) l = (es.map Prod.fst)[l]? := by
  simp [roleAt, roles]

theorem lookup_hostWorld_two {k : Nat} : lookup (hostWorld (k := k)) 2 = some oneCtr := by
  simp [lookup, toList, hostWorld, hostEntries]

theorem lengthMeta_host {k : Nat} : LengthMeta (hostWorld (k := k)) 2 1 :=
  ⟨oneCtr, by simp [hostWorld, hostEntries], lookup_hostWorld_two, fun _ _ _ _ h => h⟩

theorem hostBefore_ok (n : Nat) : HeapOk n (hostWorld (k := n)) hostBefore := by
  refine ⟨entries_meets rfl fun i e v he hv j hj W => ?_, fun l r hr => ?_⟩
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [hostEntries, hostBefore] at he hv <;> subst he hv <;> simp [anyCtr, oneCtr, isVal]
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      refine ⟨_, rfl, ?_, ?_⟩ <;>
      first
        | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [hostWorld, hostEntries])
        | exact fun _ hm => by simp [refs] at hm
        | simp [Cat, isSourceVal]

theorem hostAfter_ok (n : Nat) : HeapOk n (hostWorld' (k := n)) hostAfter := by
  refine ⟨entries_meets rfl fun i e v he hv j hj W => ?_, fun l r hr => ?_⟩
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [hostEntries, hostAfter] at he hv <;> subst he hv <;> simp [anyCtr, oneCtr, isVal]
  · simp only [hostWorld', roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      refine ⟨_, rfl, ?_, ?_⟩ <;>
      first
        | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [hostWorld', hostEntries])
        | exact fun _ hm => by simp [refs] at hm
        | simp [Cat, isSourceVal]

/-- **The three host objects are valid in the initial host world**: the
typed array's identity is in I, its host slot and length metadata in F with
the length metadata's singleton contract, its view store a view store of
that length; the array's store slot an ordinary array's store; the
object's property in F. -/
theorem host_refs {k : Nat} :
    RefsOk (hostWorld (k := k)) hostView ∧ RefsOk (hostWorld (k := k)) hostArray ∧
      RefsOk (hostWorld (k := k)) hostObject := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · simp only [hostView, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · refine ⟨fun m hm => ⟨1, ?_⟩, fun e he => ⟨1, 2, ?_, rfl, lengthMeta_host⟩⟩
      · simp [viewLengthKey, hostKey, viewElementsKey] at hm; subst hm; exact lengthMeta_host
      · simp [viewLengthKey, hostKey, viewElementsKey] at he; subst he; simp [hostWorld, hostEntries]
    · simp [RefOk, SlotRole, hostWorld, hostEntries, hostKey, arrayStoreKey, viewElementsKey]
    · simp [RefOk, SlotRole, hostWorld, hostEntries, viewLengthKey, arrayStoreKey, viewElementsKey]
    · simp [RefOk, SlotRole, hostWorld, hostEntries]
  · simp only [hostArray, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · exact ⟨fun m hm => by simp [viewLengthKey, arrayStoreKey] at hm,
        fun e he => by simp [viewElementsKey, arrayStoreKey] at he⟩
    · simp [RefOk, SlotRole, hostWorld, hostEntries]
  · simp only [hostObject, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · exact ⟨fun m hm => by simp [viewLengthKey] at hm, fun e he => by simp [viewElementsKey] at he⟩
    · simp [RefOk, SlotRole, hostWorld, hostEntries, arrayStoreKey, viewElementsKey]

/-- **The repaired view-element write is inhabited from the initial host
world**: at every budget the exact write of `1` at index 0 through the typed
array is a `ViewWriteOf` transition between the two well-formed heaps,
changing the view store and keeping the ordinary array's store. -/
theorem host_viewWrite (n : Nat) :
    ViewWriteOf .exact [hostView, .num 0, .num oneBits] (hostWorld (k := n)) hostBefore
      (hostWorld' (k := n)) hostAfter ∧ hostAfter[0]? ≠ hostBefore[0]? ∧ hostAfter[5]? = hostBefore[5]? := by
  refine ⟨⟨⟨Nat.le_refl n, by rw [trunc_id]; exact ⟨[(.elem, anyCtr)], by simp [hostWorld, hostWorld']⟩,
    hostAfter_ok n, fun l r hr hne => ?_, fun l N ls ls' hr hl hl' c hc => ?_⟩, fun _ => ?_⟩,
    by simp [hostAfter, hostBefore], rfl⟩
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      first | rfl | exact absurd rfl (hne 1)
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;>
      simp [hostAfter] at hl' <;> subst hl' <;> simp at hc <;> subst hc <;>
      exact .inr (by simp [hostBefore])
  · intro s ls hs hls
    have h0 : SafeIntegers.SafeInt (0 : UInt64) (0 : Int) := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
    have he : HeapKnowledge.elementsOf hostView = some 0 := by decide
    have hg : ([hostView, Tm.num 0, Tm.num oneBits] : List Tm).getD 0 .undef = hostView := rfl
    rw [hg, he] at hs
    cases hs
    have hls' : ls = [some 1] := by simpa [hostBefore] using hls.symm
    subst hls'
    refine ⟨[some 10], 0, 0, rfl, rfl, h0, by simp, fun j hj => ?_, 10, rfl, rfl⟩
    rcases j with _ | j
    · exact absurd rfl hj
    · simp

end Verification.Kinds
