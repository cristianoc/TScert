import Verification.Programs.TolerantFramesModelRules
import Verification.Semantics.KindsNatives
import Verification.Semantics.TolerantFramesCells
import Verification.Semantics.KindsCapabilities
/-!
# Witnesses of (View), Alloc and the view write over kinded worlds

The rules of `Programs/TolerantFramesModelRules.lean` (`view_box`,
`alloc_post`) shown on concrete well-formed heaps:

- **(View)**: no admissible transition between states validating a typed
  array changes its length from 1 to 2 (`view_change_excluded`);
- **Alloc**: the heap after an array's allocation is well-formed with the
  array valid (`alloc_wellformed`).

A view-element write (`ViewWrite`) between two concrete well-formed heaps
changes the stores of two views over the written bytes, exact for the
designated one, and keeps an ordinary array's store (`viewWrite_overlap`).
-/
namespace Verification.Kinds
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints
open Verification.TolerantFrames (allocated viewObj viewObj_length oneBits oneBits_safe IndexedHeap Admissible viewLengthOf_kept)

/-! ## (View) -/

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

/-- **The allocation keeps the heap well-formed.** The rule gives the store
slot the role of an array store and the identity its own, with contracts
`c` that survives allocation and admits the empty store, the identity's
admitting `null` alone (`idCtr`);
the allocated array's references are valid in the extended world. -/
theorem alloc_wellformed {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) (hadm : WorldAdm W)
    {c : Ctr n} (hc : CtrAdm c)
    (hcv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) (.arr [])) :
    HeapOk n (appendWs W (objectEntries [.store .array] [c])) (h ++ [.arr []] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.store .array] [c])) (allocated h) := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  obtain ⟨hsh, href⟩ := arrayObject_shaped (ls := []) c hlen hok.2 (fun _ hr => by simp [refs, storeRefs] at hr)
  refine ⟨⟨?_, hsh⟩, href⟩
  rw [List.append_assoc]
  refine HeapMeets_appendWs hok.1 hadm (fun e he => ?_) rfl (fun i d v hd hv => ?_)
  · simp only [objectEntries, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hc
    · exact idCtr_adm
  · match i with
    | 0 => simp [objectEntries] at hd hv; subst hd hv; exact hcv
    | 1 => simp [objectEntries] at hd hv; subst hd hv; exact fun _ _ => rfl
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
      ViewWriteOf (.exact .uint8) [overlapView, .num 0, .num oneBits] (roleWorld (k := n) overlapRoles)
        overlapBefore (roleWorld (k := n) (overlapRoles ++ [.elem, .elem])) overlapAfter ∧
      overlapAfter[0]? ≠ overlapBefore[0]? ∧ overlapAfter[1]? ≠ overlapBefore[1]? ∧
      roleAt (roleWorld (k := n) overlapRoles) 4 = some (.store .array) ∧
      overlapAfter[4]? = overlapBefore[4]? := by
  refine ⟨overlapBefore_ok n, ⟨⟨Nat.le_refl n, by rw [trunc_id]; exact roleWorld_ext _ _,
    overlapAfter_ok n, fun l r hr hne => ?_, fun l N ls ls' hr hl hl' c hc => ?_⟩, fun _ hk => ?_⟩,
    by simp [overlapAfter, overlapBefore], by simp [overlapAfter, overlapBefore],
    by simp [overlapRoles], rfl⟩
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;> subst hr <;>
      first | rfl | exact absurd rfl (hne 1)
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;>
      simp [overlapAfter] at hl' <;> subst hl' <;> simp at hc <;> subst hc <;>
      exact .inr (by simp [overlapBefore])
  · cases hk
    refine ⟨⟨oneBits, 1, rfl, oneBits_safe, fun lo hi he => by
      simp [CallEffects.ElementKind.range] at he; omega⟩, fun s ls hs hls => ?_⟩
    have h0 : SafeIntegers.SafeInt (0 : UInt64) (0 : Int) := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
    have he : HeapKnowledge.elementsOf overlapView = some 0 := by decide
    have hg : ([overlapView, Tm.num 0, Tm.num oneBits] : List Tm).getD 0 .undef = overlapView := rfl
    rw [hg, he] at hs
    cases hs
    have hls' : ls = [some 2] := by simpa [overlapBefore] using hls.symm
    subst hls'
    refine ⟨[some 6], 0, 0, rfl, rfl, h0, by simp, fun j hj => ?_, 6, rfl, by
      rw [show ([_, Tm.num 0, Tm.num oneBits] : List Tm).getD 2 .undef = .num oneBits from rfl, oneBits,
        CallEffects.ElementKind.convert_bitsOfNat _ (by decide)]; rfl⟩
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
  [(.store (.view 1), anyCtr), (.elem, anyCtr), (.field, oneCtr), (.field, anyCtr), (.identity, idCtr),
   (.store .array, anyCtr), (.elem, anyCtr), (.identity, idCtr), (.field, anyCtr), (.identity, idCtr)]

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
      simp [hostEntries, hostBefore] at he hv <;> subst he hv <;> simp [anyCtr, oneCtr, idCtr, isVal]
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
      simp [hostEntries, hostAfter] at he hv <;> subst he hv <;> simp [anyCtr, oneCtr, idCtr, isVal]
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
    · refine ⟨fun m hm => ⟨1, ?_⟩, fun e he => ⟨1, 2, ?_, rfl, lengthMeta_host⟩, fun _ _ => rfl⟩
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
        fun e he => by simp [viewElementsKey, arrayStoreKey] at he,
        fun e he => by simp [viewElementsKey, viewLengthKey, arrayStoreKey] at he⟩
    · simp [RefOk, SlotRole, hostWorld, hostEntries]
  · simp only [hostObject, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · exact ⟨fun m hm => by simp [viewLengthKey] at hm, fun e he => by simp [viewElementsKey] at he,
        fun e he => by simp [viewElementsKey, viewLengthKey] at he⟩
    · simp [RefOk, SlotRole, hostWorld, hostEntries, arrayStoreKey, viewElementsKey]

/-- **The repaired view-element write is inhabited from the initial host
world**: at every budget the exact write of `1` at index 0 through the typed
array is a `ViewWriteOf` transition between the two well-formed heaps,
changing the view store and keeping the ordinary array's store. -/
theorem host_viewWrite (n : Nat) :
    ViewWriteOf (.exact .uint8) [hostView, .num 0, .num oneBits] (hostWorld (k := n)) hostBefore
      (hostWorld' (k := n)) hostAfter ∧ hostAfter[0]? ≠ hostBefore[0]? ∧ hostAfter[5]? = hostBefore[5]? := by
  refine ⟨⟨⟨Nat.le_refl n, by rw [trunc_id]; exact ⟨[(.elem, anyCtr)], by simp [hostWorld, hostWorld']⟩,
    hostAfter_ok n, fun l r hr hne => ?_, fun l N ls ls' hr hl hl' c hc => ?_⟩, fun _ hk => ?_⟩,
    by simp [hostAfter, hostBefore], rfl⟩
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      first | rfl | exact absurd rfl (hne 1)
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;>
      simp [hostAfter] at hl' <;> subst hl' <;> simp at hc <;> subst hc <;>
      exact .inr (by simp [hostBefore])
  · cases hk
    refine ⟨⟨oneBits, 1, rfl, oneBits_safe, fun lo hi he => by
      simp [CallEffects.ElementKind.range] at he; omega⟩, fun s ls hs hls => ?_⟩
    have h0 : SafeIntegers.SafeInt (0 : UInt64) (0 : Int) := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
    have he : HeapKnowledge.elementsOf hostView = some 0 := by decide
    have hg : ([hostView, Tm.num 0, Tm.num oneBits] : List Tm).getD 0 .undef = hostView := rfl
    rw [hg, he] at hs
    cases hs
    have hls' : ls = [some 1] := by simpa [hostBefore] using hls.symm
    subst hls'
    refine ⟨[some 10], 0, 0, rfl, rfl, h0, by simp, fun j hj => ?_, 10, rfl, by
      rw [show ([_, Tm.num 0, Tm.num oneBits] : List Tm).getD 2 .undef = .num oneBits from rfl, oneBits,
        CallEffects.ElementKind.convert_bitsOfNat _ (by decide)]; rfl⟩
    rcases j with _ | j
    · exact absurd rfl hj
    · simp

/-! ## Every structural family at once, at every budget -/

/-- The host world extended by a binding cell, an object's prototype
property, a closure's code field and a forwarding descriptor's identity. -/
def familiesEntries {k : Nat} : List (Role × Ctr k) :=
  hostEntries ++ [(.cell, anyCtr), (.identity, idCtr), (.field, anyCtr), (.identity, idCtr),
    (.field, anyCtr), (.identity, idCtr), (.identity, idCtr)]

def familiesWorld {k : Nat} : WorldT k := ofEntries familiesEntries

def familiesHeap : Heap := hostBefore ++ [.num 0, .nul, hostObject, .nul, .nul, .nul, .nul]

/-- A binding's cell holding a number. -/
def hostCell : Val := .objAt [(valueField, 10)] .absent 11
/-- An object whose prototype is `hostObject`. -/
def hostProtoed : Val := .objAt [(CallArguments.protoField, 12)] .absent 13
/-- Graph code capturing `hostObject`, with its code field. -/
def hostClosure : Val := .objAt [(codeField, 14)] (.graph 0 [] [] 0 [hostObject] .call false) 15
/-- A forwarding descriptor of the closure, its receiver `hostObject`, its
prefix the ordinary array. -/
def hostBound : Val := .objAt [] (.bound hostClosure hostObject [hostArray]) 16

/-- The environment binding every structural family of host value. -/
def familiesEnv : Env := fun i =>
  match i with
  | 0 => hostView | 1 => hostArray | 2 => hostObject | 3 => hostCell | 4 => hostProtoed
  | 5 => hostClosure | 6 => hostBound | _ => .undef

theorem familiesWorld_adm {k : Nat} : WorldAdm (familiesWorld (k := k)) := by
  intro l c hc
  simp only [lookup, toList, familiesWorld, entries_ofEntries, List.getElem?_map, Option.map_eq_some_iff] at hc
  obtain ⟨e, he, rfl⟩ := hc
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
    simp [familiesEntries, hostEntries] at he <;> subst he <;>
    first
      | exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩
      | exact idCtr_adm
      | exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => by rw [hv]; rfl⟩

theorem lengthMeta_families {k : Nat} : LengthMeta (familiesWorld (k := k)) 2 1 :=
  ⟨oneCtr, by simp [familiesWorld, familiesEntries, hostEntries], by
    simp [lookup, toList, familiesWorld, familiesEntries, hostEntries], fun _ _ _ _ h => h⟩

theorem familiesWorld_ext {k : Nat} : WExt (hostWorld (k := k)) (familiesWorld (k := k)) :=
  ⟨[(.cell, anyCtr), (.identity, idCtr), (.field, anyCtr), (.identity, idCtr), (.field, anyCtr),
    (.identity, idCtr), (.identity, idCtr)], by simp [hostWorld, familiesWorld, familiesEntries]⟩

/-- **Every family's value is valid in the families' world**: a typed array
with its view metadata and view store, an ordinary array with its store and
element, an object, a binding cell, a prototype property, a closure with its
capture and code field, and a forwarding descriptor of the closure. -/
theorem families_refs {k : Nat} : RootsOk (familiesWorld (k := k)) familiesEnv := by
  have hview := RefsOk_mono familiesWorld_ext (host_refs (k := k)).1
  have harr := RefsOk_mono familiesWorld_ext (host_refs (k := k)).2.1
  have hobj := RefsOk_mono familiesWorld_ext (host_refs (k := k)).2.2
  have hcell : RefsOk (familiesWorld (k := k)) hostCell := by
    intro r hr
    simp only [hostCell, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
    · exact ⟨fun m hm => by simp [viewLengthKey, valueField] at hm,
        fun e he => by simp [viewElementsKey, valueField] at he,
        fun e he => by simp [viewElementsKey, viewLengthKey, valueField] at he⟩
    · simp [RefOk, SlotRole, familiesWorld, familiesEntries, hostEntries, valueField, arrayStoreKey,
        viewElementsKey]
  have hpro : RefsOk (familiesWorld (k := k)) hostProtoed := by
    intro r hr
    simp only [hostProtoed, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
    · exact ⟨fun m hm => by simp [viewLengthKey, CallArguments.protoField] at hm,
        fun e he => by simp [viewElementsKey, CallArguments.protoField] at he,
        fun e he => by simp [viewElementsKey, viewLengthKey, CallArguments.protoField] at he⟩
    · simp [RefOk, SlotRole, familiesWorld, familiesEntries, hostEntries, CallArguments.protoField,
        arrayStoreKey, viewElementsKey]
  have hclo : RefsOk (familiesWorld (k := k)) hostClosure := by
    intro r hr
    rw [hostClosure, refs_objAt] at hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
      · exact ⟨fun m hm => by simp [viewLengthKey, codeField] at hm,
          fun e he => by simp [viewElementsKey, codeField] at he,
          fun e he => by simp [viewElementsKey, viewLengthKey, codeField] at he⟩
      · simp [RefOk, SlotRole, familiesWorld, familiesEntries, hostEntries, codeField, arrayStoreKey,
          viewElementsKey]
    · simp only [codeRefs, refsArgs_eq, List.flatMap_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.nil_append] at hr
      exact hobj r hr
  have hbd : RefsOk (familiesWorld (k := k)) hostBound := by
    intro r hr
    rw [hostBound, refs_objAt] at hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [objRefs, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
      · exact ⟨fun m hm => by simp at hm, fun e he => by simp at he, fun e he => by simp at he⟩
    · simp only [codeRefs, refsArgs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · exact hclo r hr
      · exact hobj r hr
      · exact harr r hr
  intro x
  match x with
  | 0 => exact hview
  | 1 => exact harr
  | 2 => exact hobj
  | 3 => exact hcell
  | 4 => exact hpro
  | 5 => exact hclo
  | 6 => exact hbd
  | _ + 7 => exact RefsOk_undef

/-- **Non-vacuity of the kinded states for every structural family**: at
every budget, the families' heap meets the families' world, which is
admissible, and every family's value is valid in it, all at once: an
object's identity, a property and a prototype property (F), a binding cell
(C), an ordinary array's store and its element (S, E), a typed array's view
metadata and view store of its length, a closure's capture and code field,
and a forwarding descriptor's target, receiver and prefix. -/
theorem families_state (n : Nat) :
    HeapOk n (familiesWorld (k := n)) familiesHeap ∧ WorldAdm (familiesWorld (k := n)) ∧
      RootsOk (familiesWorld (k := n)) familiesEnv := by
  have hobj := RefsOk_mono familiesWorld_ext (host_refs (k := n)).2.2
  refine ⟨⟨entries_meets rfl fun i e v he hv j hj W => ?_, fun l r hr => ?_⟩, familiesWorld_adm, families_refs⟩
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [familiesEntries, hostEntries, familiesHeap, hostBefore] at he hv <;> subst he hv <;>
      simp [anyCtr, oneCtr, idCtr, isVal, hostObject]
  · simp only [familiesWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
      simp [familiesEntries, hostEntries] at hr <;> subst hr <;>
      refine ⟨_, rfl, ?_, ?_⟩ <;>
      first
        | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [familiesWorld, familiesEntries, hostEntries])
        | exact hobj
        | exact fun _ hm => by simp [refs] at hm
        | simp [Cat, isSourceVal, hostObject]


/-! ## The structural part of an initial world

A world and heap are built from the empty state by allocating declared
objects, one at a time: each declared object's fields with their storage
roles, field types and contents. The empty state is well-formed at every
budget (`empty_state`); allocating a declared object whose contents are of
their roles' categories and meet their field types, with valid references,
keeps the state well-formed and gives the object its record type
(`alloc_state`, the program's allocation rule `allocation_safe`). What
these do not construct is a callable's membership in its type: a field
holding native code meets a function type only by the host model. -/

/-- **The empty state is well-formed at every budget**, an environment of
scalars' roots valid. -/
theorem empty_state (n : Nat) :
    HeapOk n (ofEntries [] : WorldT n) [] ∧ WorldAdm (ofEntries [] : WorldT n) ∧
      RootsOk (ofEntries [] : WorldT n) (fun _ => .undef) := by
  refine ⟨⟨entries_meets rfl fun i e v he _ => by simp at he, fun l r hr => by simp at hr⟩,
    fun l c hc => by simp [lookup, toList] at hc, fun _ => RefsOk_undef⟩

open AllocationWorlds in
/-- **A declared object allocated from a well-formed state** (`allocation_safe`
at the allocation's own step): with its fields' roles `ss`, types `As` and
contents `vs`, each content of its role's category and its type, each role
fitting its key, the metadata keys fitting, and the contents' references
valid, the state after the allocation is well-formed at the successor
world, which extends the truncated one; the object is valid there and meets
its record type. -/
theorem alloc_state {Ξ : Fam} {ss : List StorageRole} {As : List Fam} (hss : ss.length = As.length)
    (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A) (p : Nat) (W : WorldT (p + 2)) (h : Heap)
    (ns : List PropKey) (vs : List Val) (hnd : ns.Nodup) (hns : ns.length = vs.length)
    (hAs : As.length = vs.length) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk (p + 2) W h)
    (hv : ∀ q ∈ As.zip vs, ∀ (j : Nat) (hj : j + 1 < p + 2), q.1 j (trunc j (by omega) W) q.2)
    (hhold : ∀ (i : Nat) (s : StorageRole) (v : Val), ss[i]? = some s → vs[i]? = some v → s.Holds v)
    (hfits : ∀ (i : Nat) (s : StorageRole), ss[i]? = some s → ∀ key : PropKey, ns[i]? = some key →
      s.fitsKey key = true)
    (hmeta : ∀ (k : Nat) (rs : List Role), concreteRoles ss vs = some rs →
      MetaFit ns rs (As.map (fun A => (res A : Ctr k))))
    (href : RefsOk W (.makeAt .absent ns vs)) :
    ∃ U : WorldT (p + 1), WExt (trunc (p + 1) (Nat.le_succ _) W) U ∧ WorldAdm U ∧
      HeapOk (p + 1) U (h ++ vs ++ [.nul]) ∧
      RefsOk U (.objAt (slots h.length ns) .absent (h.length + vs.length)) ∧
      recT (ns.zip (ss.zip As)) (p + 1) U (.objAt (slots h.length ns) .absent (h.length + vs.length)) := by
  have hs := allocation_safe (Ξ := Ξ) (Q := fun j U v => recT (ns.zip (ss.zip As)) j U v) hss hA hV
    (p + 2) W h .absent ns vs hnd hns hAs hvals hadm hok hv hhold hfits hmeta href (fun _ _ _ _ hr => hr)
  have hstep : Step h (.makeAt .absent ns vs) (h ++ vs ++ [.nul])
      (.objAt (slots h.length ns) .absent (h.length + vs.length)) := .makeFields hvals hns
  obtain ⟨-, hs⟩ := hs
  rcases hs with (⟨hval, -⟩ | ht) | ⟨U, h', t', hx, hu, hst, hh, -, hrest⟩
  · simp [isVal] at hval
  · exact absurd hstep ht.no_step
  · obtain ⟨rfl, rfl⟩ := Step_det hst hstep
    obtain ⟨hr, hrest⟩ := hrest
    refine ⟨U, hx, hu, hh, hr, ?_⟩
    rcases hrest with (⟨-, hq⟩ | ⟨_, hra, -⟩) | ⟨_, _, _, -, -, hst', -⟩
    · exact hq
    · have := raises_not_val hra; simp [isVal] at this
    · exact absurd hst' (value_no_step rfl)

end Verification.Kinds
