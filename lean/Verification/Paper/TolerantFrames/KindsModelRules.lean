import Verification.Paper.TolerantFrames.ModelRules
import Verification.Semantics.KindsNatives
import Verification.Semantics.AdmissibleCells
import Verification.Semantics.KindsCapabilities
import Verification.Semantics.ViewSpines
/-!
# Witnesses of (View), Alloc and the view write over kinded worlds

The rules of `Paper/TolerantFrames/ModelRules.lean` (`view_box`,
`alloc_post`) shown on concrete well-formed heaps:

- **Alloc**: the heap after an array's allocation is well-formed with the
  array valid (`alloc_wellformed`).

A view-element write (`ViewWrite`) between two concrete well-formed heaps
changes the view spines of two typed arrays over the written bytes, exact for
the designated one, and keeps an array's spine
(`viewWrite_overlap`).
-/
namespace Verification.Kinds
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints
open Verification.TolerantFrames (allocated oneBits oneBits_safe)

/-! ## Alloc -/

/-- **The allocation keeps the heap well-formed.** The rule gives the spine
slot the role of an array spine and the identity its own, with contracts
`c` that survives allocation and admits the empty spine, the identity's
admitting `null` alone (`idCtr`);
the allocated array's references are valid in the extended world. -/
theorem alloc_wellformed {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) (hadm : WorldAdm W)
    {c : Ctr n} (hc : CtrAdm c)
    (hcv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) (.arr [])) :
    HeapOk n (appendWs W (objectEntries [.spine .array] [c])) (h ++ [.arr []] ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries [.spine .array] [c])) (allocated h) := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  obtain ⟨hsh, href⟩ := arrayObject_shaped (ls := []) c hlen hok.2 (fun _ hr => by simp [refs, spineRefs] at hr)
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

/-- The roles of the entry heap: two view spines of format `uint8` and
length 1, their two element cells, an array's spine and its element
cell. -/
def overlapRoles : List Role :=
  [.spine (.view .uint8 1), .spine (.view .uint8 1), .elem, .elem, .spine .array, .elem]

/-- Two typed arrays over the same bytes (view spines at 0 and 1) and an
array (spine at 4). -/
def overlapBefore : Heap :=
  [.viewSpine .uint8 [2], .viewSpine .uint8 [3], .num 0, .num 0, .arr [some 5], .num 0]

/-- After a write of `oneBits` at index 0 through the first typed array: both
view spines list fresh cells holding the written value. -/
def overlapAfter : Heap :=
  [.viewSpine .uint8 [6], .viewSpine .uint8 [7], .num 0, .num 0, .arr [some 5], .num 0, .num oneBits,
    .num oneBits]

/-- The designated typed array: its descriptor names the view spine at 0. -/
def overlapView : Val := .viewAt [] 8 0 .uint8 1

theorem overlapBefore_ok (n : Nat) : HeapOk n (roleWorld overlapRoles) overlapBefore := by
  refine ⟨roleWorld_meets rfl (by simp [overlapBefore, isVal]), fun l r hr => ?_⟩
  rw [roleAt_roleWorld] at hr
  rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;> subst hr <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
      | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [overlapRoles])
      | (intro r hm; simp only [refs, List.mem_map] at hm; obtain ⟨c, hc, rfl⟩ := hm; simp at hc; subst hc; simp [RefOk, overlapRoles])
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
      | (intro r hm; simp only [refs, List.mem_map] at hm; obtain ⟨c, hc, rfl⟩ := hm; simp at hc; subst hc; simp [RefOk, overlapRoles])
      | exact fun _ hm => by simp [refs] at hm
      | simp [Cat, isSourceVal]

/-- `Uint8`'s conversion keeps the double `1`. -/
theorem conv_oneBits : ViewFormat.conv .uint8 oneBits = oneBits := by
  rw [ViewFormat.conv_safeInt oneBits_safe (fun lo hi he => by
    simp only [ViewFormat.range, Option.some.injEq, Prod.mk.injEq] at he; omega)]
  simp [int32Bits, oneBits]

/-- **The write of `1` at index 0 through a `Uint8Array` of length 1**
whose view spine at `s` lists the cell `c` before and the cell `c'`, holding
`1`, after: the exact write and the facts its precondition gives. -/
theorem exactWrite_one {i s c c' : Nat} {before after : Heap}
    (hb : before[s]? = some (.viewSpine .uint8 [c])) (ha : after[s]? = some (.viewSpine .uint8 [c']))
    (hc' : after[c']? = some (.num oneBits)) :
    CallEffects.ExactWrite .uint8 [.viewAt [] i s .uint8 1, .num 0, .num oneBits] before after ∧
      CallEffects.ExactPre .uint8 [.viewAt [] i s .uint8 1, .num 0, .num oneBits] := by
  have h0 : SafeIntegers.SafeInt (0 : UInt64) (0 : Int) := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
  refine ⟨fun x ib N hx hib hN => ?_, ⟨oneBits, 1, rfl, oneBits_safe, fun lo hi he => by
      simp [CallEffects.ElementKind.range] at he; omega⟩, 0, 0, 1, rfl, h0,
    by simp [HeapKnowledge.viewLengthOf], by decide⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero, Tm.num.injEq, CallEffects.viewLength,
    Option.some.injEq] at hx hib hN
  subst hx hib hN
  refine ⟨fun i0 hi0 hlt st ls hst hls => ?_, fun hinv => absurd (hinv 0 h0) (by omega)⟩
  obtain rfl : i0 = 0 := by omega
  rw [List.getD_cons_zero, HeapKnowledge.elementsOf_view (by rfl)] at hst
  cases hst
  rw [hb] at hls
  simp only [Option.bind_some, spineEntries, List.map_cons, List.map_nil, Option.some.injEq] at hls
  subst hls
  refine ⟨[some c'], by simp [ha, spineEntries], ⟨c', oneBits, rfl, hc', by
    show SameNumber _ (ViewFormat.conv .uint8 oneBits); rw [conv_oneBits]; exact .refl _⟩,
    fun j hj l u hl _ => ?_⟩
  rcases j with _ | j
  · exact absurd rfl hj
  · simp at hl

/-- **A view-element write changes two overlapping views' spines and keeps
an array's.** Between the two well-formed heaps, at every budget,
the exact write through the first view holds: both view spines (locations 0
and 1) change, the designated one at the written index alone, and the
array's spine (location 4) is kept. -/
theorem viewWrite_overlap (n : Nat) :
    HeapOk n (roleWorld overlapRoles) overlapBefore ∧
      ViewWriteOf (.exact .uint8) [overlapView, .num 0, .num oneBits] (roleWorld (k := n) overlapRoles)
        overlapBefore (roleWorld (k := n) (overlapRoles ++ [.elem, .elem])) overlapAfter ∧
      overlapAfter[0]? ≠ overlapBefore[0]? ∧ overlapAfter[1]? ≠ overlapBefore[1]? ∧
      roleAt (roleWorld (k := n) overlapRoles) 4 = some (.spine .array) ∧
      overlapAfter[4]? = overlapBefore[4]? := by
  refine ⟨overlapBefore_ok n, ⟨⟨Nat.le_refl n, by rw [trunc_id]; exact roleWorld_ext _ _,
    overlapAfter_ok n, fun l r hr hne => ?_, fun l f N cs cs' hr hl hl' c hc => ?_⟩, fun _ hk => ?_, fun hk => by cases hk⟩,
    by simp [overlapAfter, overlapBefore], by simp [overlapAfter, overlapBefore],
    by simp [overlapRoles], rfl⟩
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;> subst hr <;>
      first | rfl | exact absurd rfl (hne .uint8 1)
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [overlapRoles] at hr <;>
      simp [overlapAfter] at hl' <;> obtain ⟨-, rfl⟩ := hl' <;> simp at hc <;> subst hc <;>
      exact .inr (by simp [overlapBefore])
  · cases hk
    exact exactWrite_one (i := 8) (by rfl) (by rfl) (by rfl)


/-! ## A representative initial host world

A world with every role a builtin heap holds: a typed array (its view spine
of format `uint8` and length 1, its element cell and its identity), an
array (its spine, its element cell, its identity) and an object (a
property and its identity). The heap meets it at every budget with all three
objects valid, and the exact view-element write through the typed array
inhabits the contract (`ViewWriteOf`) from it, keeping the array's
spine and every other location. -/

/-- The roles and contracts of the initial host world, by location. -/
def hostEntries {k : Nat} : List (Role × Ctr k) :=
  [(.spine (.view .uint8 1), viewSpineCtr k .uint8 1), (.elem, viewCellCtr k .uint8), (.identity, idCtr),
   (.spine .array, anyCtr), (.elem, anyCtr), (.identity, idCtr), (.field "p", anyCtr), (.identity, idCtr)]

def hostWorld {k : Nat} : WorldT k := ofEntries hostEntries

/-- The world after the write: the fresh element cell appended. -/
def hostWorld' {k : Nat} : WorldT k := ofEntries (hostEntries ++ [(.elem, viewCellCtr k .uint8)])

def hostBefore : Heap :=
  [.viewSpine .uint8 [1], .num 0, .nul, .arr [some 4], .num 0, .nul, .str "x", .nul]

/-- After writing `1` at index 0 through the typed array: its view spine
lists a fresh cell holding the value. -/
def hostAfter : Heap :=
  [.viewSpine .uint8 [8], .num 0, .nul, .arr [some 4], .num 0, .nul, .str "x", .nul, .num oneBits]

/-- The typed array: its descriptor names its view spine at 0, its format
and its length 1. -/
def hostView : Val := .viewAt [] 2 0 .uint8 1
/-- The array. -/
def hostArray : Val := .objAt [(arraySpineKey, 3)] .absent 5
/-- The object with one property. -/
def hostObject : Val := .objAt [("p", 6)] .absent 7

theorem entries_meets {k : Nat} {es : List (Role × Ctr k)} {h : Heap} (hl : h.length = es.length)
    (hv : ∀ (i : Nat) (e : Role × Ctr k) (v : Val), es[i]? = some e → h[i]? = some v →
      ∀ (j : Nat) (hj : j < k) (W : WorldT j), e.2 j hj W v) : HeapMeets k (ofEntries es) h := by
  refine ⟨by simp [toList, hl], fun l c hc => ?_⟩
  simp only [lookup, toList, entries_ofEntries, List.getElem?_map, Option.map_eq_some_iff] at hc
  obtain ⟨e, he, rfl⟩ := hc
  have hlt : l < h.length := by have := (List.getElem?_eq_some_iff.mp he).1; omega
  exact ⟨h[l], List.getElem?_eq_getElem hlt, fun j hj => hv l e _ he (List.getElem?_eq_getElem hlt) j hj _⟩

/-- A heap meets a world given by its entries where each location's
contents meet its entry's contract at every lower level, at the world
truncated there. -/
theorem entries_meets' {k : Nat} {es : List (Role × Ctr k)} {h : Heap} (hl : h.length = es.length)
    (hv : ∀ (i : Nat) (e : Role × Ctr k) (v : Val), es[i]? = some e → h[i]? = some v →
      ∀ (j : Nat) (hj : j < k), e.2 j hj (trunc j (Nat.le_of_lt hj) (ofEntries es)) v) :
    HeapMeets k (ofEntries es) h := by
  refine ⟨by simp [toList, hl], fun l c hc => ?_⟩
  simp only [lookup, toList, entries_ofEntries, List.getElem?_map, Option.map_eq_some_iff] at hc
  obtain ⟨e, he, rfl⟩ := hc
  have hlt : l < h.length := by have := (List.getElem?_eq_some_iff.mp he).1; omega
  exact ⟨h[l], List.getElem?_eq_getElem hlt, fun j hj => hv l e _ he (List.getElem?_eq_getElem hlt) j hj⟩

theorem stored_uint8_zero : ViewFormat.Stored .uint8 (.num 0) :=
  ⟨0, rfl, fun lo hi he => ⟨0, ⟨by decide, .inl ⟨by decide, rfl⟩⟩, by
    simp only [ViewFormat.range, Option.some.injEq, Prod.mk.injEq] at he; omega⟩⟩

theorem stored_uint8_one : ViewFormat.Stored .uint8 (.num oneBits) :=
  ⟨oneBits, rfl, fun lo hi he => ⟨1, oneBits_safe, by
    simp only [ViewFormat.range, Option.some.injEq, Prod.mk.injEq] at he; omega⟩⟩

/-- **A `Uint8Array` view spine of length 1 meets its canonical contract**
where its cell's entry is a cell of the format. -/
theorem viewSpine_one {k j : Nat} (hj : j < k) {es : List (Role × Ctr k)} {c : Nat}
    (he : es[c]? = some (.elem, viewCellCtr k .uint8)) :
    viewSpineCtr k .uint8 1 j hj (trunc j (Nat.le_of_lt hj) (ofEntries es)) (.viewSpine .uint8 [c]) := by
  refine ⟨[c], rfl, rfl, fun c' hc => ?_⟩
  simp only [List.mem_singleton] at hc; subst hc
  have hl : lookup (ofEntries es) c' = some (viewCellCtr k .uint8) := by simp [lookup, toList, he]
  exact ⟨by simp [roleAt, roles, he, restrictE], _, lookup_trunc _ _ c' _ hl, fun _ _ _ _ => Iff.rfl⟩

@[simp] theorem roleAt_ofEntries {k : Nat} (es : List (Role × Ctr k)) (l : Nat) :
    roleAt (ofEntries es) l = (es.map Prod.fst)[l]? := by
  simp [roleAt, roles]

theorem hostBefore_ok (n : Nat) : HeapOk n (hostWorld (k := n)) hostBefore := by
  refine ⟨entries_meets' rfl fun i e v he hv j hj => ?_, fun l r hr => ?_⟩
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [hostEntries, hostBefore] at he hv <;> subst he hv <;>
      first
        | exact viewSpine_one hj (es := hostEntries (k := n)) (c := 1) rfl
        | exact stored_uint8_zero
        | simp [anyCtr, idCtr, isVal]
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      refine ⟨_, rfl, ?_, ?_⟩ <;>
      first
        | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [hostWorld, hostEntries])
        | (intro r hm; simp only [refs, List.mem_map] at hm; obtain ⟨c, hc, rfl⟩ := hm; simp at hc; subst hc; simp [RefOk, hostWorld, hostEntries])
        | exact fun _ hm => by simp [refs] at hm
        | simp [Cat, isSourceVal]

theorem hostAfter_ok (n : Nat) : HeapOk n (hostWorld' (k := n)) hostAfter := by
  refine ⟨entries_meets' rfl fun i e v he hv j hj => ?_, fun l r hr => ?_⟩
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [hostEntries, hostAfter] at he hv <;> subst he hv <;>
      first
        | exact viewSpine_one hj (es := hostEntries (k := n) ++ [(.elem, viewCellCtr n .uint8)]) (c := 8) rfl
        | exact stored_uint8_zero
        | exact stored_uint8_one
        | simp [anyCtr, idCtr, isVal]
  · simp only [hostWorld', roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      refine ⟨_, rfl, ?_, ?_⟩ <;>
      first
        | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [hostWorld', hostEntries])
        | (intro r hm; simp only [refs, List.mem_map] at hm; obtain ⟨c, hc, rfl⟩ := hm; simp at hc; subst hc; simp [RefOk, hostWorld', hostEntries])
        | exact fun _ hm => by simp [refs] at hm
        | simp [Cat, isSourceVal]

/-- **The three host objects are valid in the initial host world**: the
typed array's identity is in I and its descriptor names a view spine of its
format and length (`Ref.view`); the array's spine slot an array's
spine; the object's property in F. -/
theorem host_refs {k : Nat} :
    RefsOk (hostWorld (k := k)) hostView ∧ RefsOk (hostWorld (k := k)) hostArray ∧
      RefsOk (hostWorld (k := k)) hostObject := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · simp only [hostView, refs, objRefs, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · simp [RefOk, hostWorld, hostEntries]
  · simp only [hostArray, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · simp [RefOk, SlotRole, hostWorld, hostEntries]
  · simp only [hostObject, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · simp [RefOk, hostWorld, hostEntries]
    · simp [RefOk, SlotRole, hostWorld, hostEntries, arraySpineKey]

/-- **The view-element write is inhabited from the initial host world**: at
every budget the exact write of `1` at index 0 through the typed array is a
`ViewWriteOf` transition between the two well-formed heaps, changing the view
spine and keeping the array's spine. -/
theorem host_viewWrite (n : Nat) :
    ViewWriteOf (.exact .uint8) [hostView, .num 0, .num oneBits] (hostWorld (k := n)) hostBefore
      (hostWorld' (k := n)) hostAfter ∧ hostAfter[0]? ≠ hostBefore[0]? ∧ hostAfter[3]? = hostBefore[3]? := by
  refine ⟨⟨⟨Nat.le_refl n, by rw [trunc_id]; exact ⟨[(.elem, viewCellCtr n .uint8)], by simp [hostWorld, hostWorld']⟩,
    hostAfter_ok n, fun l r hr hne => ?_, fun l f N cs cs' hr hl hl' c hc => ?_⟩, fun _ hk => ?_, fun hk => by cases hk⟩,
    by simp [hostAfter, hostBefore], rfl⟩
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;> subst hr <;>
      first | rfl | exact absurd rfl (hne .uint8 1)
  · simp only [hostWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | l <;> simp [hostEntries] at hr <;>
      simp [hostAfter] at hl' <;> obtain ⟨-, rfl⟩ := hl' <;> simp at hc <;> subst hc <;>
      exact .inr (by simp [hostBefore])
  · cases hk
    exact exactWrite_one (i := 2) (by rfl) (by rfl) (by rfl)

/-! ## Every structural family at once, at every budget -/

/-- The host world extended by a binding cell, an object's prototype
property, a closure's code field and a forwarding descriptor's identity. -/
def familiesEntries {k : Nat} : List (Role × Ctr k) :=
  hostEntries ++ [(.cell valueField, anyCtr), (.identity, idCtr), (.field CallArguments.protoField, anyCtr),
    (.identity, idCtr), (.field codeField, anyCtr), (.identity, idCtr), (.identity, idCtr)]

def familiesWorld {k : Nat} : WorldT k := ofEntries familiesEntries

def familiesHeap : Heap := hostBefore ++ [.num 0, .nul, hostObject, .nul, .nul, .nul, .nul]

/-- A binding's cell holding a number. -/
def hostCell : Val := .objAt [(valueField, 8)] .absent 9
/-- An object whose prototype is `hostObject`. -/
def hostProtoed : Val := .objAt [(CallArguments.protoField, 10)] .absent 11
/-- Graph code capturing `hostObject`, with its code field. -/
def hostClosure : Val := .objAt [(codeField, 12)] (.graph 0 [] [] 0 [hostObject] .call false none) 13
/-- A forwarding descriptor of the closure, its receiver `hostObject`, its
prefix the array. -/
def hostBound : Val := .objAt [] (.bound hostClosure hostObject [hostArray]) 14

/-- The environment binding every structural family of host value. -/
def familiesEnv : Env := fun i =>
  match i with
  | 0 => hostView | 1 => hostArray | 2 => hostObject | 3 => hostCell | 4 => hostProtoed
  | 5 => hostClosure | 6 => hostBound | _ => .undef

theorem familiesWorld_adm {k : Nat} : WorldAdm (familiesWorld (k := k)) := by
  refine ⟨fun l c hc => ?_, fun l f N hr => ?_⟩
  · simp only [lookup, toList, familiesWorld, entries_ofEntries, List.getElem?_map, Option.map_eq_some_iff] at hc
    obtain ⟨e, he, rfl⟩ := hc
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
      simp [familiesEntries, hostEntries] at he <;> subst he <;>
      first
        | exact viewSpineCtr_adm k .uint8 1
        | exact viewCellCtr_adm k .uint8
        | exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩
        | exact idCtr_adm
        | exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => by rw [hv]; rfl⟩
  · simp only [familiesWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
      simp [familiesEntries, hostEntries] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨_, by simp [lookup, toList, familiesWorld, familiesEntries, hostEntries], fun _ _ _ _ => Iff.rfl⟩

theorem familiesWorld_ext {k : Nat} : WExt (hostWorld (k := k)) (familiesWorld (k := k)) :=
  ⟨[(.cell valueField, anyCtr), (.identity, idCtr), (.field CallArguments.protoField, anyCtr), (.identity, idCtr),
    (.field codeField, anyCtr), (.identity, idCtr), (.identity, idCtr)], by simp [hostWorld, familiesWorld, familiesEntries]⟩

/-- **Every family's value is valid in the families' world**: a typed array
with its view spine of its format and length, an array with its spine and
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
    rcases hr with rfl | rfl
    · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
    · simp [RefOk, SlotRole, familiesWorld, familiesEntries, hostEntries, valueField, arraySpineKey]
  have hpro : RefsOk (familiesWorld (k := k)) hostProtoed := by
    intro r hr
    simp only [hostProtoed, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
    · simp [RefOk, SlotRole, familiesWorld, familiesEntries, hostEntries, CallArguments.protoField,
        arraySpineKey]
  have hclo : RefsOk (familiesWorld (k := k)) hostClosure := by
    intro r hr
    rw [hostClosure, refs_objAt] at hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp [RefOk, familiesWorld, familiesEntries, hostEntries]
      · simp [RefOk, SlotRole, familiesWorld, familiesEntries, hostEntries, codeField, arraySpineKey]
    · simp only [codeRefs, refsArgs_eq, List.flatMap_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.nil_append] at hr
      exact hobj r hr
  have hbd : RefsOk (familiesWorld (k := k)) hostBound := by
    intro r hr
    rw [hostBound, refs_objAt] at hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [objRefs, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [RefOk, familiesWorld, familiesEntries, hostEntries]
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
(C), an array's spine and its element (S, E), a typed array's view
spine of its format and length, a closure's capture and code field,
and a forwarding descriptor's target, receiver and prefix. -/
theorem families_state (n : Nat) :
    HeapOk n (familiesWorld (k := n)) familiesHeap ∧ WorldAdm (familiesWorld (k := n)) ∧
      RootsOk (familiesWorld (k := n)) familiesEnv := by
  have hobj := RefsOk_mono familiesWorld_ext (host_refs (k := n)).2.2
  refine ⟨⟨entries_meets' rfl fun i e v he hv j hj => ?_, fun l r hr => ?_⟩, familiesWorld_adm, families_refs⟩
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [familiesEntries, hostEntries, familiesHeap, hostBefore] at he hv <;> subst he hv <;>
      first
        | exact viewSpine_one hj (es := familiesEntries (k := n)) (c := 1) rfl
        | exact stored_uint8_zero
        | simp [anyCtr, idCtr, isVal, hostObject]
  · simp only [familiesWorld, roleAt_ofEntries] at hr
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
      simp [familiesEntries, hostEntries] at hr <;> subst hr <;>
      refine ⟨_, rfl, ?_, ?_⟩ <;>
      first
        | exact RefsOk_arr_iff.mpr (fun c hc => by simp at hc; subst hc; simp [familiesWorld, familiesEntries, hostEntries])
        | exact hobj
        | (intro r hm; simp only [refs, List.mem_map] at hm; obtain ⟨c, hc, rfl⟩ := hm; simp at hc; subst hc; simp [RefOk, familiesWorld, familiesEntries, hostEntries])
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
    ⟨fun l c hc => by simp [lookup, toList] at hc, fun l f N hr => by simp at hr⟩, fun _ => RefsOk_undef⟩

open AllocationWorlds in
/-- **A declared object allocated from a well-formed state** (`allocation_safe`
at the allocation's own step): with its fields' roles `ss`, types `As` and
contents `vs`, each content of its role's category and its type, each role
fitting its key, and the contents' references
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
    (href : RefsOk W (.makeAt .absent ns vs)) :
    ∃ U : WorldT (p + 1), WExt (trunc (p + 1) (Nat.le_succ _) W) U ∧ WorldAdm U ∧
      HeapOk (p + 1) U (h ++ vs ++ [.nul]) ∧
      RefsOk U (.objAt (slots h.length ns) .absent (h.length + vs.length)) ∧
      recT (ns.zip (ss.zip As)) (p + 1) U (.objAt (slots h.length ns) .absent (h.length + vs.length)) := by
  have hs := allocation_safe (Ξ := Ξ) (Q := fun j U v => recT (ns.zip (ss.zip As)) j U v) hss hA hV
    (p + 2) W h .absent ns vs hnd hns hAs hvals hadm hok hv hhold hfits href (fun _ _ _ _ hr => hr)
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
