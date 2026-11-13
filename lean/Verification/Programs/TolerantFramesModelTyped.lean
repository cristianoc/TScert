import Verification.Programs.TolerantFramesWrites

/-! # Tolerant frames: the supports a typed environment gives

Three world facts the modality's atoms take as premises follow from a typed
environment (`ProgramTyping.EnvOk`):

- **allocated cells** (`StoreCells`): a slot whose type is a record whose
  store field has a type of one `.list` clause holds an object whose store
  location's contract meets a tuple contract (`storeCells_of_typed`); and an
  object of a record, dictionary or `source` clause owning the store key, in
  a graph stating the built-ins, meets the array invariant
  (`storeCells_of_builtins`);
- **stable paths** (`StableAt`): a field every clause of the slot's type
  states stable is read one way for the object's life
  (`stableAt_of_stableField`, the `stableFirst` evidence
  `stableAt_of_stableFirst`), and paths compose through a slot holding the
  intermediate value (`stableAt_cons`);
- **class evidence** (`ClassOk`): a field of source-value type holds a value,
  not a store (`valueClass_ok`), and a store field of a `.list` type holds a
  store (`storeClass_ok`), at every heap meeting the world. -/
namespace Verification.TolerantFrames
open Verification Footprints ProgramTyping PositiveGraphs PositiveRules PositiveNormalization
open ExpressionEffects HeapExpressionRules
open Verification.HeapKnowledge (ElementsBelow ElementsAbove RegionsApart)

variable {ι : Type}

/-! ## Allocated cells -/

/-- A type of one `.list` clause: an array store under tuple contracts. -/
def storeListTy (G : NormalGraph ι) (L : Ty ι) : Bool :=
  match expand G L with
  | [.list _ []] => true
  | _ => false

/-- Every alternative is a record whose first invariant operand has the
field `fld`, at a type `storeListTy` accepts in each. -/
def storeListField (G : NormalGraph ι) (cs : List (Clause (Ty ι))) (fld : PropKey) : Bool :=
  !cs.isEmpty && cs.all fun c => match clauseBagOperand c with
    | some B => B.any (fun p => decide (p.1 = fld)) && B.all (fun p => !decide (p.1 = fld) || storeListTy G p.2.2)
    | none => false

theorem storeListField_sound [DecidableEq ι] {G : NormalGraph ι} {Ref : Ty ι} {fld : PropKey} {n : Nat}
    {W : WorldT n} {v : Val}
    (hr : storeListField G (expand G Ref) fld = true) (hv : meaning G Ref n W v) :
    ∃ B s L, (fld, s, L) ∈ B ∧ storeListTy G L = true ∧
      bagT (ReferenceConjunctions.famsOf (meaning G) B) n W v := by
  simp only [storeListField, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at hr
  have hp : G.plainTy Ref = true := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hr.1
    exact plain_of_mem_expand (c := c) hc
  obtain ⟨c, hm, hc, -⟩ := (expand_sem G Ref hp n W v).mp hv
  have hb := hr.2 c hm
  cases c <;> simp only [clauseBagOperand] at hb
  all_goals try contradiction
  all_goals
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hb
    obtain ⟨hany, hall⟩ := hb
    obtain ⟨⟨g, s, El⟩, hmem, hg⟩ := List.any_eq_true.mp hany
    simp only [decide_eq_true_eq] at hg
    subst hg
    have hsrc : storeListTy G El = true := (hall _ hmem).resolve_left (by simp)
  · exact ⟨_, s, El, hmem, hsrc, recT_bag hc.1.1⟩
  · exact ⟨_, s, El, hmem, hsrc, hc.1.1.1.1⟩

/-- A member of a type of one `.list` clause is a store under a tuple
contract. -/
theorem storeListTy_listT {G : NormalGraph ι} {L : Ty ι} (hL : storeListTy G L = true) {n : Nat}
    {W : WorldT n} {u : Val} (hu : meaning G L n W u) : ∃ T, listT T n W u := by
  unfold storeListTy at hL
  split at hL
  · rename_i T hexp
    exact ⟨_, (represents_raw (show Represents G L (.list T []) from hexp) n W u hu).1⟩
  · cases hL

/-- The store field of a slot whose type `storeListField` accepts: the
object's field location, its contract agreeing with a type of one `.list`
clause. -/
theorem storeListField_at [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat}
    {W : WorldT n} {x : Nat} {Ref : Ty ι} (he : EnvOk G Γ ρ n W) (hx : Γ[x]? = some Ref)
    (hs : storeListField G (expand G Ref) arrayStoreKey = true) :
    ∃ (L : Ty ι) (st : Nat) (c : Ctr n), storeListTy G L = true ∧ storeOf (ρ x) = some st ∧
      lookup W st = some c ∧ ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ meaning G L j U u := by
  obtain ⟨B, _, L, hmem, hL, hbag⟩ := storeListField_sound hs (he.2 x Ref hx)
  obtain ⟨flds, code, oid, hv, -, hrec⟩ := hbag
  obtain ⟨flds1, fl, c, oid', hproj, hfd, hlookup, hagree⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨L, hmem, rfl⟩) hrec
  cases hproj
  refine ⟨L, fl, c, hL, by simp [storeOf, fieldsOf, hv, hfd], hlookup, hagree⟩

/-- **A typed slot's store lists only cells of its world**: where the slot's
type is a record whose store field's type is one `.list` clause, `cells(x)`
is a fact of the world, `StoreCells`. -/
theorem storeCells_of_typed [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {x : Nat} {Ref : Ty ι} (he : EnvOk G Γ ρ s.n s.W) (hx : Γ[x]? = some Ref)
    (hs : storeListField G (expand G Ref) arrayStoreKey = true) : StoreCells x ρ m s := by
  obtain ⟨L, st, c, hL, hst, hl, hagree⟩ := storeListField_at he hx hs
  exact storeCells_of_listT hst hl fun j hj U u hu => storeListTy_listT hL ((hagree j hj U u).mp hu)

/-- The element write's store check (`storeField`, `storeFieldEvery`) asks
at least what `storeListField` asks. -/
theorem storeListField_of_storeField {G : NormalGraph ι} {cs : List (Clause (Ty ι))} {fld : PropKey}
    {idx : Nat} {present : Bool} (h : storeField G cs fld idx present = true) : storeListField G cs fld = true := by
  unfold storeField at h
  unfold storeListField
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h.2 c hc
  split at this
  · rename_i B hB
    rw [hB]
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at this ⊢
    refine ⟨this.1, fun p hp => (this.2 p hp).imp id fun hp' => ?_⟩
    unfold ExpressionEffects.storeTy at hp'
    unfold storeListTy
    split at hp'
    · rename_i hexp; rw [hexp]
    · cases hp'
  · rename_i hB
    cases this

/-- **A slot every element write the pass checks writes has allocated cells.** -/
theorem storeCells_of_storeField [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {x : Nat} {Ref : Ty ι} {idx : Nat} {present : Bool} (he : EnvOk G Γ ρ s.n s.W)
    (hx : Γ[x]? = some Ref) (hs : storeField G (expand G Ref) arrayStoreKey idx present = true) :
    StoreCells x ρ m s :=
  storeCells_of_typed he hx (storeListField_of_storeField hs)

/-- **A built-in array has allocated cells**: in a graph stating the
built-ins, an object of a type whose every clause carries the array invariant
(a record, a dictionary, `source`), owning the store key. -/
theorem storeCells_of_builtins [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {x : Nat} {A : Ty ι} {r : ArrayBuiltins ι} {flds : List (PropKey × Nat)} {oid : Nat}
    (he : EnvOk G Γ ρ s.n s.W) (hx : Γ[x]? = some A) (hp : G.plainTy A = true) (hb : G.builtins = some r)
    (hall : ∀ c ∈ expand G A, c.carriesInvariant = true)
    (hv : ρ x = .objAt flds .absent oid) (hst : (flds.lookup CallArguments.arrayStoreField).isSome = true) :
    StoreCells x ρ m s := by
  obtain ⟨c, hc, hsem⟩ := (expand_sem G A hp s.n s.W (ρ x)).mp (he.2 x A hx)
  have hinv := hsem.2
  simp only [builtinInvariant, hb, hall c hc, if_true] at hinv
  exact storeCells_of_arrayInvariant hv hst hinv


/-- **(Apart, one-sided) for a typed root**: the allocated-cell premise of
`apart_grow_keep` discharged by `y`'s type. -/
theorem apart_grow_keep_typed [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {x y : Nat} {Ref : Ty ι} (he : EnvOk G Γ ρ s.n s.W) (hy : Γ[y]? = some Ref)
    (hs : storeListField G (expand G Ref) arrayStoreKey = true) (hap : ApartAt x y ρ m s) :
    Box (growOne x) (ApartAt x y) ρ m s := by
  obtain ⟨-, st, -, -, hst, -, -⟩ := storeListField_at he hy hs
  exact apart_grow_keep (by rw [hst]; rfl) hap (rootCells_of_storeCells (storeCells_of_typed he hy hs))

/-- Allocation separation for a typed root: a store allocated at or past `b`
(its location and cells) is apart from the store of a typed slot whose
location is below `b` and whose cells, allocated, are below the heap's
length `b`. -/
theorem alloc_apart_typed [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat}
    {s : IndexedHeap} {y : Nat} {Ref : Ty ι} {u : Val} {sx : Nat} {xs ys : List (Option Nat)} {sy : Nat}
    (he : EnvOk G Γ ρ s.n s.W) (hy : Γ[y]? = some Ref) (hs : storeListField G (expand G Ref) arrayStoreKey = true)
    (hx : storeOf u = some sx) (hxv : s.h[sx]? = some (.arr xs)) (hbx : s.h.length ≤ sx)
    (hax : ElementsAbove s.h.length xs) (hsy : storeOf (ρ y) = some sy) (hyv : s.h[sy]? = some (.arr ys)) :
    RegionsApart s.h u (ρ y) :=
  alloc_apart hx hxv hbx hax hsy hyv (List.getElem?_eq_some_iff.mp hyv).1
    (rootCells_of_storeCells (m := m) (storeCells_of_typed he hy hs) sy ys hsy hyv)

/-! ## Stable paths -/

/-- A present key whose location's contract admits one value, read at a
state: the one-field path from the slot is stable, reading what the heap
holds. -/
theorem stableAt_of_present {x : Nat} {f : String} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {flds : List (PropKey × Nat)} {oid : Nat} {v : Val}
    (hst : Verification.StableAt s.W flds (.str f)) (hx : ρ x = .objAt flds .absent oid)
    (hr : HeapKnowledge.readPath s.h (ρ x) [f] = some v) : StableAt x [f] v ρ m s := by
  unfold StableAt
  rw [hx] at hr ⊢
  unfold Verification.StableAt at hst
  cases hl : flds.lookup (.str f) with
  | none => simp [HeapKnowledge.readPath, hl] at hr
  | some l =>
    rw [hl] at hst
    obtain ⟨c, value, hc, hcs⟩ := hst
    have hval := s.stable_value hc hcs
    simp only [HeapKnowledge.readPath, hl, hval, Option.some.injEq] at hr
    subst hr
    exact .cons hl hc hcs .nil

/-- **A field every clause of the slot's type states stable is a stable
path** (`stableField`): the value the heap reads there is read in every state
an admissible transition reaches. -/
theorem stableAt_of_stableField {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {x : Nat} {A : Ty ι} {f : String} {v : Val} (he : EnvOk G Γ ρ s.n s.W) (hx : Γ[x]? = some A)
    (hs : stableField G A (.str f) = true) (hr : HeapKnowledge.readPath s.h (ρ x) [f] = some v) :
    StableAt x [f] v ρ m s := by
  obtain ⟨flds, oid, hv, hst⟩ := stableField_at hs (he.2 x A hx)
  exact stableAt_of_present hst hv hr

/-- The evidence the field rules check for a stable first field
(`stableFirst`: each clause states it stable, or is `null` or `undefined`)
gives the stable path wherever the field is read. -/
theorem stableAt_of_stableFirst {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {x : Nat} {f : String} {v : Val} (he : EnvOk G Γ ρ s.n s.W) (hs : stableFirst G Γ x f = true)
    (hr : HeapKnowledge.readPath s.h (ρ x) [f] = some v) : StableAt x [f] v ρ m s := by
  unfold stableFirst at hs
  split at hs
  · rename_i A hx
    rcases stableFieldPresent_at hs (he.2 x A hx) with hn | hn | ⟨flds, oid, hv, hst⟩
    · rw [hn] at hr; simp [HeapKnowledge.readPath] at hr
    · rw [hn] at hr; simp [HeapKnowledge.readPath] at hr
    · exact stableAt_of_present hst hv hr
  · cases hs

/-- **Stable paths compose through a slot holding the intermediate value.** -/
theorem stableAt_cons {x y : Nat} {f : String} {q : List String} {v : Val} {ρ : Env} {m : Nat}
    {s : IndexedHeap} (h₁ : StableAt x [f] (ρ y) ρ m s) (h₂ : StableAt y q v ρ m s) :
    StableAt x (f :: q) v ρ m s := by
  unfold StableAt at h₁ h₂ ⊢
  generalize ρ x = a at h₁ ⊢
  generalize ρ y = b at h₁ h₂
  cases h₁ with
  | cons hf hl hc hp => cases hp; exact .cons hf hl hc h₂

/-- (Grow) at a typed stable path: `y ≤ |x.f|` survives every action of
`{values: any, stores: grow}` where `f` is a field every clause of `x`'s type
states stable. -/
theorem grow_path_typed {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {m : Nat} {s : IndexedHeap}
    {x y : Nat} {A : Ty ι} {f : String} (he : EnvOk G Γ ρ s.n s.W) (hx : Γ[x]? = some A)
    (hs : stableField G A (.str f) = true) (hb : PathLowerBound y x [f] ρ m s) :
    Box growEffect.fp (PathLowerBound y x [f]) ρ m s := by
  obtain ⟨w, _, _, hw, -⟩ := id hb
  exact grow_path (stableAt_of_stableField he hx hs hw) hb

/-! ## Class evidence -/

/-- The evidence that `x`'s field `k` holds a value, not a store. -/
def valueClass (x : Nat) (k : PropKey) : ClassEvidence := fun y k' =>
  if y = x ∧ k' = k then some .value else none

/-- **A field of source-value type holds a value**: the class evidence a
footprint inclusion reads at that field holds at every heap meeting the
world, at positive budget. -/
theorem valueClass_ok [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {x : Nat} {Ref : Ty ι} {k : PropKey} (he : EnvOk G Γ ρ (n + 1) W)
    (hx : Γ[x]? = some Ref) (hs : sourceField G (expand G Ref) k = true) (hh : HeapOk (n + 1) W h) :
    ClassOk (valueClass x k) ρ h := by
  intro y k' c l hc hl _
  unfold valueClass at hc
  split at hc
  · rename_i hyk
    obtain ⟨rfl, rfl⟩ := hyk
    cases hc
    obtain ⟨B, _, A, hmem, hsrc, hbag⟩ := sourceField_sound hs (he.2 y Ref hx)
    obtain ⟨flds, code, oid, hv, -, hrec⟩ := hbag
    obtain ⟨flds1, fl, cc, oid', hproj, hfd, hlookup, hagree⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hmem, rfl⟩) hrec
    cases hproj
    rw [hv] at hl
    simp only [fieldsOf, hfd, Option.some.injEq] at hl
    subst hl
    obtain ⟨w, hw, hcw⟩ := hh.2 fl cc hlookup
    have hwsrc := sourceTy_sound hsrc ((hagree 0 (by omega) _ w).mp (hcw 0 (by omega)))
    simp only [Region.mem, hw, Cls.has]
    cases w <;> simp_all [isSourceVal, isArr]
  · cases hc

/-- **A store field of a `.list` type holds a store**: the store-class
evidence (`denseClass`) from typing, without a density fact. -/
theorem storeClass_ok [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {x : Nat} {Ref : Ty ι} (he : EnvOk G Γ ρ (n + 1) W)
    (hx : Γ[x]? = some Ref) (hs : storeListField G (expand G Ref) arrayStoreKey = true)
    (hh : HeapOk (n + 1) W h) : ClassOk (denseClass x) ρ h := by
  intro y k' c l hc hl _
  unfold denseClass at hc
  split at hc
  · rename_i hyk
    obtain ⟨rfl, rfl⟩ := hyk
    cases hc
    obtain ⟨L, st, cc, hL, hst, hlookup, hagree⟩ := storeListField_at he hx hs
    have hl' : st = l := by
      simp only [storeOf] at hst
      rw [hst] at hl
      exact Option.some.inj hl
    subst hl'
    obtain ⟨u, hu, hcu⟩ := hh.2 st cc hlookup
    obtain ⟨T, hT⟩ := storeListTy_listT hL ((hagree 0 (by omega) _ u).mp (hcu 0 (by omega)))
    obtain ⟨ls, rfl, -⟩ := hT
    simp [Region.mem, hu, Cls.has, isArr]
  · cases hc

/-- Antitonicity from typing: a footprint within another by the value-class
evidence of a typed field gives inclusion of actions from every state of the
typed environment. -/
theorem action_le_valueClass [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env}
    {s s' : IndexedHeap} {x : Nat} {Ref : Ty ι} {k : PropKey} {Φ Ψ : Footprint}
    (he : EnvOk G Γ ρ s.n s.W) (hx : Γ[x]? = some Ref) (hs : sourceField G (expand G Ref) k = true)
    (hle : Footprint.le (valueClass x k) Φ Ψ = true) (ha : Action Φ ρ s s') : Action Ψ ρ s s' := by
  obtain ⟨n, W, h, pos, adm, ok⟩ := s
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n => exact action_le hle (valueClass_ok he hx hs ok) ha

end Verification.TolerantFrames
