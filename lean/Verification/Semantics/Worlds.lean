import Verification.Semantics.Calculus
/-!
# Stratified worlds

A **world** says what each location is *for*: it assigns a contract to each
location. A contract must be able to judge values against worlds, so worlds and
contracts are mutually dependent. The circularity is broken by stratifying on a
level:

    World k = Loc → (contracts that inspect worlds at any level < k)

which is one well-founded recursion. `WorldT k` does not reduce definitionally,
so `toList`/`ofList` mediate; both round-trips are immediate.

The encoding choice that matters is that a contract is **uniform in the level**
-- it accepts any `j < k` -- rather than pinned to one level. Truncating a world
to a lower level is then only a weakening of the bound each contract accepts, so
the coherence laws are equalities and no embedding in the opposite direction is
needed. That reverse embedding is what sinks the naive `World (n+1) = List
(World n → Val → Prop)` encoding. Truncation still discards *access* to
higher-level observations, which is its purpose; what is cheap is the operation,
not the approximation.

Not every contract is a type. `CtrAdm` requires a contract to survive the world
growing, and `WorldAdm` lifts that to a world.
-/
namespace Verification

/-- A world at level `k` maps each location to a contract that may inspect
worlds at any strictly lower level. -/
def WorldT : Nat → Type
  | k => List ((j : Nat) → j < k → WorldT j → Val → Prop)
termination_by k => k
decreasing_by omega

theorem WorldT_eq (k : Nat) :
    WorldT k = List ((j : Nat) → j < k → WorldT j → Val → Prop) := by
  rw [WorldT.eq_def]

/-- A contract at level `k`: inspects worlds at any strictly lower level. -/
abbrev Ctr (k : Nat) := (j : Nat) → j < k → WorldT j → Val → Prop

/-- A stable contract admits the same single value at every level and world.
It may admit no value at some levels or worlds. -/
def CtrStable {k : Nat} (c : Ctr k) (v : Val) : Prop :=
  ∀ j hj U u, c j hj U u → u = v

theorem CtrStable.restrict {k j : Nat} {c : Ctr k} {v : Val}
    (hc : CtrStable c v) (h : j ≤ k) :
    CtrStable (fun i hi U u => c i (Nat.lt_of_lt_of_le hi h) U u) v := by
  intro i hi U u hu
  exact hc i (Nat.lt_of_lt_of_le hi h) U u hu

def toList {k : Nat} (W : WorldT k) : List (Ctr k) := cast (WorldT_eq k) W

def ofList {k : Nat} (cs : List (Ctr k)) : WorldT k := cast (WorldT_eq k).symm cs

@[simp] theorem toList_ofList {k} (cs : List (Ctr k)) : toList (ofList cs) = cs := by
  simp [toList, ofList]

@[simp] theorem ofList_toList {k} (W : WorldT k) : ofList (toList W) = W := by
  simp [toList, ofList]

/-- **Truncation is free.** Restricting a level-`k` world to level `j ≤ k` only
weakens the bound each contract accepts; nothing is approximated away. -/
def trunc {k : Nat} (j : Nat) (h : j ≤ k) (W : WorldT k) : WorldT j :=
  ofList ((toList W).map (fun c i hi w => c i (Nat.lt_of_lt_of_le hi h) w))

/-- Extension: a future world keeps every existing contract. -/
def WExt {k : Nat} (W W' : WorldT k) : Prop :=
  ∃ tail, toList W' = toList W ++ tail

theorem WExt_refl {k} (W : WorldT k) : WExt W W := ⟨[], by simp⟩

theorem WExt_trans {k} {W V U : WorldT k} (h : WExt W V) (h' : WExt V U) : WExt W U := by
  obtain ⟨a, ha⟩ := h; obtain ⟨b, hb⟩ := h'
  exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

/-- Lookup. -/
def lookup {k : Nat} (W : WorldT k) (l : Nat) : Option (Ctr k) := (toList W)[l]?

/-- Truncation commutes with lookup, which is what any proof will need. -/
theorem lookup_trunc {k j : Nat} (h : j ≤ k) (W : WorldT k) (l : Nat) (c : Ctr k)
    (hl : lookup W l = some c) :
    lookup (trunc j h W) l = some (fun i hi w => c i (Nat.lt_of_lt_of_le hi h) w) := by
  simp only [lookup, trunc, toList_ofList, List.getElem?_map]
  simp only [lookup] at hl
  rw [hl]
  rfl

theorem lookup_trunc_inv {k j : Nat} (h : j ≤ k) (W : WorldT k) (l : Nat) (c' : Ctr j)
    (hl : lookup (trunc j h W) l = some c') :
    ∃ c, lookup W l = some c ∧ c' = fun i hi w => c i (Nat.lt_of_lt_of_le hi h) w := by
  simp only [lookup, trunc, toList_ofList, List.getElem?_map] at hl
  rcases hd : (toList W)[l]? with _ | c
  · rw [hd] at hl; simp at hl
  · rw [hd] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    exact ⟨c, by simpa [lookup] using hd, hl.symm⟩

theorem WExt_lookup {k : Nat} {W W' : WorldT k} (hx : WExt W W') {l : Nat} {c : Ctr k}
    (hl : lookup W l = some c) : lookup W' l = some c := by
  obtain ⟨tail, ht⟩ := hx
  simp only [lookup] at hl ⊢
  rw [ht]
  have := (List.getElem?_eq_some_iff.mp hl).1
  simpa [List.getElem?_append, this] using hl

/-! ## Coherence

Truncation is an identity at the same level, composes, and preserves
extension. -/


theorem trunc_id {k : Nat} (h : k ≤ k) (W : WorldT k) : trunc k h W = W := by
  simp only [trunc]
  have : (fun (c : Ctr k) (i : Nat) (hi : i < k) (w : WorldT i) =>
      c i (Nat.lt_of_lt_of_le hi h) w) = id := by funext c; rfl
  rw [this, List.map_id, ofList_toList]

theorem trunc_trunc {k j i : Nat} (h1 : i ≤ j) (h2 : j ≤ k) (W : WorldT k) :
    trunc i h1 (trunc j h2 W) = trunc i (Nat.le_trans h1 h2) W := by
  simp only [trunc, toList_ofList, List.map_map]
  rfl

theorem WExt_trunc {k j : Nat} (h : j ≤ k) {W W' : WorldT k} (hx : WExt W W') :
    WExt (trunc j h W) (trunc j h W') := by
  obtain ⟨tail, ht⟩ := hx
  refine ⟨tail.map (fun c i hi w => c i (Nat.lt_of_lt_of_le hi h) w), ?_⟩
  simp only [trunc, toList_ofList, ht, List.map_append]

/-! ## Allocation extends a world -/


/-- Allocation appends a contract. -/
def appendW {k : Nat} (W : WorldT k) (c : Ctr k) : WorldT k := ofList (toList W ++ [c])

theorem WExt_appendW {k : Nat} (W : WorldT k) (c : Ctr k) : WExt W (appendW W c) :=
  ⟨[c], by simp [appendW]⟩

/-- One allocation appends one contract per named field, in order. -/
def appendWs {k : Nat} (W : WorldT k) (cs : List (Ctr k)) : WorldT k :=
  ofList (toList W ++ cs)

@[simp] theorem appendWs_nil {k : Nat} (W : WorldT k) : appendWs W [] = W := by
  simp [appendWs]

theorem appendWs_cons {k : Nat} (W : WorldT k) (c : Ctr k) (cs : List (Ctr k)) :
    appendWs W (c :: cs) = appendWs (appendW W c) cs := by
  simp [appendWs, appendW]

theorem WExt_appendWs {k : Nat} (W : WorldT k) (cs : List (Ctr k)) : WExt W (appendWs W cs) :=
  ⟨cs, by simp [appendWs]⟩

theorem lookup_appendWs {k : Nat} (W : WorldT k) (cs : List (Ctr k)) {i : Nat}
    (_hi : i < cs.length) :
    lookup (appendWs W cs) ((toList W).length + i) = cs[i]? := by
  simp only [lookup, appendWs, toList_ofList]
  rw [List.getElem?_append_right (by omega)]
  simp

/-! ## Which contracts are types -/


/-- Only worlds whose contracts are themselves stable under allocation can
carry a heap: preserving the contents obligation across an allocation is a
property of the contracts. A contract admits only values, so a
location of a heap that meets its world holds a value. -/
def CtrAdm {k : Nat} (c : Ctr k) : Prop :=
  (∀ (j : Nat) (hj : j < k) (W W' : WorldT j), WExt W W' → ∀ v, c j hj W v → c j hj W' v) ∧
    ∀ (j : Nat) (hj : j < k) (W : WorldT j) v, c j hj W v → isVal v = true

def WorldAdm {k : Nat} (W : WorldT k) : Prop := ∀ l c, lookup W l = some c → CtrAdm c

theorem WorldAdm_trunc {k j : Nat} (h : j ≤ k) {W : WorldT k} (hA : WorldAdm W) :
    WorldAdm (trunc j h W) := by
  intro l c' hl
  obtain ⟨c, hc, rfl⟩ := lookup_trunc_inv h W l c' hl
  exact ⟨fun i hi U U' hx v hv => (hA l c hc).1 i (Nat.lt_of_lt_of_le hi h) U U' hx v hv,
    fun i hi U v hv => (hA l c hc).2 i (Nat.lt_of_lt_of_le hi h) U v hv⟩

theorem WorldAdm_append {k : Nat} {W : WorldT k} {c : Ctr k}
    (hW : WorldAdm W) (hc : CtrAdm c) : WorldAdm (appendW W c) := by
  intro l d hl
  simp only [lookup, appendW, toList_ofList] at hl
  by_cases hlt : l < (toList W).length
  · rw [List.getElem?_append_left hlt] at hl
    exact hW l d (by simpa [lookup] using hl)
  · have hb : l < (toList W).length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hl).1; simpa using this
    have : l = (toList W).length := by omega
    subst this
    rw [List.getElem?_append_right (Nat.le_refl _)] at hl
    simp at hl
    subst hl
    exact hc

theorem WorldAdm_appendWs {k : Nat} {W : WorldT k} {cs : List (Ctr k)}
    (hW : WorldAdm W) (hc : ∀ c ∈ cs, CtrAdm c) : WorldAdm (appendWs W cs) := by
  induction cs generalizing W with
  | nil => simpa using hW
  | cons c cs ih =>
    rw [appendWs_cons]
    exact ih (WorldAdm_append hW (hc c (by simp))) (fun d hd => hc d (by simp [hd]))

end Verification
