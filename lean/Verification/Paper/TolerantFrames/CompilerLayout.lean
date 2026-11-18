import Verification.Paper.TolerantFrames.OperationCode
import Verification.Programs.GraphCode
import Verification.Paper.TolerantFrames.Admission

/-! # Finite named frames in shared graph environments

Existing envMap/push/instantiate provide the representation. Source names,
host code and the exit payload have distinct slots. Total unused B names
retain their original environment, independent of graph default changes.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification PointClaims

/-- Source names occupy [0,bound), then three host slots and an exit payload. -/
def width (bound : Nat) : Nat := bound + 4

def hostTemplate (bound : Nat) : NativeCode :=
  ⟨.var bound, .var (bound + 1), .var (bound + 2)⟩

def slotValue (bound : Nat) (ρ : Env) (host : NativeCode) (payload : Tm) (i : Nat) : Tm :=
  if i < bound then ρ i
  else if i = bound then host.viewRead
  else if i = bound + 1 then host.viewWrite
  else if i = bound + 2 then host.viewLength else payload

def slots (bound : Nat) (ρ : Env) (host : NativeCode) (payload : Tm) : List Tm :=
  (List.range (width bound)).map (slotValue bound ρ host payload)

theorem slots_length (bound : Nat) (ρ : Env) (host : NativeCode) (payload : Tm) :
    (slots bound ρ host payload).length = width bound := by simp [slots]

theorem slots_get {bound ρ host payload i d} (hi : i < width bound) :
    envOf (slots bound ρ host payload) d i = slotValue bound ρ host payload i := by
  simp [envOf, slots, List.getD_eq_getElem?_getD, hi]

theorem slots_named {bound ρ host payload i d} (hi : i < bound) :
    envOf (slots bound ρ host payload) d i = ρ i := by
  rw [slots_get (by unfold width; omega)]
  simp [slotValue, hi]

theorem slots_host (bound : Nat) (ρ : Env) (host : NativeCode) (payload d : Tm) :
    (hostTemplate bound).close (envOf (slots bound ρ host payload) d) = host := by
  cases host
  simp only [hostTemplate, NativeCode.close, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  congr 1 <;> rw [slots_get (by unfold width; omega)] <;> simp [slotValue] <;> omega

def replaceMap (w x : Nat) : Mapping :=
  some ((List.range w).map fun i => if i = x then 0 else i + 1)

def dropMap (w : Nat) : Mapping := some ((List.range w).map (· + 1))

theorem slot_replace {w x i} (hi : i < w) :
    PointClaims.slot (replaceMap w x) i = if i = x then 0 else i + 1 := by
  simp [PointClaims.slot, replaceMap, hi]

theorem slot_drop {w i} (hi : i < w) : PointClaims.slot (dropMap w) i = i + 1 := by
  simp [PointClaims.slot, dropMap, hi]

theorem mapped_replace {w x i} (hi : i < w) (ρ : Env) (v : Tm) :
    mapEnv (replaceMap w x) (push v ρ) i = bindName ρ x v i := by
  rw [mapEnv, slot_replace hi]
  by_cases he : i = x <;> simp [he, push, bindName]

theorem mapped_drop {w i} (hi : i < w) (ρ : Env) (v : Tm) :
    mapEnv (dropMap w) (push v ρ) i = ρ i := by
  rw [mapEnv, slot_drop hi]
  rfl

theorem envMap_replace {w x i L d v} (hi : i < w) :
    envOf (envMap (replaceMap w x) (v :: L) d).1
      (envMap (replaceMap w x) (v :: L) d).2 i = bindName (envOf L d) x v i := by
  rw [← GraphCode.mapEnv_envOf, ← GraphCode.push_envOf]
  exact mapped_replace hi _ _

theorem envMap_drop {w i L d v} (hi : i < w) :
    envOf (envMap (dropMap w) (v :: L) d).1
      (envMap (dropMap w) (v :: L) d).2 i = envOf L d i := by
  rw [← GraphCode.mapEnv_envOf, ← GraphCode.push_envOf]
  exact mapped_drop hi _ _

/-- The graph's default may change on an edge. Only finite source slots are
read from it; total unused named values retain the original B environment. -/
def restore (bound : Nat) (outer graph : Env) : Env := fun i =>
  if i < bound then graph i else outer i

theorem restore_slots (bound : Nat) (ρ : Env) (host : NativeCode) (payload d : Tm) :
    restore bound ρ (envOf (slots bound ρ host payload) d) = ρ := by
  funext i
  by_cases hi : i < bound
  · simp [restore, hi, slots_named hi]
  · simp [restore, hi]

theorem restore_replace {bound x} (hx : x < bound) (outer graph : Env) (v : Tm) :
    restore bound outer (mapEnv (replaceMap (width bound) x) (push v graph)) =
      bindName (restore bound outer graph) x v := by
  funext i
  by_cases hi : i < bound
  · simp only [restore, hi, ↓reduceIte]
    rw [mapped_replace (by unfold width; omega)]
    by_cases he : i = x <;> simp [bindName, restore, he, hi]
  · have he : i ≠ x := by omega
    simp [restore, hi, bindName, he]

theorem host_replace {bound x} (hx : x < bound) (graph : Env) (v : Tm) :
    (hostTemplate bound).close (mapEnv (replaceMap (width bound) x) (push v graph)) =
      (hostTemplate bound).close graph := by
  simp only [hostTemplate, NativeCode.close, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  congr 1 <;> rw [mapped_replace (by unfold width; omega)] <;> simp [bindName, show bound ≠ x by omega,
    show bound + 1 ≠ x by omega, show bound + 2 ≠ x by omega]

theorem replace_length (w x : Nat) (L : List Tm) (d : Tm) :
    (envMap (replaceMap w x) L d).1.length = w := by simp [envMap, replaceMap]

theorem drop_length (w : Nat) (L : List Tm) (d : Tm) :
    (envMap (dropMap w) L d).1.length = w := by simp [envMap, dropMap]

/-- Slot mapping, including its changed default, retains actual values.
This invariant is weaker than source/world validity of named program slots. -/
theorem envMap_values {m L d}
    (hL : ∀ v ∈ L, isVal v = true) (hd : isVal d = true) :
    (∀ v ∈ (envMap m L d).1, isVal v = true) ∧ isVal (envMap m L d).2 = true := by
  have hv (v : Tm) (h : v ∈ (envMap m L d).1 ∨ v = (envMap m L d).2) : isVal v = true := by
    rcases envMap_mem h with hm | rfl
    · exact hL v hm
    · exact hd
  exact ⟨fun v h => hv v (Or.inl h), hv _ (Or.inr rfl)⟩

theorem slotValue_value {bound ρ host payload i}
    (hρ : ∀ x, isVal (ρ x) = true)
    (hh : isVal host.viewRead = true ∧ isVal host.viewWrite = true ∧ isVal host.viewLength = true)
    (hp : isVal payload = true) : isVal (slotValue bound ρ host payload i) = true := by
  unfold slotValue
  split
  · exact hρ i
  · split
    · exact hh.1
    · split
      · exact hh.2.1
      · split
        · exact hh.2.2
        · exact hp

theorem slots_values {bound ρ host payload}
    (hρ : ∀ x, isVal (ρ x) = true)
    (hh : isVal host.viewRead = true ∧ isVal host.viewWrite = true ∧ isVal host.viewLength = true)
    (hp : isVal payload = true) : ∀ v ∈ slots bound ρ host payload, isVal v = true := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  exact slotValue_value hρ hh hp

/-- Replacing only the payload leaves every named value unchanged. -/
theorem restore_payload (bound : Nat) (outer graph : Env) (v : Tm) :
    restore bound outer (mapEnv (replaceMap (width bound) (bound + 3)) (push v graph)) =
      restore bound outer graph := by
  funext i
  by_cases hi : i < bound
  · simp only [restore, hi, ↓reduceIte]
    rw [mapped_replace (by unfold width; omega)]
    simp [bindName, show i ≠ bound + 3 by omega]
  · simp [restore, hi]

theorem host_payload (bound : Nat) (graph : Env) (v : Tm) :
    (hostTemplate bound).close (mapEnv (replaceMap (width bound) (bound + 3)) (push v graph)) =
      (hostTemplate bound).close graph := by
  simp only [hostTemplate, NativeCode.close, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  congr 1 <;> rw [mapped_replace (by unfold width; omega)] <;>
    simp [bindName]

/-- World/source validity is required only of finite SOURCE slots. Host and
payload slots have their separate machine-value invariant, not this premise. -/
theorem restore_valid {bound outer graph mark s t}
    (context : ValidContext outer mark s) (ha : TolerantFrames.Admissible s t)
    (refs : ∀ i, i < bound → RefsOk t.W (graph i))
    (source : ∀ i, i < bound → isSourceVal (graph i) = true) :
    ValidContext (restore bound outer graph) mark t := by
  have persisted := context.admissible ha
  refine ⟨?_, ?_, persisted.2.2⟩
  · intro i
    by_cases hi : i < bound
    · simpa [restore, hi] using refs i hi
    · simpa [restore, hi] using persisted.1 i
  · intro i
    by_cases hi : i < bound
    · simpa [restore, hi] using source i hi
    · simpa [restore, hi] using persisted.2.1 i

end Verification.Paper.TolerantFrames.Compiler
