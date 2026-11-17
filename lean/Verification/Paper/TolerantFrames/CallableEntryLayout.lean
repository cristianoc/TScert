import Verification.Paper.TolerantFrames.CompilerLayout
import Verification.Semantics.CallArguments

/-! # Fixed-arity invocation input layouts

The existing CallArguments.parameters function pads missing inputs and ignores
already evaluated extras. Finite selectors map its real receiver/parameter/
capture/self pack to the compiler frame. Host-only slots require machine
values. A separate theorem assumes valid caller inputs and selected program
captures; self's explicit reference validity may constrain capture references.
-/
namespace Verification.Paper.TolerantFrames.Compiler.Callable
open Verification
open Verification.TolerantFrames

inductive Selector (arity captures : Nat) where
  | undefined
  | receiver
  | parameter (index : Fin arity)
  | capture (index : Fin captures)
  | calleeSelf
  deriving DecidableEq, Repr

structure Layout (arity captures : Nat) where
  source : List (Selector arity captures)
  viewRead : Fin captures
  viewWrite : Fin captures
  viewLength : Fin captures

/-- Indices in the pack after the adapter binds its undefined result. -/
def Selector.index {arity captures} : Selector arity captures → Nat
  | .undefined => 0
  | .receiver => 1
  | .parameter i => i.val + 2
  | .capture i => arity + i.val + 2
  | .calleeSelf => arity + captures + 2

def inputs (arity : Nat) (receiver : Tm) (args caps : List Tm) (self : Tm) : List Tm :=
  receiver :: CallArguments.parameters arity args ++ (caps ++ [self])

def Selector.read {arity} (receiver : Tm) (args caps : List Tm) (self : Tm) : Selector arity caps.length → Tm
  | .undefined => .undef
  | .receiver => receiver
  | .parameter i => (CallArguments.parameters arity args).getD i.val .undef
  | .capture i => caps.getD i.val .undef
  | .calleeSelf => self

def Layout.env {arity} {caps : List Tm} (layout : Layout arity caps.length) (receiver : Tm) (args : List Tm) (self : Tm) : Env :=
  fun i => (layout.source.getD i .undefined).read receiver args caps self

def Layout.host {arity} {caps : List Tm} (layout : Layout arity caps.length) : NativeCode :=
  ⟨caps.getD layout.viewRead.val .undef, caps.getD layout.viewWrite.val .undef,
    caps.getD layout.viewLength.val .undef⟩

def Layout.slot {arity captures} (layout : Layout arity captures) (bound i : Nat) : Selector arity captures :=
  if i < bound then layout.source.getD i .undefined
  else if i = bound then .capture layout.viewRead
  else if i = bound + 1 then .capture layout.viewWrite
  else if i = bound + 2 then .capture layout.viewLength else .undefined

def Layout.mapping {arity captures} (layout : Layout arity captures) (bound : Nat) : PointClaims.Mapping :=
  some ((List.range (width bound)).map fun i => (layout.slot bound i).index)

theorem parameters_length (arity : Nat) (args : List Tm) :
    (CallArguments.parameters arity args).length = arity := by
  induction arity generalizing args with
  | zero => rfl
  | succ arity ih => cases args <;> simp [CallArguments.parameters, ih]

theorem inputs_length (arity : Nat) (receiver : Tm) (args caps : List Tm) (self : Tm) :
    (inputs arity receiver args caps self).length = arity + caps.length + 2 := by
  simp [inputs, parameters_length]; omega

theorem Selector.index_bound {arity captures} (s : Selector arity captures) :
    s.index < arity + captures + 3 := by
  cases s with
  | undefined | receiver | calleeSelf => simp only [index] <;> omega
  | parameter i | capture i => have hi := i.isLt; simp only [index] <;> omega

/-- Equality holds for every default because selected indices are in bounds. -/
theorem Selector.read_index {arity} (s : Selector arity caps.length)
    (receiver : Tm) (args : List Tm) (self d : Tm) :
    envOf (.undef :: inputs arity receiver args caps self) d s.index = s.read receiver args caps self := by
  cases s with
  | undefined | receiver => rfl
  | parameter i =>
    simp [envOf, inputs, index, read, List.getD_eq_getElem?_getD, List.getElem?_append,
      parameters_length, i.isLt]
  | capture i =>
    have hn : ¬ arity + i.val < arity := by omega
    simp [envOf, inputs, index, read, List.getD_eq_getElem?_getD, List.getElem?_append,
      parameters_length, i.isLt, hn]
  | calleeSelf =>
    simp [envOf, inputs, index, read, List.getD_eq_getElem?_getD, parameters_length]

theorem Layout.slot_read {arity} (layout : Layout arity caps.length) (bound i : Nat)
    (receiver : Tm) (args : List Tm) (self : Tm) :
    (layout.slot bound i).read receiver args caps self =
      slotValue bound (layout.env receiver args self) layout.host .undef i := by
  by_cases hn : i < bound
  · simp only [slot, slotValue, if_pos hn, env]
  · by_cases hr : i = bound
    · simp only [slot, slotValue, if_neg hn, if_pos hr, Selector.read, host]
    · by_cases hw : i = bound + 1
      · simp only [slot, slotValue, if_neg hn, if_neg hr, if_pos hw, Selector.read, host]
      · by_cases hl : i = bound + 2
        · simp only [slot, slotValue, if_neg hn, if_neg hr, if_neg hw, if_pos hl, Selector.read, host]
        · simp only [slot, slotValue, if_neg hn, if_neg hr, if_neg hw, if_neg hl, Selector.read]

/-- The bind continuation produces exactly the established compiler frame. -/
theorem Layout.map_inputs {arity} (layout : Layout arity caps.length) (bound : Nat)
    (receiver : Tm) (args : List Tm) (self d : Tm) :
    envMap (layout.mapping bound) (.undef :: inputs arity receiver args caps self) d =
      (slots bound (layout.env receiver args self) layout.host .undef, .undef) := by
  simp only [envMap, mapping, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (Selector.read_index _ _ _ _ _).trans (layout.slot_read bound i receiver args self)

private theorem getD_property {P : Tm → Prop} {xs : List Tm} {d : Tm}
    (hd : P d) (hx : ∀ v ∈ xs, P v) (i : Nat) : P (xs.getD i d) := by
  rcases getD_mem_or xs i d with hm | he
  · exact hx _ hm
  · rw [he]; exact hd

/-- Program captures are selected explicitly; unselected host captures need
no source predicate here. Parameters use the actual padding operation. -/
theorem Selector.read_property {arity} {caps : List Tm} (s : Selector arity caps.length)
    {P : Tm → Prop} {receiver self : Tm} {args : List Tm}
    (hu : P .undef) (hr : P receiver) (ha : ∀ a ∈ args, P a) (hs : P self)
    (hc : ∀ j : Fin caps.length, s = .capture j → P (caps.getD j.val .undef)) :
    P (s.read receiver args caps self) := by
  cases s with
  | undefined => exact hu
  | receiver => exact hr
  | parameter i => exact getD_property hu (CallArguments.parameters_property hu ha) i.val
  | capture j => exact hc j rfl
  | calleeSelf => exact hs

theorem Layout.env_property {arity} {caps : List Tm} (layout : Layout arity caps.length)
    {P : Tm → Prop} {receiver self : Tm} {args : List Tm}
    (hu : P .undef) (hr : P receiver) (ha : ∀ a ∈ args, P a) (hs : P self)
    (hc : ∀ j : Fin caps.length, Selector.capture j ∈ layout.source → P (caps.getD j.val .undef)) :
    ∀ i, P (layout.env receiver args self i) := by
  intro i
  simp only [env, List.getD_eq_getElem?_getD]
  cases h : layout.source[i]? with
  | none => exact hu
  | some s =>
    apply Selector.read_property s hu hr ha hs
    intro j hj
    cases hj
    exact hc j (List.mem_of_getElem? h)

theorem Layout.env_values {arity} {caps : List Tm} (layout : Layout arity caps.length)
    {receiver self : Tm} {args : List Tm}
    (hr : isVal receiver = true) (ha : CallArguments.Values args) (hs : isVal self = true)
    (hc : CallArguments.Values caps) : ∀ i, isVal (layout.env receiver args self i) = true :=
  layout.env_property (P := fun v => isVal v = true) rfl hr ha hs
    (fun j _ => getD_property (P := fun v => isVal v = true) rfl hc j.val)

theorem Layout.host_values {arity} {caps : List Tm} (layout : Layout arity caps.length)
    (hc : CallArguments.Values caps) :
    isVal layout.host.viewRead = true ∧ isVal layout.host.viewWrite = true ∧ isVal layout.host.viewLength = true :=
  ⟨getD_property (P := fun v => isVal v = true) rfl hc _,
    getD_property (P := fun v => isVal v = true) rfl hc _,
    getD_property (P := fun v => isVal v = true) rfl hc _⟩

/-- The body starts at exactly the invocation heap and its entry mark.
These are input facts, independent of any native safety or body summary. -/
theorem Layout.entry_valid {arity} {caps : List Tm} (layout : Layout arity caps.length)
    {s : IndexedHeap} {receiver self : Tm} {args : List Tm}
    (hr : isSourceVal receiver = true ∧ RefsOk s.W receiver)
    (ha : ∀ a ∈ args, isSourceVal a = true ∧ RefsOk s.W a)
    (hs : isSourceVal self = true ∧ RefsOk s.W self)
    (hc : ∀ j : Fin caps.length, Selector.capture j ∈ layout.source →
      isSourceVal (caps.getD j.val .undef) = true ∧ RefsOk s.W (caps.getD j.val .undef)) :
    ValidContext (layout.env receiver args self) s.h.length s := by
  have good := layout.env_property (P := fun v => isSourceVal v = true ∧ RefsOk s.W v)
    ⟨rfl, RefsOk_undef⟩ hr ha hs hc
  exact ⟨fun i => (good i).2, (fun i => (good i).1), Nat.le_refl _⟩

theorem Layout.mapped_host {arity} {caps : List Tm} (layout : Layout arity caps.length)
    (bound : Nat) (receiver : Tm) (args : List Tm) (self d : Tm) :
    (hostTemplate bound).close
      (envOf (envMap (layout.mapping bound) (.undef :: inputs arity receiver args caps self) d).1
        (envMap (layout.mapping bound) (.undef :: inputs arity receiver args caps self) d).2) = layout.host := by
  rw [layout.map_inputs]
  exact slots_host _ _ _ _ _

theorem Layout.restored_inputs {arity} {caps : List Tm} (layout : Layout arity caps.length)
    (bound : Nat) (receiver : Tm) (args : List Tm) (self d : Tm) :
    restore bound (layout.env receiver args self)
      (envOf (envMap (layout.mapping bound) (.undef :: inputs arity receiver args caps self) d).1
        (envMap (layout.mapping bound) (.undef :: inputs arity receiver args caps self) d).2) =
      layout.env receiver args self := by
  rw [layout.map_inputs]
  exact restore_slots _ _ _ _ _

end Verification.Paper.TolerantFrames.Compiler.Callable
