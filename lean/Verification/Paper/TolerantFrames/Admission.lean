import Verification.Paper.TolerantFrames.Commands

/-! # The paper's region and command scope judgments

The shared region datatype has implementation helpers, and raw commands can
reuse slots. Those representations must not be confused with the paper's
admissible syntax. These judgments state the paper's seven region forms,
declared path conditions, live command variables and fresh result bindings.
The type system's declared path classification is an explicit parameter.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.Parity (Path)

/-- Declared path classifications of §3. These concern the declared type,
not a run-time narrowing. The surrounding type system supplies them. -/
structure DeclaredPaths where
  collection : Path → Prop
  object : Path → Prop
  field : Path → String → Prop

/-- Shift declared program roots beneath an existential value binder.
The new logical value has no declared collection/object type. -/
def DeclaredPaths.underValue (types : DeclaredPaths) : DeclaredPaths where
  collection p := 0 < p.root ∧ types.collection ⟨p.root - 1, p.fields⟩
  object p := 0 < p.root ∧ types.object ⟨p.root - 1, p.fields⟩
  field p f := 0 < p.root ∧ types.field ⟨p.root - 1, p.fields⟩ f

/-- Precisely the paper's seven region forms and their static conditions.
Shared `.all` and `.inCls` helpers are not extra source-region forms. -/
inductive RegionWellFormed (types : DeclaredPaths) : Region → Prop where
  | values : RegionWellFormed types (.cls .values)
  | spines : RegionWellFormed types (.cls .spines)
  | views : RegionWellFormed types (.cls .views)
  | spine {x fs} : types.collection ⟨x, fs⟩ → RegionWellFormed types (.spine x fs)
  | cells {x fs} : types.collection ⟨x, fs⟩ → RegionWellFormed types (.pathCells x fs)
  | fields {x fs} : types.object ⟨x, fs⟩ → RegionWellFormed types (.pathFields x fs)
  | field {x fs f} : types.object ⟨x, fs⟩ → types.field ⟨x, fs⟩ f → RegionWellFormed types (.path x fs (.str f))

/-- Every entry, not just those used by a particular proof, is well formed. -/
def EffectWellFormed (types : DeclaredPaths) (Φ : Footprint) : Prop :=
  ∀ e ∈ Φ, RegionWellFormed types e.1

/-- Assertion admission adds the declared-type restrictions on its regions.
Term suffixes and scalar literal restrictions are enforced by their types. -/
def Formula.WellFormed (types : DeclaredPaths) : Formula → Prop
  | .truth | .falsity | .atom _ | .separated _ _ | .apart _ _ => True
  | .and F G | .or F G => F.WellFormed types ∧ G.WellFormed types
  | .existsValue F => F.WellFormed types.underValue
  | .fresh r => RegionWellFormed types r
  | .box Φ F => EffectWellFormed types Φ ∧ F.WellFormed types

/-- Slots live in the lexical scope. A total runtime valuation is storage,
not a declaration that every slot is in scope. -/
abbrev Scope := Nat → Prop

def Argument.Scoped (Γ : Scope) : Argument → Prop
  | .variable x => Γ x
  | .literal _ => True

def Operation.Scoped (Γ : Scope) : Operation → Prop
  | .value a | .not a => a.Scoped Γ
  | .binary _ a b | .and a b | .or a b => a.Scoped Γ ∧ b.Scoped Γ
  | .fieldRead x _ | .arrayLength x | .viewLength x | .stringLength x => Γ x
  | .fieldWrite x _ a | .elementRead x a | .viewRead x a | .stringRead x a => Γ x ∧ a.Scoped Γ
  | .elementWrite x i v | .viewWrite x i v => Γ x ∧ i.Scoped Γ ∧ v.Scoped Γ
  | .objectLiteral fs => ∀ p ∈ fs, p.2.Scoped Γ
  | .arrayLiteral as => ∀ a ∈ as, a.Scoped Γ
  | .methodCall x _ as | .call x as | .construct x as => Γ x ∧ ∀ a ∈ as, a.Scoped Γ

/-- Which listed paper steps bind a result, rather than mutate storage. -/
def Operation.Binds : Operation → Prop
  | .fieldWrite .. | .elementWrite .. | .viewWrite .. => False
  | _ => True

/-- A command's lexical scope. Loops discard iteration-local names; loop
mutation of captured variables is represented by private cells. A handler's
caught name is fresh and local to its handler. -/
inductive Command.WellScoped : Scope → Command → Scope → Prop where
  | bind {Γ x op} : ¬ Γ x → op.Scoped Γ → op.Binds →
      Command.WellScoped Γ (.step (.bind x op)) (fun y => y = x ∨ Γ y)
  | perform {Γ op} : op.Scoped Γ → ¬ op.Binds → Command.WellScoped Γ (.step (.perform op)) Γ
  | seq {Γ Δ Θ a b} : Command.WellScoped Γ a Δ → Command.WellScoped Δ b Θ → Command.WellScoped Γ (.seq a b) Θ
  | choice {Γ Δ Θ Ω test a b} : test.Scoped Γ → Command.WellScoped Γ a Δ → Command.WellScoped Γ b Θ →
      (∀ x, Ω x → Δ x ∧ Θ x) → Command.WellScoped Γ (.choice test a b) Ω
  | loop {Γ Δ b} : Command.WellScoped Γ b Δ → Command.WellScoped Γ (.loop b) Γ
  | handle {Γ Δ Θ Ω b x d} : ¬ Γ x → Command.WellScoped Γ b Δ →
      Command.WellScoped (fun y => y = x ∨ Γ y) d Θ →
      (∀ y, Ω y → Δ y ∧ Θ y) → Command.WellScoped Γ (.handle b x d) Ω
  | return_ {Γ a} : a.Scoped Γ → Command.WellScoped Γ (.return_ a) Γ
  | throw_ {Γ a} : a.Scoped Γ → Command.WellScoped Γ (.throw_ a) Γ
  | break_ {Γ} : Command.WellScoped Γ .break_ Γ

end Verification.Paper.TolerantFrames
