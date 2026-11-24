/-! # The paper's rules for effect variables, as propositions

The rules of the paper "An effect language for TScert"
(`docs/drafts/effect-languages-note/note.tex`, Section "Rules for effect
variables") that the experimental mode of `docs/drafts/paper-rules-mode.md`
applies, each stated as a proposition over a semantics. Nothing here is
proved: a semantics that meets a rule proves it (`Model.lean` for the
idealised model), and the mode's soundness theorem takes `PaperRules` of
TScert's semantics as a premise.

A semantics gives the paper's notions their meaning:

- `Act Φ s s'`: the transitions from `s` that the effect `Φ` bounds;
- `Reaches s₀ s`: a run leads from `s₀` to `s`;
- `Within Φ Ψ s`: at `s`, the change `Φ` allows at each location is within
  the one `Ψ` allows, what the order's sufficient condition establishes;
- `Same Φ s₀ s`: `Φ` allows at `s` what it allows at `s₀`, on the locations
  of `s₀`;
- `Anchored Φ s₀`: `Φ` is an instance anchored at the call state `s₀`;
- `old s₀`: the effect keeping every external location allocated since `s₀`
  (`{old: any}` extended with confined module states);
- `meet Φ Ψ`: the intersection of two effects;
- `rename σ Φ`, `RenOk σ Φ`: an effect read at a call's arguments, and the
  condition that the renaming reads each of its positions at the caller;
- `Mod`, `modEff M`, `ModDisjoint M Φ s`: a confined module-state region
  `M.@state`, its effect `{ M.@state : any; else : keep }`, and the
  condition that `M.@state` is disjoint from every constrained entry of `Φ`
  and permitted by `Φ`'s default.
-/

namespace Verification.Paper.EffectLanguage

/-- A semantics of the paper's effects. -/
structure Semantics where
  St : Type
  Eff : Type
  Ren : Type
  Mod : Type
  Act : Eff → St → St → Prop
  Reaches : St → St → Prop
  Within : Eff → Eff → St → Prop
  Same : Eff → St → St → Prop
  Anchored : Eff → St → Prop
  old : St → Eff
  meet : Eff → Eff → Eff
  rename : Ren → Eff → Eff
  RenOk : Ren → Eff → Prop
  modEff : Mod → Eff
  ModDisjoint : Mod → Eff → St → Prop

namespace Semantics

/-- Inclusion from a state: every transition from `s` that `Φ` bounds, `Ψ`
bounds. -/
def Incl (S : Semantics) (Φ Ψ : S.Eff) (s : S.St) : Prop :=
  ∀ s', S.Act Φ s s' → S.Act Ψ s s'

/-- A finite run from `s₀` to `s` whose steps are each bounded by `Φ₁` or `Φ₂`. -/
inductive Steps (S : Semantics) (Φ₁ Φ₂ : S.Eff) : S.St → S.St → Prop where
  | refl {s} : Steps S Φ₁ Φ₂ s s
  | step {s₁ s₂ s₃} : (S.Act Φ₁ s₁ s₂ ∨ S.Act Φ₂ s₁ s₂) → Steps S Φ₁ Φ₂ s₂ s₃ → Steps S Φ₁ Φ₂ s₁ s₃

/-- A predicate `P` is preserved by an effect `Ψ`: every `Ψ`-bounded step keeps `P`. -/
def Preserves (S : Semantics) (Ψ : S.Eff) (P : S.St → Prop) : Prop :=
  ∀ s s', P s → S.Act Ψ s s' → P s'

end Semantics

/-- **Bound**: an anchored instance within its bound at the call is
included in the bound at every later state where the bound allows what it
allowed at the call. -/
def BoundRule (S : Semantics) : Prop :=
  ∀ θ Φ s₀ s, S.Within θ Φ s₀ → S.Reaches s₀ s → S.Anchored θ s₀ → S.Same Φ s₀ s →
    S.Incl θ Φ s

/-- **Anch**: an instance anchored at a call changes no external location
allocated since the call. -/
def AnchRule (S : Semantics) : Prop :=
  ∀ θ s₀ s, S.Anchored θ s₀ → S.Reaches s₀ s → S.Incl θ (S.old s₀) s

/-- **Meet**: an effect included in two effects is included in their meet. -/
def MeetRule (S : Semantics) : Prop :=
  ∀ E Φ₁ Φ₂ s, S.Incl E Φ₁ s → S.Incl E Φ₂ s → S.Incl E (S.meet Φ₁ Φ₂) s

/-- **Inst**, its substitution: a transition an effect bounds at the
callee's positions is bounded by the effect read at the caller's
arguments. -/
def InstRule (S : Semantics) : Prop :=
  ∀ σ E s s', S.RenOk σ E → S.Act E s s' → S.Act (S.rename σ E) s s'

/-- **Confined** (module-private confined state `M.@state`): a confined
module's state effect is anchored at every state (fresh-only growth never
modifies external post-entry allocations) and lies within every effect whose
constrained regions are disjoint from `M.@state` and whose default permits it. -/
def ConfinedRule (S : Semantics) : Prop :=
  ∀ M s₀, S.Anchored (S.modEff M) s₀ ∧
    ∀ Φ, S.ModDisjoint M Φ s₀ → S.Within (S.modEff M) Φ s₀

/-- **Callback-Inv** (scoped callback invariant): if a caller predicate `P`
holds at the call state `s₀` and is preserved by a self-stabilizing support
effect `Ψ` (every `Ψ`-bounded step keeps `P` and preserves `Ψ`'s own meaning
`Same Ψ`), and both the callee's own effect `Φ_own` and the callback's effect
`Φ_cb` are anchored at `s₀` and within `Ψ` at `s₀`, then `P` holds at every
state `s` reached during a run interleaving `Φ_own`-bounded steps and
`Φ_cb`-bounded steps. When the callback does not escape the call's dynamic
extent, every invocation of the callback occurs in such a state, so the
callback body may assume `P` on entry. -/
def CallbackInvRule (S : Semantics) : Prop :=
  ∀ (Φ_own Φ_cb Ψ : S.Eff) (P : S.St → Prop) (s₀ s : S.St),
    P s₀ →
    S.Preserves Ψ P →
    (∀ a b, S.Act Ψ a b → S.Same Ψ a b) →
    S.Within Φ_own Ψ s₀ → S.Anchored Φ_own s₀ →
    S.Within Φ_cb Ψ s₀ → S.Anchored Φ_cb s₀ →
    S.Steps Φ_own Φ_cb s₀ s →
    P s

/-- The rules the experimental mode applies. -/
structure PaperRules (S : Semantics) : Prop where
  bound : BoundRule S
  anch : AnchRule S
  meet : MeetRule S
  inst : InstRule S
  confined : ConfinedRule S
  callbackInv : CallbackInvRule S

end Verification.Paper.EffectLanguage
