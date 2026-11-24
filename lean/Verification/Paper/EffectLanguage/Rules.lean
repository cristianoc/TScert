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

/-- The rules the experimental mode applies. -/
structure PaperRules (S : Semantics) : Prop where
  bound : BoundRule S
  anch : AnchRule S
  meet : MeetRule S
  inst : InstRule S
  confined : ConfinedRule S

end Verification.Paper.EffectLanguage
