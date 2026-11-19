import Verification.Semantics.HeapObservations

/-! # Evaluation contexts

The draft "Accepting a unit through the read-only frame" (`docs/drafts/framed-acceptance.md`,
"The calls the claim is about", `isolate`). An evaluation context
(`EvalCtx K`) is a term with one hole at a position `Step` evaluates: one
congruence position of a step rule, under every earlier position a value,
nested; a frame's running term (`frameC`) among them. A program whose state
is `K[t]` runs `t` in `K`:

- `EvalCtx.step` (proved): a step of `t` is a step of `K[t]`.
- `EvalCtx.steps_inv` (proved, `isolate` at the calculus): an execution
  from `K[t]` is an execution of `t` in `K`, or reaches, by an execution of
  `t` in `K`, a state `K[t₁]` whose `t₁` takes no step (a value, a throw or
  a stuck term), from which the rest of it runs. By determinism
  (`Step_det`). -/
namespace Verification.HeapObservations
open Verification

/-- **An evaluation context**: the hole, or a congruence position of a step
rule (its earlier positions values) around an evaluation context. -/
inductive EvalCtx : (Tm → Tm) → Prop where
  | hole : EvalCtx fun t => t
  | callL {K : Tm → Tm} (r : Tm) (args : List Tm) : EvalCtx K → EvalCtx fun t => .invoke (K t) r args
  | callRecv {K : Tm → Tm} {f : Tm} (args : List Tm) : isVal f = true → EvalCtx K →
      EvalCtx fun t => .invoke f (K t) args
  | callArg {K : Tm → Tm} {f r : Tm} {args : List Tm} {i : Nat} : isVal f = true → isVal r = true →
      i < args.length → (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) → EvalCtx K →
      EvalCtx fun t => .invoke f r (args.set i (K t))
  | constructL {K : Tm → Tm} (args : List Tm) : EvalCtx K → EvalCtx fun t => .construct (K t) args
  | constructArg {K : Tm → Tm} {f : Tm} {args : List Tm} {i : Nat} : isVal f = true → i < args.length →
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) → EvalCtx K →
      EvalCtx fun t => .construct f (args.set i (K t))
  | letC {K : Tm → Tm} (b : Tm) : EvalCtx K → EvalCtx fun t => .letE (K t) b
  | spreadC {K : Tm → Tm} : EvalCtx K → EvalCtx fun t => .spread (K t)
  | makeArg {K : Tm → Tm} {c : CallCode} {ns : List PropKey} {inits : List Tm} {i : Nat} : i < inits.length →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) → EvalCtx K →
      EvalCtx fun t => .makeAt c ns (inits.set i (K t))
  | readC {K : Tm → Tm} (f : PropKey) : EvalCtx K → EvalCtx fun t => .readAt f (K t)
  | indexC1 {K : Tm → Tm} (key : Tm) : EvalCtx K → EvalCtx fun t => .indexAt (K t) key
  | indexC2 {K : Tm → Tm} {a : Tm} : isVal a = true → EvalCtx K → EvalCtx fun t => .indexAt a (K t)
  | writeC1 {K : Tm → Tm} (f : PropKey) (b : Tm) : EvalCtx K → EvalCtx fun t => .writeAt f (K t) b
  | writeC2 {K : Tm → Tm} (f : PropKey) {a : Tm} : isVal a = true → EvalCtx K → EvalCtx fun t => .writeAt f a (K t)
  | testC {K : Tm → Tm} (k : Tag) : EvalCtx K → EvalCtx fun t => .test k (K t)
  | iteC {K : Tm → Tm} (a b : Tm) : EvalCtx K → EvalCtx fun t => .ite (K t) a b
  | arithC1 {K : Tm → Tm} (op : Arith) (b : Tm) : EvalCtx K → EvalCtx fun t => .arith op (K t) b
  | arithC2 {K : Tm → Tm} (op : Arith) {a : Tm} : isVal a = true → EvalCtx K → EvalCtx fun t => .arith op a (K t)
  | arrArg {K : Tm → Tm} {inits : List Tm} {i : Nat} : i < inits.length →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) → EvalCtx K →
      EvalCtx fun t => .arrLit (inits.set i (K t))
  | elemC1 {K : Tm → Tm} (i : Tm) : EvalCtx K → EvalCtx fun t => .elemAt (K t) i
  | elemC2 {K : Tm → Tm} {a : Tm} : isVal a = true → EvalCtx K → EvalCtx fun t => .elemAt a (K t)
  | setC1 {K : Tm → Tm} (i v : Tm) : EvalCtx K → EvalCtx fun t => .setElem (K t) i v
  | setC2 {K : Tm → Tm} {a : Tm} (v : Tm) : isVal a = true → EvalCtx K → EvalCtx fun t => .setElem a (K t) v
  | setC3 {K : Tm → Tm} {a i : Tm} : isVal a = true → isVal i = true → EvalCtx K →
      EvalCtx fun t => .setElem a i (K t)
  | lenC {K : Tm → Tm} : EvalCtx K → EvalCtx fun t => .lenOf (K t)
  | throwC {K : Tm → Tm} : EvalCtx K → EvalCtx fun t => .throw (K t)
  | mergeC1 {K : Tm → Tm} (d : List PropKey) (b : Tm) : EvalCtx K → EvalCtx fun t => .merge d (K t) b
  | mergeC2 {K : Tm → Tm} (d : List PropKey) {a : Tm} : isVal a = true → EvalCtx K → EvalCtx fun t => .merge d a (K t)
  | makeKeyC1 {K : Tm → Tm} (a : Tm) : EvalCtx K → EvalCtx fun t => .makeKey (K t) a
  | makeKeyC2 {K : Tm → Tm} {k : Tm} : isVal k = true → EvalCtx K → EvalCtx fun t => .makeKey k (K t)
  | frameC {K : Tm → Tm} (E : List Tm) (Kc : List (ControlFlow.Continuation × Option ControlFlow.Target))
      (L : List Tm) (d : Tm) (k : ControlFlow.Continuation) (x : Option ControlFlow.Target) (comp : ComponentTag) :
      EvalCtx K → EvalCtx fun t => .frame E Kc (K t) L d k x comp

theorem set_prefix {xs : List Tm} {i : Nat} {a : Tm}
    (hpre : ∀ j, j < i → ∀ v, xs[j]? = some v → isVal v = true) :
    ∀ j, j < i → ∀ v, (xs.set i a)[j]? = some v → isVal v = true := by
  intro j hj v hv
  rw [List.getElem?_set_ne (by omega)] at hv
  exact hpre j hj v hv

/-- **A step of the hole is a step of the context** (proved). -/
theorem EvalCtx.step {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {h t h' t'}, Step h t h' t' → Step h (K t) h' (K t') := by
  induction hK with
  | hole => exact fun s => s
  | callL _ _ _ ih => exact fun s => .callL (ih s)
  | callRecv _ hf _ ih => exact fun s => .callRecv hf (ih s)
  | callArg hf hr hi hpre _ ih =>
    intro _ _ _ _ s
    have := Step.callArg hf hr (List.getElem?_set_self hi) (set_prefix hpre) (ih s)
    rwa [List.set_set] at this
  | constructL _ _ ih => exact fun s => .constructL (ih s)
  | constructArg hf hi hpre _ ih =>
    intro _ _ _ _ s
    have := Step.constructArg hf (List.getElem?_set_self hi) (set_prefix hpre) (ih s)
    rwa [List.set_set] at this
  | letC _ _ ih => exact fun s => .letC (ih s)
  | spreadC _ ih => exact fun s => .spreadC (ih s)
  | @makeArg _ c ns _ _ hi hpre _ ih =>
    intro _ _ _ _ s
    have := Step.makeArg (c := c) (ns := ns) (List.getElem?_set_self hi) (set_prefix hpre) (ih s)
    rwa [List.set_set] at this
  | readC _ _ ih => exact fun s => .readC (ih s)
  | indexC1 _ _ ih => exact fun s => .indexC1 (ih s)
  | indexC2 ha _ ih => exact fun s => .indexC2 ha (ih s)
  | writeC1 _ _ _ ih => exact fun s => .writeC1 (ih s)
  | writeC2 _ ha _ ih => exact fun s => .writeC2 ha (ih s)
  | testC _ _ ih => exact fun s => .testC (ih s)
  | iteC _ _ _ ih => exact fun s => .iteC (ih s)
  | arithC1 _ _ _ ih => exact fun s => .arithC1 (ih s)
  | arithC2 _ ha _ ih => exact fun s => .arithC2 ha (ih s)
  | arrArg hi hpre _ ih =>
    intro _ _ _ _ s
    have := Step.arrArg (List.getElem?_set_self hi) (set_prefix hpre) (ih s)
    rwa [List.set_set] at this
  | elemC1 _ _ ih => exact fun s => .elemC1 (ih s)
  | elemC2 ha _ ih => exact fun s => .elemC2 ha (ih s)
  | setC1 _ _ _ ih => exact fun s => .setC1 (ih s)
  | setC2 _ ha _ ih => exact fun s => .setC2 ha (ih s)
  | setC3 ha hi _ ih => exact fun s => .setC3 ha hi (ih s)
  | lenC _ ih => exact fun s => .lenC (ih s)
  | throwC _ ih => exact fun s => .throwC (ih s)
  | mergeC1 _ _ _ ih => exact fun s => .mergeC1 (ih s)
  | mergeC2 _ ha _ ih => exact fun s => .mergeC2 ha (ih s)
  | makeKeyC1 _ _ ih => exact fun s => .makeKeyC1 (ih s)
  | makeKeyC2 hk _ ih => exact fun s => .makeKeyC2 hk (ih s)
  | frameC _ _ _ _ _ _ _ _ ih => exact fun s => .frameC (ih s)

/-- **An execution of the hole is an execution of the context** (proved). -/
theorem EvalCtx.steps {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {j h t h' t'}, Steps j h t h' t' → Steps j h (K t) h' (K t')
  | _, _, _, _, _, .refl => .refl
  | _, _, _, _, _, .next st hrest => .next (hK.step st) (hK.steps hrest)

/-- **A step of the context whose hole steps is the hole's** (proved, by
determinism). -/
theorem EvalCtx.step_inv {K : Tm → Tm} (hK : EvalCtx K) {h t h₁ t₁ h₂ u}
    (hs : Step h t h₁ t₁) (hs' : Step h (K t) h₂ u) : h₂ = h₁ ∧ u = K t₁ := by
  obtain ⟨h₁', h₂'⟩ := Step_det hs' (hK.step hs)
  exact ⟨h₁', h₂'⟩

open Classical in
/-- **An execution from a context runs its hole in it** (proved; the
draft's `isolate` at the calculus): an execution of `j` steps from `K[t]`
is an execution of `t` in `K` to `K[t']`, or reaches, by `i < j` steps of
`t` in `K`, a state `K[t₁]` whose `t₁` takes no step, from which the rest
of the execution runs. -/
theorem EvalCtx.steps_inv {K : Tm → Tm} (hK : EvalCtx K) :
    ∀ {j h t h' u}, Steps j h (K t) h' u →
      (∃ t', Steps j h t h' t' ∧ u = K t') ∨
      (∃ i h₁ t₁, i < j ∧ Steps i h t h₁ t₁ ∧ (∀ h₂ t₂, ¬ Step h₁ t₁ h₂ t₂) ∧ Steps (j - i) h₁ (K t₁) h' u)
  | 0, _, t, _, _, .refl => .inl ⟨t, .refl, rfl⟩
  | j + 1, h, t, h', u, .next st hrest => by
    by_cases hstep : ∃ h₁ t₁, Step h t h₁ t₁
    · obtain ⟨h₁, t₁, st₁⟩ := hstep
      obtain ⟨rfl, rfl⟩ := hK.step_inv st₁ st
      rcases hK.steps_inv hrest with ⟨t', hs, rfl⟩ | ⟨i, h₂, t₂, hi, hs, hn, hr⟩
      · exact .inl ⟨t', .next st₁ hs, rfl⟩
      · exact .inr ⟨i + 1, h₂, t₂, by omega, .next st₁ hs, hn, by rwa [show j + 1 - (i + 1) = j - i by omega]⟩
    · refine .inr ⟨0, h, t, by omega, .refl, fun h₂ t₂ hs => hstep ⟨h₂, t₂, hs⟩, ?_⟩
      simpa using Steps.next st hrest

end Verification.HeapObservations
