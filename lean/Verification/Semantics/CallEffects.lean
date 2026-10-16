import Verification.Semantics.HeapObservations
import Verification.Semantics.Purity

/-! Call postconditions qualify the same receiver/arguments/result contract
as ordinary arrows. They concern calls admitted by that contract, not every
untyped invocation of a function. Fresh allocation is permitted; preserving
the input heap means keeping its existing locations unchanged on return.
Throws carry no return postcondition, just as in `SafePost`. -/
namespace Verification.CallEffects
open HeapObservations

/-- What a call signature guarantees beyond its contract. The first two are
heap effects: the signature's result operand is the result's type. A promise
qualifies an argument instead: its result operand is the promise's type.
`guards p` is a type guard's, `(x: A) => x is T`: the result is `true` or
`false`, and a `true` result leaves the actual at `p` in the result operand.
`asserts p` is an assertion function's, `(x: A) => asserts x is T`: a normal
return is `undefined`, and leaves the actual at `p` in the result operand. -/
inductive Effect where
  | unrestricted
  | preservesInputHeap
  | guards (param : Nat)
  | asserts (param : Nat)
  deriving Repr, DecidableEq

/-- One qualified call contract. `Args` distinguishes fixed argument lists
from a fixed prefix followed by an argument-pack contract. Mapping the type
operands preserves the effect by construction. -/
structure Contract (Receiver Args Result : Type) where
  receiver : Receiver
  arguments : Args
  result : Result
  effect : Effect
  deriving Repr, DecidableEq

def Contract.map (f : Receiver → Receiver') (g : Args → Args') (h : Result → Result')
    (s : Contract Receiver Args Result) : Contract Receiver' Args' Result' :=
  ⟨f s.receiver, g s.arguments, h s.result, s.effect⟩

/-- A host-relative method supplies its receiver when read. All other parts
of its signature, including its effect, are retained unchanged. -/
def Contract.withReceiver (receiver : Receiver') (s : Contract Receiver Args Result) :
    Contract Receiver' Args Result :=
  ⟨receiver, s.arguments, s.result, s.effect⟩

abbrev Arrow (α : Type) := Contract α (List α) α
abbrev RestArrow (α : Type) := Contract α (List α × α) α
abbrev MethodArrow (α : Type) := Contract Unit (List α) α
abbrev MethodRestArrow (α : Type) := Contract Unit (List α × α) α

def Arrow.map (f : α → β) (s : Arrow α) : Arrow β := Contract.map f (List.map f) f s
/-- Interpret fixed positions as value families and the rest as an argument
family, preserving the same effect. Ordinary renaming uses the same map for
both kinds of operand. -/
def RestArrow.mapWith (f : α → β) (g : α → γ) (s : RestArrow α) : Contract β (List β × γ) β :=
  Contract.map f (fun p => (p.1.map f, g p.2)) f s

def RestArrow.map (f : α → β) (s : RestArrow α) : RestArrow β := RestArrow.mapWith f f s

def MethodArrow.map (f : α → β) (s : MethodArrow α) : MethodArrow β :=
  Contract.map id (List.map f) f s

def MethodRestArrow.mapWith (f : α → β) (g : α → γ) (s : MethodRestArrow α) :
    Contract Unit (List β × γ) β :=
  Contract.map id (fun p => (p.1.map f, g p.2)) f s

def MethodRestArrow.map (f : α → β) (s : MethodRestArrow α) : MethodRestArrow β :=
  MethodRestArrow.mapWith f f s

/-- The body row of a rest signature keeps its effect and fixed parameters. -/
def RestArrow.fixed (s : RestArrow α) : Arrow α :=
  ⟨s.receiver, s.arguments.1, s.result, s.effect⟩

def Arrow.operands (s : Arrow α) : List α := s.receiver :: s.arguments ++ [s.result]
def RestArrow.operands (s : RestArrow α) : List α :=
  s.receiver :: s.arguments.1 ++ [s.arguments.2, s.result]
def MethodArrow.operands (s : MethodArrow α) : List α := s.arguments ++ [s.result]
def MethodRestArrow.operands (s : MethodRestArrow α) : List α :=
  s.arguments.1 ++ [s.arguments.2, s.result]

private theorem map_fixed {f : α → α} {xs : List α} (h : ∀ x ∈ xs, f x = x) :
    xs.map f = xs := by
  rw [List.map_congr_left (g := id) h, List.map_id]

theorem Arrow.map_of_operands {f : α → α} {s : Arrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, args, result, effect⟩
  have hr := h r (by simp [operands])
  have hd := h result (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, Contract.map, hr, hd, ha]

theorem RestArrow.map_of_operands {f : α → α} {s : RestArrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, ⟨args, rest⟩, result, effect⟩
  have hr := h r (by simp [operands])
  have hd := h result (by simp [operands])
  have he := h rest (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, mapWith, Contract.map, hr, hd, he, ha]

theorem MethodArrow.map_of_operands {f : α → α} {s : MethodArrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, args, result, effect⟩
  have hd := h result (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, Contract.map, hd, ha]

theorem MethodRestArrow.map_of_operands {f : α → α} {s : MethodRestArrow α}
    (h : ∀ a ∈ s.operands, f a = a) : s.map f = s := by
  rcases s with ⟨r, ⟨args, rest⟩, result, effect⟩
  have hd := h result (by simp [operands])
  have he := h rest (by simp [operands])
  have ha := map_fixed (xs := args) (fun x hx => h x (by simp [operands, hx]))
  simp [map, mapWith, Contract.map, hd, he, ha]

/-- Deliberate forgetting, for ordinary call elimination. -/
def Arrow.plain (s : Arrow α) : α × List α × α := (s.receiver, s.arguments, s.result)

def Effect.post : Effect → Heap → Post
  | .unrestricted, _ | .guards _, _ | .asserts _, _ => fun _ _ => True
  | .preservesInputHeap, before => fun after _ => before.IsPrefix after

/-- Whether the signature's result operand is the result's type: a heap
effect's, never a promise's. -/
def Effect.plain : Effect → Bool
  | .unrestricted | .preservesInputHeap => true
  | .guards _ | .asserts _ => false

/-- The actual a promise is about: the one at its parameter, `undefined` where
the call passes none. A heap effect is about none. -/
def Effect.promised : Effect → List Tm → Tm
  | .guards p, args | .asserts p, args => args.getD p .undef
  | .unrestricted, _ | .preservesInputHeap, _ => .undef

/-- What a call's result meets, given the signature's result operand `R` and
the promised actual `a`. -/
def Effect.result : Effect → Fam → Tm → Fam
  | .unrestricted, R, _ | .preservesInputHeap, R, _ => R
  | .guards _, T, a => fun k W u => (u = .tru ∧ T k W a) ∨ u = .fls
  | .asserts _, T, a => fun k W u => u = .undef ∧ T k W a

@[simp] theorem Effect.result_unrestricted (R : Fam) (a : Tm) : Effect.unrestricted.result R a = R := rfl
@[simp] theorem Effect.result_preservesInputHeap (R : Fam) (a : Tm) :
    Effect.preservesInputHeap.result R a = R := rfl

theorem Effect.result_plain {e : Effect} (h : e.plain = true) (R : Fam) (a : Tm) : e.result R a = R := by
  cases e <;> simp_all [Effect.plain, Effect.result]

theorem Effect.result_mono (e : Effect) {R T : Fam} {a : Tm} {k W u}
    (h : ∀ u, R k W u → T k W u) (hr : ∀ a', R k W a' → T k W a') :
    e.result R a k W u → e.result T a k W u := by
  cases e with
  | unrestricted | preservesInputHeap => exact h u
  | guards _ => exact fun hu => hu.imp (fun ⟨hu, ha⟩ => ⟨hu, hr a ha⟩) id
  | asserts _ => exact fun ⟨hu, ha⟩ => ⟨hu, hr a ha⟩

theorem Effect.result_agree (e : Effect) {R T : Fam} {a : Tm} {n}
    (h : Agree R T n) : Agree (e.result R a) (e.result T a) n := by
  intro m hm W u
  cases e with
  | unrestricted | preservesInputHeap => exact h m hm W u
  | guards _ => exact or_congr (and_congr Iff.rfl (h m hm W a)) Iff.rfl
  | asserts _ => exact and_congr Iff.rfl (h m hm W a)

/-- A promise's parameter, counted after `n` saved actuals: what a bound
signature promises of its own actuals. Defined where the promise is about one
of them. -/
def Effect.drop (n : Nat) : Effect → Effect
  | .guards p => .guards (p - n)
  | .asserts p => .asserts (p - n)
  | e => e

/-- Whether binding `n` actuals keeps the promise about an actual of the
bound call. -/
def Effect.keeps (n : Nat) : Effect → Bool
  | .guards p | .asserts p => n ≤ p
  | _ => true

@[simp] theorem Effect.drop_zero (e : Effect) : e.drop 0 = e := by cases e <;> rfl

@[simp] theorem Effect.keeps_zero (e : Effect) : e.keeps 0 = true := by
  cases e <;> simp [Effect.keeps]

theorem Effect.promised_drop {e : Effect} {pre args : List Tm} (h : e.keeps pre.length = true) :
    (e.drop pre.length).promised args = e.promised (pre ++ args) := by
  cases e <;> simp_all [Effect.keeps, Effect.drop, Effect.promised, List.getD_eq_getElem?_getD,
    List.getElem?_append_right]

/-- Whether a promise is about one of the first `n` parameters, the ones code
of arity `n` binds. -/
def Effect.below (n : Nat) : Effect → Bool
  | .guards p | .asserts p => p < n
  | _ => true

private theorem parameters_getD : ∀ (n : Nat) (args : List Tm) (p : Nat), p < n →
    (CallArguments.parameters n args).getD p .undef = args.getD p .undef
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], 0, _ => rfl
  | n + 1, [], p + 1, h => by
    simpa [CallArguments.parameters] using parameters_getD n [] p (by omega)
  | n + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: args, p + 1, h => by
    simpa [CallArguments.parameters] using parameters_getD n args p (by omega)

theorem Effect.parameters_length : ∀ (n : Nat) (args : List Tm), (CallArguments.parameters n args).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp [CallArguments.parameters, parameters_length n []]
  | n + 1, _ :: args => by simp [CallArguments.parameters, parameters_length n args]

/-- Code binding `n` parameters holds a promised actual among them. -/
theorem Effect.promised_frame {e : Effect} {n : Nat} (h : e.below n = true) (args vs : List Tm) :
    e.promised (CallArguments.parameters n args ++ vs) = e.promised args := by
  cases e with
  | unrestricted | preservesInputHeap => rfl
  | guards p | asserts p =>
    simp only [Effect.below, decide_eq_true_eq] at h
    simp only [Effect.promised]
    rw [← parameters_getD n args p h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [Effect.parameters_length]; exact h)]

/-- Actuals past those code binds do not change what it promises about. -/
theorem Effect.promised_take {e : Effect} {n m : Nat} (h : e.below n = true) (hm : n ≤ m) (args : List Tm) :
    e.promised (args.take m) = e.promised args := by
  cases e with
  | unrestricted | preservesInputHeap => rfl
  | guards p | asserts p =>
    simp only [Effect.below, decide_eq_true_eq] at h
    simp only [Effect.promised, List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]

theorem Effect.result_drop (e : Effect) (n : Nat) (R : Fam) (a : Tm) :
    (e.drop n).result R a = e.result R a := by
  cases e <;> rfl

theorem Effect.post_drop (e : Effect) (n : Nat) : (e.drop n).post = e.post := by
  cases e <;> rfl

/-- Fresh entry allocation composes with preservation of the body's input heap. -/
theorem Effect.post_prefix (effect : Effect) {before middle after : Heap} {v : Val}
    (hprefix : before.IsPrefix middle) : effect.post middle after v → effect.post before after v := by
  cases effect with
  | unrestricted | guards _ | asserts _ => exact id
  | preservesInputHeap => exact fun h => hprefix.trans h

/-- Conjoining two guarantees for the same call retains both. This is a
meet in the order of contracts: heap preservation is stronger than the
unrestricted guarantee. -/
def Effect.meet : Effect → Effect → Effect
  | .preservesInputHeap, _ => .preservesInputHeap
  | .unrestricted, other => other
  | e, _ => e

/-- Two guarantees whose results mean the same: two heap effects, or one
promise twice. Only these combine. -/
def Effect.sameResult : Effect → Effect → Bool
  | .guards p, .guards q | .asserts p, .asserts q => p == q
  | a, b => a.plain && b.plain

theorem Effect.post_meet {a b : Effect} (hs : a.sameResult b = true) (before after : Heap) (value : Val) :
    (a.meet b).post before after value ↔ a.post before after value ∧ b.post before after value := by
  cases a <;> cases b <;> simp_all [Effect.meet, Effect.post, Effect.sameResult, Effect.plain]

theorem Effect.meet_same {a b : Effect} (hs : a.sameResult b = true) :
    (a.meet b).result = a.result ∧ (a.meet b).promised = a.promised ∧
      b.result = a.result ∧ b.promised = a.promised := by
  cases a <;> cases b <;> simp [Effect.sameResult, Effect.plain] at hs <;> (try subst hs) <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The arrow equation, with a heap postcondition relative to this call's
entry heap. The input and result contracts are exactly those of `Promise`.
The effect is per signature: one overload may preserve its input heap while
another overload of the same value does not. -/
def PromiseWith (Ξ : Fam) (effect : Effect)
    (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc R : Fam)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → ∀ r, isVal r = true → Rc j U r →
      ∀ args, CallArguments.Values args → Acc j U args →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafePost Ξ (effect.result R (effect.promised args)) (effect.post heap) j U heap result

/-- A heap effect's signature is an ordinary arrow once its postcondition is
forgotten. A promise's is not: its result operand is not the result's type. -/
theorem PromiseWith.erase {effect Acc Rc R k W v} (hp : effect.plain = true)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : Promise Ξ Acc Rc R k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh r hrv hr args hv ha
  rw [Effect.result_plain hp] at hs
  exact ⟨result, hi, HeapObservations.erase hs⟩

theorem PromiseWith.down {effect Acc Rc R n W v}
    (h : PromiseWith Ξ effect Acc Rc R (n + 1) W v) :
    PromiseWith Ξ effect Acc Rc R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hrv hr args hv ha

theorem PromiseWith.mono {effect Acc Rc R n W W' v} (hx : WExt W W')
    (h : PromiseWith Ξ effect Acc Rc R n W v) : PromiseWith Ξ effect Acc Rc R n W' v := by
  intro j hj U hy hu heap hh r hrv hr args hv ha
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hrv hr args hv ha

/-- Effect coverage is implication of the normal-return postcondition and of
what the result meets, at every result operand. There is deliberately no rule
strengthening an unrestricted signature, and none relating a promise to a heap
effect, whose result operands mean different things. -/
def Effect.Covers (source target : Effect) : Prop :=
  (∀ before after value, source.post before after value → target.post before after value) ∧
  ∀ R args k W u, source.result R (source.promised args) k W u → target.result R (target.promised args) k W u

def Effect.covers : Effect → Effect → Bool
  | .preservesInputHeap, .unrestricted | .preservesInputHeap, .preservesInputHeap => true
  | .unrestricted, .unrestricted => true
  | .guards p, .guards q | .asserts p, .asserts q => p == q
  | _, _ => false

theorem Effect.covers_sound {a b : Effect} (h : a.covers b = true) : a.Covers b := by
  cases a <;> cases b <;> simp_all [Effect.covers, Effect.Covers, Effect.post, Effect.result, Effect.promised]

theorem Effect.Covers.refl (e : Effect) : e.Covers e := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Two executions' results combine as the results of their operands do. -/
theorem Effect.cross_result (e : Effect) {B C D : Fam} {a : Tm} {n}
    (h : CrossCompatUpTo n B C D) : CrossCompatUpTo n (e.result B a) (e.result C a) (e.result D a) := by
  intro j hj W W' heap hok hok' u hb hc
  cases e with
  | unrestricted | preservesInputHeap => exact h j hj W W' heap hok hok' u hb hc
  | guards _ =>
    rcases hb with ⟨rfl, hb⟩ | rfl
    · rcases hc with ⟨-, hc⟩ | hc
      · exact .inl ⟨rfl, h j hj W W' heap hok hok' a hb hc⟩
      · cases hc
    · exact .inr rfl
  | asserts _ => exact ⟨hb.1, h j hj W W' heap hok hok' a hb.2 hc.2⟩

theorem PromiseWith.weaken' {Ξ Ξ' : Fam} {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hexc : ∀ j, j < k → ∀ U u, Ξ j U u → Ξ' j U u)
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ' effect' Acc' Rc' T k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨result, hi, hs⟩ :=
    h j hj U hx hu heap hh r hrv (hrecv j hj U r hr) args hv (hacc j hj U args ha)
  exact ⟨result, hi, consequence_below' (fun m hm => hexc m (by omega))
    (fun m hm U' u hu => he.2 T args m U' u
      (Effect.result_mono effect (hres m (by omega) U') (hres m (by omega) U') hu)) (he.1 heap) hs⟩

theorem PromiseWith.weaken {Ξ : Fam} {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ effect' Acc' Rc' T k W v :=
  h.weaken' he (fun _ _ _ _ h => h) hrecv hacc hres

/-- Receiver restriction may depend on the calling world, without changing effects. -/
theorem PromiseWith.weaken_recv {effect : Effect} {Acc : ArgFam} {Rc Rc' R : Fam}
    {k W v}
    (hrecv : ∀ j (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ r, Rc' j U r → Rc j U r)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ effect Acc Rc' R k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  exact h j hj U hx hu heap hh r hrv (hrecv j hj U hx r hr) args hv ha

theorem PromiseWith.congr {Ξ Ξ' : Fam} {effect Acc Acc' Rc Rc' R T n W v}
    (hexc : Agree Ξ Ξ' n)
    (hrecv : Agree Rc Rc' n)
    (hacc : ∀ j, j < n → ∀ U args, Acc j U args ↔ Acc' j U args)
    (hres : Agree R T n) :
    PromiseWith Ξ effect Acc Rc R n W v ↔ PromiseWith Ξ' effect Acc' Rc' T n W v := by
  constructor <;> intro h
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mp)
      (fun j hj U r => (hrecv j hj U r).mpr)
      (fun j hj U args => (hacc j hj U args).mpr)
      (fun j hj U u => (hres j hj U u).mp)
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mpr)
      (fun j hj U r => (hrecv j hj U r).mp)
      (fun j hj U args => (hacc j hj U args).mp)
      (fun j hj U u => (hres j hj U u).mpr)

/-- Combining result guarantees retains the effects established for this call
domain by either premise. World-sensitive results still require the same
cross-world compatibility as ordinary arrows. Effects concern the shared final
heap, so they do not depend on which result world supplies the conclusion. -/
theorem PromiseWith.combine {effect other Acc Rc B C D k W v}
    (hs : effect.sameResult other = true)
    (hb : PromiseWith Ξ effect Acc Rc B k W v)
    (hc : PromiseWith Ξ other Acc Rc C k W v)
    (hcross : ∀ n, n < k → CrossCompatUpTo n B C D) :
    PromiseWith Ξ (effect.meet other) Acc Rc D k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨b, hib, hsb⟩ := hb j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨c, hic, hsc⟩ := hc j hj U hx hu heap hh r hrv hr args hv ha
  cases CallArguments.invoke_deterministic hib hic
  obtain ⟨hr1, hp1, hr2, hp2⟩ := Effect.meet_same hs
  rw [hr2, hp2] at hsc
  rw [hr1, hp1]
  exact ⟨b, hib, HeapObservations.weaken
    (fun heap' value hpost => (Effect.post_meet hs heap heap' value).mpr hpost)
    (cross_upto j (Effect.cross_result effect (hcross j hj)) U U heap b hh hh hsb hsc)⟩

/-- Binding saves a receiver and argument prefix, then forwards without
changing the heap. This generic rule covers fixed and variadic signatures;
only the argument-admission premise differs. The callee's effect is retained
at the heap where the forwarded call actually starts; a promise, about an
actual past the saved prefix, is about the same actual of the bound call. -/
theorem PromiseWith.bound {effect : Effect} {Acc Rest : ArgFam} {Rt R Rc : Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hkeeps : effect.keeps pre.length = true)
    (ht : PromiseWith Ξ effect Acc Rt R k W tv)
    (hRt : Adm Rt) (hRest : Adm Rest)
    (hrv : isVal rv = true) (hr : Rt k W rv) (hp : CallArguments.Values pre)
    (hprefix : ∀ j (hj : j < k) U, WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ args, Rest j U args → Acc j U (pre ++ args)) :
    PromiseWith Ξ (effect.drop pre.length) Rest Rc R k W (.objAt fs (.bound tv rv pre) oid) := by
  intro j hj U hx hu heap hh r hv _ args hargs ha
  refine ⟨_, .bound hv hargs, ?_⟩
  cases j with
  | zero => trivial
  | succ i =>
    have hi : i < k := by omega
    have hxU : WExt (trunc i (Nat.le_of_lt hi) W) (trunc i (Nat.le_succ i) U) := by
      have hx' := WExt_trunc (Nat.le_succ i) hx
      rwa [trunc_trunc] at hx'
    have hu' := WorldAdm_trunc (Nat.le_succ i) hu
    have hh' := HeapOk_trunc i U heap hh
    have hr' := hRt.mono i _ _ hxU rv (hRt.down_le k i (Nat.le_of_lt hi) W rv hr)
    have ha' := hRest.down i U args ha
    have hall : CallArguments.Values (pre ++ args) := by
      intro a hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hp a hm
      · exact hargs a hm
    obtain ⟨res, hinv, hsafe⟩ := ht i hi _ hxU hu' heap hh' rv hrv hr'
      (pre ++ args) hall (hprefix i hi _ hxU args ha')
    rw [Effect.result_drop, Effect.post_drop, Effect.promised_drop hkeeps]
    exact .inr ⟨_, heap, res, WExt_refl _, hu', hinv.step heap, hh', hsafe⟩

/-- Application consumes a qualified signature, without inspecting the
callee's implementation. Its entry heap is after actual evaluation. -/
theorem call_safe {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith Ξ effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    SafePost Ξ (effect.result R (effect.promised vs)) (effect.post heap) n W heap (.invoke f r vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    obtain ⟨body, hi, hs⟩ := hf n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) r hrv (hRc.down n W r hr)
      vs hv (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _))
    exact .inr ⟨U, heap, body, WExt_refl _, WorldAdm_trunc _ hw, hi.step heap,
      HeapOk_trunc n W heap hh, hs⟩

/-- An operational invariant that only appends fresh locations supplies
the normal-return preservation postcondition, supplementing ordinary safety.
The safety proof supplies the same worlds and result contract at every step. -/
theorem prefix_safe {P : Tm → Prop} {R : Fam}
    (hstep : ∀ {h t h' t'}, P t → Step h t h' t' → h.IsPrefix h' ∧ P t') :
    ∀ {n W heap t}, P t → Safe Ξ R n W heap t →
      SafePost Ξ R (Effect.preservesInputHeap.post heap) n W heap t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t hp hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, ⟨[], by simp⟩⟩)
    · exact .inl (.inr hth)
    · obtain ⟨hprefix, hp'⟩ := hstep hp step
      exact .inr ⟨U, h', t', hx, hu, step, hh,
        HeapObservations.weaken (fun _ _ hpost => hprefix.trans hpost) (ih hp' hs)⟩

/-- The conservative executable purity check enriches independently proved
safety. It cannot manufacture safety or a return type on its own. -/
theorem pure_safe {R : Fam} {n W heap t}
    (hp : Purity.PureRun t) (hs : Safe Ξ R n W heap t) :
    SafePost Ξ R (Effect.preservesInputHeap.post heap) n W heap t :=
  prefix_safe Purity.CollectingRun.step (.pure hp) hs

def callsT (Ξ : Fam) (L : List (Arrow Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L, PromiseWith Ξ s.effect (ArgsShort s.arguments) s.receiver s.result k W v

/-- Assemble an intersection from its individual qualified signatures. -/
theorem callsT_of_signatures {L : List (Arrow Fam)} {n W v}
    (hi : Invocable v) (hs : ∀ p ∈ L, callsT Ξ [p] n W v) : callsT Ξ L n W v :=
  ⟨hi, fun p hp => (hs p hp).2 p (List.mem_singleton_self _)⟩

theorem callsT_adm (L : List (Arrow Fam)) : Adm (callsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem callsT_erase {L : List (Arrow Fam)} {n W v} (hp : ∀ s ∈ L, s.effect.plain = true)
    (h : callsT Ξ L n W v) : Verification.callsT Ξ (L.map Arrow.plain) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  exact (h.2 s hs).erase (hp s hs)

theorem callsT_select {L n W v p} (hf : callsT Ξ L n W v) (hp : p ∈ L) :
    callsT Ξ [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

/-- A bound fixed signature keeps its effect, with the saved prefix removed
from its domain. -/
theorem callsT_bound {effect : Effect} {Rt R Rc : Fam} {Ps Ds : List Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hDs : ∀ A ∈ Ds, Adm A)
    (hkeeps : effect.keeps pre.length = true)
    (ht : callsT Ξ [⟨Rt, Ps ++ Ds, R, effect⟩] k W tv)
    (hrv : isVal rv = true) (hsr : Scoped 0 rv) (hr : Rt k W rv)
    (hp : ArgsT Ps k W pre) (hv : CallArguments.Values pre) (hsp : ∀ a ∈ pre, Scoped 0 a) :
    callsT Ξ [⟨Rc, Ds, R, effect.drop pre.length⟩] k W (.objAt fs (.bound tv rv pre) oid) := by
  refine ⟨⟨fs, _, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hm
    cases List.mem_singleton.mp hm
    exact (ht.2 _ (List.mem_singleton_self _)).bound hkeeps hRt
      (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer hDs ha j hj U hx)) hrv hr hv
      (fun j hj U hx args ha => ArgsShort_prefix (ArgsT_transfer hPs hp j (Nat.le_of_lt hj) U hx) ha)

theorem callsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → Arrow Fam) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments (g x).arguments ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : callsT Ξ (l.map f) n W v ↔ callsT Ξ' (l.map g) n W v := by
  unfold callsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr hexc (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr hexc (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr (hs (g x) (List.mem_map_of_mem hm))

/-- Fixed arguments are value families, whereas the rest is an argument-list
family. Both are operands of the same effect-qualified contract. -/
abbrev RestSignature := Contract Fam (List Fam × ArgFam) Fam

def restsT (Ξ : Fam) (L : List RestSignature) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L,
    PromiseWith Ξ s.effect (ArgsRest s.arguments.1 s.arguments.2) s.receiver s.result k W v

/-- Assemble an intersection from its individual qualified signatures. -/
theorem restsT_of_signatures {L : List (RestSignature)} {n W v}
    (hi : Invocable v) (hs : ∀ p ∈ L, restsT Ξ [p] n W v) : restsT Ξ L n W v :=
  ⟨hi, fun p hp => (hs p hp).2 p (List.mem_singleton_self _)⟩

theorem restsT_select {L n W v p} (hf : restsT Ξ L n W v) (hp : p ∈ L) :
    restsT Ξ [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

theorem restsT_adm (L : List RestSignature) : Adm (restsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem restsT_erase {L : List RestSignature} {n W v} (hp : ∀ s ∈ L, s.effect.plain = true)
    (h : restsT Ξ L n W v) :
    Verification.restsT Ξ (L.map fun s => (s.receiver, s.arguments.1, s.arguments.2, s.result)) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  exact (h.2 s hs).erase (hp s hs)

/-- Binding a variadic signature retains the same effect. A saved prefix
extending into the rest requires a contract closed under prepending those
saved values, exactly as for ordinary variadic binding. -/
theorem restsT_bound {effect : Effect} {Rt R Rc : Fam} {E : ArgFam} {Ps : List Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hE : Adm E)
    (hkeeps : effect.keeps pre.length = true)
    (ht : restsT Ξ [⟨Rt, (Ps, E), R, effect⟩] k W tv)
    (hrv : isVal rv = true) (hsr : Scoped 0 rv) (hr : Rt k W rv)
    (hp : ArgsT (Ps.take pre.length) k W (pre.take Ps.length))
    (hext : ∀ j (hj : j ≤ k) U, WExt (trunc j hj W) U →
      ∀ ys, E j U ys → E j U (pre.drop Ps.length ++ ys))
    (hv : CallArguments.Values pre) (hsp : ∀ a ∈ pre, Scoped 0 a) :
    restsT Ξ [⟨Rc, (Ps.drop pre.length, E), R, effect.drop pre.length⟩] k W (.objAt fs (.bound tv rv pre) oid) := by
  refine ⟨⟨fs, _, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hm
    cases List.mem_singleton.mp hm
    exact (ht.2 _ (List.mem_singleton_self _)).bound hkeeps hRt
      (Adm.of_transfer (fun ha j hj U hx =>
        ArgsRest_transfer (fun A hm => hPs A (List.mem_of_mem_drop hm)) hE ha j hj U hx))
      hrv hr hv (fun j hj U hx args ha => ArgsRest_prefix
        (ArgsT_transfer (fun A hm => hPs A (List.mem_of_mem_take hm)) hp j (Nat.le_of_lt hj) U hx)
        (hext j (Nat.le_of_lt hj) U hx) ha)

/-- Conjunction and overload normalization preserve every signature's effect. -/
theorem callsT_append (L M : List (Arrow Fam)) (n W v) :
    callsT Ξ (L ++ M) n W v ↔ callsT Ξ L n W v ∧ callsT Ξ M n W v := by
  simp only [callsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_append (L M : List RestSignature) (n W v) :
    restsT Ξ (L ++ M) n W v ↔ restsT Ξ L n W v ∧ restsT Ξ M n W v := by
  simp only [restsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → RestSignature) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments.1 (g x).arguments.1 ∧
      Agree (f x).arguments.2 (g x).arguments.2 n ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : restsT Ξ (l.map f) n W v ↔ restsT Ξ' (l.map g) n W v := by
  have args : ∀ x ∈ l, ∀ j, j < n → ∀ U vs,
      ArgsRest (f x).arguments.1 (f x).arguments.2 j U vs ↔
      ArgsRest (g x).arguments.1 (g x).arguments.2 j U vs := by
    intro x hx j hj U vs
    have hl := ArgsAgree_length (h x hx).2.1
    unfold ArgsRest
    rw [hl]
    exact and_congr (ArgsShort_congr (h x hx).2.1 hj U _) ((h x hx).2.2.1 j hj U _)
  unfold restsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr hexc (h x hm).1 (args x hm) (h x hm).2.2.2).mp
      (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr hexc (h x hm).1 (args x hm) (h x hm).2.2.2).mpr
      (hs (g x) (List.mem_map_of_mem hm))

end Verification.CallEffects
