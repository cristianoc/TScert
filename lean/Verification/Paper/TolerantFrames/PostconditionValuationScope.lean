import Verification.Paper.TolerantFrames.PostconditionScope

/-! # Separate entry/current environment agreement

Extend the existing logical-valuation agreement proof to program valuations in
both phases. Indexed heaps (including worlds and budgets) stay identical.
No inclusion between the two program scopes is required. In particular old
never reads a current-only result name, and boxes retain the same futures.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

structure State.Agrees (programs : Nat → Prop) (s t : State) : Prop where
  heap : s.heap = t.heap
  env : ∀ x, programs x → s.env x = t.env x

theorem Root.eval_valuation_agree {programs indices values η ζ ρ ρ'}
    (ha : LogicalEnv.Agrees indices values η ζ) (hp : ∀ x, programs x → ρ x = ρ' x)
    {r : Root} (hr : r.Scoped programs values) : r.eval ρ η.values = r.eval ρ' ζ.values := by
  cases r with
  | program x => exact hp x hr
  | value x => exact ha.2 x hr

theorem Path.read_valuation_agree {programs indices values η ζ s t}
    (ha : LogicalEnv.Agrees indices values η ζ) (hs : State.Agrees programs s t)
    {p : Path} (hp : p.Scoped programs values) : p.read s η.values = p.read t ζ.values := by
  simp only [Path.read, hs.heap, Root.eval_valuation_agree ha hs.env hp]

theorem BaseValue.eval_valuation_agree {programs indices values η ζ s t}
    (ha : LogicalEnv.Agrees indices values η ζ) (hs : State.Agrees programs s t)
    {v : BaseValue} (hv : v.Scoped programs values) : v.eval s η.values = v.eval t ζ.values := by
  cases v with
  | root r => exact Root.eval_valuation_agree ha hs.env hv
  | literal _ => rfl

theorem Value.eval_valuation_agree {programs indices values η ζ s t}
    (ha : LogicalEnv.Agrees indices values η ζ) (hs : State.Agrees programs s t)
    {v : Value} (hv : v.Scoped programs values) : v.eval s η.values = v.eval t ζ.values := by
  cases v <;> simp only [Value.eval, BaseValue.eval_valuation_agree ha hs hv]

mutual
theorem Term.eval_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {t : Term} (ht : t.Scoped entryPrograms programs indices values) :
    t.eval entry focus η = t.eval entry' focus' ζ := by
  cases t with
  | literal _ => rfl
  | index x => exact congrArg some (ha.1 x ht)
  | path k p | lengthPath p => simp only [Term.eval, hf.heap, Path.read_valuation_agree ha hf ht]
  | element k p i fs valid | lengthElement p i fs =>
    simp only [Term.eval, hf.heap, Path.read_valuation_agree ha hf ht.1,
      Expression.eval_valuation_agree ha he hf ht.2]
  | old t => exact Term.eval_valuation_agree ha he he ht

theorem Expression.eval_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {e : Expression} (hs : e.Scoped entryPrograms programs indices values) :
    e.eval entry focus η = e.eval entry' focus' ζ := by
  cases e with
  | constant _ => rfl
  | scale c t => simp only [Expression.eval, Term.eval_valuation_agree ha he hf hs]
  | add e f => simp only [Expression.eval, Expression.eval_valuation_agree ha he hf hs.1,
      Expression.eval_valuation_agree ha he hf hs.2]
end

theorem BodyTerm.eval_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {t : BodyTerm} (ht : t.Scoped entryPrograms programs indices values) (z : Val) (i : Int) :
    t.eval entry focus η z i = t.eval entry' focus' ζ z i := by
  cases t with
  | free t => exact Term.eval_valuation_agree ha he hf ht
  | _ => simp only [BodyTerm.eval, hf.heap]

theorem BodyExpression.eval_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {e : BodyExpression} (hs : e.Scoped entryPrograms programs indices values) (z : Val) (i : Int) :
    e.eval entry focus η z i = e.eval entry' focus' ζ z i := by
  induction e with
  | constant _ => rfl
  | scale c t => simp only [BodyExpression.eval, BodyTerm.eval_valuation_agree ha he hf hs z i]
  | add e f ihe ihf => simp only [BodyExpression.eval, ihe hs.1, ihf hs.2]

theorem Clause.holds_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {c : Clause} (hs : c.Scoped entryPrograms programs indices values) (z : Val) (i : Int) :
    c.Holds entry focus η z i ↔ c.Holds entry' focus' ζ z i := by
  induction c with
  | le e f => simp only [Clause.Holds, BodyExpression.eval_valuation_agree ha he hf hs.1 z i,
      BodyExpression.eval_valuation_agree ha he hf hs.2 z i]
  | or c d ihc ihd => exact or_congr (ihc hs.1) (ihd hs.2)

theorem Body.holds_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {b : Body} (hs : b.Scoped entryPrograms programs indices values) (z : Val) (i : Int) :
    b.Holds entry focus η z i ↔ b.Holds entry' focus' ζ z i := by
  induction b with
  | clause c => exact Clause.holds_valuation_agree ha he hf hs z i
  | and b c ihb ihc => exact and_congr (ihb hs.1) (ihc hs.2)

theorem Atom.holds_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {a : Atom} (hs : a.Scoped entryPrograms programs indices values) :
    a.Holds entry focus η ↔ a.Holds entry' focus' ζ := by
  cases a with
  | le e f => simp only [Atom.Holds, Expression.eval_valuation_agree ha he hf hs.1,
      Expression.eval_valuation_agree ha he hf hs.2]
  | equal p v => simp only [Atom.Holds, Path.read_valuation_agree ha hf hs.1,
      Value.eval_valuation_agree ha hf hs.2]
  | optionalEqual p f v =>
    simp only [Atom.Holds, optionalRead]
    rw [p.read_shared focus η.values, p.read_shared focus' ζ.values,
      Path.read_valuation_agree ha hf hs.1]
    simp only [hf.heap, Value.eval_valuation_agree ha hf hs.2]
  | dense r e => simp only [Atom.Holds, hf.heap, Root.eval_valuation_agree ha hf.env hs.1,
      Expression.eval_valuation_agree ha he hf hs.2]
  | contents p V => simp only [Atom.Holds, Path.read_valuation_agree ha hf hs]
  | element p e v => simp only [Atom.Holds, hf.heap, Path.read_valuation_agree ha hf hs.1,
      Expression.eval_valuation_agree ha he hf hs.2.1, Value.eval_valuation_agree ha hf hs.2.2]
  | every p e b => simp only [Atom.Holds, hf.heap, Path.read_valuation_agree ha hf hs.1,
      Expression.eval_valuation_agree ha he hf hs.2.1, Body.holds_valuation_agree ha he hf hs.2.2]

theorem mixedEnv_valuation_agree {programs : Nat → Prop} {indices values η ζ ρ ρ'}
    (ha : LogicalEnv.Agrees indices values η ζ) (hp : ∀ x, programs x → ρ x = ρ' x)
    {x : Nat} (hx : if x % 2 = 0 then programs (x / 2) else x / 2 < values) :
    mixedEnv ρ η.values x = mixedEnv ρ' ζ.values x := by
  unfold mixedEnv
  split
  · rename_i h; exact hp _ (by simpa [h] using hx)
  · rename_i h; exact ha.2 _ (by simpa [h] using hx)

theorem region_mem_valuation_agree {programs indices values η ζ ρ ρ'}
    (ha : LogicalEnv.Agrees indices values η ζ) (hp : ∀ x, programs x → ρ x = ρ' x)
    {r : Region} (hr : RegionScoped programs values r) (h : Heap) (l : Nat) :
    r.mem (mixedEnv ρ η.values) h l = r.mem (mixedEnv ρ' ζ.values) h l := by
  induction r with
  | field x k | fields x | cells x | path x p k | pathFields x p | pathCells x p | spine x p =>
    simp only [Region.mem, mixedEnv_valuation_agree ha hp hr]
  | cls _ | all => rfl
  | inCls r c ih => simp only [Region.mem, ih hr]

theorem action_valuation_agree {programs indices values η ζ ρ ρ'}
    (ha : LogicalEnv.Agrees indices values η ζ) (hp : ∀ x, programs x → ρ x = ρ' x)
    {Φ : Footprint} (hΦ : EffectScoped programs values Φ) (s t : IndexedHeap) :
    Action Φ (mixedEnv ρ η.values) s t ↔ Action Φ (mixedEnv ρ' ζ.values) s t := by
  have allowed : ∀ l v v', Allowed Φ (mixedEnv ρ η.values) s.h l v v' ↔
      Allowed Φ (mixedEnv ρ' ζ.values) s.h l v v' := by
    intro l v v'
    simp only [Allowed]
    apply or_congr Iff.rfl
    exact exists_congr fun e => and_congr_right fun member =>
      and_congr (by rw [region_mem_valuation_agree ha hp (hΦ e member)]) Iff.rfl
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun v =>
    imp_congr_right fun _ => exists_congr fun v' => and_congr Iff.rfl (allowed l v v')))

theorem Assertion.holds_valuation_agree {entryPrograms programs indices values η ζ entry entry' focus focus'}
    (ha : LogicalEnv.Agrees indices values η ζ)
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {F : Assertion} (hs : F.Scoped entryPrograms programs indices values) (m : Nat) :
    F.Holds entry focus m η ↔ F.Holds entry' focus' m ζ := by
  induction F generalizing indices values η ζ focus focus' with
  | truth | falsity => rfl
  | atom a => exact Atom.holds_valuation_agree ha he hf hs
  | and F G ihF ihG => exact and_congr (ihF ha hf hs.1) (ihG ha hf hs.2)
  | or F G ihF ihG => exact or_congr (ihF ha hf hs.1) (ihG ha hf hs.2)
  | existsValue F ih =>
    simp only [Assertion.Holds, hf.heap]
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ => ih (ha.pushValue v) hf hs
  | separated p q => simp only [Assertion.Holds, hf.heap, Root.eval_valuation_agree ha hf.env hs.1,
      Root.eval_valuation_agree ha hf.env hs.2]
  | apart p q => simp only [Assertion.Holds, hf.heap, Parity.Apart, Parity.Path.read, mixedEnv_root,
      Root.eval_valuation_agree ha hf.env hs.1, Root.eval_valuation_agree ha hf.env hs.2]
  | fresh r => simp only [Assertion.Holds, Fresh, hf.heap, region_mem_valuation_agree ha hf.env hs]
  | box Φ F ih =>
    simp only [Assertion.Holds]
    rw [hf.heap]
    exact forall_congr' fun t => imp_congr (action_valuation_agree ha hf.env hs.1 _ t)
      (ih ha ⟨rfl, hf.env⟩ hs.2)

theorem Post.holds_valuation_agree {entryPrograms programs indices values η ζ}
    (ha : LogicalEnv.Agrees indices values η ζ) {entry entry' focus focus' : State}
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    {Q : Post} (hs : Q.Scoped entryPrograms programs indices values) (m : Nat) :
    Q.Holds ⟨entry, focus, m⟩ η ↔ Q.Holds ⟨entry', focus', m⟩ ζ := by
  induction Q generalizing indices values η ζ with
  | assertion F => exact Assertion.holds_valuation_agree ha he hf hs m
  | old F => exact Assertion.holds_valuation_agree ha he he hs m
  | transition Φ =>
    simp only [Post.Holds, he.heap, hf.heap]
    exact action_valuation_agree ha he.env hs _ _
  | and Q R ihQ ihR => exact and_congr (ihQ ha hs.1) (ihR ha hs.2)
  | or Q R ihQ ihR => exact or_congr (ihQ ha hs.1) (ihR ha hs.2)
  | implication Q R ihQ ihR => exact imp_congr (ihQ ha hs.1) (ihR ha hs.2)
  | forallIndex Q ih => exact forall_congr' fun i => ih (ha.pushIndex i) hs
  | forallValue Q ih =>
    simp only [Post.Holds, hf.heap]
    exact forall_congr' fun v => imp_congr_right fun _ => imp_congr_right fun _ => ih (ha.pushValue v) hs

/-- Separate phase scopes, including different current-only result names. -/
theorem Post.environment_agree {entryPrograms programs indices values} {Q : Post}
    (scope : Q.Scoped entryPrograms programs indices values)
    {entry entry' focus focus' : State}
    (he : State.Agrees entryPrograms entry entry') (hf : State.Agrees programs focus focus')
    (m : Nat) (η : LogicalEnv) :
    Q.Holds ⟨entry, focus, m⟩ η ↔ Q.Holds ⟨entry', focus', m⟩ η :=
  Q.holds_valuation_agree ⟨fun _ _ => rfl, fun _ _ => rfl⟩ he hf scope m

end Verification.Paper.TolerantFrames.TwoState
