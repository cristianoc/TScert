import Verification.Paper.TolerantFrames.PostconditionSyntax

/-! # Logical scope and valuation agreement

Closed postcondition syntax is independent of all unused logical slots. The
proof follows both term phases, quantified bodies, and all regional effects.
In particular changing a modality's future focus never changes its entry.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

/-- Agreement on exactly the logical slots in scope. -/
def LogicalEnv.Agrees (indices values : Nat) (η ζ : LogicalEnv) : Prop :=
  (∀ i, i < indices → η.indices i = ζ.indices i) ∧
  (∀ v, v < values → η.values v = ζ.values v)

theorem LogicalEnv.Agrees.pushIndex {indices values η ζ} (h : LogicalEnv.Agrees indices values η ζ) (i : Int) :
    LogicalEnv.Agrees (indices + 1) values {η with indices := TwoState.pushIndex i η.indices}
      {ζ with indices := TwoState.pushIndex i ζ.indices} := by
  refine ⟨?_, h.2⟩
  intro x hx
  cases x with
  | zero => rfl
  | succ x => exact h.1 x (by omega)

theorem LogicalEnv.Agrees.pushValue {indices values η ζ} (h : LogicalEnv.Agrees indices values η ζ) (v : Val) :
    LogicalEnv.Agrees indices (values + 1) {η with values := push v η.values}
      {ζ with values := push v ζ.values} := by
  refine ⟨h.1, ?_⟩
  intro x hx
  cases x with
  | zero => rfl
  | succ x => exact h.2 x (by omega)

theorem Root.eval_agree {programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {r : Root} (hr : r.Scoped programs values) (ρ : Env) : r.eval ρ η.values = r.eval ρ ζ.values := by
  cases r with
  | program _ => rfl
  | value x => exact ha.2 x hr

theorem Path.read_agree {programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {p : Path} (hp : p.Scoped programs values) (s : State) : p.read s η.values = p.read s ζ.values := by
  simp only [Path.read, Root.eval_agree ha hp]

theorem BaseValue.eval_agree {programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {v : BaseValue} (hv : v.Scoped programs values) (s : State) : v.eval s η.values = v.eval s ζ.values := by
  cases v with
  | root r => exact Root.eval_agree ha hv s.env
  | literal _ => rfl

theorem Value.eval_agree {programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {v : Value} (hv : v.Scoped programs values) (s : State) : v.eval s η.values = v.eval s ζ.values := by
  cases v <;> simp only [Value.eval, BaseValue.eval_agree ha hv]

mutual
theorem Term.eval_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {t : Term} (ht : t.Scoped entryPrograms programs indices values) (entry focus : State) :
    t.eval entry focus η = t.eval entry focus ζ := by
  cases t with
  | literal _ => rfl
  | index x => exact congrArg some (ha.1 x ht)
  | path k p | lengthPath p => simp only [Term.eval, Path.read_agree ha ht]
  | element k p i fs valid | lengthElement p i fs =>
    simp only [Term.eval, Path.read_agree ha ht.1, Expression.eval_agree ha ht.2]
  | old t => exact Term.eval_agree (t := t) (programs := entryPrograms) ha ht entry entry

theorem Expression.eval_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {e : Expression} (he : e.Scoped entryPrograms programs indices values) (entry focus : State) :
    e.eval entry focus η = e.eval entry focus ζ := by
  cases e with
  | constant _ => rfl
  | scale c t => simp only [Expression.eval, Term.eval_agree ha he]
  | add e f => simp only [Expression.eval, Expression.eval_agree ha he.1, Expression.eval_agree ha he.2]
end

theorem BodyTerm.eval_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {t : BodyTerm} (ht : t.Scoped entryPrograms programs indices values) (entry focus : State) (z : Val) (i : Int) :
    t.eval entry focus η z i = t.eval entry focus ζ z i := by
  cases t with
  | free t => exact Term.eval_agree ha ht entry focus
  | _ => rfl

theorem BodyExpression.eval_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {e : BodyExpression} (he : e.Scoped entryPrograms programs indices values) (entry focus : State) (z : Val) (i : Int) :
    e.eval entry focus η z i = e.eval entry focus ζ z i := by
  induction e with
  | constant _ => rfl
  | scale c t => simp only [BodyExpression.eval, BodyTerm.eval_agree ha he]
  | add e f ihe ihf => simp only [BodyExpression.eval, ihe he.1, ihf he.2]

theorem Clause.holds_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {c : Clause} (hc : c.Scoped entryPrograms programs indices values) (entry focus : State) (z : Val) (i : Int) :
    c.Holds entry focus η z i ↔ c.Holds entry focus ζ z i := by
  induction c with
  | le e f => simp only [Clause.Holds, BodyExpression.eval_agree ha hc.1, BodyExpression.eval_agree ha hc.2]
  | or c d ihc ihd => exact or_congr (ihc hc.1) (ihd hc.2)

theorem Body.holds_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {b : Body} (hb : b.Scoped entryPrograms programs indices values) (entry focus : State) (z : Val) (i : Int) :
    b.Holds entry focus η z i ↔ b.Holds entry focus ζ z i := by
  induction b with
  | clause c => exact Clause.holds_agree ha hb entry focus z i
  | and b c ihb ihc => exact and_congr (ihb hb.1) (ihc hb.2)

theorem Atom.holds_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {a : Atom} (ha' : a.Scoped entryPrograms programs indices values) (entry focus : State) :
    a.Holds entry focus η ↔ a.Holds entry focus ζ := by
  cases a with
  | le e f => simp only [Atom.Holds, Expression.eval_agree ha ha'.1, Expression.eval_agree ha ha'.2]
  | equal p v => simp only [Atom.Holds, Path.read_agree ha ha'.1, Value.eval_agree ha ha'.2]
  | optionalEqual p f v =>
    simp only [Atom.Holds, optionalRead, p.read_shared focus, Path.read_agree ha ha'.1,
      Value.eval_agree ha ha'.2]
  | dense r e => simp only [Atom.Holds, Root.eval_agree ha ha'.1, Expression.eval_agree ha ha'.2]
  | contents p V => simp only [Atom.Holds, Path.read_agree ha ha']
  | element p e v =>
    simp only [Atom.Holds, Path.read_agree ha ha'.1, Expression.eval_agree ha ha'.2.1,
      Value.eval_agree ha ha'.2.2]
  | every p e b =>
    simp only [Atom.Holds, Path.read_agree ha ha'.1, Expression.eval_agree ha ha'.2.1,
      Body.holds_agree ha ha'.2.2]

/-- Shared encoded roots use only admitted logical value slots. -/
theorem mixedEnv_agree {programs : Nat → Prop} {indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {x : Nat} (hx : if x % 2 = 0 then programs (x / 2) else x / 2 < values) (ρ : Env) :
    mixedEnv ρ η.values x = mixedEnv ρ ζ.values x := by
  unfold mixedEnv
  split
  · rfl
  · rename_i hodd
    exact ha.2 _ (by simpa [hodd] using hx)

theorem region_mem_agree {programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {r : Region} (hr : RegionScoped programs values r) (ρ : Env) (h : Heap) (l : Nat) :
    r.mem (mixedEnv ρ η.values) h l = r.mem (mixedEnv ρ ζ.values) h l := by
  induction r with
  | field x k | fields x | cells x | path x p k | pathFields x p | pathCells x p | spine x p =>
    simp only [Region.mem, mixedEnv_agree ha hr]
  | cls _ | all => rfl
  | inCls r c ih => simp only [Region.mem, ih hr]

/-- Agreement preserves the entire action, including all regional entries. -/
theorem action_agree {programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {Φ : Footprint} (hΦ : EffectScoped programs values Φ) (ρ : Env) (s t : IndexedHeap) :
    Action Φ (mixedEnv ρ η.values) s t ↔ Action Φ (mixedEnv ρ ζ.values) s t := by
  have allowed : ∀ l v v', Allowed Φ (mixedEnv ρ η.values) s.h l v v' ↔
      Allowed Φ (mixedEnv ρ ζ.values) s.h l v v' := by
    intro l v v'
    simp only [Allowed]
    apply or_congr Iff.rfl
    exact exists_congr fun e => and_congr_right fun he =>
      and_congr (by rw [region_mem_agree ha (hΦ e he)]) Iff.rfl
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun v =>
    imp_congr_right fun _ => exists_congr fun v' => and_congr Iff.rfl (allowed l v v')))

theorem Assertion.holds_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {F : Assertion} (hF : F.Scoped entryPrograms programs indices values) (entry focus : State) (m : Nat) :
    F.Holds entry focus m η ↔ F.Holds entry focus m ζ := by
  induction F generalizing indices values η ζ focus with
  | truth | falsity => rfl
  | atom a => exact Atom.holds_agree ha hF entry focus
  | and F G ihF ihG => exact and_congr (ihF ha hF.1 focus) (ihG ha hF.2 focus)
  | or F G ihF ihG => exact or_congr (ihF ha hF.1 focus) (ihG ha hF.2 focus)
  | existsValue F ih =>
    simp only [Assertion.Holds]
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ =>
      ih (ha.pushValue v) hF focus
  | separated p q =>
    simp only [Assertion.Holds, Root.eval_agree ha hF.1, Root.eval_agree ha hF.2]
  | apart p q =>
    simp only [Assertion.Holds, Parity.Apart, Parity.Path.read, mixedEnv_root,
      Root.eval_agree ha hF.1, Root.eval_agree ha hF.2]
  | fresh r =>
    simp only [Assertion.Holds, Fresh, region_mem_agree ha hF]
  | box Φ F ih =>
    simp only [Assertion.Holds]
    exact forall_congr' fun t => imp_congr (action_agree ha hF.1 focus.env focus.heap t)
      (ih ha hF.2 {focus with heap := t})

theorem Post.holds_agree {entryPrograms programs indices values η ζ} (ha : LogicalEnv.Agrees indices values η ζ)
    {Q : Post} (hQ : Q.Scoped entryPrograms programs indices values) (c : Context) : Q.Holds c η ↔ Q.Holds c ζ := by
  induction Q generalizing indices values η ζ with
  | assertion F => exact Assertion.holds_agree ha hQ c.entry c.current c.mark
  | old F => exact Assertion.holds_agree ha hQ c.entry c.entry c.mark
  | transition Φ => exact action_agree ha hQ c.entry.env c.entry.heap c.current.heap
  | and Q R ihQ ihR => exact and_congr (ihQ ha hQ.1) (ihR ha hQ.2)
  | or Q R ihQ ihR => exact or_congr (ihQ ha hQ.1) (ihR ha hQ.2)
  | implication Q R ihQ ihR => exact imp_congr (ihQ ha hQ.1) (ihR ha hQ.2)
  | forallIndex Q ih => exact forall_congr' fun i => ih (ha.pushIndex i) hQ
  | forallValue Q ih => exact forall_congr' fun v => imp_congr_right fun _ => imp_congr_right fun _ => ih (ha.pushValue v) hQ

/-- A closed postcondition's meaning is independent of the chosen total
valuations for unused logical slots. -/
theorem Post.closed_valuation {entryPrograms programs : Nat → Prop} {Q : Post} (hQ : Q.Scoped entryPrograms programs 0 0) (c : Context) (η ζ : LogicalEnv) :
    Q.Holds c η ↔ Q.Holds c ζ :=
  Q.holds_agree ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim⟩ hQ c

end Verification.Paper.TolerantFrames.TwoState
