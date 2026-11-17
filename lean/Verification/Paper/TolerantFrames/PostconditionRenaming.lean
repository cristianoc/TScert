import Verification.Paper.TolerantFrames.PostconditionAdmission

/-! # Capture-avoiding two-state renaming

Program names, mathematical indices and logical values have independent maps.
Only the bound namespace lifts below each binder. Regional effects participate
in the same transport, at the phase where their action is interpreted.
-/
namespace Verification.Paper.TolerantFrames.TwoState
open Verification Footprints HeapKnowledge TolerantFrames

structure Renaming where
  programs : Nat → Nat
  indices : Nat → Nat
  values : Nat → Nat

def Renaming.liftValue (σ : Renaming) : Renaming := {σ with values := liftRenaming σ.values}
def Renaming.liftIndex (σ : Renaming) : Renaming := {σ with indices := liftRenaming σ.indices}

def Renaming.encoded (σ : Renaming) (x : Nat) : Nat :=
  if x % 2 = 0 then 2 * σ.programs (x / 2) else 2 * σ.values (x / 2) + 1

def State.rename (σ : Renaming) (s : State) : State := {s with env := fun x => s.env (σ.programs x)}
def Context.rename (σ : Renaming) (c : Context) : Context :=
  {c with entry := c.entry.rename σ, current := c.current.rename σ}
def LogicalEnv.rename (σ : Renaming) (η : LogicalEnv) : LogicalEnv :=
  ⟨fun x => η.indices (σ.indices x), fun x => η.values (σ.values x)⟩

def Root.rename (σ : Renaming) : Root → Root
  | .program x => .program (σ.programs x)
  | .value x => .value (σ.values x)

def Path.rename (σ : Renaming) (p : Path) : Path := ⟨p.root.rename σ, p.fields⟩

def BaseValue.rename (σ : Renaming) : BaseValue → BaseValue
  | .root r => .root (r.rename σ)
  | .literal v => .literal v

def Value.rename (σ : Renaming) : Value → Value
  | .base v => .base (v.rename σ)
  | .converted f v => .converted f (v.rename σ)

mutual
def Term.rename (σ : Renaming) : Term → Term
  | .literal n => .literal n
  | .index x => .index (σ.indices x)
  | .path k p => .path k (p.rename σ)
  | .element k p e fs valid => .element k (p.rename σ) (e.rename σ) fs valid
  | .old t => .old (t.rename σ)

def Expression.rename (σ : Renaming) : Expression → Expression
  | .constant n => .constant n
  | .scale c t => .scale c (t.rename σ)
  | .add e f => .add (e.rename σ) (f.rename σ)
end

def BodyTerm.rename (σ : Renaming) : BodyTerm → BodyTerm
  | .index => .index
  | .element d => .element d
  | .project k fs valid => .project k fs valid
  | .free t => .free (t.rename σ)

def BodyExpression.rename (σ : Renaming) : BodyExpression → BodyExpression
  | .constant n => .constant n
  | .scale c t => .scale c (t.rename σ)
  | .add e f => .add (e.rename σ) (f.rename σ)

def Clause.rename (σ : Renaming) : Clause → Clause
  | .le e f => .le (e.rename σ) (f.rename σ)
  | .or c d => .or (c.rename σ) (d.rename σ)

def Body.rename (σ : Renaming) : Body → Body
  | .clause c => .clause (c.rename σ)
  | .and b c => .and (b.rename σ) (c.rename σ)

def Atom.rename (σ : Renaming) : Atom → Atom
  | .le e f => .le (e.rename σ) (f.rename σ)
  | .equal p v => .equal (p.rename σ) (v.rename σ)
  | .optionalEqual p f v => .optionalEqual (p.rename σ) f (v.rename σ)
  | .dense r e => .dense (r.rename σ) (e.rename σ)
  | .contents p V => .contents (p.rename σ) V
  | .element p e v => .element (p.rename σ) (e.rename σ) (v.rename σ)
  | .every p e b => .every (p.rename σ) (e.rename σ) (b.rename σ)

def Assertion.rename (σ : Renaming) : Assertion → Assertion
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (a.rename σ)
  | .and F G => .and (F.rename σ) (G.rename σ)
  | .or F G => .or (F.rename σ) (G.rename σ)
  | .existsValue F => .existsValue (F.rename σ.liftValue)
  | .separated p q => .separated (p.rename σ) (q.rename σ)
  | .apart p q => .apart (p.rename σ) (q.rename σ)
  | .fresh r => .fresh (r.rename σ.encoded)
  | .box Φ F => .box (Footprint.rename σ.encoded Φ) (F.rename σ)

def Post.rename (σ : Renaming) : Post → Post
  | .assertion F => .assertion (F.rename σ)
  | .old F => .old (F.rename σ)
  | .transition Φ => .transition (Footprint.rename σ.encoded Φ)
  | .and Q R => .and (Q.rename σ) (R.rename σ)
  | .or Q R => .or (Q.rename σ) (R.rename σ)
  | .implication Q R => .implication (Q.rename σ) (R.rename σ)
  | .forallIndex Q => .forallIndex (Q.rename σ.liftIndex)
  | .forallValue Q => .forallValue (Q.rename σ.liftValue)

theorem Root.encode_rename (r : Root) (σ : Renaming) : (r.rename σ).encode = σ.encoded r.encode := by
  cases r with
  | program x => simp [Root.rename, Root.encode, Renaming.encoded]
  | value x =>
    have hd : (2 * x + 1) / 2 = x := by omega
    simp [Root.rename, Root.encode, Renaming.encoded, Nat.add_mod, hd]

theorem mixedEnv_rename (σ : Renaming) (ρ : Env) (ν : Nat → Val) :
    (fun x => mixedEnv ρ ν (σ.encoded x)) =
      mixedEnv (fun x => ρ (σ.programs x)) (fun x => ν (σ.values x)) := by
  funext x
  by_cases hx : x % 2 = 0
  · simp [Renaming.encoded, mixedEnv, hx]
  · have hd : (2 * σ.values (x / 2) + 1) / 2 = σ.values (x / 2) := by omega
    simp [Renaming.encoded, mixedEnv, hx, Nat.add_mod, hd]

theorem LogicalEnv.rename_pushValue (σ : Renaming) (η : LogicalEnv) (v : Val) :
    ({η with values := push v η.values}).rename σ.liftValue =
      {η.rename σ with values := push v (η.rename σ).values} := by
  simp only [LogicalEnv.rename, Renaming.liftValue, liftRenaming_push]

theorem LogicalEnv.rename_pushIndex (σ : Renaming) (η : LogicalEnv) (i : Int) :
    ({η with indices := pushIndex i η.indices}).rename σ.liftIndex =
      {η.rename σ with indices := pushIndex i (η.rename σ).indices} := by
  have hi : (fun x => pushIndex i η.indices (liftRenaming σ.indices x)) =
      pushIndex i (fun x => η.indices (σ.indices x)) := by
    funext x; cases x <;> rfl
  simp only [LogicalEnv.rename, Renaming.liftIndex, hi]

theorem Root.eval_rename (σ : Renaming) (r : Root) (focus : State) (η : LogicalEnv) :
    (r.rename σ).eval focus.env η.values = r.eval (focus.rename σ).env (η.rename σ).values := by
  cases r <;> rfl

theorem Path.read_rename (σ : Renaming) (p : Path) (focus : State) (η : LogicalEnv) :
    (p.rename σ).read focus η.values = p.read (focus.rename σ) (η.rename σ).values := by
  simp only [Path.rename, Path.read, Root.eval_rename]; rfl

theorem BaseValue.eval_rename (σ : Renaming) (v : BaseValue) (focus : State) (η : LogicalEnv) :
    (v.rename σ).eval focus η.values = v.eval (focus.rename σ) (η.rename σ).values := by
  cases v with
  | root r => exact Root.eval_rename σ r focus η
  | literal _ => rfl

theorem Value.eval_rename (σ : Renaming) (v : Value) (focus : State) (η : LogicalEnv) :
    (v.rename σ).eval focus η.values = v.eval (focus.rename σ) (η.rename σ).values := by
  cases v <;> simp only [Value.rename, Value.eval, BaseValue.eval_rename]

mutual
theorem Term.eval_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (t : Term) :
    (t.rename σ).eval entry focus η = t.eval (entry.rename σ) (focus.rename σ) (η.rename σ) := by
  cases t with
  | literal _ | index _ => rfl
  | path k p => simp only [Term.rename, Term.eval, Path.read_rename]; rfl
  | element k p e fs valid =>
    simp only [Term.rename, Term.eval, Path.read_rename, Expression.eval_rename]; rfl
  | old t => exact Term.eval_rename σ entry entry η t

theorem Expression.eval_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (e : Expression) :
    (e.rename σ).eval entry focus η = e.eval (entry.rename σ) (focus.rename σ) (η.rename σ) := by
  cases e with
  | constant _ => rfl
  | scale c t => simp only [Expression.rename, Expression.eval, Term.eval_rename]
  | add e f => simp only [Expression.rename, Expression.eval, Expression.eval_rename]
end

theorem BodyTerm.eval_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) (t : BodyTerm) :
    (t.rename σ).eval entry focus η z i = t.eval (entry.rename σ) (focus.rename σ) (η.rename σ) z i := by
  cases t <;> simp only [BodyTerm.rename, BodyTerm.eval, Term.eval_rename] <;> rfl

theorem BodyExpression.eval_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) (e : BodyExpression) :
    (e.rename σ).eval entry focus η z i = e.eval (entry.rename σ) (focus.rename σ) (η.rename σ) z i := by
  induction e with
  | constant _ => rfl
  | scale c t => simp only [BodyExpression.rename, BodyExpression.eval, BodyTerm.eval_rename]
  | add e f ihe ihf => simp only [BodyExpression.rename, BodyExpression.eval, ihe, ihf]

theorem Clause.holds_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) (c : Clause) :
    (c.rename σ).Holds entry focus η z i ↔ c.Holds (entry.rename σ) (focus.rename σ) (η.rename σ) z i := by
  induction c with
  | le e f => simp only [Clause.rename, Clause.Holds, BodyExpression.eval_rename]
  | or c d ihc ihd => exact or_congr ihc ihd

theorem Body.holds_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) (b : Body) :
    (b.rename σ).Holds entry focus η z i ↔ b.Holds (entry.rename σ) (focus.rename σ) (η.rename σ) z i := by
  induction b with
  | clause c => exact Clause.holds_rename σ entry focus η z i c
  | and b c ihb ihc => exact and_congr ihb ihc

theorem Atom.holds_rename (σ : Renaming) (entry focus : State) (η : LogicalEnv) (a : Atom) :
    (a.rename σ).Holds entry focus η ↔ a.Holds (entry.rename σ) (focus.rename σ) (η.rename σ) := by
  cases a <;> simp only [Atom.rename, Atom.Holds, Path.read_rename, Root.eval_rename,
    Expression.eval_rename, Value.eval_rename, Body.holds_rename, State.rename]
  case optionalEqual p f v =>
    have hr : (p.rename σ).shared = {p.shared with root := σ.encoded p.shared.root} := by
      simp only [Path.shared, Path.rename, Root.encode_rename]
    have he := congrFun (mixedEnv_rename σ focus.env η.values) p.shared.root
    simp only [hr, optionalRead, Parity.Path.read, he, LogicalEnv.rename]

/-- Total capture-avoiding transport, with entry, mark and logical namespace
meanings preserved through modal future states. -/
theorem Assertion.holds_rename (σ : Renaming) (entry focus : State) (m : Nat) (η : LogicalEnv) (F : Assertion) :
    (F.rename σ).Holds entry focus m η ↔ F.Holds (entry.rename σ) (focus.rename σ) m (η.rename σ) := by
  induction F generalizing σ focus η with
  | truth | falsity => rfl
  | atom a => exact Atom.holds_rename σ entry focus η a
  | and F G ihF ihG => exact and_congr (ihF σ focus η) (ihG σ focus η)
  | or F G ihF ihG => exact or_congr (ihF σ focus η) (ihG σ focus η)
  | existsValue F ih =>
    simp only [Assertion.rename, Assertion.Holds, ih]
    exact exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ => by
      rw [LogicalEnv.rename_pushValue]
      rfl
  | separated p q => simp only [Assertion.rename, Assertion.Holds, Path.rename, Root.eval_rename]; rfl
  | apart p q =>
    simp only [Assertion.rename, Assertion.Holds, Parity.Apart, Parity.Path.read,
      mixedEnv_root, Root.eval_rename, State.rename]
  | fresh r =>
    simp only [Assertion.rename, Assertion.Holds, Fresh, Region.mem_rename, mixedEnv_rename,
      State.rename, LogicalEnv.rename]
  | box Φ F ih =>
    simp only [Assertion.rename, Assertion.Holds, ih]
    apply forall_congr'
    intro t
    have hact := Verification.Parity.EffectAction.rename_iff σ.encoded (Φ := Φ)
      (η := mixedEnv focus.env η.values) (s := focus.heap) (s' := t)
    rw [mixedEnv_rename] at hact
    exact imp_congr hact Iff.rfl

theorem Post.holds_rename (σ : Renaming) (c : Context) (η : LogicalEnv) (Q : Post) :
    (Q.rename σ).Holds c η ↔ Q.Holds (c.rename σ) (η.rename σ) := by
  induction Q generalizing σ η with
  | assertion F | old F => exact Assertion.holds_rename σ _ _ _ η F
  | transition Φ =>
    have hact := Verification.Parity.EffectAction.rename_iff σ.encoded (Φ := Φ)
      (η := mixedEnv c.entry.env η.values) (s := c.entry.heap) (s' := c.current.heap)
    simpa only [Verification.Parity.EffectAction, Post.rename, Post.Holds, Context.rename, State.rename, LogicalEnv.rename,
      mixedEnv_rename] using hact
  | and Q R ihQ ihR => exact and_congr (ihQ σ η) (ihR σ η)
  | or Q R ihQ ihR => exact or_congr (ihQ σ η) (ihR σ η)
  | implication Q R ihQ ihR => exact imp_congr (ihQ σ η) (ihR σ η)
  | forallIndex Q ih =>
    simp only [Post.rename, Post.Holds, ih]
    exact forall_congr' fun i => by
      rw [LogicalEnv.rename_pushIndex]
      rfl
  | forallValue Q ih =>
    simp only [Post.rename, Post.Holds, ih]
    exact forall_congr' fun v => imp_congr_right fun _ => by
      rw [LogicalEnv.rename_pushValue]
      rfl

end Verification.Paper.TolerantFrames.TwoState
