import Verification.Paper.TolerantFrames.ReadOnlyLocated

/-! # Read-only handles: a checked solution of the flow constraints

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
flow a component's checks read"). The checks of a component read a finite
abstraction of its executions: at each node of each code, the sites and
keys a location may have, the targets a call may reach. An untrusted
proposal gives the abstraction; it is checked as a post-fixed point of
constraints derived from the lowered graphs, so no least solution need be
computed and no solver is trusted.

- **Keys** (`KeySet`): a finite set of concrete keys, or every key
  (`any`), the abstraction of a key computed at run time. `none`, the key
  of a location no key names, is one concrete key among the others
  (`KeySet.mem_any`); a finite set is no encoding of every key.
  Inclusion (`KeySet.le`) and join (`KeySet.join`) are sound for
  membership (`KeySet.le_sound`, `KeySet.mem_join_left`,
  `KeySet.mem_join_right`).
- **Constraints** (`Constraint`): from a node to a node, a monotone
  transfer of the abstract state. A proposal is checked by one comparison
  per constraint (`checkPost`); a checked proposal meets every constraint
  (`checkPost_sound`).
- **Soundness of a checked proposal** (`realizes_along`): where a
  concrete relation realises the abstraction (`Realizes`), each concrete
  step from a realised state is covered by a constraint whose transfer is
  sound for it (`Covered`), and the abstraction's order is sound for
  realisation, every state of an execution is realised at its node: the
  proposal's state there over-approximates it. A join is a node with
  several incoming constraints, each checked into the same proposal. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-! ## Keys -/

/-- **An abstract set of keys**: finitely many concrete keys, or every key. -/
inductive KeySet where
  | some (ks : List (Option PropKey))
  | any

namespace KeySet

/-- Membership of a concrete key, `none` among them. -/
def Mem (k : Option PropKey) : KeySet → Prop
  | .some ks => k ∈ ks
  | .any => True

/-- Inclusion, checked. -/
def le : KeySet → KeySet → Bool
  | _, .any => true
  | .any, .some _ => false
  | .some ks, .some ks' => ks.all (· ∈ ks')

/-- Join. -/
def join : KeySet → KeySet → KeySet
  | .some ks, .some ks' => .some (ks ++ ks')
  | _, _ => .any

/-- **Every key is a key of `any`**, the key no key names included. -/
theorem mem_any (k : Option PropKey) : Mem k .any := trivial

/-- **Inclusion is sound for membership** (proved). -/
theorem le_sound {a b : KeySet} (h : le a b = true) {k : Option PropKey} (hk : Mem k a) :
    Mem k b := by
  cases a with
  | some ks =>
    cases b with
    | some ks' => simp only [le, List.all_eq_true, decide_eq_true_eq] at h; exact h k hk
    | any => trivial
  | any => cases b with
    | some _ => simp [le] at h
    | any => trivial

theorem mem_join_left {a b : KeySet} {k : Option PropKey} (hk : Mem k a) : Mem k (join a b) := by
  cases a <;> cases b <;> simp_all [join, Mem]

theorem mem_join_right {a b : KeySet} {k : Option PropKey} (hk : Mem k b) : Mem k (join a b) := by
  cases a <;> cases b <;> simp_all [join, Mem]

end KeySet

/-! ## Constraints and their checked solution -/

/-- **A constraint**: the abstract state at `src`, transferred, is below the
state at `dst`. -/
structure Constraint (N A : Type) where
  src : N
  dst : N
  transfer : A → A

/-- **A proposal meets every constraint**, checked: one comparison each. -/
def checkPost {N A : Type} (le : A → A → Bool) (cs : List (Constraint N A)) (sol : N → A) : Bool :=
  cs.all fun c => le (c.transfer (sol c.src)) (sol c.dst)

/-- **A checked proposal meets every constraint** (proved). -/
theorem checkPost_sound {N A : Type} {le : A → A → Bool} {cs : List (Constraint N A)} {sol : N → A}
    (h : checkPost le cs sol = true) : ∀ c ∈ cs, le (c.transfer (sol c.src)) (sol c.dst) = true := by
  simpa [checkPost] using h

/-- **The proposal realises a state**: the state is at a node, and the
proposal's abstract state there over-approximates it. -/
def Realizes {N A S : Type} (node : S → N → Prop) (γ : A → S → Prop) (sol : N → A) (s : S) : Prop :=
  ∃ n, node s n ∧ γ (sol n) s

/-- **Every concrete step is covered**: from a state at a node whose
abstraction it meets, a step reaches a state at the destination of some
constraint from that node, whose transfer it meets. -/
def Covered {N A S : Type} (R : S → S → Prop) (node : S → N → Prop) (γ : A → S → Prop)
    (cs : List (Constraint N A)) : Prop :=
  ∀ s s' n a, R s s' → node s n → γ a s → ∃ c ∈ cs, c.src = n ∧ node s' c.dst ∧ γ (c.transfer a) s'

/-- **A checked proposal over-approximates every state of an execution**
(proved): where every step is covered and the order is sound for the
abstraction, a state realised at the start is followed by states realised
at their nodes. -/
theorem realizes_along {N A S : Type} {le : A → A → Bool} {cs : List (Constraint N A)} {sol : N → A}
    {R : S → S → Prop} {q : S → Prop} {node : S → N → Prop} {γ : A → S → Prop}
    (hc : checkPost le cs sol = true) (hcov : Covered R node γ cs)
    (hle : ∀ a b s, le a b = true → γ a s → γ b s) {n : Nat} {s e : S} (hex : Ex R q n s e)
    (hs : Realizes node γ sol s) : Realizes node γ sol e :=
  hex.carry (r := Realizes node γ sol) (fun s s' _ hR ⟨m, hm, hγ⟩ => by
    obtain ⟨c, hcs, hsrc, hdst, hγ'⟩ := hcov s s' m (sol m) hR hm hγ
    subst hsrc
    exact ⟨c.dst, hdst, hle _ _ _ (checkPost_sound hc c hcs) hγ'⟩) hs

end Verification.TolerantFrames.ReadOnly
