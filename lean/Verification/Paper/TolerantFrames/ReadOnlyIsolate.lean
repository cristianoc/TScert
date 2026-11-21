import Verification.Paper.TolerantFrames.ReadOnlyPublic
import Verification.Semantics.EvalContexts

/-! # Read-only handles: the innermost run in its context

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The calls the claim is about",
`isolate`). A term whose innermost run (`innermostGoto`) is a run of graph
code not yet entered is that run in an evaluation context
(`innermostGoto_ctx`): the client's context `K` around it, its frames
included. From such a state the program's execution is the run's
execution in `K`, until the run takes no step (`isolate`, by
`EvalCtx.steps_inv`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification HeapObservations

/-- Whether a term is a run of graph code not yet entered. -/
def isGoto : Tm → Bool
  | .goto .. => true
  | _ => false

/-- **A wrapped path's innermost run** (proved): wrapping the last element
of a path by a rebuilding that is never a run not yet entered keeps a head
that is one. -/
theorem head_wrap_goto {g : Tm → Tm} (hg : ∀ s, isGoto (g s) = false) {P : List (ComponentTag × Tm)}
    {x : ComponentTag × Tm} (h : (wrap g P).head? = some x) (hx : isGoto x.2 = true) : P.head? = some x := by
  match P, h with
  | [y], h =>
    simp only [wrap, mapLast, List.head?_cons, Option.some.injEq] at h
    subst h
    rw [hg] at hx; cases hx
  | y :: z :: zs, h => simpa [wrap, mapLast_cons_cons] using h

theorem head?_append_ne {α : Type} {l : List α} (l' : List α) (h : l ≠ []) : (l ++ l').head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem not_val {a : Tm} (h : ¬ isVal a = false) : isVal a = true := by simpa using h

/-- **The innermost run of a list of terms evaluated left to right**
(proved): where the path through the list heads at a run not yet entered,
and the rebuilding is never one, that run is on the path of the list's
first term that is not a value. -/
theorem pathArgs_innermost {c : ComponentTag} {x : ComponentTag × Tm} (hx : isGoto x.2 = true) :
    ∀ (xs : List Tm) (k : List Tm → Tm), (∀ ys, isGoto (k ys) = false) → (pathArgs Realm.empty c false k xs).head? = some x →
      ∃ (i : Nat) (a : Tm), xs[i]? = some a ∧ (∀ j, j < i → ∀ v, xs[j]? = some v → isVal v = true) ∧ isVal a = false ∧
        (path Realm.empty c false a).head? = some x
  | [], k, hk, h => by
    simp only [pathArgs, List.head?_cons, Option.some.injEq] at h
    subst h
    rw [hk] at hx; cases hx
  | a :: as, k, hk, h => by
    simp only [pathArgs] at h
    split at h
    · rename_i ha
      exact ⟨0, a, rfl, fun _ hj => absurd hj (Nat.not_lt_zero _), ha, head_wrap_goto (fun s => hk _) h hx⟩
    · rename_i ha
      obtain ⟨i, b, hb, hpre, hbv, hp⟩ := pathArgs_innermost hx as (fun ys => k (a :: ys)) (fun ys => hk _) h
      refine ⟨i + 1, b, by simpa using hb, fun j hj v hv => ?_, hbv, hp⟩
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv; exact not_val ha
      | succ j => exact hpre j (by omega) v (by simpa using hv)

/-- The context of a list position, from a context of the term there. -/
theorem argCtx {xs : List Tm} {i : Nat} {a : Tm} (hi : xs[i]? = some a) {Ka : Tm → Tm} (ha : a = Ka x) :
    i < xs.length ∧ xs = xs.set i (Ka x) := by
  refine ⟨(List.getElem?_eq_some_iff.mp hi).1, ?_⟩
  rw [← ha, set_self hi]

/-- **A term is its innermost run in a context** (proved): where the head
of a term's path is a run of graph code not yet entered, the term is that
run in an evaluation context. -/
theorem path_goto_ctx (t : Tm) :
    ∀ (c : ComponentTag) (x : ComponentTag × Tm), (path Realm.empty c false t).head? = some x → isGoto x.2 = true →
      ∃ Kx, EvalCtx Kx ∧ t = Kx x.2 := by
  induction t using Tm.induct with
  | goto E K l L d comp =>
    intro c x h hx
    simp only [path, List.head?_cons, Option.some.injEq] at h
    subst h
    exact ⟨_, .hole, rfl⟩
  | frame E K t L d k y comp _ iht =>
    intro c x h hx
    simp only [path] at h
    rw [head?_append_ne _ (wrap_ne_nil (path_ne_nil _ _))] at h
    obtain ⟨Kt, hKt, rfl⟩ := iht comp x (head_wrap_goto (fun _ => rfl) h hx) hx
    exact ⟨_, .frameC E K L d k y comp hKt, rfl⟩
  | invoke f r args ihf ihr iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := ihf c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .callL r args hK', rfl⟩
    · rename_i hf
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihr c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .callRecv args (not_val hf) hK', rfl⟩
      · rename_i hr
        obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx args _ (fun _ => rfl) h
        obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
        obtain ⟨hl, hset⟩ := argCtx hi ha
        exact ⟨_, .callArg (not_val hf) (not_val hr) hl hpre hK', by rw [← hset]⟩
  | construct f args ihf iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := ihf c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .constructL args hK', rfl⟩
    · rename_i hf
      obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx args _ (fun _ => rfl) h
      obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
      obtain ⟨hl, hset⟩ := argCtx hi ha
      exact ⟨_, .constructArg (not_val hf) hl hpre hK', by rw [← hset]⟩
  | letE a b iha _ =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .letC b hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | makeBound t r pre ns args _ _ _ iha =>
    intro c x h hx
    simp only [path] at h
    obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx args _ (fun _ => rfl) h
    obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
    obtain ⟨hl, hset⟩ := argCtx hi ha
    exact ⟨_, .makeArg hl hpre hK', by rw [← hset]⟩
  | alloc ns args iha =>
    intro c x h hx
    simp only [path] at h
    obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx args _ (fun _ => rfl) h
    obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
    obtain ⟨hl, hset⟩ := argCtx hi ha
    exact ⟨_, .makeArg hl hpre hK', by rw [← hset]⟩
  | makeView s f n ns args iha =>
    intro c x h hx
    simp only [path] at h
    obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx args _ (fun _ => rfl) h
    obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
    obtain ⟨hl, hset⟩ := argCtx hi ha
    exact ⟨_, .makeArg hl hpre hK', by rw [← hset]⟩
  | makeGraph n E K s caps k r comp ns args _ _ iha =>
    intro c x h hx
    simp only [path] at h
    obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx args _ (fun _ => rfl) h
    obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
    obtain ⟨hl, hset⟩ := argCtx hi ha
    exact ⟨_, .makeArg hl hpre hK', by rw [← hset]⟩
  | arrLit inits iha =>
    intro c x h hx
    simp only [path] at h
    obtain ⟨i, a, hi, hpre, -, hp⟩ := pathArgs_innermost hx inits _ (fun _ => rfl) h
    obtain ⟨K', hK', ha⟩ := iha a (List.mem_of_getElem? hi) c x hp hx
    obtain ⟨hl, hset⟩ := argCtx hi ha
    exact ⟨_, .arrArg hl hpre hK', by rw [← hset]⟩
  | read f a iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .readC f hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | index a key iha ihk =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .indexC1 key hK', rfl⟩
    · rename_i ha
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihk c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .indexC2 (not_val ha) hK', rfl⟩
      · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | write f a b iha ihb =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .writeC1 f b hK', rfl⟩
    · rename_i ha
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihb c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .writeC2 f (not_val ha) hK', rfl⟩
      · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | test k a iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .testC k hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | ite cnd a b ihc _ _ =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := ihc c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .iteC a b hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | arith op a b iha ihb =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .arithC1 op b hK', rfl⟩
    · rename_i ha
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihb c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .arithC2 op (not_val ha) hK', rfl⟩
      · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | elemAt a i iha ihi =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .elemC1 i hK', rfl⟩
    · rename_i ha
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihi c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .elemC2 (not_val ha) hK', rfl⟩
      · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | setElem a i v iha ihi ihv =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .setC1 i v hK', rfl⟩
    · rename_i ha
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihi c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .setC2 v (not_val ha) hK', rfl⟩
      · rename_i hi
        split at h
        · obtain ⟨K', hK', rfl⟩ := ihv c x (head_wrap_goto (fun _ => rfl) h hx) hx
          exact ⟨_, .setC3 (not_val ha) (not_val hi) hK', rfl⟩
        · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | lenOf a iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .lenC hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | spread a iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .spreadC hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | throw a iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .throwC hK', rfl⟩
    · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | merge d a b iha ihb =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .mergeC1 d b hK', rfl⟩
    · rename_i ha
      split at h
      · obtain ⟨K', hK', rfl⟩ := ihb c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .mergeC2 d (not_val ha) hK', rfl⟩
      · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | makeKey k a ihk iha =>
    intro c x h hx
    simp only [path] at h
    split at h
    · obtain ⟨K', hK', rfl⟩ := ihk c x (head_wrap_goto (fun _ => rfl) h hx) hx
      exact ⟨_, .makeKeyC1 a hK', rfl⟩
    · rename_i hk
      split at h
      · obtain ⟨K', hK', rfl⟩ := iha c x (head_wrap_goto (fun _ => rfl) h hx) hx
        exact ⟨_, .makeKeyC2 (not_val hk) hK', rfl⟩
      · simp only [List.head?_cons, Option.some.injEq] at h; subst h; cases hx
  | _ =>
    intro c x h hx
    simp only [path, List.head?_cons, Option.some.injEq] at h
    subst h; cases hx

/-- **The innermost run in its context** (proved): a term whose innermost
run is the code `m` at label `l`, slots `L`, default `d` and tag `cc` is
that run in an evaluation context. -/
theorem innermostGoto_ctx {t : Tm} {m : Code} {l : Nat} {L : List Tm} {d : Tm} {cc : ComponentTag}
    (h : innermostGoto t = some (m, l, L, d, cc)) :
    ∃ K, EvalCtx K ∧ t = K (.goto m.1 m.2 l L d cc) := by
  unfold innermostGoto at h
  split at h
  · rename_i _ E Kc l' L' d' c' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact path_goto_ctx t none _ heq rfl
  · cases h

/-- **Isolation** (proved; the draft, `isolate`): from a state whose
innermost run is the code `m` at label `l`, slots `L`, default `d` and tag
`cc`, an execution of `j` steps is that run's execution in the client's
context `K`, or reaches, by `i < j` steps of the run in `K`, a state where
the run takes no step (a value, a throw), the rest of the execution running
from `K` around it. -/
theorem isolate {t : Tm} {m : Code} {l : Nat} {L : List Tm} {d : Tm} {cc : ComponentTag}
    (h : innermostGoto t = some (m, l, L, d, cc)) :
    ∃ K, EvalCtx K ∧ t = K (.goto m.1 m.2 l L d cc) ∧
      ∀ {j : Nat} {hp hp' : Heap} {u : Tm}, Steps j hp t hp' u →
        (∃ t', Steps j hp (.goto m.1 m.2 l L d cc) hp' t' ∧ u = K t') ∨
        (∃ i h₁ t₁, i < j ∧ Steps i hp (.goto m.1 m.2 l L d cc) h₁ t₁ ∧ (∀ h₂ t₂, ¬ Step h₁ t₁ h₂ t₂) ∧
          Steps (j - i) h₁ (K t₁) hp' u) := by
  obtain ⟨K, hK, rfl⟩ := innermostGoto_ctx h
  exact ⟨K, hK, rfl, fun hs => hK.steps_inv hs⟩

end Verification.TolerantFrames.ReadOnly
