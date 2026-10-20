import Verification.Semantics.Rules

/-! Current-content assertions over the existing heap semantics. These are not
value types or ownership permissions. `SafePost` strengthens the existing safety
predicate with a heap-dependent postcondition; it uses exactly the same steps,
world extensions and heap invariant. This module establishes semantic rules,
not an extension of the source checker or its certificate format. -/
namespace Verification.HeapObservations
open Verification

abbrev Post := Heap → Val → Prop

def Observes (h : Heap) (l : Nat) (v : Val) : Prop := h[l]? = some v

def exact (v : Val) : Fam := fun _ _ u => u = v

/-- At budget zero there is no observation, just as in `Safe`. At positive
budget, termination establishes both the value type and a fact about that heap.
A throw, as in `Safe`, is an outcome with no postcondition: the facts `Q`
describe the heap a value is produced in, and a thrown value is not one.
Divergence remains permitted; this is safety with partial correctness. -/
def SafePost (Ξ : Fam) (T : Fam) (Q : Post) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      ((isVal t = true ∧ T (n + 1) W t ∧ Q h t) ∨ Thrown Ξ (n + 1) W t) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧
          HeapOk n U h' ∧ SafePost Ξ T Q n U h' t')

theorem erase {T Q} : ∀ {n W h t}, SafePost Ξ T Q n W h t → Safe Ξ T n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (⟨hv,ht,_⟩ | hr) | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl (Or.inl ⟨hv,ht⟩)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

/-- A stable contract frames its location through every modeled execution on
normal return. External calls receiving the host object rely on F1′ (T1′)
and T8 for their correspondence with this execution. A thrown outcome carries
no postcondition, so this rule supplies no link to an exceptional edge. -/
theorem stable_frame {T Q} {l : Nat} {v : Val} : ∀ {n W h t} {c : Ctr n},
    lookup W l = some c → CtrStable c v → HeapOk n W h →
    SafePost Ξ T Q n W h t →
    SafePost Ξ T (fun h' u => Q h' u ∧ h'[l]? = some v) n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t c hl hc hh hs
    rcases hs with (⟨hv, ht, hq⟩ | hr) | ⟨U, h', t', hx, hu, step, hh', hs⟩
    · exact .inl (.inl ⟨hv, ht, hq, hh.stable_value (Nat.zero_lt_succ n) hl hc⟩)
    · exact .inl (.inr hr)
    · exact .inr ⟨U, h', t', hx, hu, step, hh',
        ih (WExt_lookup hx (lookup_trunc (Nat.le_succ n) W l c hl))
          (hc.restrict (Nat.le_succ n)) hh' hs⟩

/-- A semantic stable-key requirement frames the value read at that own key
through a normally returning execution. The heap identifies the contract's
fixed value at the positive starting level. -/
theorem stable_key_frame {T Q} {keys : List PropKey} {key : PropKey}
    {n : Nat} {W : WorldT n} {h : Heap} {object t : Tm}
    (hn : 0 < n) (hk : key ∈ keys) (ho : stableKeysT keys n W object)
    (hh : HeapOk n W h) (hs : SafePost Ξ T Q n W h t) :
    ∃ (flds : List (PropKey × Nat)) (oid l : Nat) (value : Val),
      object = .objAt flds .absent oid ∧ flds.lookup key = some l ∧
      h[l]? = some value ∧
      SafePost Ξ T (fun h' u => Q h' u ∧ h'[l]? = some value) n W h t := by
  obtain ⟨flds, oid, l, c, value, he, hf, hw, hc⟩ := stableKeysT_at ho hk
  exact ⟨flds, oid, l, value, he, hf, hh.stable_value hn hw hc,
    stable_frame hw hc hh hs⟩

/-- Overload combination compares two executions of the same term. The
worlds may differ, but determinism makes the final heap and value the same.
Both executions' postconditions survive in the first result world; the
postconditions concern the shared heap, not either world's interpretation.
Result compatibility alone cannot manufacture a postcondition. -/
theorem cross_upto {B C D : Fam} {Q R : Post} : ∀ (n : Nat), CrossCompatUpTo n B C D →
    ∀ (W W' : WorldT n) (h : Heap) (t : Tm), HeapOk n W h → HeapOk n W' h →
      SafePost Ξ B Q n W h t → SafePost Ξ C R n W' h t →
        SafePost Ξ D (fun heap value => Q heap value ∧ R heap value) n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro hc W W' h t hok hok'
    rintro ((⟨hv1, hBv, hQ⟩ | hr1) | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩)
      ((⟨hv2, hCv, hR⟩ | hr2) | ⟨Z', h2, t2, -, -, hst2, hok2, hcont2⟩)
    · exact .inl (.inl ⟨hv1, hc (p + 1) (Nat.le_refl _) W W' h hok hok' t hBv hCv, hQ, hR⟩)
    · rw [hr2.not_val] at hv1; contradiction
    · exact absurd hst2 (value_no_step hv1)
    · rw [hr1.not_val] at hv2; contradiction
    · exact .inl (.inr hr1)
    · exact absurd hst2 hr1.no_step
    · exact absurd hst1 (value_no_step hv2)
    · exact absurd hst1 hr2.no_step
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact .inr ⟨Z, h1, t1, hz, huz, hst1, hok1,
        ih (fun j hj => hc j (by omega)) Z Z' h1 t1 hok1 hok2 hcont1 hcont2⟩

/-- Finite closure of the existing step relation, with its step count. This
introduces no new reduction rules. -/
inductive Steps : Nat → Heap → Tm → Heap → Tm → Prop where
  | refl : Steps 0 h t h t
  | next : Step h t h' t' → Steps k h' t' h'' t'' → Steps (k+1) h t h'' t''

/-- An ordinary arrow supplies no heap postcondition. Forgetting observations
lets its existing safety theorem be used without strengthening its meaning. -/
theorem forget {T} : ∀ {n W h t}, Safe Ξ T n W h t → SafePost Ξ T (fun _ _ => True) n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (⟨hv,ht⟩ | hr) | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl (Or.inl ⟨hv,ht,trivial⟩)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

/-- Add a postcondition entailed by the final value's type. This preserves the
same operational behavior and does not assume that the initial heap survives. -/
theorem of_value_property {T Q} (hq : ∀ n W h v, T n W v → Q h v) :
    ∀ {n W h t}, Safe Ξ T n W h t → SafePost Ξ T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (⟨hv,ht⟩ | hr) | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl (Or.inl ⟨hv,ht,hq _ _ _ _ ht⟩)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

/-- Consequence at the budgets an execution can reach. This bounded form is
what recursive call contracts need: their operands agree only below the
caller's current approximation level. -/
theorem consequence_below' {Ξ Ξ' T U : Fam} {Q R : Post} : ∀ {n},
    (∀ j, j ≤ n → ∀ W v, Ξ j W v → Ξ' j W v) →
    (∀ j, j ≤ n → ∀ W v, T j W v → U j W v) →
    (∀ h v, Q h v → R h v) →
    ∀ {W h t}, SafePost Ξ T Q n W h t → SafePost Ξ' U R n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro hexc hsub hpost W h t hs
    rcases hs with (⟨hv, ht, hq⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hsub _ (Nat.le_refl _) _ _ ht, hpost _ _ hq⟩)
    · exact .inl (.inr (hth.mono (hexc _ (Nat.le_refl _) _)))
    · exact .inr ⟨U, h', t', hx, hu, step, hh,
        ih (fun j hj => hexc j (by omega)) (fun j hj => hsub j (by omega)) hpost hs⟩

theorem consequence_below {Ξ T U : Fam} {Q R : Post} {n}
    (hsub : ∀ j, j ≤ n → ∀ W v, T j W v → U j W v)
    (hpost : ∀ h v, Q h v → R h v) {W h t} (hs : SafePost Ξ T Q n W h t) : SafePost Ξ U R n W h t :=
  consequence_below' (fun _ _ _ _ h => h) hsub hpost hs

theorem consequence {T U : Fam} {Q R : Post}
    (hsub : ∀ n W v, T n W v → U n W v) (hr : ∀ h v, Q h v → R h v) :
    ∀ {n W h t}, SafePost Ξ T Q n W h t → SafePost Ξ U R n W h t := by
  intro n W h t hs
  exact consequence_below (fun j _ => hsub j) hr hs

theorem weaken {T Q R} (hr : ∀ h v, Q h v → R h v)
    {n W h t} (hs : SafePost Ξ T Q n W h t) : SafePost Ξ T R n W h t :=
  consequence (fun _ _ _ ht => ht) hr hs

theorem value {T Q n W h v} (hv : isVal v = true) (ht : T n W v) (hq : Q h v) :
    SafePost Ξ T Q n W h v := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl (Or.inl ⟨hv,ht,hq⟩)

theorem refine_value {T Q n W h v} (hv : isVal v = true) (hq : Q h v)
    (hs : Safe Ξ T n W h v) : SafePost Ξ T Q n W h v := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨_,ht⟩ | hr) | ⟨_,_,_,_,_,step,_,_⟩
    · exact Or.inl (Or.inl ⟨hv,ht,hq⟩)
    · exact absurd hr (val_not_thrown hv)
    · exact False.elim (value_no_step hv step)

/-- Enrich an existing one-step safety rule with its actual post-state, using
operational determinism. This reuses storage preservation rather than reproving it. -/
theorem one_step {T Q n W h t h' v} (ht : isVal t = false) (hv : isVal v = true)
    (step : Step h t h' v) (hq : Q h' v) (hs : Safe Ξ T n W h t) :
    SafePost Ξ T Q n W h t := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with (⟨hval,_⟩ | hr) | ⟨U,h'',t'',hx,hu,step',hh,hs'⟩
    · simp [ht] at hval
    · exact absurd step hr.no_step
    · obtain ⟨rfl,rfl⟩ := Step_det step step'
      exact Or.inr ⟨U,h',v,hx,hu,step',hh,refine_value hv hq hs'⟩

/-- Composition passes facts about the heap actually produced by the subterm,
not facts about the initial heap. Works for every existing evaluation context. -/
theorem bind {A B : Fam} {Q R : Post} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (raise : ∀ {t v}, Raises t v → Raises (C t) v) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → SafePost Ξ A Q n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Q h' v →
        SafePost Ξ B R j U h' (C v)) → SafePost Ξ B R n W h (C t) := by
  intro n; induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro W h t hw hh hs hc
    rcases hs with (⟨hv,ha,hq⟩ | hr) | ⟨U,h',t',hx,hu,step,hh',hs'⟩
    · exact hc (p+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ha hq
    · exact Or.inl (Or.inr (hr.lift raise))
    · refine Or.inr ⟨U,h',C t',hx,hu,lift step,hh',ih U h' t' hu hh' hs' ?_⟩
      intro j hj V he hv h'' v hh'' hval ha hq
      apply hc j (by omega) V _ hv h'' v hh'' hval ha hq
      have he' := WExt_trunc hj hx
      rw [trunc_trunc] at he'
      exact WExt_trans he' he

theorem bind_value {T Q n} {W : WorldT (n+1)} {h b a}
    (hv : isVal a = true) (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : SafePost Ξ T Q n (trunc n (Nat.le_succ n) W) h (subst 0 a b)) :
    SafePost Ξ T Q (n+1) W h (.letE a b) :=
  Or.inr ⟨_,h,_,WExt_refl _,WorldAdm_trunc _ hw,.letV hv,HeapOk_trunc n W h hh,hs⟩

theorem write_new {h : Heap} {l v} (hlt : l < h.length) : Observes (h.set l v) l v := by
  simp [Observes,hlt]

/-- One object takes as many locations as it has fields; an observation of an
older one survives all of them. -/
theorem alloc_frames {h l u} (vs : List Val) (ho : Observes h l u) :
    Observes (h ++ vs) l u := by
  have hlt := (List.getElem?_eq_some_iff.mp ho).1
  simpa [Observes, List.getElem?_append_left hlt] using ho

end Verification.HeapObservations
