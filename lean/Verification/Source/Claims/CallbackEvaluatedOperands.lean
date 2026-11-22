import Verification.Source.Claims.CallbackPublicContract
import Verification.Source.Claims.CallbackCallPositions
import Verification.Semantics.KindsCalls

namespace Verification.SourceClaimJson.CallbackInferencePlan
open CallArguments HeapObservations TolerantFrames ProgramTyping PositiveGraphs PositiveRules

/-- Individual operand runs, in call evaluation order. The budget counts
all their evaluation steps, while each read uses the same heap. -/
inductive OperandRuns (h : Heap) : Nat → List Tm → List Tm → Prop where
  | nil : OperandRuns h 0 [] []
  | cons : Steps k h t h v → OperandRuns h j ts vs → OperandRuns h (k+j) (t::ts) (v::vs)

private theorem OperandRuns.prepend {h ts us vs k} (step : ArgStep h ts h' us) (eq : h' = h)
    (tail : OperandRuns h k us vs) : OperandRuns h (k+1) ts vs := by
  induction step generalizing k vs with
  | head head =>
    subst_vars
    cases tail with
    | cons run remaining => simpa [Nat.succ_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using OperandRuns.cons (.next head run) remaining
  | tail ready next ih =>
    cases tail with
    | cons run remaining => simpa [Nat.add_assoc] using OperandRuns.cons run (ih eq remaining)

private theorem fixedReadStep {h ts us} (step : ArgStep h ts h' us) (reads : ts.all Purity.readTerm = true)
    (values : ∀ (i : Nat) t, h[i]? = some t → isVal t = true) : us.all Purity.readTerm = true := by
  induction step with
  | head head =>
    obtain ⟨r,rs⟩ := Bool.and_eq_true_iff.mp reads
    exact Bool.and_eq_true_iff.mpr ⟨(Purity.read_step head r values).2,rs⟩
  | tail ready next ih =>
    obtain ⟨r,rs⟩ := Bool.and_eq_true_iff.mp reads
    exact Bool.and_eq_true_iff.mpr ⟨r,ih rs values⟩

theorem Prepared.fixedOperandRuns {h first last spent}
    (trace : Prepared h spent first last) (callee : isVal first.callee = true)
    (reads : (first.recv::first.args).all Purity.readTerm = true)
    (values : ∀ (i : Nat) t, h[i]? = some t → isVal t = true) :
    OperandRuns h spent (first.recv::first.args) (last.recv::last.args) := by
  induction trace with
  | refl =>
    have ident (ts : List Tm) : OperandRuns h 0 ts ts := by
      induction ts with | nil => exact .nil | cons _ _ ih => exact .cons (.refl) ih
    exact ident _
  | next step trace ih =>
    cases step with
    | callee st => exact (value_no_step callee st).elim
    | recv _ st =>
      have pair := Bool.and_eq_true_iff.mp reads
      exact OperandRuns.prepend (.head st) rfl (ih callee (Bool.and_eq_true_iff.mpr ⟨(Purity.read_step st pair.1 values).2,pair.2⟩))
    | args fn recv st =>
      have pair := Bool.and_eq_true_iff.mp reads
      exact OperandRuns.prepend (.tail recv st) rfl (ih callee (Bool.and_eq_true_iff.mpr ⟨pair.1,fixedReadStep st pair.2 values⟩))
    | splice fn rc eq good spliced =>
      have before := (Bool.and_eq_true_iff.mp reads).2
      rw [eq] at before
      simp [Purity.readTerm] at before


/-- Each as-yet unevaluated operand remains well typed in every reachable
world over this heap. Evaluation can therefore begin after earlier operands
have spent their part of the budget. -/
inductive OperandTypes (Ξ : Fam) (s : IndexedHeap) : List Fam → List Tm → Prop where
  | nil : OperandTypes Ξ s [] []
  | cons : (∀ (future : IndexedHeap), WorldReach s.W future.W → future.h = s.h →
      Safe Ξ A future.n future.W future.h term) →
      OperandTypes Ξ s As terms → OperandTypes Ξ s (A::As) (term::terms)

private theorem OperandTypes.transfer {Ξ s As ts} (types : OperandTypes Ξ s As ts) {u : IndexedHeap}
    (reached : WorldReach s.W u.W) (heap : u.h = s.h) : OperandTypes Ξ u As ts := by
  induction types with
  | nil => exact .nil
  | cons head tail ih => exact .cons (fun v next same => head v (reached.trans next) (same.trans heap)) ih

/-- Evaluate each operand below the remaining budget in its actual world.
The retained invariant can describe caller capture types. -/
theorem OperandRuns.typed {Ξ : Fam} {I : ∀ k, WorldT k → Prop}
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    {s : IndexedHeap} {As ts vs k} (runs : OperandRuns s.h k ts vs)
    (types : OperandTypes Ξ s As ts) (stable : ∀ A ∈ As, Adm A) (vals : Values vs)
    (initial : I s.n s.W) (room : k < s.n) :
    ∃ u : IndexedHeap, u.h = s.h ∧ u.n + k = s.n ∧ WorldReach s.W u.W ∧ I u.n u.W ∧ ArgsT As u.n u.W vs := by
  have truncInv {a b} {W : WorldT b} (le : a ≤ b) (h : I b W) : I a (trunc a le W) := by
    induction le with
    | refl => simpa only [trunc_id] using h
    | step le ih => simpa only [trunc_trunc] using ih (persist h (WExt_refl _))
  have one {s : IndexedHeap} {t v k A} (steps : Steps k s.h t s.h v)
      (safety : Safe Ξ A s.n s.W s.h t) (iv : I s.n s.W) (value : isVal v = true) (room : k < s.n) :
      ∃ u : IndexedHeap, u.h = s.h ∧ u.n + k = s.n ∧ WorldReach s.W u.W ∧ I u.n u.W ∧ A u.n u.W v := by
    cases k with
    | zero =>
      cases steps
      refine ⟨s,rfl,by simp,.refl _,iv,?_⟩
      obtain ⟨n,W,h,pos,adm,ok⟩ := s
      cases n with | zero => contradiction | succ => exact safe_value_mem value safety
    | succ k =>
      have safe := SafePostExc.of_post (R := fun _ => True) (fun _ => trivial) (of_safe safety)
      obtain ⟨j,le,U,count,ext,adm,ok,_,done⟩ := SafePostExcW.exit steps room s.adm s.ok safe (.inl value)
      rcases done with ⟨_,ty,_⟩ | ⟨err,raises,_⟩
      · have prev : j+2 ≤ s.n := by omega
        have atPrev := truncInv prev iv
        have extended : WExt (trunc (j+1) (Nat.le_succ _) (trunc (j+2) prev s.W)) U := by simpa only [trunc_trunc] using ext
        exact ⟨⟨j+1,U,s.h,by omega,adm,ok⟩,rfl,count,⟨le,ext⟩,persist atPrev extended,ty⟩
      · exact (by rw [raises_not_val raises] at value; contradiction)
  generalize hh : s.h = h at runs
  induction runs generalizing s As with
  | nil => cases types; exact ⟨s,hh,by simp,.refl _,initial,trivial⟩
  | @cons k t v j ts vs head tail ih =>
    cases types with
    | @cons A _ As _ safe rest =>
      obtain ⟨u,uh,un,uw,ui,has⟩ := one (s := s) (hh ▸ head) (safe s (.refl _) rfl) initial
        (vals _ (List.mem_cons_self ..)) (by omega)
      obtain ⟨f,fh,fn,fw,fi,fs⟩ := ih (s := u) (rest.transfer uw uh)
        (fun B mem => stable B (List.mem_cons_of_mem _ mem)) (fun b mb => vals b (List.mem_cons_of_mem _ mb)) ui (by omega) (uh.trans hh)
      obtain ⟨le,ext⟩ := fw
      have ad := stable A (List.mem_cons_self ..)
      exact ⟨f,fh,by omega,uw.trans ⟨le,ext⟩,fi,
        ad.mono _ _ _ ext _ (ad.down_le _ _ le _ _ has),fs⟩

end Verification.SourceClaimJson.CallbackInferencePlan
