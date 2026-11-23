import Verification.Programs.CertificateProducer
import Verification.Semantics.ExitComposition

/-! A worklist proposes entry footprints and exit footprints. Reading its
result once validates the entry and both exits of each reachable node. -/

namespace Verification.SourceClaimJson.CallbackEffectInference
open ControlFlow CallEffects Footprints CertificateProducer HeapObservations

abbrev Summary := Exits (Option Footprint)

abbrev Entries := Array (Option Footprint)

private def pointsTo (node : Node) (exit : Completion) : List (Option Nat) :=
  match exit with
  | .normal => if node.continuation == .ret then [none]
    else (successors node.continuation).map (some ∘ Target.label)
  | .exceptional => [node.handler.map Target.label]

private def boundAt (entries : Entries) (out : Summary) (exit : Completion) : Option Nat → Option Footprint
  | none => out.get exit
  | some l => entries.getD l none

private def checkFlowExit (entries : Entries) (out : Summary) (node : Node) (prior : Footprint)
    (ls : Summary) (exit : Completion) : Bool :=
  match ls.get exit with
  | none => true
  | some writes => (pointsTo node exit).all fun dest =>
    (boundAt entries out exit dest).any fun bound => (prior ++ writes).all bound.contains

private def checkFlowAt (nodes : Array Node) (locals : Array (Option Summary))
    (entries : Entries) (out : Summary) (l : Nat) : Bool :=
  match entries.getD l none with
  | none => true
  | some prior =>
    match nodes[l]?, locals.getD l none with
    | some node, some ls =>
      checkFlowExit entries out node prior ls .normal && checkFlowExit entries out node prior ls .exceptional
    | _, _ => false

def checkFlow (P : Program) (start : Nat) (locals : Array (Option Summary))
    (entries : Entries) (out : Summary) : Bool :=
  start < P.length && (entries.getD start none).isSome &&
    (List.range P.length).all (checkFlowAt P.toArray locals entries out)

private theorem flowEdge {P start locals entries out}
    (ok : checkFlow P start locals entries out = true)
    {l node prior ls writes dest} (exit : Completion)
    (hn : P[l]? = some node) (he : entries.getD l none = some prior)
    (hs : locals.getD l none = some ls) (hw : ls.get exit = some writes)
    (hd : dest ∈ pointsTo node exit) :
    ∃ bound, boundAt entries out exit dest = some bound ∧ ∀ e ∈ prior ++ writes, e ∈ bound := by
  have hcheck := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 l
    (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hn).1)
  simp only [checkFlowAt, he, List.getElem?_toArray, hn, hs, Bool.and_eq_true] at hcheck
  have hx : checkFlowExit entries out node prior ls exit = true := by
    cases exit
    · exact hcheck.1
    · exact hcheck.2
  simp only [checkFlowExit, hw] at hx
  have d := List.all_eq_true.mp hx dest hd
  cases hf : boundAt entries out exit dest with
  | none => simp [hf] at d
  | some bound =>
    refine ⟨bound, rfl, ?_⟩
    simp only [hf, Option.any_some] at d
    exact fun e he => List.contains_iff_mem.mp (List.all_eq_true.mp d e he)

/-- Local soundness at concrete invocations: every completed evaluation
from a reached graph node has an exit summary, and composing that summary
with any valid prior bounds its final heap relative to graph entry. -/
def LocalExitSound (P : Program) (start : Nat) (locals : Array (Option Summary))
    (ρ₀ : Env) (h₀ : Heap) : Prop :=
  ∀ {l node h ρ k}, Execution P k h₀ (.at start ρ₀) h (.at l ρ) → P[l]? = some node →
    ∀ {j h' t}, Steps j h (instantiate 0 ρ node.expression) h' t →
    ∀ exit : Completion, (match exit with
      | .normal => isVal t = true
      | .exceptional => ∃ v, Raises t v) →
    ∃ ls writes, locals.getD l none = some ls ∧ ls.get exit = some writes ∧
      ∀ prior : Footprint, Footprints.Post prior ρ₀ h₀ h →
        Footprints.Post (prior ++ writes).eraseDups ρ₀ h₀ h'

/-- Local evaluations whose entry, expression steps and exit fit in the run. -/
def BoundedLocalExitSound (P : Program) (start : Nat) (locals : Array (Option Summary))
    (ρ₀ : Env) (h₀ : Heap) (limit : Nat) : Prop :=
  ∀ {l node h ρ k}, Execution P k h₀ (.at start ρ₀) h (.at l ρ) → P[l]? = some node →
    ∀ {j h' t}, Steps j h (instantiate 0 ρ node.expression) h' t →
    k + 1 + j + 1 ≤ limit → ∀ exit : Completion, (match exit with
      | .normal => isVal t = true
      | .exceptional => ∃ v, Raises t v) →
    ∃ ls writes, locals.getD l none = some ls ∧ ls.get exit = some writes ∧
      ∀ prior : Footprint, Footprints.Post prior ρ₀ h₀ h →
        Footprints.Post (prior ++ writes).eraseDups ρ₀ h₀ h'

private theorem execSnoc {P n h s h' s' h'' s''} (h₁ : Execution P n h s h' s')
    (h₂ : Transition P h' s' h'' s'') : Execution P (n+1) h s h'' s'' := by
  induction h₁ with
  | refl => exact .next h₂ .refl
  | next step _ ih => exact .next step (ih h₂)

private theorem stepsSnoc {n h t h' t' h'' t''} (h₁ : Steps n h t h' t')
    (h₂ : Step h' t' h'' t'') : Steps (n+1) h t h'' t'' := by
  induction h₁ with
  | refl => exact .next h₂ .refl
  | next step _ ih => exact .next step (ih h₂)

private def Invariant (P : Program) (start : Nat) (entries : Entries) (out : Summary)
    (ρ₀ : Env) (h₀ h : Heap) (elapsed : Nat) : State → Prop
  | .at l ρ => Execution P elapsed h₀ (.at start ρ₀) h (.at l ρ) ∧
      ∃ prior, entries.getD l none = some prior ∧ Footprints.Post prior ρ₀ h₀ h
  | .eval t ρ cont handler => ∃ l node k before, P[l]? = some node ∧ node.continuation = cont ∧
      node.handler = handler ∧ Execution P k h₀ (.at start ρ₀) before (.at l ρ) ∧
      (∃ j, k + 1 + j = elapsed ∧ Steps j before (instantiate 0 ρ node.expression) h t) ∧
      ∃ prior, entries.getD l none = some prior ∧ Footprints.Post prior ρ₀ h₀ before
  | .done _ => ∃ frame, out.normal = some frame ∧ Footprints.Post frame ρ₀ h₀ h
  | .raised _ => ∃ frame, out.exceptional = some frame ∧ Footprints.Post frame ρ₀ h₀ h

private theorem evalExit {P start locals entries out ρ₀ h₀ h t ρ cont handler}
    (hc : checkFlow P start locals entries out = true)
    (sound : BoundedLocalExitSound P start locals ρ₀ h₀ limit)
    (room : elapsed + 1 ≤ limit)
    (inv : Invariant P start entries out ρ₀ h₀ h elapsed (.eval t ρ cont handler))
    (exit : Completion) {dest}
    (ends : match exit with | .normal => isVal t = true | .exceptional => ∃ v, Raises t v)
    (edge : dest ∈ pointsTo ⟨.undef, cont, handler⟩ exit) :
    ∃ bound, boundAt entries out exit dest = some bound ∧ Footprints.Post bound ρ₀ h₀ h := by
  obtain ⟨l,node,k,before,hn,hcEq,hhEq,reach,⟨j,hj,steps⟩,prior,he,hprior⟩ := inv
  obtain ⟨ls,writes,hs,hw,run⟩ := sound reach hn steps (by omega) exit ends
  have edge' : dest ∈ pointsTo node exit := by cases exit <;> simpa only [pointsTo, ← hcEq, ← hhEq] using edge
  obtain ⟨bound,hb,hsub⟩ := flowEdge hc exit hn he hs hw edge'
  exact ⟨bound,hb, (run prior hprior).mono (cl := fun _ _ => none)
    (Footprint.le_of_subset fun _ h => hsub _ (List.mem_eraseDups.mp h))
    (by intro _ _ _ _ miss; contradiction)⟩

private theorem invStep {P start locals entries out ρ₀ h₀ h s h' s'}
    (hc : checkFlow P start locals entries out = true)
    (sound : BoundedLocalExitSound P start locals ρ₀ h₀ limit)
    (room : elapsed + 1 ≤ limit)
    (inv : Invariant P start entries out ρ₀ h₀ h elapsed s)
    (step : Transition P h s h' s')
    (reach : Execution P (elapsed+1) h₀ (.at start ρ₀) h' s') :
    Invariant P start entries out ρ₀ h₀ h' (elapsed+1) s' := by
  cases step with
  | enter hn =>
    obtain ⟨hr,prior,he,hp⟩ := inv
    exact ⟨_,_,elapsed,_,hn,rfl,rfl,hr,⟨0,rfl,.refl⟩,prior,he,hp⟩
  | expr step =>
    obtain ⟨l,node,k,before,hn,hk,hx,hr,⟨j,hj,steps⟩,prior,he,hp⟩ := inv
    exact ⟨l,node,k,before,hn,hk,hx,hr,⟨j+1,by omega,stepsSnoc steps step⟩,prior,he,hp⟩
  | ret hv => exact evalExit hc sound room inv .normal (dest := none) hv (by simp [pointsTo])
  | raise hr => exact evalExit hc sound room inv .exceptional (dest := none) ⟨_,hr⟩ (by simp [pointsTo])
  | bind hv | effect hv | yesBind | noBind | yes | no | tagBind hv | handle =>
    all_goals
      refine ⟨reach,?_⟩
      first
      | apply evalExit hc sound room inv .normal (dest := some _) hv
      | apply evalExit hc sound room inv .normal (dest := some _) rfl
      | apply evalExit hc sound room inv .exceptional (dest := some _) ⟨_,by assumption⟩
      all_goals simp [pointsTo, successors]
      all_goals split <;> simp

/-- Every finite execution of the graph returning or throwing meets the
corresponding checked exit footprint, with its regions read in the closure's
entry heap and environment. -/
theorem checkFlow_execution_bounded {P start locals entries out ρ₀ h₀ h' s' n}
    (hc : checkFlow P start locals entries out = true)
    (sound : BoundedLocalExitSound P start locals ρ₀ h₀ n)
    (run : Execution P n h₀ (.at start ρ₀) h' s') (exit : Completion) (v : Val)
    (done : s' = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Footprints.Post bound ρ₀ h₀ h' := by
  have preserve {j h s h' s'} (steps : Execution P j h s h' s') :
      ∀ elapsed, elapsed + j ≤ n → Execution P elapsed h₀ (.at start ρ₀) h s →
      Invariant P start entries out ρ₀ h₀ h elapsed s → Invariant P start entries out ρ₀ h₀ h' (elapsed+j) s' := by
    induction steps with
    | refl => exact fun _ _ _ inv => inv
    | next step _ ih =>
      intro elapsed room reach inv
      have reach' := execSnoc reach step
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (elapsed+1) (by omega) reach' (invStep hc sound (by omega) inv step reach')
  have he : (entries.getD start none).isSome = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  obtain ⟨prior, hp⟩ := Option.isSome_iff_exists.mp he
  have inv := preserve run 0 (by omega) .refl ⟨.refl,prior,hp,Footprints.Post.refl ..⟩
  subst s'
  cases exit <;> exact inv

theorem checkFlow_execution {P start locals entries out ρ₀ h₀ h' s' n}
    (hc : checkFlow P start locals entries out = true)
    (sound : LocalExitSound P start locals ρ₀ h₀)
    (run : Execution P n h₀ (.at start ρ₀) h' s') (exit : Completion) (v : Val)
    (done : s' = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Footprints.Post bound ρ₀ h₀ h' := by
  exact checkFlow_execution_bounded hc (by intro l node h ρ k reach hn j h' t steps _; exact sound reach hn steps) run exit v done

/-! ### Composition of a property kept by every admitted step

The same flow certificate composes a property of heaps that each node's
evaluation keeps whenever its exit summary is admitted, the admitted
summaries closed under sub-footprints. An evaluation leaving the graph
establishes the property of that exit instead. Instantiated with "a support
is kept since entry", it gives a support kept by every completed run whose
exit bound respects it, without reading any region at a later heap. -/

/-- Whether a node's exit leaves the graph: a normal exit of a returning
node, an exceptional exit of a node without a handler. -/
def finalExit (node : Node) : Completion → Bool
  | .normal => node.continuation == .ret
  | .exceptional => node.handler.isNone

private theorem pointsTo_final {node : Node} {exit : Completion} {dest : Option Nat}
    (h : dest ∈ pointsTo node exit) : finalExit node exit = true ↔ dest = none := by
  cases exit with
  | normal =>
    simp only [pointsTo, finalExit] at h ⊢
    split at h
    · rename_i hr; simp only [List.mem_singleton] at h; simp [hr, h]
    · rename_i hr
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp h
      simp [hr]
  | exceptional =>
    simp only [pointsTo, finalExit, List.mem_singleton] at h ⊢
    subst h
    cases node.handler <;> simp

/-- Each completed evaluation of a reached node has an exit summary; when it
is admitted, the evaluation keeps `inside`, or establishes `atExit` of an
exit leaving the graph. -/
def BoundedLocalKeeps (P : Program) (start : Nat) (locals : Array (Option Summary))
    (ρ₀ : Env) (h₀ : Heap) (limit : Nat) (admit : Footprint → Prop) (inside : Heap → Prop)
    (atExit : Completion → Heap → Prop) : Prop :=
  ∀ {l node h ρ k}, Execution P k h₀ (.at start ρ₀) h (.at l ρ) → P[l]? = some node →
    ∀ {j h' t}, Steps j h (instantiate 0 ρ node.expression) h' t →
    k + 1 + j + 1 ≤ limit → ∀ exit : Completion, (match exit with
      | .normal => isVal t = true
      | .exceptional => ∃ v, Raises t v) →
    ∃ ls writes, locals.getD l none = some ls ∧ ls.get exit = some writes ∧
      (admit writes → inside h → if finalExit node exit then atExit exit h' else inside h')

private def KeepInvariant (P : Program) (start : Nat) (entries : Entries) (out : Summary)
    (ρ₀ : Env) (h₀ h : Heap) (elapsed : Nat) (admit : Footprint → Prop) (inside : Heap → Prop)
    (atExit : Completion → Heap → Prop) : State → Prop
  | .at l ρ => Execution P elapsed h₀ (.at start ρ₀) h (.at l ρ) ∧
      ∃ prior, entries.getD l none = some prior ∧ (admit prior → inside h)
  | .eval t ρ cont handler => ∃ l node k before, P[l]? = some node ∧ node.continuation = cont ∧
      node.handler = handler ∧ Execution P k h₀ (.at start ρ₀) before (.at l ρ) ∧
      (∃ j, k + 1 + j = elapsed ∧ Steps j before (instantiate 0 ρ node.expression) h t) ∧
      ∃ prior, entries.getD l none = some prior ∧ (admit prior → inside before)
  | .done _ => ∃ frame, out.normal = some frame ∧ (admit frame → atExit .normal h)
  | .raised _ => ∃ frame, out.exceptional = some frame ∧ (admit frame → atExit .exceptional h)

private def AtDest (inside : Heap → Prop) (atExit : Completion → Heap → Prop) (exit : Completion)
    (h : Heap) : Option Nat → Prop
  | none => atExit exit h
  | some _ => inside h

private theorem keepExit {P start locals entries out ρ₀ h₀ h t ρ cont handler admit inside atExit}
    (hc : checkFlow P start locals entries out = true)
    (sound : BoundedLocalKeeps P start locals ρ₀ h₀ limit admit inside atExit)
    (mono : ∀ {a b : Footprint}, (∀ e ∈ a, e ∈ b) → admit b → admit a)
    (room : elapsed + 1 ≤ limit)
    (inv : KeepInvariant P start entries out ρ₀ h₀ h elapsed admit inside atExit (.eval t ρ cont handler))
    (exit : Completion) {dest}
    (ends : match exit with | .normal => isVal t = true | .exceptional => ∃ v, Raises t v)
    (edge : dest ∈ pointsTo ⟨.undef, cont, handler⟩ exit) :
    ∃ bound, boundAt entries out exit dest = some bound ∧ (admit bound → AtDest inside atExit exit h dest) := by
  obtain ⟨l,node,k,before,hn,hcEq,hhEq,reach,⟨j,hj,steps⟩,prior,he,hprior⟩ := inv
  obtain ⟨ls,writes,hs,hw,run⟩ := sound reach hn steps (by omega) exit ends
  have edge' : dest ∈ pointsTo node exit := by cases exit <;> simpa only [pointsTo, ← hcEq, ← hhEq] using edge
  obtain ⟨bound,hb,hsub⟩ := flowEdge hc exit hn he hs hw edge'
  refine ⟨bound, hb, fun ha => ?_⟩
  have kept := run (mono (fun e he => hsub e (List.mem_append_right _ he)) ha)
    (hprior (mono (fun e he => hsub e (List.mem_append_left _ he)) ha))
  have final := pointsTo_final edge'
  cases dest with
  | none => simpa [AtDest, final.mpr rfl] using kept
  | some d =>
    have : finalExit node exit = false := by
      cases hf : finalExit node exit
      · rfl
      · exact absurd (final.mp hf) (by simp)
    simpa [AtDest, this] using kept

private theorem keepStep {P start locals entries out ρ₀ h₀ h s h' s' admit inside atExit}
    (hc : checkFlow P start locals entries out = true)
    (sound : BoundedLocalKeeps P start locals ρ₀ h₀ limit admit inside atExit)
    (mono : ∀ {a b : Footprint}, (∀ e ∈ a, e ∈ b) → admit b → admit a)
    (room : elapsed + 1 ≤ limit)
    (inv : KeepInvariant P start entries out ρ₀ h₀ h elapsed admit inside atExit s)
    (step : Transition P h s h' s')
    (reach : Execution P (elapsed+1) h₀ (.at start ρ₀) h' s') :
    KeepInvariant P start entries out ρ₀ h₀ h' (elapsed+1) admit inside atExit s' := by
  cases step with
  | enter hn =>
    obtain ⟨hr,prior,he,hp⟩ := inv
    exact ⟨_,_,elapsed,_,hn,rfl,rfl,hr,⟨0,rfl,.refl⟩,prior,he,hp⟩
  | expr step =>
    obtain ⟨l,node,k,before,hn,hk,hx,hr,⟨j,hj,steps⟩,prior,he,hp⟩ := inv
    exact ⟨l,node,k,before,hn,hk,hx,hr,⟨j+1,by omega,stepsSnoc steps step⟩,prior,he,hp⟩
  | ret hv => exact keepExit hc sound mono room inv .normal (dest := none) hv (by simp [pointsTo])
  | raise hr => exact keepExit hc sound mono room inv .exceptional (dest := none) ⟨_,hr⟩ (by simp [pointsTo])
  | bind hv | effect hv | yesBind | noBind | yes | no | tagBind hv | handle =>
    all_goals
      refine ⟨reach,?_⟩
      first
      | apply keepExit hc sound mono room inv .normal (dest := some _) hv
      | apply keepExit hc sound mono room inv .normal (dest := some _) rfl
      | apply keepExit hc sound mono room inv .exceptional (dest := some _) ⟨_,by assumption⟩
      all_goals simp [pointsTo, successors]
      all_goals split <;> simp

/-- Every finite execution returning or throwing establishes that exit's
property whenever the corresponding checked exit footprint is admitted. -/
theorem checkFlow_keeps_bounded {P start locals entries out ρ₀ h₀ h' s' n admit inside atExit}
    (hc : checkFlow P start locals entries out = true)
    (sound : BoundedLocalKeeps P start locals ρ₀ h₀ n admit inside atExit)
    (mono : ∀ {a b : Footprint}, (∀ e ∈ a, e ∈ b) → admit b → admit a)
    (initial : inside h₀)
    (run : Execution P n h₀ (.at start ρ₀) h' s') (exit : Completion) (v : Val)
    (done : s' = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ (admit bound → atExit exit h') := by
  have preserve {j h s h' s'} (steps : Execution P j h s h' s') :
      ∀ elapsed, elapsed + j ≤ n → Execution P elapsed h₀ (.at start ρ₀) h s →
      KeepInvariant P start entries out ρ₀ h₀ h elapsed admit inside atExit s →
      KeepInvariant P start entries out ρ₀ h₀ h' (elapsed+j) admit inside atExit s' := by
    induction steps with
    | refl => exact fun _ _ _ inv => inv
    | next step _ ih =>
      intro elapsed room reach inv
      have reach' := execSnoc reach step
      simpa only [Nat.add_assoc, Nat.add_comm 1] using
        ih (elapsed+1) (by omega) reach' (keepStep hc sound mono (by omega) inv step reach')
  have he : (entries.getD start none).isSome = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  obtain ⟨prior, hp⟩ := Option.isSome_iff_exists.mp he
  have inv := preserve run 0 (by omega) .refl ⟨.refl,prior,hp,fun _ => initial⟩
  subst s'
  cases exit <;> exact inv

end Verification.SourceClaimJson.CallbackEffectInference
