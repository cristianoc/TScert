import Verification.Source.Claims.CallbackCallerAccepted
import Verification.Source.Claims.CallbackPublication
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackPreservation

theorem validated_demands {candidate p : Published} (h : candidate.validate = .ok p) :
    candidate = p ∧ ∀ d ∈ p.interface.demands, d.parameter < p.formals ∧
      (∀ e ∈ d.support.normal ++ d.support.exceptional, publicRegion p.formals e.1 = true) ∧
      (∀ root ∈ d.actualRoots, root.all (fun path => path.1 < p.formals) = true) := by
  unfold Published.validate Published.referencesFixedParameters at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i valid
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at valid
    cases h
    exact ⟨rfl, fun d hd => ⟨(valid d hd).1.1, (valid d hd).1.2, (valid d hd).2⟩⟩

/-- A publisher's serialized requirements contain exactly the obligations
computed by its own accepted inference and its checked forwarding sites. -/
theorem writeInterface_accepted {f : FilePlans} {i fuel dependencies p}
    (accepted : writeInterface f i fuel dependencies = .ok p) :
    ∃ fn plan source own forwarded,
      f.fr.units[i]? = some (fn,plan,source) ∧
      let marked := fn.params.zipIdx.filterMap fun (param, slot) =>
        if param.inferPreserves then some slot else none
      CallbackInferencePlan.infer f i fuel marked = .ok own ∧
      (if dependencies.isEmpty then .ok [] else check f i fuel dependencies marked) = .ok forwarded ∧
      p.name = fn.name ∧ p.position = some fn.namePos ∧
      p.receiver = fn.params.head?.any (·.name == "this") ∧
      p.formals = (fn.params.takeWhile (!·.rest)).length ∧
      p.interface.demands = (own.demands ++ forwarded).eraseDups := by
  unfold writeInterface at accepted
  split at accepted <;> try contradiction
  rename_i fn plan source unit
  dsimp only at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  generalize hi : CallbackInferencePlan.infer _ _ _ _ = ri at accepted
  cases ri with
  | error _ => contradiction
  | ok own =>
    dsimp only [bind, Except.bind] at accepted
    split at accepted
    · rename_i empty
      dsimp only [bind, Except.bind, pure, Except.pure] at accepted
      obtain ⟨rfl,_⟩ := validated_demands accepted
      exact ⟨fn, plan, source, own, [], unit, hi, by simp [empty], rfl,rfl,rfl,rfl,rfl⟩
    · rename_i nonempty
      generalize hf : check _ _ _ _ _ = rf at accepted
      cases rf with
      | error _ => contradiction
      | ok forwarded =>
        obtain ⟨rfl,_⟩ := validated_demands accepted
        exact ⟨fn, plan, source, own, forwarded, unit, hi, by simpa [nonempty] using hf,
          rfl,rfl,rfl,rfl,rfl⟩

end Verification.SourceClaimJson.CallbackInterfaceCheck
