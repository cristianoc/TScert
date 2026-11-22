import Verification.Source.Claims.CallbackMarkedCopies
import Verification.Source.Claims.CallbackCallPositions
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackInferencePlan CallbackPreservation ProgramTyping ControlFlow CallArguments Footprints

theorem empty_supply {d : Demand} {entry h after} (empty : d.support.normal.isEmpty = true) :
    Supported d.support.normal entry h after := by
  have eq := List.isEmpty_iff.mp empty
  rw [eq]
  intro _ no
  cases no

theorem typedSlot_undef {ι : Type} {G : PositiveGraphs.NormalGraph ι} {Γ ρ n W i A}
    (typed : EnvOk G Γ ρ n W) (slot : Γ[i]? = some A) (only : PositiveRules.expand G A = [.undef]) :
    ρ i = .undef := represents_raw only n W _ (typed.2 i _ slot)

theorem absent_no_dispatch {h k f r args v after}
    (ok : readCall (.invoke f r args) = true)
    (heaps : ∀ (l : Nat) (x : Tm), h[l]? = some x → isVal x = true)
    (absent : f = .undef) (run : HeapObservations.Steps k h (.invoke f r args) after v)
    (finished : isVal v = true) : False := by
  obtain ⟨_,_,_,_,_,trace,invoke,_⟩ := readCall_dispatch run finished ok heaps
  have eq := trace.keepsCallee absent (by rfl)
  cases invoke <;> cases eq

/-- Rebasing a public callback can retain an actual root only if the
forwarding call names its original root and the enclosing input. -/
theorem forwarded_binding {d forwarded : Demand} {roots : RootMap} {param p x} {inner outer : Env}
    {recv args h} (mapped : d.forward param roots = some forwarded)
    (realized : RealizesRoots roots inner outer h)
    (original : ∀ p j, d.actualRoots[p]? = some (some (j,[])) → inner j = CallEffects.callEnv recv args p)
    (retained : forwarded.actualRoots[p]? = some (some (x,[]))) : outer x = CallEffects.callEnv recv args p := by
  unfold Demand.forward at mapped
  cases normal : project roots d.support.normal with
  | none => simp [normal] at mapped
  | some norm =>
    cases exceptional : project roots d.support.exceptional with
    | none => simp [normal,exceptional] at mapped
    | some exc =>
      simp [normal,exceptional] at mapped
      subst forwarded
      rw [List.getElem?_map] at retained
      obtain ⟨item,lookup,hit⟩ := Option.map_eq_some_iff.mp retained
      cases item with
      | none => contradiction
      | some pair =>
        obtain ⟨j,tail⟩ := pair
        cases get : roots j with
        | none => simp [get] at hit
        | some pair =>
          obtain ⟨x',path⟩ := pair
          simp [get] at hit
          obtain ⟨rfl,rfl,rfl⟩ := hit
          have root := realized j _ [] get
          exact (Option.some.inj root).trans (original _ _ lookup)

end Verification.SourceClaimJson.CallbackInterfaceCheck
