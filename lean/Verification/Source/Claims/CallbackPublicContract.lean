import Verification.Source.Claims.CallbackProducerReturns
import Verification.Source.Claims.CallbackTypedEntry

namespace Verification.SourceClaimJson.CallbackInferencePlan
open PositiveGraphs Footprints TolerantFrames CallEffects CallbackPreservation HeapObservations ProgramTyping PositiveRules

/-- Interpretation of an interface in the public parameter environment. A
client constrains the completed, evaluated call of the value bound to the
marked parameter. The judgment does not mention a producer graph, local
state, proposal, or particular checker's traversal. -/
def PublicDemandsWith (I : ∀ n, WorldT n → Prop)
    (domain : Nat → IndexedHeap → Tm → List Tm → Prop) (out : Interface) (entry : Env) : Prop :=
  ∀ (d : Demand), d ∈ out.demands → ∀ (s : IndexedHeap) (recv : Tm) (args : List Tm),
    I s.n s.W → domain d.parameter s recv args →
    isVal recv = true → CallArguments.Values args →
    RefsOk s.W (entry d.parameter) → RefsOk s.W recv → (∀ t ∈ args, RefsOk s.W t) →
    (∀ i x path, d.actualRoots[i]? = some (some (x,path)) →
      HeapKnowledge.readPath s.h (entry x) path = some (callEnv recv args i)) →
    ∀ k after v, Steps k s.h (.invoke (entry d.parameter) recv args) after v →
      k < s.n → isVal v = true → Supported d.support.normal entry s.h after

/-- The public row at a fixed callback signature supplies the ordinary
receiver type, fixed argument types, and declared call precondition. -/
def FixedCallbackDomain {ι : Type} (G : NormalGraph ι) (row : Arrow (Ty ι))
    (s : IndexedHeap) (recv : Tm) (args : List Tm) : Prop :=
  meaning G row.receiver s.n s.W recv ∧ ArgsShort (row.arguments.map (meaning G)) s.n s.W args ∧
    ∀ F ∈ row.effect.pre, F.HoldsAt ⟨callEnv recv args,s.h⟩ (callEnv recv args) s.h

def formalDomain {ι : Type} (G : NormalGraph ι) (inputs : List (Ty ι)) (p : Nat)
    (s : IndexedHeap) (recv : Tm) (args : List Tm) : Prop :=
  ∀ row, (inputs[p]?.bind (fixedCallbackSignature G)) = some row → FixedCallbackDomain G row s recv args

/-- The callable meaning of a separately certified receiverless declaration.
The caller binds a concrete closure to this meaning and proves its public
requirement at the actual argument values. -/
def ConditionalCall {ι : Type} (G : NormalGraph ι) (inputs : List (Ty ι))
    (result : Ty ι) (out : Interface) (self : Tm) (Allowed : ∀ n, WorldT n → Prop) : Prop :=
  ∀ (args : List Tm) (n : Nat) (W : WorldT n) (h : Heap) (I : ∀ j, WorldT j → Prop),
    (∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V) →
    Allowed n W → I n W → ArgsT (inputs.map (meaning G)) n W args →
    RootsOk W (envOf args .undef) → RefsOk W self → WorldAdm W → HeapOk n W h →
    PublicDemandsWith I (formalDomain G inputs) out (envOf args .undef) →
    SafePostExc (excOf G) (meaning G result) (fun _ _ => True) (fun _ => True) n W h (.invoke self .undef args)

end Verification.SourceClaimJson.CallbackInferencePlan
