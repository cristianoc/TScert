import Verification.Source.Claims.CallbackTypicalEffects
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open PositiveRules ControlFlow CallbackOrigins CallbackInferencePlan GraphCode ProgramTyping PositiveGraphs

/-- Recover each named capture's type from an ordinary caller slot carrying
the same checked origin. The caller can retain extra compiler temporaries. -/
def CaptureSlots {ι : Type} (atBirth atCall : Slots) (Γ : List (Ty ι)) :
    List Tm → List (Ty ι) → Prop
  | [], [] => True
  | .var fromSlot :: rest, A :: types =>
    (∃ i o, namedAt atBirth fromSlot = some o ∧ namedAt atCall i = some o ∧ Γ[i]? = some A) ∧
      CaptureSlots atBirth atCall Γ rest types
  | _, _ => False

def checkCaptureSlots {ι : Type} [BEq ι] (atBirth atCall : Slots) (Γ : List (Ty ι)) :
    List Tm → List (Ty ι) → Bool
  | [], [] => true
  | .var fromSlot :: rest, A :: types =>
    ((List.range Γ.length).any fun i => (namedAt atBirth fromSlot).isSome &&
      namedAt atCall i == namedAt atBirth fromSlot && Γ[i]? == some A) &&
      checkCaptureSlots atBirth atCall Γ rest types
  | _, _ => false

theorem checkCaptureSlots_sound {ι : Type} [BEq ι] [LawfulBEq ι] {atBirth atCall Γ caps} {Cs : List (Ty ι)}
    (ok : checkCaptureSlots atBirth atCall Γ caps Cs = true) : CaptureSlots atBirth atCall Γ caps Cs := by
  induction caps generalizing Cs with
  | nil => cases Cs <;> simp_all [CaptureSlots,checkCaptureSlots]
  | cons term terms ih =>
    cases term <;> cases Cs <;> simp only [checkCaptureSlots,Bool.false_eq_true] at ok <;> try contradiction
    obtain ⟨found,tail⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨i,_,hi⟩ := List.any_eq_true.mp found
    simp only [Bool.and_eq_true,beq_iff_eq] at hi
    obtain ⟨⟨someName,equal⟩,slot⟩ := hi
    obtain ⟨o,atBirth⟩ := Option.isSome_iff_exists.mp someName
    exact ⟨⟨i,o,atBirth,equal.trans atBirth,slot⟩,ih tail⟩

/-- The checked prefix gives types only to the source inputs and computed
locals needed before the marked call. All slots still hold closed values. -/
def PartialEnv {ι : Type} (G : NormalGraph ι) (Γ : List (Option (Ty ι))) (ρ : Env)
    (n : Nat) (W : WorldT n) : Prop :=
  (∀ i, Scoped 0 (ρ i)) ∧ ∀ i A, Γ[i]?.join = some A → meaning G A n W (ρ i)

theorem PartialEnv.transfer {ι : Type} {G : NormalGraph ι} {Γ ρ n W} (typed : PartialEnv G Γ ρ n W)
    (k : Nat) (le : k ≤ n) (U : WorldT k) (ext : WExt (trunc k le W) U) : PartialEnv G Γ ρ k U :=
  ⟨typed.1,fun i A hit => (meaning_adm G A).mono _ _ _ ext _ ((meaning_adm G A).down_le _ _ le W _ (typed.2 i A hit))⟩

def visibleNames (slotTypes : List (Option (Ty ι))) (names : Slots) : Slots :=
  names.zipIdx.map fun (slot,i) => if slotTypes[i]?.join.isSome then slot else []

private theorem visibleNames_at {ι : Type} {Γ : List (Option (Ty ι))} {names i o}
    (named : namedAt (visibleNames Γ names) i = some o) :
    namedAt names i = some o ∧ Γ[i]?.join.isSome := by
  unfold namedAt visibleNames at named
  cases old : names[i]? with
  | none => simp [old] at named
  | some s =>
    cases present : Γ[i]?.join with
    | none => simp [old,present] at named
    | some A => exact ⟨by simpa [namedAt,old,present] using named, by simp⟩

private theorem denotes_unique {history entry inputs o a b}
    (left : denotes history entry inputs o a) (right : denotes history entry inputs o b) : a = b := by
  cases o with
  | input i => exact left.2.symm.trans right.2
  | allocated p =>
    obtain ⟨x,hx,ha⟩ := left
    obtain ⟨y,hy,hb⟩ := right
    rw [hx] at hy
    cases hy
    exact ha.symm.trans hb
  | _ => contradiction

theorem captureSlots_typed {ι : Type} {G : NormalGraph ι} {Γ ρ n W history entry inputs atBirth atCall allocation self}
    (typed : EnvOk G Γ ρ n W) (birth : slotsHold history entry inputs atBirth allocation)
    (now : slotsHold history entry inputs atCall ρ) (closed : Scoped 0 self) {caps Cs}
    (slots : CaptureSlots atBirth atCall Γ caps Cs) :
    EnvOk G Cs (envOf (instantiateArgs 0 allocation caps ++ [self]) .nul) n W := by
  induction caps generalizing Cs with
  | nil =>
    cases Cs with
    | nil =>
      refine ⟨?_,by simp⟩
      intro i
      cases i with
      | zero => exact closed
      | succ i => simp [instantiateArgs,envOf,Scoped]
    | cons => contradiction
  | cons term terms ih =>
    cases Cs with
    | nil => cases term <;> contradiction
    | cons A As =>
      cases term <;> try contradiction
      rename_i src
      obtain ⟨⟨i,o,ha,hb,ht⟩,tail⟩ := slots
      have equal := denotes_unique (birth src o ha).1 (now i o hb).1
      have env := (ih tail).push (typed.2 i A ht)
      rw [push_envOf] at env
      simpa [instantiateArgs,instantiate,equal] using env

theorem reached_captureTypes {ι : Type} {G : NormalGraph ι} {Γ ρ n W P table entry inputs l h mark}
    (reached : atHistory P table entry inputs mark l ρ h)
    {arg site node arity E K start caps kind rest comp ns vals Cs}
    (origin : originOf (table.at l) arg = some (.allocated site)) (lookup : P[site]? = some node)
    (literal : node.expression = .makeAt (.graph arity E K start caps kind rest comp) ns vals)
    (projected : CaptureSlots (table.at site) (table.at l) Γ caps Cs)
    (typed : EnvOk G Γ ρ n W) (closed : Scoped 0 (instantiate 0 ρ arg)) :
    ∀ fs vs oid, instantiate 0 ρ arg = .objAt fs (.graph arity E K start vs kind rest comp) oid →
      EnvOk G Cs (envOf (vs ++ [instantiate 0 ρ arg]) .nul) n W := by
  obtain ⟨hist,valid,_,_,_,held⟩ := reached
  obtain ⟨slot,rfl,atSlot⟩ := namedOrigin_slot origin
  obtain ⟨⟨b,member,equal⟩,_⟩ := held slot (.allocated site) (by simp [namedAt,atSlot])
  obtain ⟨atSite,born,named⟩ := valid site b member
  have hn := born.1
  rw [atSite,lookup] at hn
  obtain ⟨fs',oid',value⟩ := literalBirth born ((Option.some.inj hn).symm ▸ literal)
  intro fs vs oid obj
  simp only [instantiate,Nat.not_lt_zero,ite_false,Nat.sub_zero] at obj closed ⊢
  rw [← equal,value] at obj
  cases obj
  exact captureSlots_typed typed named held closed projected

theorem captureSlots_partial {ι : Type} {G : NormalGraph ι} {Γ ρ n W history entry inputs atBirth atCall allocation self}
    (typed : PartialEnv G Γ ρ n W) (birth : slotsHold history entry inputs atBirth allocation)
    (now : slotsHold history entry inputs atCall ρ) (closed : Scoped 0 self) {caps Cs}
    (slots : CaptureSlots atBirth (visibleNames Γ atCall) (Γ.map (·.getD [])) caps Cs) :
    EnvOk G Cs (envOf (instantiateArgs 0 allocation caps ++ [self]) .nul) n W := by
  induction caps generalizing Cs with
  | nil =>
    cases Cs with
    | nil =>
      refine ⟨?_,by simp⟩
      intro i
      cases i with
      | zero => exact closed
      | succ i => simp [instantiateArgs,envOf,Scoped]
    | cons => contradiction
  | cons term terms ih =>
    cases Cs with
    | nil => cases term <;> contradiction
    | cons A As =>
      cases term <;> try contradiction
      rename_i src
      obtain ⟨⟨i,o,ha,hb,ht⟩,tail⟩ := slots
      have ⟨orig,visible⟩ := visibleNames_at hb
      have typedSlot : Γ[i]?.join = some A := by
        cases e : Γ[i]? with
        | none => simp [e] at visible
        | some t => cases t <;> simp_all
      have equal := denotes_unique (birth src o ha).1 (now i o orig).1
      have env := (ih tail).push (typed.2 i A typedSlot)
      rw [push_envOf] at env
      simpa [instantiateArgs,instantiate,equal] using env

theorem reached_partialCaptureTypes {ι : Type} {G : NormalGraph ι} {Γ ρ n W P table entry inputs l h mark}
    (reached : atHistory P table entry inputs mark l ρ h)
    {arg site node arity E K start caps kind rest comp ns vals Cs}
    (origin : originOf (table.at l) arg = some (.allocated site)) (lookup : P[site]? = some node)
    (literal : node.expression = .makeAt (.graph arity E K start caps kind rest comp) ns vals)
    (projected : CaptureSlots (table.at site) (visibleNames Γ (table.at l)) (Γ.map (·.getD [])) caps Cs)
    (typed : PartialEnv G Γ ρ n W) (closed : Scoped 0 (instantiate 0 ρ arg)) :
    ∀ fs vs oid, instantiate 0 ρ arg = .objAt fs (.graph arity E K start vs kind rest comp) oid →
      EnvOk G Cs (envOf (vs ++ [instantiate 0 ρ arg]) .nul) n W := by
  obtain ⟨hist,valid,_,_,_,held⟩ := reached
  obtain ⟨slot,rfl,atSlot⟩ := namedOrigin_slot origin
  obtain ⟨⟨b,member,equal⟩,_⟩ := held slot (.allocated site) (by simp [namedAt,atSlot])
  obtain ⟨atSite,born,named⟩ := valid site b member
  have hn := born.1
  rw [atSite,lookup] at hn
  obtain ⟨fs',oid',value⟩ := literalBirth born ((Option.some.inj hn).symm ▸ literal)
  intro fs vs oid obj
  simp only [instantiate,Nat.not_lt_zero,ite_false,Nat.sub_zero] at obj closed ⊢
  rw [← equal,value] at obj
  cases obj
  exact captureSlots_partial typed named held closed projected

end Verification.SourceClaimJson.CallbackInterfaceCheck
