import Verification.Semantics.ContractExits

/-! # Callable contracts

The callable type's contract of a signature, read through its specification
per completion (`Exits.exitPostW`, the note's Call on both exits): the
native-contract condition at the signature's precondition and result, its
normal and exceptional exits instantiated at each call. The signature's
effect and the native-contract condition are in `EffectSignatures`. -/
namespace Verification.CallEffects
open HeapObservations

/-- **The arrow equation** (the note's Call on both exits): the
native-contract condition at a signature's precondition (`Effect.Requires`),
its result (`Effect.result`) and its specification per completion, each exit
instantiated at the call and read from the call's entry world and heap
(`Exits.exitPostW`). The effect is per signature: one overload may preserve
its input heap while another overload of the same value does not. -/
def PromiseWith (Ξ : Fam) (effect : Effect) (Acc : ArgFam) (Rc R : Fam) (k : Nat) (W : WorldT k)
    (v : Val) : Prop :=
  NativeContract Ξ Acc Rc effect.Requires (fun _ args => effect.result R (effect.promised args))
    (fun r args _ U heap => effect.schema.exitPostW .normal r args U heap)
    (fun r args _ U heap => effect.schema.exitPostW .exceptional r args U heap) k W v

/-- **The arrow equation read at the signature's postconditions**
(`NativeContract.iff_exits`): the normal one `Effect.postW`, the throw's
`Effect.excPostW`. -/
theorem PromiseWith.iff_legacy {Ξ : Fam} {effect : Effect} {Acc : ArgFam} {Rc R : Fam} {k : Nat} {W : WorldT k}
    {v : Val} :
    PromiseWith Ξ effect Acc Rc R k W v ↔
      NativeContract Ξ Acc Rc effect.Requires (fun _ args => effect.result R (effect.promised args))
        (fun r args _ U heap => effect.postW r args U heap)
        (fun r args _ _ heap => (effect.excPostW r args heap).liftV) k W v :=
  NativeContract.iff_exits.symm

/-- A heap effect's signature is an ordinary arrow once its postcondition is
forgotten. A promise's is not: its result operand is not the result's type;
nor is a precondition's, which an ordinary call does not establish. -/
theorem PromiseWith.erase {effect Acc Rc R k W v} (hp : effect.plain = true)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : Promise Ξ Acc Rc R k W v := by
  intro j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha
  obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha
    (Effect.requires_none (Effect.plain_requires hp) (Effect.plain_pre hp) r args heap)
  dsimp only at hs
  rw [Effect.result_plain hp] at hs
  exact ⟨result, hi, SafePostW.erase (SafePostExcV.post hs)⟩

theorem PromiseWith.down {effect Acc Rc R n W v}
    (h : PromiseWith Ξ effect Acc Rc R (n + 1) W v) :
    PromiseWith Ξ effect Acc Rc R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha hq
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh hvr r hrv hr hrr args hv har ha hq

theorem PromiseWith.mono {effect Acc Rc R n W W' v} (hx : WExt W W')
    (h : PromiseWith Ξ effect Acc Rc R n W v) : PromiseWith Ξ effect Acc Rc R n W' v := by
  intro j hj U hy hu heap hh hvr r hrv hr hrr args hv har ha hq
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh hvr r hrv hr hrr args hv har ha hq

/-- Effect coverage is implication of the normal-return postcondition and of
what the result meets, at every result operand. There is deliberately no rule
relating a promise to a signature without one, whose result operands mean
different things. -/
def Effect.Covers (source target : Effect) : Prop :=
  (∀ r args j (U : WorldT j) before k (W' : WorldT k) after value,
    source.postW r args U before k W' after value → target.postW r args U before k W' after value) ∧
  (∀ R args k W u, source.result R (source.promised args) k W u → target.result R (target.promised args) k W u) ∧
  (∀ r args before after, source.excPost r args before after → target.excPost r args before after) ∧
  ∀ r args heap, target.Requires r args heap → source.Requires r args heap

/-- A precondition implying another's: none, or a predicate at most the
other's. -/
def requiresCovers : Option ElemPred → Option ElemPred → Bool
  | none, _ => true
  | some a, some b => b.le a
  | some _, none => false

/-- An elements promise implying another's: the other states none, or a
predicate at least this one's. -/
def elementsCovers : Option ElemPred → Option ElemPred → Bool
  | _, none => true
  | some a, some b => a.le b
  | none, some _ => false

/-- A precondition on the call's values implying another's: each fact of the
other's is one of this one's. -/
def preCovers (a b : List HeapKnowledge.IndexFact) : Bool := a.all b.contains

/-- A postcondition implying another: each of the other's facts is one of its facts. -/
def ensuresCovers (a b : List HeapKnowledge.IndexFact) : Bool := b.all a.contains

theorem requiresCovers_sound {a b : Effect} (h : requiresCovers a.requires b.requires = true)
    (hp : preCovers a.pre b.pre = true) {r args heap}
    (hb : b.Requires r args heap) : a.Requires r args heap := by
  refine ⟨fun R hR => ?_, fun F hF => hb.2 F (List.contains_iff_mem.mp (List.all_eq_true.mp hp F hF))⟩
  rw [hR] at h
  cases hq : b.requires with
  | none => rw [hq] at h; cases h
  | some R' => rw [hq] at h; exact (hb.1 R' hq).mono h

theorem elementsCovers_sound {a b : Effect} (h : elementsCovers a.elements b.elements = true) {r after} {v : Tm}
    (ha : ∀ R, a.elements = some R → v = .tru → ElemsAt R r after) :
    ∀ R, b.elements = some R → v = .tru → ElemsAt R r after := by
  intro R hR hv
  rw [hR] at h
  cases hq : a.elements with
  | none => rw [hq] at h; cases h
  | some R' => rw [hq] at h; exact (ha R' hq hv).mono h

/-- A frame within another's. Where the other states no store regions:
a smaller coarse bound; the receiver's store excepted only where the other
excepts it and not the receiver's own locations, or lets everything change;
and the receiver's own locations excepted only where the other excepts them
or lets everything change. Where it states store regions, which add the
locations they select, each entry of the frame lies in one of the other's
(`Footprint.le`), or the other's closed bound lets everything change. -/
def Effect.frameCovers (a b : Effect) : Bool :=
  if b.regions.isEmpty then
    a.footprint.le b.footprint &&
      (!a.receiverStore || (b.receiverStore && !b.receiverOwn) || b.footprint == .top) &&
      (!a.receiverOwn || b.receiverOwn || b.footprint == .top)
  else Footprints.Footprint.le (fun _ _ => none) a.frame b.frame || b.closed == .top

theorem Effect.frameCovers_sound {a b : Effect} (h : a.frameCovers b = true) {r : Tm} {args : List Tm}
    {before after : Heap} (hwa : a.within r args before after) : b.within r args before after := by
  unfold Effect.frameCovers at h
  split at h
  · rename_i hb
    have hbr : b.regions = [] := List.isEmpty_iff.mp hb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hle, hs⟩, hw⟩ := h
    have htop_of : b.footprint = .top → b.within r args before after := fun ht =>
      Effect.within_of_footprint hbr (by rw [ht]; exact Effect.within_top hwa)
    by_cases hao : a.receiverOwn = true
    · simp only [hao, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hw
      rcases hw with hbo | htop
      · exact Effect.within_of_own hbr hbo ((Effect.within_outside_own hwa hao).mono hle)
          ((Effect.within_inside_own hwa hao).mono (Effect.ownChange_le hle))
      · exact htop_of htop
    · simp only [Bool.not_eq_true] at hao
      by_cases has : a.receiverStore = true
      · simp only [has, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          Bool.not_eq_true'] at hs
        rcases hs with ⟨hbs, hbo⟩ | htop
        · exact Effect.within_of_store hbr hbo hbs ((Effect.within_outside_store hwa hao).mono hle)
        · exact htop_of htop
      · simp only [Bool.not_eq_true] at has
        cases hbo : b.receiverOwn
        · cases hbs : b.receiverStore
          · exact Effect.within_of_footprint hbr ((Effect.within_holds hwa has hao).mono hle)
          · exact Effect.within_of_store hbr hbo hbs
              (((Effect.within_holds hwa has hao).mono hle).on _)
        · exact Effect.within_of_own hbr hbo (((Effect.within_holds hwa has hao).mono hle).on _)
            ((((Effect.within_holds hwa has hao).mono hle).mono b.le_ownChange).on _)
  · simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with hle | htop
    · exact Footprints.Post.mono hle (fun _ _ _ _ hc => by cases hc) hwa
    · apply Effect.within_of_holds
      rw [htop]
      exact Effect.within_top hwa

/-- A frame within the other's and the same promise; a fresh result, or a
fresh object, where the other states one; `onThrow` where the other states
it; a weaker precondition and stronger promises. -/
def Effect.covers (a b : Effect) : Bool :=
  a.frameCovers b && a.promise == b.promise && (!b.fresh || a.fresh) && (!b.onThrow || a.onThrow) &&
    (!b.freshObject || a.freshObject) &&
    requiresCovers a.requires b.requires && elementsCovers a.elements b.elements && preCovers a.pre b.pre &&
    ensuresCovers a.ensures b.ensures && (!b.receiverGrows || a.receiverGrows) &&
    (b.elementWrite.isNone || a.elementWrite == b.elementWrite)

theorem Effect.covers_sound {a b : Effect} (h : a.covers b = true) : a.Covers b := by
  simp only [Effect.covers, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfc, hp⟩, hf⟩, ho⟩, hfo⟩, hrq⟩, hel⟩, hpre⟩, hens⟩, hgr⟩, hwr⟩ := h
  simp only [beq_iff_eq] at hp
  have hwrite : ∀ w, b.elementWrite = some w → a.elementWrite = some w := fun w hb => by
    simp only [hb, Option.isNone_some, Bool.false_or, beq_iff_eq] at hwr; exact hwr
  refine ⟨fun r args j U before k W' after v ⟨⟨hw, hfr, hfro, hels, hen, hga, hwa⟩, hview⟩ =>
      ⟨⟨Effect.frameCovers_sound hfc hw, fun hb => hfr ?_,
      fun hb => hfro ?_, elementsCovers_sound hel hels,
      fun F hF => hen F (List.contains_iff_mem.mp (List.all_eq_true.mp hens F hF)),
      fun hb => hga (by simp only [hb, Bool.not_true, Bool.false_or] at hgr; exact hgr),
      fun w hb => hwa w (hwrite w hb)⟩, fun w hb => hview w (hwrite w hb)⟩,
    fun R args k W u hu => ?_, fun r args before after he hb => Effect.frameCovers_sound hfc (he ?_),
    fun r args heap hq => requiresCovers_sound hrq hpre hq⟩
  · rw [hb] at hf; simpa using hf
  · rw [hb] at hfo; simpa using hfo
  · simpa [Effect.result, Effect.promised, hp] using hu
  · rw [hb] at ho; simpa using ho

/-- Whether binding `n` actuals of a signature keeps what it guarantees and
the bound signature covers `b`. -/
def Effect.bindCovers (n : Nat) (a b : Effect) : Bool := a.keeps n && (a.drop n).covers b

theorem Effect.bindCovers_keeps {n : Nat} {a b : Effect} (h : a.bindCovers n b = true) : a.keeps n = true := by
  simp only [Effect.bindCovers, Bool.and_eq_true] at h; exact h.1

theorem Effect.bindCovers_covers {n : Nat} {a b : Effect} (h : a.bindCovers n b = true) :
    (a.drop n).covers b = true := by
  simp only [Effect.bindCovers, Bool.and_eq_true] at h; exact h.2

theorem Effect.Covers.refl (e : Effect) : e.Covers e :=
  ⟨fun _ _ _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h⟩

/-- Two executions' results combine as the results of their operands do. -/
theorem Effect.cross_result (e : Effect) {B C D : Fam} {a : Tm} {n}
    (h : CrossCompatUpTo n B C D) : CrossCompatUpTo n (e.result B a) (e.result C a) (e.result D a) := by
  intro j hj W W' heap hok hok' u hb hc
  unfold Effect.result at hb hc ⊢
  match hp : e.promise with
  | none => rw [hp] at hb hc; exact h j hj W W' heap hok hok' u hb hc
  | some (.guards _) =>
    rw [hp] at hb hc
    rcases hb with ⟨rfl, hb⟩ | rfl
    · rcases hc with ⟨-, hc⟩ | hc
      · exact .inl ⟨rfl, h j hj W W' heap hok hok' a hb hc⟩
      · cases hc
    · exact .inr rfl
  | some (.asserts _) =>
    rw [hp] at hb hc
    exact ⟨hb.1, h j hj W W' heap hok hok' a hb.2 hc.2⟩

theorem PromiseWith.weaken' {Ξ Ξ' : Fam} {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hexc : ∀ j, j < k → ∀ U u, Ξ j U u → Ξ' j U u)
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ' effect' Acc' Rc' T k W v := by
  rw [PromiseWith.iff_legacy] at h ⊢
  intro j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha hq
  obtain ⟨result, hi, hs⟩ :=
    h j hj U hx hu heap hh hvr r hrv (hrecv j hj U r hr) hrr args hv har (hacc j hj U args ha) (he.2.2.2 r args heap hq)
  exact ⟨result, hi, SafePostExcV.iff_lift.mpr <| SafePostExcW.consequence_below' (fun m hm => hexc m (by omega))
    (fun m hm U' u hu => he.2.1 T args m U' u
      (Effect.result_mono effect (hres m (by omega) U') (hres m (by omega) U') hu))
    (fun m _ => he.1 r args j U heap m) (fun _ _ _ h' => he.2.2.1 r args heap h') (SafePostExcV.iff_lift.mp hs)⟩

theorem PromiseWith.weaken {Ξ : Fam} {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ effect' Acc' Rc' T k W v :=
  h.weaken' he (fun _ _ _ _ h => h) hrecv hacc hres

/-- Receiver restriction may depend on the calling world, without changing effects. -/
theorem PromiseWith.weaken_recv {effect : Effect} {Acc : ArgFam} {Rc Rc' R : Fam}
    {k W v}
    (hrecv : ∀ j (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ r, Rc' j U r → Rc j U r)
    (h : PromiseWith Ξ effect Acc Rc R k W v) : PromiseWith Ξ effect Acc Rc' R k W v := by
  intro j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha hq
  exact h j hj U hx hu heap hh hvr r hrv (hrecv j hj U hx r hr) hrr args hv har ha hq

theorem PromiseWith.congr {Ξ Ξ' : Fam} {effect Acc Acc' Rc Rc' R T n W v}
    (hexc : Agree Ξ Ξ' n)
    (hrecv : Agree Rc Rc' n)
    (hacc : ∀ j, j < n → ∀ U args, Acc j U args ↔ Acc' j U args)
    (hres : Agree R T n) :
    PromiseWith Ξ effect Acc Rc R n W v ↔ PromiseWith Ξ' effect Acc' Rc' T n W v := by
  constructor <;> intro h
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mp)
      (fun j hj U r => (hrecv j hj U r).mpr)
      (fun j hj U args => (hacc j hj U args).mpr)
      (fun j hj U u => (hres j hj U u).mp)
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mpr)
      (fun j hj U r => (hrecv j hj U r).mp)
      (fun j hj U args => (hacc j hj U args).mp)
      (fun j hj U u => (hres j hj U u).mpr)

/-! ### Construct signatures -/

/-- The promise of one construct signature, independent of argument-list
syntax: the construction condition at the signature's precondition, result
and specification per completion (`Exits.exitPostW`), the receiver
`undefined`. -/
def ConstructPromise (Ξ : Fam) (effect : Effect) (P : ArgFam) (R : Fam) (k : Nat) (W : WorldT k)
    (v : Val) : Prop :=
  NativeConstruct Ξ P (effect.Requires .undef) (fun args => effect.result R (effect.promised args))
    (fun r args _ U heap => effect.schema.exitPostW .normal r args U heap)
    (fun r args _ U heap => effect.schema.exitPostW .exceptional r args U heap) k W v

/-- The promise of a construct signature read at its postconditions
(`NativeConstruct.iff_exits`). -/
theorem ConstructPromise.iff_legacy {Ξ : Fam} {effect : Effect} {P : ArgFam} {R : Fam} {k : Nat} {W : WorldT k}
    {v : Val} :
    ConstructPromise Ξ effect P R k W v ↔
      NativeConstruct Ξ P (effect.Requires .undef) (fun args => effect.result R (effect.promised args))
        (fun r args _ U heap => effect.postW r args U heap)
        (fun r args _ _ heap => (effect.excPostW r args heap).liftV) k W v :=
  NativeConstruct.iff_exits.symm

theorem ConstructPromise.down {effect P R n W v}
    (h : ConstructPromise Ξ effect P R (n + 1) W v) :
    ConstructPromise Ξ effect P R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh hvr args hv har ha hq
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh hvr args hv har ha hq

theorem ConstructPromise.mono {effect P R n W W' v} (hx : WExt W W')
    (h : ConstructPromise Ξ effect P R n W v) : ConstructPromise Ξ effect P R n W' v := by
  intro j hj U hy hu heap hh hvr args hv har ha hq
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh hvr args hv har ha hq

theorem ConstructPromise.weaken' {Ξ Ξ' : Fam} {effect effect' P P' R T k W v}
    (he : effect.Covers effect')
    (hexc : ∀ j, j < k → ∀ U u, Ξ j U u → Ξ' j U u)
    (hacc : ∀ j, j < k → ∀ U args, P' j U args → P j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : ConstructPromise Ξ effect P R k W v) : ConstructPromise Ξ' effect' P' T k W v := by
  rw [ConstructPromise.iff_legacy] at h ⊢
  intro j hj U hx hu heap hh hvr args hv har ha hq
  obtain ⟨result, hc, hs⟩ := h j hj U hx hu heap hh hvr args hv har (hacc j hj U args ha) (he.2.2.2 .undef args heap hq)
  exact ⟨result, hc, SafePostExcV.iff_lift.mpr <| SafePostExcW.consequence_below' (fun m hm => hexc m (by omega))
    (fun m hm U' u hu => he.2.1 T args m U' u
      (Effect.result_mono effect (hres m (by omega) U') (hres m (by omega) U') hu))
    (fun m _ => he.1 .undef args j U heap m) (fun _ _ _ h' => he.2.2.1 .undef args heap h') (SafePostExcV.iff_lift.mp hs)⟩

theorem ConstructPromise.congr {Ξ Ξ' : Fam} {effect P P' R T n W v}
    (hexc : Agree Ξ Ξ' n)
    (hacc : ∀ j, j < n → ∀ U args, P j U args ↔ P' j U args)
    (hres : Agree R T n) :
    ConstructPromise Ξ effect P R n W v ↔ ConstructPromise Ξ' effect P' T n W v := by
  constructor <;> intro h
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mp)
      (fun j hj U args => (hacc j hj U args).mpr)
      (fun j hj U u => (hres j hj U u).mp)
  · exact h.weaken' (Effect.Covers.refl _)
      (fun j hj U u => (hexc j hj U u).mpr)
      (fun j hj U args => (hacc j hj U args).mp)
      (fun j hj U u => (hres j hj U u).mpr)

/-- A plain signature's promise gives a safe construction once its
postcondition is forgotten. -/
theorem ConstructPromise.erase {effect P R k W v} (hp : effect.plain = true)
    (h : ConstructPromise Ξ effect P R k W v) :
    ∀ (j : Nat) (hj : j < k) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U → ∀ (heap : Heap), HeapOk j U heap →
        RefsOk U v → ∀ args, CallArguments.Values args → (∀ a ∈ args, RefsOk U a) → P j U args →
          ∃ result, ConstructsTo v args result ∧ Safe Ξ R j U heap result := by
  intro j hj U hx hu heap hh hvr args hv har ha
  obtain ⟨result, hc, hs⟩ := h j hj U hx hu heap hh hvr args hv har ha
    (Effect.requires_none (Effect.plain_requires hp) (Effect.plain_pre hp) .undef args heap)
  dsimp only at hs
  rw [Effect.result_plain hp] at hs
  exact ⟨result, hc, SafePostW.erase (SafePostExcV.post hs)⟩

/-- **Construct signatures.** Values meeting every signature `(parameters,
result)` under `new`, each with its effect (`ConstructPromise`). The code is
construct-only, so a plain call cannot run it, and no code without
`[[Construct]]` is one. As for call signatures, the promise is about the term
after the step, which is what lets the signature's variance be used only
below the current level. -/
def ctorsT (Ξ : Fam) (L : List (MethodArrow Fam)) : Fam := fun k W v =>
  Constructible v ∧ ∀ p ∈ L, ConstructPromise Ξ p.effect (ArgsT p.arguments) p.result k W v

theorem ctorsT_adm (L : List (MethodArrow Fam)) : Adm (ctorsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

/-- A variadic construct signature: its fixed parameters, then, as one
argument pack, the rest. -/
abbrev CtorRestSignature := Contract Unit (List Fam × ArgFam) Fam

/-- **Variadic construct signatures** `(parameters, rest, result)`: as
`ctorsT`, for the lists `CtorRest` admits. -/
def ctorRestsT (Ξ : Fam) (S : List CtorRestSignature) : Fam := fun k W v =>
  Constructible v ∧ ∀ s ∈ S,
    ConstructPromise Ξ s.effect (CtorRest s.arguments.1 s.arguments.2) s.result k W v

theorem ctorRestsT_adm (S : List CtorRestSignature) : Adm (ctorRestsT Ξ S) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

theorem ctorRestsT_append (S T : List CtorRestSignature) (k : Nat) (W : WorldT k) (v : Val) :
    ctorRestsT Ξ (S ++ T) k W v ↔ ctorRestsT Ξ S k W v ∧ ctorRestsT Ξ T k W v := by
  simp only [ctorRestsT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨hc, hl, hm⟩; exact ⟨⟨hc, hl⟩, hc, hm⟩
  · rintro ⟨⟨hc, hl⟩, -, hm⟩; exact ⟨hc, hl, hm⟩

theorem ctorsT_select {L n W v p} (hf : ctorsT Ξ L n W v) (hp : p ∈ L) : ctorsT Ξ [p] n W v :=
  ⟨hf.1, fun q hq => by cases List.mem_singleton.mp hq; exact hf.2 p hp⟩

theorem ctorsT_append (L M : List (MethodArrow Fam)) (k : Nat) (W : WorldT k) (v : Val) :
    ctorsT Ξ (L ++ M) k W v ↔ ctorsT Ξ L k W v ∧ ctorsT Ξ M k W v := by
  simp only [ctorsT, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨hc, hl, hm⟩; exact ⟨⟨hc, hl⟩, hc, hm⟩
  · rintro ⟨⟨hc, hl⟩, -, hm⟩; exact ⟨hc, hl, hm⟩

theorem ctorsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → MethodArrow Fam) {n : Nat}
    (hΞ : Agree Ξ Ξ' n)
    (h : ∀ x ∈ l, (f x).effect = (g x).effect ∧ ArgsAgree n (f x).arguments (g x).arguments ∧
      Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : ctorsT Ξ (l.map f) n W v ↔ ctorsT Ξ' (l.map g) n W v := by
  unfold ctorsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩ <;>
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
  · have hp := hs (f x) (List.mem_map_of_mem hm)
    rw [(h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (fun j hj U args => ArgsT_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp hp
  · have hp := hs (g x) (List.mem_map_of_mem hm)
    rw [← (h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (fun j hj U args => ArgsT_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr hp

theorem ctorRestsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → CtorRestSignature) {n : Nat}
    (hΞ : Agree Ξ Ξ' n)
    (h : ∀ x ∈ l, (f x).effect = (g x).effect ∧ ArgsAgree n (f x).arguments.1 (g x).arguments.1 ∧
      Agree (f x).arguments.2 (g x).arguments.2 n ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : ctorRestsT Ξ (l.map f) n W v ↔ ctorRestsT Ξ' (l.map g) n W v := by
  unfold ctorRestsT
  have hacc : ∀ x ∈ l, ∀ j, j < n → ∀ U args,
      CtorRest (f x).arguments.1 (f x).arguments.2 j U args ↔
        CtorRest (g x).arguments.1 (g x).arguments.2 j U args := by
    intro x hm j hj U args
    have hl := ArgsAgree_length (h x hm).2.1
    unfold CtorRest
    rw [hl]
    exact and_congr Iff.rfl (and_congr (ArgsT_congr (h x hm).2.1 hj U _) ((h x hm).2.2.1 j hj U _))
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩ <;>
    obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
  · have hp := hs (f x) (List.mem_map_of_mem hm)
    rw [(h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (hacc x hm) (h x hm).2.2.2).mp hp
  · have hp := hs (g x) (List.mem_map_of_mem hm)
    rw [← (h x hm).1] at hp
    exact (ConstructPromise.congr hΞ (hacc x hm) (h x hm).2.2.2).mpr hp

/-- Combining result guarantees retains the effects established for this call
domain by either premise. World-sensitive results still require the same
cross-world compatibility as ordinary arrows. Effects concern the shared final
heap, so they do not depend on which result world supplies the conclusion. -/
theorem PromiseWith.combine {effect other Acc Rc B C D k W v}
    (hs : effect.sameResult other = true)
    (hb : PromiseWith Ξ effect Acc Rc B k W v)
    (hc : PromiseWith Ξ other Acc Rc C k W v)
    (hcross : ∀ n, n < k → CrossCompatUpTo n B C D) :
    PromiseWith Ξ (effect.meet other) Acc Rc D k W v := by
  rw [PromiseWith.iff_legacy] at hb hc ⊢
  intro j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha hq
  have hq' : other.Requires r args heap := by
    simp only [Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs
    exact ⟨fun R hR => hq.1 R (by simp only [Effect.meet]; rw [hs.1.1.1.1.2]; exact hR),
      fun F hF => hq.2 F (by simp only [Effect.meet]; rw [hs.1.1.2]; exact hF)⟩
  obtain ⟨b, hib, hsb⟩ := hb j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha ⟨hq.1, hq.2⟩
  obtain ⟨c, hic, hsc⟩ := hc j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha hq'
  replace hsb := SafePostExcV.iff_lift.mp hsb
  replace hsc := SafePostExcV.iff_lift.mp hsc
  cases CallArguments.invoke_deterministic hib hic
  obtain ⟨hr1, hp1, hr2, hp2⟩ := Effect.meet_same hs
  rw [hr2, hp2] at hsc
  rw [hr1, hp1]
  have hsc' : SafePostExc Ξ (effect.result C (effect.promised args)) (other.post r args heap)
      (other.excPost r args heap) j U heap b :=
    SafePostExcW.weaken (fun _ _ _ _ hp => hp.1) (fun _ _ _ hp => hp) hsc
  exact ⟨b, hib, SafePostExcV.iff_lift.mpr <| SafePostExcW.weaken
    (fun k' W' heap' value hpost => (Effect.postW_meet hs r args U heap k' W' heap' value).mpr hpost)
    (fun _ _ heap' hexc => Effect.excPost_meet hs r args heap heap' hexc.1 hexc.2)
    (SafePostExcW.cross j (Effect.cross_result effect (hcross j hj)) U U heap b hh hh hsb hsc')⟩

/-- Binding saves a receiver and argument prefix, then forwards without
changing the heap. This generic rule covers fixed and variadic signatures;
only the argument-admission premise differs. The callee's effect is retained
at the heap where the forwarded call actually starts; a promise, about an
actual past the saved prefix, is about the same actual of the bound call. -/
theorem PromiseWith.bound {effect : Effect} {Acc Rest : ArgFam} {Rt R Rc : Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hkeeps : effect.keeps pre.length = true)
    (ht : PromiseWith Ξ effect Acc Rt R k W tv)
    (hRt : Adm Rt) (hRest : Adm Rest)
    (hrv : isVal rv = true) (hr : Rt k W rv) (hp : CallArguments.Values pre)
    (hprefix : ∀ j (hj : j < k) U, WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ args, Rest j U args → Acc j U (pre ++ args)) :
    PromiseWith Ξ (effect.drop pre.length) Rest Rc R k W (.objAt fs (.bound tv rv pre) oid) := by
  rw [PromiseWith.iff_legacy] at ht ⊢
  intro j hj U hx hu heap hh hvr r hv _ _ args hargs har ha _
  refine ⟨_, .bound hv hargs, ?_⟩
  have hobj : RefsOk U tv ∧ RefsOk U rv ∧ ∀ a ∈ pre, RefsOk U a := by
    refine ⟨fun x hx => hvr x ?_, fun x hx => hvr x ?_, fun a ha x hx => hvr x ?_⟩ <;>
      simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    · exact .inr (.inl (.inl hx))
    · exact .inr (.inl (.inr hx))
    · exact .inr (.inr ⟨a, ha, hx⟩)
  have hinv : RefsOk U (.invoke tv rv (pre ++ args)) :=
    RefsOk_invoke.mpr ⟨hobj.1, hobj.2.1, fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact hobj.2.2 a ha
      · exact har a ha⟩
  cases j with
  | zero => exact hinv
  | succ i =>
    have hi : i < k := by omega
    have hxU : WExt (trunc i (Nat.le_of_lt hi) W) (trunc i (Nat.le_succ i) U) := by
      have hx' := WExt_trunc (Nat.le_succ i) hx
      rwa [trunc_trunc] at hx'
    have hu' := WorldAdm_trunc (Nat.le_succ i) hu
    have hh' := HeapOk_trunc i U heap hh
    have hr' := hRt.mono i _ _ hxU rv (hRt.down_le k i (Nat.le_of_lt hi) W rv hr)
    have ha' := hRest.down i U args ha
    have hall : CallArguments.Values (pre ++ args) := by
      intro a hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hp a hm
      · exact hargs a hm
    have hall' : ∀ a ∈ pre ++ args, RefsOk (trunc i (Nat.le_succ i) U) a := fun a ha =>
      RefsOk_trunc _ ((RefsOk_invoke.mp hinv).2.2 a ha)
    obtain ⟨res, hinv', hsafe⟩ := ht i hi _ hxU hu' heap hh' (RefsOk_trunc _ hobj.1) rv hrv hr'
      (RefsOk_trunc _ hobj.2.1) (pre ++ args) hall hall' (hprefix i hi _ hxU args ha')
      (Effect.requires_none (Effect.keeps_requires hkeeps) (Effect.keeps_pre hkeeps) rv (pre ++ args) heap)
    replace hsafe := SafePostExcV.iff_lift.mp hsafe
    dsimp only at hsafe ⊢
    rw [Effect.result_drop, Effect.promised_drop hkeeps]
    -- The target is entered one step after the bound call, at the same
    -- heap: its view write from that world is one from the bound call's
    -- entry (`Kinds.ViewWrite.prefix_left`).
    have hxi : WExt (trunc i (Nat.le_succ i) U) (trunc i (Nat.le_succ i) U) := WExt_refl _
    exact ⟨hinv, .inr ⟨_, heap, res, WExt_refl _, hu', hinv'.step heap, hh',
      SafePostExcV.iff_lift.mpr <| SafePostExcW.weaken (fun _ _ _ _ h => ⟨Effect.post_drop pre.length h.1, fun w hw => by
          simp only [Effect.drop, Option.map_eq_some_iff] at hw
          obtain ⟨w0, h0, rfl⟩ := hw
          exact ⟨⟨(h.2 w0 h0).1.1.prefix_left (Nat.le_succ i) hxi hh (List.prefix_refl _),
            fun _ he => (by cases he), fun he => (by cases he)⟩, fun he => absurd rfl he⟩⟩)
        (fun _ _ _ h => Effect.excPost_drop pre.length h) hsafe⟩⟩

/-- Application consumes a qualified signature, without inspecting the
callee's implementation. Its entry heap is after actual evaluation. -/
theorem call_safe_exc {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith Ξ effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires r vs heap)
    (href : RefsOk W (.invoke f r vs)) :
    SafePostExc Ξ (effect.result R (effect.promised vs)) (effect.post r vs heap) (effect.excPost r vs heap)
      n W heap (.invoke f r vs) := by
  rw [PromiseWith.iff_legacy] at hf
  cases n with
  | zero => exact href
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    obtain ⟨hfr, hrr, har⟩ := RefsOk_invoke.mp href
    obtain ⟨body, hi, hs⟩ := hf n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) (RefsOk_trunc _ hfr) r hrv (hRc.down n W r hr)
      (RefsOk_trunc _ hrr) vs hv (fun a ha => RefsOk_trunc _ (har a ha))
      (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _)) hq
    exact ⟨href, .inr ⟨U, heap, body, WExt_refl _, WorldAdm_trunc _ hw, hi.step heap,
      HeapOk_trunc n W heap hh, SafePostExcW.weaken (fun _ _ _ _ hp => hp.1) (fun _ _ _ hp => hp) (SafePostExcV.iff_lift.mp hs)⟩⟩

theorem call_safe {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith Ξ effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires r vs heap)
    (href : RefsOk W (.invoke f r vs)) :
    SafePost Ξ (effect.result R (effect.promised vs)) (effect.post r vs heap) n W heap (.invoke f r vs) :=
  (call_safe_exc hP hRc hf hr hrv hv ha hw hh hq href).post

/-- **A call at a signature's exits** (the note's Call, `invoke_exits`): a
value meeting the signature, invoked at value actuals meeting its input
contract and precondition, is safe at the signature's specification at those
actuals, from an invocation entry held from the call's (`HeldEntry`). -/
theorem call_exits {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith Ξ effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires r vs heap)
    (href : RefsOk W (.invoke f r vs)) :
    SafePostExcV Ξ (effect.result R (effect.promised vs)) (effect.schema.fromEntry .normal r vs (HeldEntry W heap))
      (effect.schema.fromEntry .exceptional r vs (HeldEntry W heap)) n W heap (.invoke f r vs) := by
  cases n with
  | zero => exact href
  | succ n =>
    exact invoke_exits hf hw hh hrv (hRc.down n W r hr) hv (hP.transfer ha n (Nat.le_succ n) _ (WExt_refl _)) hq href

/-- Trailing `undefined` actuals change no precondition: a construction's
positions past its actuals hold `undefined` either way (`callEnv_pad`). -/
theorem Effect.requires_pad {e : Effect} {r : Tm} {args pad : List Tm} {h : Heap}
    (hpad : ∀ a ∈ pad, a = .undef) (hq : e.Requires r args h) : e.Requires r (args ++ pad) h := by
  refine ⟨hq.1, fun F hF => ?_⟩
  rw [callEnv_pad r args hpad]
  exact hq.2 F hF

/-- A construction of a class value with value actuals takes one step to the
body its signature makes safe, meeting the signature's effect from the heap
it starts in, where the signature's precondition holds of the construction's
actuals (`call-requires`) and it states no promise, so its result operand is
the result's type. The signature may declare trailing positions the
construction omits: each admits `undefined`, which the step binds there. -/
theorem construct_safe_exc_requires {effect : Effect} (hpr : effect.promise = none) {P : ArgFam} {R : Fam}
    (hP : Adm P) {n W heap v vs pad}
    (hf : ConstructPromise Ξ effect P R n W v) (hv : CallArguments.Values vs)
    (hpad : ∀ a ∈ pad, a = .undef) (ha : P n W (vs ++ pad))
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hq : effect.Requires .undef vs heap)
    (href : RefsOk W (.construct v vs)) :
    SafePostExc Ξ R (effect.post .undef vs heap) (effect.excPost .undef vs heap) n W heap (.construct v vs) := by
  rw [ConstructPromise.iff_legacy] at hf
  cases n with
  | zero => exact href
  | succ n =>
    obtain ⟨hvr, har⟩ := RefsOk_construct.mp href
    let U := trunc n (Nat.le_succ n) W
    have hvp : CallArguments.Values (vs ++ pad) := by
      intro a h
      rcases List.mem_append.mp h with h | h
      · exact hv a h
      · rw [hpad a h]; rfl
    obtain ⟨result, ⟨fs, c, enter, oid, rfl, hc, rfl⟩, hs⟩ := hf n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) (RefsOk_trunc _ hvr) _ hvp
      (fun a ha => by
        rcases List.mem_append.mp ha with ha | ha
        · exact RefsOk_trunc _ (har a ha)
        · rw [hpad a ha]; exact RefsOk_undef)
      (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _))
      (Effect.requires_pad hpad hq)
    dsimp only at hs
    rw [CallArguments.construction_pad hc _ _ hpad, Effect.result_none hpr] at hs
    exact ⟨href, .inr ⟨U, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
      CallArguments.construction_step hc hv heap, HeapOk_trunc n W heap hh,
      SafePostExcW.weaken (fun _ _ _ _ h => Effect.post_pad rfl hpad h.1) (fun _ _ _ h => Effect.excPost_pad hpad h) (SafePostExcV.iff_lift.mp hs)⟩⟩

/-- A construction at a plain signature, whose precondition is empty. -/
theorem construct_safe_exc {effect : Effect} (hpl : effect.plain = true) {P : ArgFam} {R : Fam}
    (hP : Adm P) {n W heap v vs pad}
    (hf : ConstructPromise Ξ effect P R n W v) (hv : CallArguments.Values vs)
    (hpad : ∀ a ∈ pad, a = .undef) (ha : P n W (vs ++ pad))
    (hw : WorldAdm W) (hh : HeapOk n W heap) (href : RefsOk W (.construct v vs)) :
    SafePostExc Ξ R (effect.post .undef vs heap) (effect.excPost .undef vs heap) n W heap (.construct v vs) :=
  construct_safe_exc_requires
    (by simp only [Effect.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hpl; exact hpl.1.1)
    hP hf hv hpad ha hw hh (Effect.requires_none (Effect.plain_requires hpl) (Effect.plain_pre hpl) .undef vs heap) href

/-- An operational invariant that only appends fresh locations supplies
the normal-return preservation postcondition, supplementing ordinary safety.
The safety proof supplies the same worlds and result contract at every step. -/
theorem prefix_safe {P : Tm → Prop} {R : Fam} {r : Tm} {args : List Tm}
    (hstep : ∀ {h t h' t'}, P t → Step h t h' t' → h.IsPrefix h' ∧ P t') :
    ∀ {n W heap t}, P t → Safe Ξ R n W heap t →
      SafePost Ξ R ((Effect.ofFootprint .empty).post r args heap) n W heap t := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro W heap t hp hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, (Effect.post_ofFootprint _ _ _ _ _ _).mpr
        (Footprints.Closed.holds_empty.mpr ⟨[], by simp⟩)⟩)
    · exact .inl (.inr hth)
    · obtain ⟨hprefix, hp'⟩ := hstep hp step
      exact .inr ⟨U, h', t', hx, hu, step, hh,
        HeapObservations.weaken (fun _ _ hpost => (Effect.post_ofFootprint _ _ _ _ _ _).mpr
          (Footprints.Closed.holds_empty.mpr
          (hprefix.trans (Footprints.Closed.holds_empty.mp ((Effect.post_ofFootprint _ _ _ _ _ _).mp hpost)))))
          (ih hp' hs)⟩

/-- The same invariant bounds the heap a throw leaves: every step keeps the
heap a prefix, so a raise does too. -/
theorem prefix_safe_exc {P : Tm → Prop} {R : Fam} {r : Tm} {args : List Tm}
    (hstep : ∀ {h t h' t'}, P t → Step h t h' t' → h.IsPrefix h' ∧ P t') :
    ∀ {n W heap t}, P t → Safe Ξ R n W heap t →
      SafePostExc Ξ R ((Effect.ofFootprint .empty).post r args heap)
        (fun h' => Footprints.Closed.empty.Holds heap h') n W heap t := by
  intro n W heap t hp hs
  have hpost := prefix_safe (r := r) (args := args) hstep hp hs
  suffices ∀ {n W h t}, P t → heap.IsPrefix h → SafePost Ξ R ((Effect.ofFootprint .empty).post r args heap) n W h t →
      SafePostExc Ξ R ((Effect.ofFootprint .empty).post r args heap)
        (fun h' => Footprints.Closed.empty.Holds heap h') n W h t from this hp (List.prefix_refl _) hpost
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro W h t hp hpre hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (hv | hr) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ⟨hr, Footprints.Closed.holds_empty.mpr hpre⟩)
    · obtain ⟨hprefix, hp'⟩ := hstep hp step
      exact .inr ⟨U, h', t', hx, hu, step, hh, ih hp' (hpre.trans hprefix) hs⟩

theorem pure_safe_exc {R : Fam} {r : Tm} {args : List Tm} {n W heap t}
    (hp : Purity.PureRun t) (hs : Safe Ξ R n W heap t) :
    SafePostExc Ξ R ((Effect.ofFootprint .empty).post r args heap)
      (fun h' => Footprints.Closed.empty.Holds heap h') n W heap t :=
  prefix_safe_exc Purity.CollectingRun.step (.pure hp) hs

def callsT (Ξ : Fam) (L : List (Arrow Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L, PromiseWith Ξ s.effect (ArgsShort s.arguments) s.receiver s.result k W v

/-- Assemble an intersection from its individual qualified signatures. -/
theorem callsT_of_signatures {L : List (Arrow Fam)} {n W v}
    (hi : Invocable v) (hs : ∀ p ∈ L, callsT Ξ [p] n W v) : callsT Ξ L n W v :=
  ⟨hi, fun p hp => (hs p hp).2 p (List.mem_singleton_self _)⟩

theorem callsT_adm (L : List (Arrow Fam)) : Adm (callsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem callsT_erase {L : List (Arrow Fam)} {n W v} (hp : ∀ s ∈ L, s.effect.plain = true)
    (h : callsT Ξ L n W v) : Verification.callsT Ξ (L.map Arrow.plain) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  exact (h.2 s hs).erase (hp s hs)

theorem callsT_select {L n W v p} (hf : callsT Ξ L n W v) (hp : p ∈ L) :
    callsT Ξ [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

/-- A bound fixed signature keeps its effect, with the saved prefix removed
from its domain. -/
theorem callsT_bound {effect : Effect} {Rt R Rc : Fam} {Ps Ds : List Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hDs : ∀ A ∈ Ds, Adm A)
    (hkeeps : effect.keeps pre.length = true)
    (ht : callsT Ξ [⟨Rt, Ps ++ Ds, R, effect⟩] k W tv)
    (hrv : isVal rv = true) (hsr : Scoped 0 rv) (hr : Rt k W rv)
    (hp : ArgsT Ps k W pre) (hv : CallArguments.Values pre) (hsp : ∀ a ∈ pre, Scoped 0 a) :
    callsT Ξ [⟨Rc, Ds, R, effect.drop pre.length⟩] k W (.objAt fs (.bound tv rv pre) oid) := by
  refine ⟨⟨fs, _, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hm
    cases List.mem_singleton.mp hm
    exact (ht.2 _ (List.mem_singleton_self _)).bound hkeeps hRt
      (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer hDs ha j hj U hx)) hrv hr hv
      (fun j hj U hx args ha => ArgsShort_prefix (ArgsT_transfer hPs hp j (Nat.le_of_lt hj) U hx) ha)

theorem callsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → Arrow Fam) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments (g x).arguments ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : callsT Ξ (l.map f) n W v ↔ callsT Ξ' (l.map g) n W v := by
  unfold callsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr hexc (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr hexc (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr (hs (g x) (List.mem_map_of_mem hm))

/-- Fixed arguments are value families, whereas the rest is an argument-list
family. Both are operands of the same effect-qualified contract. -/
abbrev RestSignature := Contract Fam (List Fam × ArgFam) Fam

def restsT (Ξ : Fam) (L : List RestSignature) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L,
    PromiseWith Ξ s.effect (ArgsRest s.arguments.1 s.arguments.2) s.receiver s.result k W v

/-- Assemble an intersection from its individual qualified signatures. -/
theorem restsT_of_signatures {L : List (RestSignature)} {n W v}
    (hi : Invocable v) (hs : ∀ p ∈ L, restsT Ξ [p] n W v) : restsT Ξ L n W v :=
  ⟨hi, fun p hp => (hs p hp).2 p (List.mem_singleton_self _)⟩

theorem restsT_select {L n W v p} (hf : restsT Ξ L n W v) (hp : p ∈ L) :
    restsT Ξ [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

theorem restsT_adm (L : List RestSignature) : Adm (restsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem restsT_erase {L : List RestSignature} {n W v} (hp : ∀ s ∈ L, s.effect.plain = true)
    (h : restsT Ξ L n W v) :
    Verification.restsT Ξ (L.map fun s => (s.receiver, s.arguments.1, s.arguments.2, s.result)) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  exact (h.2 s hs).erase (hp s hs)

/-- Binding a variadic signature retains the same effect. A saved prefix
extending into the rest requires a contract closed under prepending those
saved values, exactly as for ordinary variadic binding. -/
theorem restsT_bound {effect : Effect} {Rt R Rc : Fam} {E : ArgFam} {Ps : List Fam}
    {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {tv rv : Val} {pre : List Tm}
    (hRt : Adm Rt) (hPs : ∀ A ∈ Ps, Adm A) (hE : Adm E)
    (hkeeps : effect.keeps pre.length = true)
    (ht : restsT Ξ [⟨Rt, (Ps, E), R, effect⟩] k W tv)
    (hrv : isVal rv = true) (hsr : Scoped 0 rv) (hr : Rt k W rv)
    (hp : ArgsT (Ps.take pre.length) k W (pre.take Ps.length))
    (hext : ∀ j (hj : j ≤ k) U, WExt (trunc j hj W) U →
      ∀ ys, E j U ys → E j U (pre.drop Ps.length ++ ys))
    (hv : CallArguments.Values pre) (hsp : ∀ a ∈ pre, Scoped 0 a) :
    restsT Ξ [⟨Rc, (Ps.drop pre.length, E), R, effect.drop pre.length⟩] k W (.objAt fs (.bound tv rv pre) oid) := by
  refine ⟨⟨fs, _, _, rfl, rfl, ?_⟩, ?_⟩
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨ht.1.scoped, hsr, hsp⟩
  · intro p hm
    cases List.mem_singleton.mp hm
    exact (ht.2 _ (List.mem_singleton_self _)).bound hkeeps hRt
      (Adm.of_transfer (fun ha j hj U hx =>
        ArgsRest_transfer (fun A hm => hPs A (List.mem_of_mem_drop hm)) hE ha j hj U hx))
      hrv hr hv (fun j hj U hx args ha => ArgsRest_prefix
        (ArgsT_transfer (fun A hm => hPs A (List.mem_of_mem_take hm)) hp j (Nat.le_of_lt hj) U hx)
        (hext j (Nat.le_of_lt hj) U hx) ha)

/-- Conjunction and overload normalization preserve every signature's effect. -/
theorem callsT_append (L M : List (Arrow Fam)) (n W v) :
    callsT Ξ (L ++ M) n W v ↔ callsT Ξ L n W v ∧ callsT Ξ M n W v := by
  simp only [callsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_append (L M : List RestSignature) (n W v) :
    restsT Ξ (L ++ M) n W v ↔ restsT Ξ L n W v ∧ restsT Ξ M n W v := by
  simp only [restsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_congr {Ξ Ξ' : Fam} {α : Type} (l : List α) (f g : α → RestSignature) {n : Nat}
    (hexc : Agree Ξ Ξ' n)
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments.1 (g x).arguments.1 ∧
      Agree (f x).arguments.2 (g x).arguments.2 n ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : restsT Ξ (l.map f) n W v ↔ restsT Ξ' (l.map g) n W v := by
  have args : ∀ x ∈ l, ∀ j, j < n → ∀ U vs,
      ArgsRest (f x).arguments.1 (f x).arguments.2 j U vs ↔
      ArgsRest (g x).arguments.1 (g x).arguments.2 j U vs := by
    intro x hx j hj U vs
    have hl := ArgsAgree_length (h x hx).2.1
    unfold ArgsRest
    rw [hl]
    exact and_congr (ArgsShort_congr (h x hx).2.1 hj U _) ((h x hx).2.2.1 j hj U _)
  unfold restsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr hexc (h x hm).1 (args x hm) (h x hm).2.2.2).mp
      (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr hexc (h x hm).1 (args x hm) (h x hm).2.2.2).mpr
      (hs (g x) (List.mem_map_of_mem hm))

end Verification.CallEffects
