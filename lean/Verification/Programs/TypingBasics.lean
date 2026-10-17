import Verification.Programs.CallableObjects
import Verification.Programs.ObjectMerge
import Verification.Programs.ComputedKey
import Verification.Types.PositiveCertificates

/-! # Program typing: the ingredients

Types as label lists, represented clauses, the environments and frames code
runs in, the built-in prototype type, allocation against the built-ins'
invariant, and the checked code entries the typing judgement cites. -/
namespace Verification.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower
open CallEffects (Arrow RestArrow MethodArrow MethodRestArrow Contract Effect PromiseWith ctorsT ctorsT_adm
  ctorRestsT ctorRestsT_adm)
open HeapObservations (SafePost)

variable {ι : Type}

abbrev Ty (ι : Type) := List ι

def Represents (G : NormalGraph ι) (A : Ty ι) (c : Clause (Ty ι)) : Prop :=
  expand G A = [c]

/-- A type represented by a clause is of clause rows. -/
theorem Represents.plain {G : NormalGraph ι} {A c} (hr : Represents G A c) :
    G.plainTy A = true :=
  plain_of_mem_expand (c := c) (by simp [show expand G A = [c] from hr])

theorem represents_sem {G : NormalGraph ι} {A c} (hr : Represents G A c) (n W v) :
    meaning G A n W v ↔ clauseSem G c n W v := by
  rw [expand_sem G A hr.plain, show expand G A = [c] from hr]
  simp [setSem]

/-- A member of a represented type is a member of its clause. -/
theorem represents_raw {G : NormalGraph ι} {A c} (hr : Represents G A c) (n W v) :
    meaning G A n W v → semWithArgs (excOf G) (meaning G) (argMeaning G) c n W v :=
  fun h => ((represents_sem hr n W v).mp h).1

/-- A member of a clause that is not a record's is a member of the type it
represents: the built-ins asks nothing of it. -/
theorem represents_back {G : NormalGraph ι} {A c} (hr : Represents G A c) (n W v)
    (hc : c.carriesInvariant = false := by rfl) :
    semWithArgs (excOf G) (meaning G) (argMeaning G) c n W v → meaning G A n W v :=
  fun h => (represents_sem hr n W v).mpr ⟨h, builtinInvariant_of_withoutInvariant hc n W v⟩

/-- A value of a class's key clause is a key the class admits, by the
`ToPropertyKey` a computed key's step applies. -/
theorem keyClause_admits {G : NormalGraph ι} {K : IndexKeys} {n W v}
    (h : semWithArgs (excOf G) (meaning G) (argMeaning G) (keyClause K) n W v) :
    ∃ f, propertyKey v = some f ∧ K.Admits f := by
  cases K
  · obtain ⟨s, rfl⟩ := h; exact ⟨_, rfl, trivial⟩
  · obtain ⟨b, rfl⟩ := h; exact ⟨_, rfl, numeric_admits_number b⟩
  · obtain ⟨i, rfl⟩ := h; exact ⟨_, rfl, trivial⟩

theorem meaning_adm (G : NormalGraph ι) (A : Ty ι) : Adm (meaning G A) :=
  setSem_adm (normalDenote_adm G) A

theorem argMeaning_adm (G : NormalGraph ι) (P : Ty ι) : Adm (argMeaning G P) :=
  graphArguments_adm G G.env _ (fun S => meaning_adm G S) P

/-- A union of label lists means either side. -/
theorem meaning_append (G : NormalGraph ι) (A B : Ty ι) (n W v) :
    meaning G (A ++ B) n W v ↔ meaning G A n W v ∨ meaning G B n W v := by
  simp [meaning, setSem, List.mem_append, or_and_right, exists_or]

/-- The type a tuple contract states for an index, syntactically: a required
position's, an optional position's, or the rest's where any further position
may be. -/
def positionTy (T : Tuple (Ty ι)) (i : Nat) : Option (Ty ι) :=
  match T.required[i]? with
  | some A => some A
  | none => match T.optional[i - T.required.length]? with
    | some A => some A
    | none => if T.required.length + T.optional.length ≤ i then T.rest else none

theorem positionFam_tupleFams {X : Ty ι → Fam} (T : Tuple (Ty ι)) (i : Nat) :
    positionFam (tupleFams X T) i = (positionTy T i).map X := by
  simp only [positionFam, positionTy, tupleFams, List.getElem?_map, List.length_map]
  cases T.required[i]? <;> cases T.optional[i - T.required.length]? <;> simp <;> split <;> simp

theorem meaning_value {G : NormalGraph ι} {A n W v} (h : meaning G A n W v) :
    isVal v = true ∧ Scoped 0 v := by
  obtain ⟨_, _, hv⟩ := h
  exact normalDenote_value hv

theorem meaning_valOnly (G : NormalGraph ι) (A : Ty ι) : ValOnly (meaning G A) :=
  fun _ _ _ h => (meaning_value h).1

def EnvOk (G : NormalGraph ι) (Γ : List (Ty ι)) (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  (∀ i, Scoped 0 (ρ i)) ∧ ∀ i A, Γ[i]? = some A → meaning G A n W (ρ i)

theorem EnvOk.transfer {G : NormalGraph ι} {Γ ρ n W} (h : EnvOk G Γ ρ n W)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) : EnvOk G Γ ρ j U :=
  ⟨h.1, fun i A hi => (meaning_adm G A).mono j _ U hx _
    ((meaning_adm G A).down_le n j hj W _ (h.2 i A hi))⟩

theorem EnvOk.push {G : NormalGraph ι} {Γ ρ n W A a} (h : EnvOk G Γ ρ n W)
    (ha : meaning G A n W a) : EnvOk G (A :: Γ) (push a ρ) n W := by
  constructor
  · intro i; cases i with
    | zero => exact (meaning_value ha).2
    | succ i => exact h.1 i
  · intro i B hi; cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
              subst B; exact ha
    | succ i => exact h.2 i B hi

/-- Parameter zero stays at slot zero; captures follow all parameters. -/
theorem EnvOk.prepend {G : NormalGraph ι} {Γ ρ n W As args}
    (h : EnvOk G Γ ρ n W) (ha : ArgsT (As.map (meaning G)) n W args) :
    EnvOk G (As ++ Γ) (prependArgs args ρ) n W := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT, prependArgs]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args => exact (ih ha.2).push ha.1

/-- The context a closure body is checked in at one signature: the
receiver, then the parameters the code takes, then the captures. -/
abbrev bodyFrame (arity : Nat) (p : Arrow (Ty ι)) (Γ : List (Ty ι)) : List (Ty ι) :=
  p.receiver :: p.arguments.take arity ++ Γ

/-- The rows a closure's code is checked at: its fixed signatures, then each
variadic signature's receiver, fixed parameters and result. Code of fixed
arity meets a variadic signature whose fixed parameters cover its arity:
binding discards the actuals past them (`restsT_of_invocationSpec`). -/
def offerRows (L : List (Arrow (Ty ι))) (S : List (RestArrow (Ty ι))) :
    List (Arrow (Ty ι)) :=
  L ++ S.map fun s => s.fixed


export PositiveRules (readsFrom freeMapOf closureFuel builtinsFree)

/-! ### The built-in prototype type

The array invariant reads `ArrayProto` at one fixed assignment
(`ParameterInterpretation.builtinsAt`); a type reading no parameter row means the
same at every assignment, which a rule relating the invariant to a type checks
of the built-in prototype type. -/

/-- Such a type means at the graph's assignment what the invariant reads. -/
theorem builtinsFree_meaning [DecidableEq ι] {G : NormalGraph ι} {P : Ty ι}
    (h : builtinsFree G P = true) (n W v) : meaning G P n W v ↔ builtinValues G P n W v := by
  simp only [builtinsFree, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    List.isEmpty_iff] at h
  obtain ⟨hF, hP⟩ := h
  have heq : ∀ l ∈ P, normalDenote G l = qDenoteWithArgs G (mixedParameters G)
      (ParameterAssignment.empty .mixed, l) := fun l hl =>
    agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF) G.env _ l (hP l hl).1
      (fun p hp => by rw [(hP l hl).2] at hp; cases hp)
  constructor
  · rintro ⟨l, hl, hv⟩
    refine ⟨l, hl, ?_⟩
    show qDenoteWithArgs G (mixedParameters G) (ParameterAssignment.empty .mixed, l) n W v
    rw [← heq l hl]; exact hv
  · rintro ⟨l, hl, hv⟩
    refine ⟨l, hl, ?_⟩
    change qDenoteWithArgs G (mixedParameters G) (ParameterAssignment.empty .mixed, l) n W v at hv
    rw [← heq l hl] at hv; exact hv

/-- A type containing only JavaScript values. -/
def SourceValues (G : NormalGraph ι) (A : Ty ι) : Prop := sourceTy G A = true

instance [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) : Decidable (SourceValues G A) := by
  unfold SourceValues; infer_instance

theorem SourceValues.sound {G : NormalGraph ι} {A : Ty ι} (h : SourceValues G A)
    {n W v} (hv : meaning G A n W v) : isSourceVal v = true :=
  (sourceTy_sound h G.env n W v hv).1

/-- A value of a type of JavaScript values is of the graph's exception family. -/
theorem SourceValues.exc {G : NormalGraph ι} {A : Ty ι} (h : SourceValues G A)
    {n W v} (hv : meaning G A n W v) : excOf G n W v :=
  sourceTy_exc h G.env n W v hv

/-- A type whose every clause is a store's. -/
def storeTy (G : NormalGraph ι) (S : Ty ι) : Bool :=
  G.plainTy S && (expand G S).all fun c => match c with
    | .list a _ => a.operands.all (sourceTy G)
    | _ => false

/-- A store type's members are stores of the built-ins, given a type `U` holding
the built-ins' `unknown`. -/
theorem storeTy_sound {G : NormalGraph ι} {S U : Ty ι} (h : storeTy G S = true)
    (hu : unknownTy G U = true) {η : MixedAssignment ι} {n W v}
    (hv : meaning G S n W v) : builtinStoreT (mixedValues G η U) n W v := by
  simp only [storeTy, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨c, hc, hv, -⟩ := (expand_sem G S h.1 n W v).mp hv
  have hl := h.2 c hc
  cases c with
  | list a bs =>
    have hj : ∀ B ∈ a.operands, SourceValues G B := by
      simpa only [List.all_eq_true, SourceValues] using hl
    refine listT_builtinStore (fun A hA j W' u hu' => ?_) hv.1
    simp only [tupleFams] at hA
    rcases hA with hA | hA | hA
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact unknownTy_sound hu ((hj B (by simp [Tuple.operands, hB])).exc hu')
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact unknownTy_sound hu ((hj B (by simp [Tuple.operands, hB])).exc hu')
    · obtain ⟨B, hB, he⟩ := Option.map_eq_some_iff.mp hA; subst he
      exact unknownTy_sound hu ((hj B (by simp [Tuple.operands, hB])).exc hu')
  | _ => simp at hl

/-- A type all of whose clauses are stores: its values are lists. -/
def listsOnly [DecidableEq ι] (G : NormalGraph ι) (S : Ty ι) : Bool :=
  G.plainTy S && (expand G S).all fun c => match c with | .list .. => true | _ => false

theorem listsOnly_sound [DecidableEq ι] {G : NormalGraph ι} {S : Ty ι} (h : listsOnly G S = true)
    {n W u} (hu : meaning G S n W u) : ∃ ls, u = .arr ls := by
  simp only [listsOnly, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨c, hc, hv, -⟩ := (expand_sem G S h.1 n W u).mp hu
  have := h.2 c hc
  cases c <;> simp only [Bool.false_eq_true] at this
  obtain ⟨ls, rfl, -⟩ := hv.1
  exact ⟨ls, rfl⟩

/-- **An allocation meets the built-ins' invariant**: it owns no store, or it is
a built-in array, holding a store and the built-in prototype and owning
no key that prototype provides; without a builtins, an array whose store is a
list. -/
def allocBuiltins [DecidableEq ι] (G : NormalGraph ι) (parts : List (PropKey × Ty ι)) : Bool :=
  !parts.any (·.1 == CallArguments.arrayStoreField) ||
  match G.builtins with
  | none => parts.any (fun p => p.1 == CallArguments.arrayStoreField && listsOnly G p.2)
  | some r => builtinsFree G r.proto && unknownTy G r.unknown && parts.all (fun p => !r.keys.contains p.1) &&
      parts.all (fun p => !IndexKeys.numeric.may p.1) &&
      parts.any (fun p => p.1 == CallArguments.arrayStoreField && storeTy G p.2) &&
      parts.any (fun p => p.1 == CallArguments.protoField && p.2 == r.proto)

/-- `allocBuiltins` with the prototype check the graph's image checker
decides once (`InstanceImageCheck.builtinsOk`): what the certificate checker
runs at each allocation. -/
def allocBuiltinsUsing [DecidableEq ι] {G : NormalGraph ι} (images : PositiveCertificates.InstanceImageCheck G)
    (parts : List (PropKey × Ty ι)) : Bool :=
  !parts.any (·.1 == CallArguments.arrayStoreField) ||
  match G.builtins with
  | none => parts.any (fun p => p.1 == CallArguments.arrayStoreField && listsOnly G p.2)
  | some r => images.builtinsOk.get && unknownTy G r.unknown && parts.all (fun p => !r.keys.contains p.1) &&
      parts.all (fun p => !IndexKeys.numeric.may p.1) &&
      parts.any (fun p => p.1 == CallArguments.arrayStoreField && storeTy G p.2) &&
      parts.any (fun p => p.1 == CallArguments.protoField && p.2 == r.proto)

theorem allocBuiltins_of_using [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {parts : List (PropKey × Ty ι)}
    (h : allocBuiltinsUsing images parts = true) : allocBuiltins G parts = true := by
  unfold allocBuiltinsUsing at h
  unfold allocBuiltins
  cases hb : G.builtins with
  | none => simpa [hb] using h
  | some r =>
    simp only [hb, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨⟨⟨⟨⟨hok, hu⟩, hk⟩, hn⟩, hs⟩, hp⟩
    · exact .inl h
    · exact .inr ⟨⟨⟨⟨⟨images.builtinsOk_sound hok r hb, hu⟩, hk⟩, hn⟩, hs⟩, hp⟩

theorem allocBuiltins_sound [DecidableEq ι] {G : NormalGraph ι} {parts : List (PropKey × Ty ι)}
    (hok : allocBuiltins G parts = true) (_hnd : (parts.map Prod.fst).Nodup) (c : Clause (Ty ι))
    {k : Nat} {V : WorldT k} {base : Nat}
    (hrec : recT ((parts.map Prod.fst).zip (parts.map fun p => meaning G p.2)) k V
      (.objAt (slots base (parts.map Prod.fst)) .absent oid)) :
    builtinInvariant G (builtinValues G) c k V (.objAt (slots base (parts.map Prod.fst)) .absent oid) := by
  have hmem : ∀ p ∈ parts, (p.1, meaning G p.2) ∈ (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2) := by
    intro p hp
    rw [List.zip_map']
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  unfold allocBuiltins at hok
  cases hs : parts.any (·.1 == CallArguments.arrayStoreField)
  · apply builtinInvariant_of_lookup
    apply ObjectMerge.lookup_slots_none
    intro hm
    obtain ⟨p, hp, hk⟩ := List.mem_map.mp hm
    have := List.any_eq_false.mp hs p hp
    simp [hk] at this
  · simp only [hs, Bool.not_true, Bool.false_or] at hok
    cases hr : G.builtins with
    | none =>
      rw [hr] at hok
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hok
      obtain ⟨ps, hps, hsk, hst⟩ := hok
      unfold builtinInvariant
      rw [hr]
      cases c.carriesInvariant
      · trivial
      · intro flds oid he _
        cases he
        intro f T hm
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        obtain ⟨flds, l, c, oid', he, hl, hw, hag⟩ := recT_at (hmem ps hps) hrec
        exact ⟨flds, l, c, oid', he, by rw [← hsk]; exact hl, hw, fun j hj W' u hu =>
          listsOnly_sound hst ((hag j hj W' u).mp hu)⟩
    | some r =>
      rw [hr] at hok
      simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true',
        beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨hfree, hunk⟩, hkeys⟩, hnum⟩, ⟨ps, hps, hsk, hst⟩⟩, ⟨pp, hpp, hpk, hpr⟩⟩ := hok
      unfold builtinInvariant
      rw [hr]
      cases c.carriesInvariant
      · trivial
      · intro flds oid he _
        cases he
        refine ⟨fun f T hm => ?_, ⟨_, _, rfl, fun q hq => ?_⟩, ?_⟩
        · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨flds, l, c, oid', he, hl, hw, hag⟩ := recT_at (hmem ps hps) hrec
            refine ⟨flds, l, c, oid', he, by rw [← hsk]; exact hl, hw, fun j hj W' u hu => ?_⟩
            exact storeTy_sound hst hunk ((hag j hj W' u).mp hu)
          · obtain ⟨flds, l, c, oid', he, hl, hw, hag⟩ := recT_at (hmem pp hpp) hrec
            refine ⟨flds, l, c, oid', he, by rw [← hpk]; exact hl, hw, fun j hj W' u hu => ?_⟩
            rw [← hpr]
            exact (builtinsFree_meaning (hpr ▸ hfree) j W' u).mp ((hag j hj W' u).mp hu)
        · obtain ⟨p, hp, hq1⟩ := List.mem_map.mp (ObjectMerge.slots_fst_mem hq)
          simp only [KeyBound.admits, hq1 ▸ hkeys p hp]
          rfl
        · -- The allocation owns no field at a canonical numeric key.
          obtain ⟨flds, l, c, oid', he, hl, hw, -⟩ := recT_at (hmem ps hps) hrec
          cases he
          refine numericOwn_of_none (by rw [← hsk]; exact hl) hw fun key hkey => ?_
          apply ObjectMerge.lookup_slots_none
          intro hm
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
          have := hnum p hp
          rw [IndexKeys.may_of_admits hkey] at this
          cases this

/-- The rows capture types reach, and those rows' free parameter rows: the
domain and map a generic closure's captures are checked over. -/
def captureDomain [DecidableEq ι] (G : NormalGraph ι) (Cs : List (Ty ι)) : List ι :=
  readsFrom G closureFuel Cs.flatten

def captureFree [DecidableEq ι] (G : NormalGraph ι) (Cs : List (Ty ι)) : FreeMap ι :=
  freeMapOf G (captureDomain G Cs) closureFuel []

/-- No capture type reads a binder of the scheme `s`: the computed free rows
are checked (`FreeOk`) and exclude them. -/
def capturesFree [DecidableEq ι] (G : NormalGraph ι) (s : SchemeRow ι) (Cs : List (Ty ι)) : Bool :=
  FreeOk G (captureDomain G Cs) (captureFree G Cs) &&
    Cs.all fun C => C.all fun l =>
      decide (l ∈ captureDomain G Cs ∧ ∀ p ∈ fv (captureFree G Cs) l, p ∉ s.binders)

theorem capturesFree_sound [DecidableEq ι] {G : NormalGraph ι} {s : SchemeRow ι} {Cs : List (Ty ι)}
    (h : capturesFree G s Cs = true) :
    FreeOk G (captureDomain G Cs) (captureFree G Cs) = true ∧
      ∀ C ∈ Cs, ∀ l ∈ C, l ∈ captureDomain G Cs ∧ ∀ p ∈ fv (captureFree G Cs) l, p ∉ s.binders := by
  simp only [capturesFree, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

/-- The frame graph code is run from at one signature: the receiver, the
parameters the code takes, then the captures (`bodyFrame`); code with a rest
finds the store of the further actuals first, at the rest's store type. -/
def codeFrame (arity : Nat) (row : Arrow (Ty ι)) (Cs : List (Ty ι)) :
    Option (Ty ι) → List (Ty ι)
  | none => bodyFrame arity row Cs
  | some S => S :: bodyFrame arity row Cs

/-- Where a frame's parameters start: after the receiver, and after the store
of a rest where the code collects one. -/
def frameOffset : Option α → Nat
  | none => 1
  | some _ => 2

/-- The frame slot holding the actual a promise is about, past `offset`
slots: what an entry environment `envOf L .nul` holds there. -/
def framePromised (e : CallEffects.Effect) (offset : Nat) (L : List Tm) : Tm :=
  match e.promise with
  | some p => envOf L .nul (offset + p.param)
  | none => .undef

/-- A frame of code binding `arity` parameters holds a promised actual among
them, as the call passed it. -/
theorem framePromised_params {e : CallEffects.Effect} {arity : Nat} (h : e.below arity = true)
    (pre : List Tm) (args vs : List Tm) :
    framePromised e pre.length (pre ++ CallArguments.parameters arity args ++ vs) = e.promised args := by
  rw [← CallEffects.Effect.promised_frame h args vs]
  rcases e with ⟨c, _ | q⟩
  · rfl
  · simp only [CallEffects.Effect.below, decide_eq_true_eq] at h
    have hlen : q.param < (CallArguments.parameters arity args ++ vs).length := by
      have := CallEffects.Effect.parameters_length arity args
      simp [this]; omega
    simp only [framePromised, envOf, CallEffects.Effect.promised, List.append_assoc,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlen, Option.getD_some]

/-- **Graph code at a signature.** Code of `arity` whose body is the graph of
the node lists `E`, `K`, entered at `start`, with captures at `Cs`, meets the
signature `row` when every run of it started from an environment meeting the
frame the row describes (`codeFrame`: with a rest, its store at `store`) is
safe at the row's result, a promise's about the parameter it names. The graph
checker establishes this (`GraphCode.goto_safe`); a code-creating rule takes
it as a premise. -/
def GraphCodeSpec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : Arrow (Ty ι)) (store : Option (Ty ι) := none) : Prop :=
  arity ≤ row.arguments.length ∧ row.effect.below arity = true ∧
  ∀ n W h L, EnvOk G (codeFrame arity row Cs store) (envOf L .nul) n W → WorldAdm W →
    HeapOk n W h → CallArguments.Values L →
      HeapObservations.SafePostExc (excOf G)
        (row.effect.result (meaning G row.result) (framePromised row.effect (frameOffset store) L))
        (fun after v => ∀ r, row.effect.post r h after v) (fun after => ∀ r, row.effect.excPost r h after)
        n W h (.goto E K start L .nul)

/-- A graph code the certificate of a unit has checked at one signature: the
code, its captures' types, the signature, and, for code collecting a rest, the
type of the store it collects. A table of them is what a code creation's
evidence names (`ProgramCertificates.Rule.funGraph`). -/
structure CodeEntry (ι : Type) where
  arity : Nat
  exprs : List Tm
  conts : List (ControlFlow.Continuation × Option ControlFlow.Target)
  start : Nat
  captures : List (Ty ι)
  row : Arrow (Ty ι)
  store : Option (Ty ι) := none
  deriving DecidableEq, Repr

def CodeEntry.Spec (G : NormalGraph ι) (c : CodeEntry ι) : Prop :=
  GraphCodeSpec G c.arity c.exprs c.conts c.start c.captures c.row c.store

theorem prependArgs_envOf (args L : List Tm) (d : Tm) :
    prependArgs args (envOf L d) = envOf (args ++ L) d := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [prependArgs, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Captured values meeting their types, as an environment. -/
theorem EnvOk.envOf_nul {G : NormalGraph ι} {Cs : List (Ty ι)} {vs : List Tm} {n W}
    (hs : ∀ v ∈ vs, Scoped 0 v) (hlen : vs.length = Cs.length)
    (hm : ∀ (i : Nat) (A : Ty ι), Cs[i]? = some A → ∀ v, vs[i]? = some v → meaning G A n W v) :
    EnvOk G Cs (envOf vs .nul) n W := by
  refine ⟨fun i => ?_, fun i A hA => ?_⟩
  · show Scoped 0 (vs.getD i .nul)
    rcases getD_mem_or vs i .nul with h | h
    · exact hs _ h
    · rw [h]; trivial
  · have hi : i < vs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hA).1
    show meaning G A n W (vs.getD i .nul)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hm i A hA _ (List.getElem?_eq_getElem hi)

/-- **The frame of an invocation.** A receiver and an admitted list, bound as
invocation binds them (the actuals the code takes, padded with `undefined`),
before the captures, meet the frame the signature describes. -/
theorem frame_envOk {G : NormalGraph ι} {arity Cs row vs n W}
    (hle : arity ≤ row.arguments.length) (hvs : EnvOk G Cs (envOf vs .nul) n W)
    {j : Nat} (hj : j ≤ n) {U : WorldT j} (hx : WExt (trunc j hj W) U) {r : Tm}
    (hr : meaning G row.receiver j U r) {args : List Tm}
    (ha : ArgsShort (row.arguments.map (meaning G)) j U args) :
    EnvOk G (bodyFrame arity row Cs) (envOf (r :: CallArguments.parameters arity args ++ vs) .nul)
      j U := by
  have hpad := ArgsShort_pad ha
  let args' := args ++ List.replicate ((row.arguments.map (meaning G)).length - args.length) Tm.undef
  have hlen' : args'.length = row.arguments.length := by
    have := ha.1
    simp only [List.length_map] at this
    simp only [args', List.length_append, List.length_replicate, List.length_map]
    omega
  have ht : ArgsT ((row.arguments.map (meaning G)).take arity) j U (args'.take arity) :=
    (ArgsT_take_drop arity hpad).1
  have htl : (args'.take arity).length = arity := by
    rw [List.length_take, hlen', Nat.min_eq_left hle]
  have hparams : CallArguments.parameters arity args = args'.take arity := by
    rw [← CallArguments.parameters_pad arity args _ (fun a hm => List.eq_of_mem_replicate hm),
      ← CallArguments.parameters_take]
    have := CallArguments.parameters_exact (args'.take arity)
    rw [htl] at this
    exact this
  have hall : ArgsT ((row.receiver :: row.arguments.take arity).map (meaning G)) j U (r :: args'.take arity) :=
    ⟨hr, by simpa [List.map_take] using ht⟩
  have henv := (hvs.transfer j hj U hx).prepend hall
  rw [prependArgs_envOf] at henv
  rw [hparams]
  simpa [bodyFrame, List.append_assoc] using henv

/-- Code of kind `kind` binds every receiver the type `R` admits as `this`
(`Invoke.binds`): `call` code every receiver, `sloppy` code only objects. -/
def KindBinds (G : NormalGraph ι) (kind : Invoke) (R : Ty ι) : Prop :=
  ∀ j U r, meaning G R j U r → kind.binds r = true

/-- Code of any kind but construct code has `[[Call]]`. -/
theorem callable_of_kind {kind : Invoke} (hk : kind ≠ .construct) {arity E K start caps rest} :
    (CallCode.graph arity E K start caps kind rest).callable = true := by
  cases kind <;> simp_all [CallCode.callable]

/-- **Invoking graph code.** A call with a receiver and an admitted list runs
the code from the frame its signature describes: the actuals it takes, padded
with `undefined`, then the captures. -/
theorem graph_invoke {G : NormalGraph ι} {arity E K start Cs row vs n W}
    (hs : GraphCodeSpec G arity E K start Cs row) (hvs : EnvOk G Cs (envOf vs .nul) n W) (hvalues : CallArguments.Values vs)
    {j : Nat} (hj : j < n) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args) :
    HeapObservations.SafePostExc (excOf G) (row.effect.result (meaning G row.result) (row.effect.promised args))
      (row.effect.post r heap) (row.effect.excPost r heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) := by
  have hsafe := hs.2.2 j U heap _ (frame_envOk hs.1 hvs (Nat.le_of_lt hj) hx hr ha) hu hh (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (meaning_value hr).1
    · rcases List.mem_append.mp hv with hv | hv
      · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl
          (ArgsT_values (fun A hA => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hA); exact meaning_valOnly G a) ha.2.1) v hv
      · exact hvalues v hv)
  have hp := framePromised_params hs.2.1 [r] args vs
  simp only [List.length_singleton, List.singleton_append] at hp
  rw [show frameOffset (none : Option (Ty ι)) = 1 from rfl, hp] at hsafe
  exact HeapObservations.SafePostExc.weaken (fun _ _ h => h r) (fun _ h => h r) hsafe

/-- Graph code with captured values meets its fixed signatures, where its
kind binds each signature's receivers. -/
theorem callsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {kind : Invoke}
    {L : List (Arrow (Ty ι))} (fs : List (PropKey × Nat)) (hk : kind ≠ .construct)
    (hb : ∀ p ∈ L, KindBinds G kind p.receiver)
    (hs : ∀ p ∈ L, GraphCodeSpec G arity E K start Cs p) (hvs : EnvOk G Cs (envOf vs .nul) n W)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.callsT (excOf G) (L.map (Arrow.map (meaning G))) n W
      (.objAt fs (.graph arity E K start vs kind) oid) := by
  refine ⟨⟨fs, _, _, rfl, callable_of_kind hk, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj U hx hu heap hh r hrv hr args hvals ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact ⟨_, .graph hrv hvals (hb p hp j U r hr), graph_invoke (hs p hp) hvs hvalues hj hx hu hh hr ha⟩

/-- Graph code of fixed arity meets a variadic signature whose fixed
parameters cover it and whose fixed part it meets: the further actuals are
discarded. -/
theorem restsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {kind : Invoke}
    {S : List (RestArrow (Ty ι))} (fs : List (PropKey × Nat)) (hk : kind ≠ .construct)
    (hb : ∀ s ∈ S, KindBinds G kind s.receiver)
    (hs : ∀ s ∈ S, GraphCodeSpec G arity E K start Cs s.fixed)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W (.objAt fs (.graph arity E K start vs kind) oid) := by
  refine ⟨⟨fs, _, _, rfl, callable_of_kind hk, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj U hx hu heap hh r hrv hr args hvals ha
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  have hspec := hs s hsm
  have hle : arity ≤ s.arguments.1.length := hspec.1
  have hbelow : s.fixed.effect.below arity = true := hspec.2.1
  have hsafe := graph_invoke hspec hvs hvalues hj hx hu hh
    (args := args.take s.arguments.1.length) hr
    (by simpa [RestArrow.mapWith, Contract.map, RestArrow.fixed] using ha.1)
  have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
      CallArguments.parameters arity args := by
    rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
      Nat.min_eq_left hle, CallArguments.parameters_take]
  rw [hp, CallEffects.Effect.promised_take (e := s.fixed.effect) hbelow hle] at hsafe
  exact ⟨_, .graph hrv hvals (hb s hsm j U r hr), hsafe⟩

/-- An equality established by a branch can refine one immutable slot. -/
theorem EnvOk.refine {G : NormalGraph ι} {Γ ρ n W i A B}
    (h : EnvOk G Γ ρ n W) (hi : Γ[i]? = some A)
    (hb : meaning G B n W (ρ i)) : EnvOk G (Γ.set i B) ρ n W := by
  refine ⟨h.1, ?_⟩
  intro j C hc
  by_cases hj : j = i
  · subst j
    have hi' := (List.getElem?_eq_some_iff.mp hi).1
    rw [List.getElem?_set_self hi'] at hc
    cases Option.some.inj hc
    exact hb
  · rw [List.getElem?_set_ne (Ne.symm hj)] at hc
    exact h.2 j C hc

/-- General evaluation-context composition. Contexts are supplied with their
ordinary small-step congruence rule. -/
theorem bind {A B : Fam} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (raise : ∀ {t v}, Raises t v → Raises (C t) v) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → Safe Ξ A n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Safe Ξ B j U h' (C v)) →
    Safe Ξ B n W h (C t) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hw hh hs hk
    rcases hs with (⟨hv, ht⟩ | hr) | ⟨U, h', t', hx, hu, step, hh', ht'⟩
    · exact hk (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ht
    · exact Or.inl (Or.inr (hr.lift raise))
    · refine Or.inr ⟨U, h', C t', hx, hu, lift step, hh', ih U h' t' hu hh' ht' ?_⟩
      intro j hj V hx' hv h'' v hh'' hval ha
      apply hk j (by omega) V _ hv h'' v hh'' hval ha
      apply WExt_trans _ hx'
      simpa only [trunc_trunc] using WExt_trunc hj hx

/-- An operand remains safe after earlier operands spend budget or change the heap. -/
def FutureSafe (Ξ : Fam) (A : Fam) (n : Nat) (W : WorldT n) (t : Tm) : Prop :=
  ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
    ∀ heap, HeapOk j U heap → Safe Ξ A j U heap t

theorem FutureSafe.transfer {A n W t} (h : FutureSafe Ξ A n W t)
    {j : Nat} (hj : j ≤ n) {U : WorldT j} (hx : WExt (trunc j hj W) U) :
    FutureSafe Ξ A j U t := by
  intro k hk V hy hv heap hh
  apply h k (by omega) V _ hv heap hh
  apply WExt_trans _ hy
  simpa only [trunc_trunc] using WExt_trunc hk hx

/-- Compose left-to-right argument evaluation with a continuation over the
resulting values. Earlier values retain their types across later heap effects. -/
theorem bind_list {B : Fam} (xs : List (Fam × Tm))
    (hA : ∀ p ∈ xs, Adm p.1) (C : List Tm → Tm)
    (lift : ∀ {h args h' args'}, CallArguments.ArgStep h args h' args' → Step h (C args) h' (C args'))
    (raise : ∀ {args v}, CallArguments.ArgRaises args v → Raises (C args) v)
    {n W heap} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (ht : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2)
    (hk : ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ heap args, HeapOk j U heap → ArgsT (xs.map Prod.fst) j U args → Safe Ξ B j U heap (C args)) :
    Safe Ξ B n W heap (C (xs.map Prod.snd)) := by
  induction xs generalizing n C heap with
  | nil =>
    exact hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap [] hh trivial
  | cons p xs ih =>
    apply bind (fun a => C (a :: xs.map Prod.snd)) (fun hs => lift (.head hs)) (fun hr => raise (.head hr))
      n W heap p.2 hw hh
      (ht p (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh)
    intro j hj U hx hu heap' v hok hv ha
    apply ih (fun q hq => hA q (by simp [hq])) (fun args => C (v :: args))
      (fun hs => lift (.tail hv hs)) (fun hr => raise (.tail hv hr)) hu hok
      (fun q hq => (ht q (by simp [hq])).transfer hj hx)
    intro k hk' V hy hv' heap'' args hok' hargs
    have hworld : WExt (trunc k (Nat.le_trans hk' hj) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc hk' hx
    apply hk k (Nat.le_trans hk' hj) V hworld hv' heap'' (v :: args) hok'
    exact ⟨(hA p (by simp)).mono k _ V hy v ((hA p (by simp)).down_le j k hk' U v ha), hargs⟩

/-- A family holds of a saved value across two later worlds. -/
theorem adm_transfer2 {A : Fam} (hA : Adm A) {j i k : Nat} {U : WorldT j} {X : WorldT i}
    {V : WorldT k} {v : Val} (ha : A j U v) (hi : i ≤ j) (hy : WExt (trunc i hi U) X)
    (hk : k ≤ i) (hz : WExt (trunc k hk X) V) : A k V v :=
  hA.mono k _ V hz v (hA.down_le i k hk X v (hA.mono i _ X hy v (hA.down_le j i hi U v ha)))

/-- `new f(args)`: the constructor runs first, then the actuals left to right;
the construct step then enters the class's body, which the constructor's
signature makes safe one level down. The signature may declare trailing
positions `Us` the source omits: each admits `undefined`, which is what the
step binds there, so the body entered is the one the padded list enters. The
signature's effect is plain, so its result operand is the result's type. -/
theorem construct_safe {B : Fam} {e : Effect} (he : e.plain = true) (xs : List (Fam × Tm)) (Us : List Fam)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    (hUA : ∀ A ∈ Us, Adm A)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (ctorsT Ξ [⟨(), xs.map Prod.fst ++ Us, B, e⟩]) n W heap f)
    (ha : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe Ξ A n W .undef) :
    Safe Ξ B n W heap (.construct f (xs.map Prod.snd)) := by
  apply bind (fun f => .construct f (xs.map Prod.snd)) Step.constructL Raises.constructL n W heap f hw hh hf
  intro j hj U hx hw' heap' v hok hv hctor
  apply bind_list xs hA (Tm.construct v) (fun hs => CallArguments.Step.constructArgs hv hs)
    (fun hr => hr.construct hv) hw' hok
    (fun p hp => (ha p hp).transfer hj hx)
  intro k hk V hz hv' heap3 args hok3 hargs
  cases k with
  | zero => trivial
  | succ k =>
    have hc := adm_transfer2 (ctorsT_adm _) hctor (Nat.le_refl j)
      (by rw [trunc_id]; exact WExt_refl _) hk hz
    have hAm : ∀ A ∈ xs.map Prod.fst ++ Us, Adm A := by
      intro A hA'
      rcases List.mem_append.mp hA' with hA' | hA'
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA'; exact hA p hp
      · exact hUA A hA'
    have hAvm : ∀ A ∈ xs.map Prod.fst, ValOnly A := by
      intro A hA'; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA'; exact hAv p hp
    have hvals : CallArguments.Values args := ArgsT_values hAvm hargs
    have hundef : ∀ A ∈ Us, A (k+1) V .undef := by
      intro A hA'
      exact safe_value_mem rfl
        ((((hu A hA').transfer hj hx)).transfer hk hz (k+1) (Nat.le_refl _) V
          (by rw [trunc_id]; exact WExt_refl _) hv' heap3 hok3)
    have hpad : ∀ a ∈ List.replicate Us.length Tm.undef, a = .undef :=
      fun _ h => List.eq_of_mem_replicate h
    have hall := ArgsT_append hargs (ArgsT_undef hundef)
    have hpvals : CallArguments.Values (args ++ List.replicate Us.length .undef) := by
      intro a h
      rcases List.mem_append.mp h with h | h
      · exact hvals a h
      · rw [hpad a h]; rfl
    obtain ⟨result, ⟨fs, c, enter, oid, rfl, hc', rfl⟩, hsafe⟩ :=
      (hc.2 _ (List.mem_singleton_self _)).erase he k (Nat.lt_succ_self k) (trunc k (Nat.le_succ k) V)
        (WExt_refl _) (WorldAdm_trunc _ hv') heap3 (HeapOk_trunc k V heap3 hok3) _ hpvals
        (ArgsT_transfer hAm hall k (Nat.le_succ k) _ (WExt_refl _))
    rw [CallArguments.construction_pad hc' _ _ hpad] at hsafe
    exact Or.inr ⟨trunc k (Nat.le_succ k) V, heap3, _, WExt_refl _, WorldAdm_trunc _ hv',
      CallArguments.construction_step hc' hvals heap3, HeapOk_trunc k V heap3 hok3, hsafe⟩

/-- A call that writes fewer actuals than its selected signature declares. The
callee runs first, then the receiver, then the actuals. The omitted positions
are exactly the ones whose contract admits `undefined`, which is the value the
machine binds there; nothing is added to the source term. -/
theorem call_safe_short {Rc B : Fam} (xs : List (Fam × Tm)) (Us : List Fam)
    (hRc : Adm Rc) (_hRcv : ValOnly Rc)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    (hUA : ∀ A ∈ Us, Adm A) (hUAv : ∀ A ∈ Us, ValOnly A)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (callsT Ξ [(Rc, xs.map Prod.fst ++ Us, B)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r)
    (ha : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe Ξ A n W .undef) :
    Safe Ξ B n W heap (.invoke f r (xs.map Prod.snd)) := by
  apply bind (fun f => .invoke f r (xs.map Prod.snd)) Step.callL Raises.callL n W heap f hw hh hf
  intro j hj U hx hw' heap' v hok hv hfun
  apply bind (fun r => .invoke v r (xs.map Prod.snd)) (Step.callRecv hv) (Raises.callRecv hv) j U heap' r hw' hok
    ((hr.transfer hj hx) j (Nat.le_refl _) U (by rw [trunc_id]; exact WExt_refl _) hw' heap' hok)
  intro i hi X hy hX heap'' rv hok'' hrv hrm
  apply bind_list xs hA (Tm.invoke v rv)
    (fun hs => (CallArguments.Prepare.args hv hrv hs).step) (fun hr => hr.invoke hv hrv) hX hok''
    (fun p hp => ((ha p hp).transfer hj hx).transfer hi hy)
  intro k hk V hz hv' heap3 args hok3 hargs
  cases k with
  | zero => trivial
  | succ k =>
    have hf' := adm_transfer2 (callsT_adm _) hfun hi hy hk hz
    have hr' := adm_transfer2 hRc hrm (Nat.le_refl i) (by rw [trunc_id]; exact WExt_refl _) hk hz
    have hundef : ∀ A ∈ Us, A (k+1) V .undef := by
      intro A hA'
      exact safe_value_mem rfl
        ((((hu A hA').transfer hj hx).transfer hi hy).transfer hk hz (k+1) (Nat.le_refl _) V
          (by rw [trunc_id]; exact WExt_refl _) hv' heap3 hok3)
    refine call_elim_short (p := (Rc, xs.map Prod.fst ++ Us, B))
      (pad := List.replicate Us.length .undef) hRc
      (by
        intro A h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hA p hp
        · exact hUA A h)
      (by
        intro A h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hAv p hp
        · exact hUAv A h)
      (by intro a h; exact List.eq_of_mem_replicate h) hrv
      hf' (List.mem_singleton_self _) hr'
      (ArgsT_append hargs (ArgsT_undef hundef)) hv' hok3

/-- A shape-only test has a fixed answer. Numeric equality needs the
singleton bits; the whole number family has no uniform answer. -/
def tagShape (tag : Tag) (s : Nat) : Option Bool :=
  match tag with
  | .isNul => some (s == 0) | .isBool => some (s == 1) | .isRef => some (s == 2)
  -- A class value (shape 11) is a function to `typeof`, as a callable is.
  | .isFun => some (s == 3 || s == 11) | .isUndef => some (s == 4)
  | .isNullish => some (s == 0 || s == 4) | .isNum => some (s == 5)
  | .numEq _ => if s == 5 then none else some false
  | .isStr => some (s == 6)
  | .strEq _ => if s == 6 then none else some false
  | .boolEq _ => if s == 1 then none else some false
  | .bigintEq _ => if s == 9 then none else some false
  | .isBigint => some (s == 9)
  | .isSymbol => some (s == 10)
  -- Null and undefined are falsy; every object, function, class, symbol and
  -- store is truthy; a Boolean, number, string or bigint needs its singleton.
  | .truthy => if s == 0 || s == 4 then some false
      else if s == 1 || s == 5 || s == 6 || s == 9 || s == 12 then none else some true
  -- Only a plain object may be an array: its clause decides (`arrayAnswer`).
  | .isArray => if s == 2 then none else some false
  -- `typeof` answers "object" for null and a plain object, array included.
  | .typeofObject => some (s == 0 || s == 2)
  -- An object's clause decides its keys (`keyAnswer`); a primitive owns none.
  | .hasKey _ => if s == 2 || s == 3 || s == 11 then none else some false

/-- Whether an object clause's members own the key `k`: a clause stating the
key present says they do; one whose own-key bound excludes it says they do
not; an open record may do either. -/
def keyAnswer (k : PropKey) (c : Clause α) : Option Bool :=
  if c.presentKeys.contains k then some true
  else if c.keyBounds.any (fun K => !K.admits k) then some false
  else none

/-- Whether `k in o` holds of an object clause's members: a clause stating
the key present says it does; one whose bounds exclude both the key and the
prototype key says it does not, since the object neither owns the key nor
has a prototype that could hold it; any other may do either. -/
def inAnswer (k : PropKey) (c : Clause α) : Option Bool :=
  if c.presentKeys.contains k then some true
  else if c.keyBounds.any (fun K => !K.admits k) &&
      c.keyBounds.any (fun K => !K.admits CallArguments.protoField) then some false
  else none

theorem inAnswer_keyAnswer {k : PropKey} {c : Clause α} {q : Bool} (h : inAnswer k c = some q) :
    keyAnswer k c = some q := by
  unfold inAnswer at h
  unfold keyAnswer
  by_cases hp : c.presentKeys.contains k = true
  · rw [if_pos hp] at h ⊢; exact h
  · rw [if_neg hp] at h ⊢
    by_cases hb : (c.keyBounds.any fun K => !K.admits k) = true
    · rw [if_pos hb]
      by_cases hb2 : (c.keyBounds.any fun K => !K.admits CallArguments.protoField) = true
      · rw [if_pos (by simp [hb, hb2])] at h; exact h
      · rw [if_neg (by simp [hb2])] at h; cases h
    · rw [if_neg (by simp [hb])] at h; cases h

/-- `Array.isArray` on an object clause: whether it owns the store key. A
clause saying its object owns the store key is of arrays; one whose bound
excludes the key is of other objects; an open record may be either, since an
array may carry other keys. -/
def arrayAnswer (c : Clause α) : Option Bool := keyAnswer CallArguments.arrayStoreField c

def tagClause (tag : Tag) (c : Clause α) : Option Bool :=
  match tag, c with
  | _, .top | _, .source => none
  | .numEq bits, .numLit value => some (numberEqual value bits)
  | .strEq s, .strLit t => some (s == t)
  | .boolEq b, .boolLit c => some (b == c)
  | .bigintEq i, .bigintLit j => some (i == j)
  | .truthy, .boolLit b => some b
  | .truthy, .numLit value => some (numberTruthy value)
  | .truthy, .strLit t => some (t != "")
  | .truthy, .bigintLit i => some (i != 0)
  | .isArray, .refs .. | .isArray, .dict .. => arrayAnswer c
  | .hasKey k, .refs .. | .hasKey k, .dict .. => inAnswer k c
  | _, _ => tagShape tag (shape c)

/-- An object clause's answer for a key is its members': each is a plain
object, owning the key exactly as the answer says. -/
theorem keyAnswer_sound {S : α → Fam} {P : α → ArgFam} {c : Clause α} {k : PropKey} {q n W v}
    (hq : keyAnswer k c = some q) (hv : semWithArgs Ξ S P c n W v) :
    ∃ flds oid, v = .objAt flds .absent oid ∧ (flds.lookup k).isSome = q := by
  unfold keyAnswer at hq
  by_cases hp : c.presentKeys.contains k = true
  · simp only [hp, ↓reduceIte, Option.some.injEq] at hq
    subst q
    obtain ⟨flds, l, oid, rfl, hl⟩ := semWithArgs_owns hv (List.contains_iff_mem.mp hp)
    exact ⟨flds, oid, rfl, by simp [hl]⟩
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hq
    by_cases hb : c.keyBounds.any (fun K => !K.admits k) = true
    · simp only [hb, ↓reduceIte, Option.some.injEq] at hq
      subst q
      obtain ⟨K, hK, hadm⟩ := List.any_eq_true.mp hb
      obtain ⟨flds, oid, rfl, hk⟩ := semWithArgs_bounded hv hK
      have hl : flds.lookup k = none :=
        ownKeysT_lookup (b := K) (k := n) (W := W) ⟨flds, oid, rfl, hk⟩ (f := k) (by simpa using hadm)
      exact ⟨flds, oid, rfl, by simp [hl]⟩
    · simp [hb] at hq

/-- An object clause's `Array.isArray` answer is its members'. -/
theorem arrayAnswer_sound {S : α → Fam} {P : α → ArgFam} {c : Clause α} {q n W v}
    (hq : arrayAnswer c = some q) (hv : semWithArgs Ξ S P c n W v) : tagHolds .isArray v = q := by
  obtain ⟨flds, oid, rfl, h⟩ := keyAnswer_sound hq hv
  simpa [tagHolds, CallArguments.arrayStoreField] using h

/-- A finite syntactic check; unknown numeric answers cannot establish either
branch. It neither executes a term nor queries semantic membership. `A` must be
of clause rows: a parameter row's members could be anything. -/
def Answers (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Prop :=
  G.plainTy A = true ∧ ∀ c ∈ expand G A, tagClause tag c = some q

/-- A shape's answer is the test's on every value of that shape. Shape 7
collects the terms that are no values, which a clause other than top and
source never admits. -/
private theorem tagShape_sound {tag : Tag} {v : Val} {q : Bool} (h7 : valueShape v ≠ 7)
    (hq : tagShape tag (valueShape v) = some q) : tagHolds tag v = q := by
  cases tag <;> cases v
  all_goals first
    | exact absurd rfl h7
    | (cases hq <;> rfl)
    | (rename_i code _; cases code <;> first
        | exact absurd rfl h7
        | (cases hq <;> rfl)
        | (rename_i kind _; cases kind <;> (cases hq <;> rfl)))

theorem tagClause_sound {S : α → Fam} {P : α → ArgFam} {c tag q n W v}
    (hq : tagClause tag c = some q) (hv : semWithArgs Ξ S P c n W v) : tagHolds tag v = q := by
  by_cases hc : c = .top
  · subst hc; cases tag <;> simp [tagClause] at hq
  by_cases hj : c = .source
  · subst hj; cases tag <;> simp [tagClause] at hq
  have hs := semWithArgs_shape hc hj hv
  -- Every clause but an object clause and a singleton answers by its shape.
  have byShape : tagClause tag c = tagShape tag (shape c) → tagHolds tag v = q := fun h =>
    tagShape_sound (by rw [hs]; cases c <;> simp_all [shape]) (by rw [hs, ← h]; exact hq)
  cases tag <;> cases c
  all_goals try first
    | exact absurd rfl hc
    | exact absurd rfl hj
    | exact byShape rfl
  case numEq.numLit value =>
    change v = .num value at hv; subst v; simpa only [tagClause, tagHolds, Option.some.injEq] using hq
  case strEq.strLit t =>
    change v = .str t at hv; subst v; simpa only [tagClause, tagHolds, Option.some.injEq] using hq
  case boolEq.boolLit b c =>
    change v = (if c then .tru else .fls) at hv; subst v
    simp only [tagClause, Option.some.injEq] at hq; subst q; cases b <;> cases c <;> rfl
  case bigintEq.bigintLit i j =>
    change v = .bigint j at hv; subst v; simpa only [tagClause, tagHolds, Option.some.injEq] using hq
  case truthy.boolLit b =>
    simp only [tagClause, Option.some.injEq] at hq; subst q; cases b <;> cases hv <;> rfl
  case truthy.numLit value =>
    change v = .num value at hv; subst v; simpa only [tagClause, tagHolds, Option.some.injEq] using hq
  case truthy.strLit t =>
    change v = .str t at hv; subst v; simpa only [tagClause, tagHolds, Option.some.injEq] using hq
  case truthy.bigintLit i =>
    change v = .bigint i at hv; subst v; simpa only [tagClause, tagHolds, Option.some.injEq] using hq
  case isArray.refs => exact arrayAnswer_sound (by simpa only [tagClause] using hq) hv
  case isArray.dict => exact arrayAnswer_sound (by simpa only [tagClause] using hq) hv
  case hasKey.refs k _ _ _ _ _ _ =>
    obtain ⟨flds, oid, rfl, h⟩ :=
      keyAnswer_sound (inAnswer_keyAnswer (by simpa only [tagClause] using hq)) hv
    simpa [tagHolds] using h
  case hasKey.dict k _ _ _ _ _ _ _ _ =>
    obtain ⟨flds, oid, rfl, h⟩ :=
      keyAnswer_sound (inAnswer_keyAnswer (by simpa only [tagClause] using hq)) hv
    simpa [tagHolds] using h

theorem answers_sound {G : NormalGraph ι} {A tag q n W v}
    (hq : Answers G A tag q) (hv : meaning G A n W v) : tagHolds tag v = q := by
  obtain ⟨c, hc, hv, -⟩ := (expand_sem G A hq.1 n W v).mp hv
  exact tagClause_sound (hq.2 c hc) hv

theorem inAnswer_protoFree {S : α → Fam} {P : α → ArgFam} {c : Clause α} {k : PropKey} {q n W v}
    (hin : inAnswer k c = some q) (hv : semWithArgs Ξ S P c n W v) : protoFree (.hasKey k) v = true := by
  unfold inAnswer at hin
  by_cases hp : c.presentKeys.contains k = true
  · obtain ⟨flds, l, oid, rfl, hl⟩ := semWithArgs_owns hv (List.contains_iff_mem.mp hp)
    simp [protoFree, hl]
  · rw [if_neg hp] at hin
    by_cases hb : ((c.keyBounds.any fun K => !K.admits k) &&
        c.keyBounds.any fun K => !K.admits CallArguments.protoField) = true
    · simp only [Bool.and_eq_true] at hb
      obtain ⟨K, hK, hadm⟩ := List.any_eq_true.mp hb.2
      obtain ⟨flds, oid, rfl, hk⟩ := semWithArgs_bounded hv hK
      have hl : flds.lookup CallArguments.protoField = none :=
        ownKeysT_lookup (b := K) (k := n) (W := W) ⟨flds, oid, rfl, hk⟩ (by simpa using hadm)
      simp [protoFree, hl]
    · rw [if_neg hb] at hin; cases hin

/-- A clause that answers `key in o` reads no prototype: its members own the
key, or have no prototype. -/
theorem tagClause_protoFree {S : α → Fam} {P : α → ArgFam} {c tag q n W v}
    (hq : tagClause tag c = some q) (hv : semWithArgs Ξ S P c n W v) : protoFree tag v = true := by
  cases tag
  case hasKey k =>
    cases c
    case refs a bs vs os ms ks =>
      have hin : inAnswer k (Clause.refs a bs vs os ms ks) = some q := by simpa [tagClause] using hq
      exact inAnswer_protoFree hin hv
    case dict a bs vs ds os ms ks cs =>
      have hin : inAnswer k (Clause.dict a bs vs ds os ms ks cs) = some q := by simpa [tagClause] using hq
      exact inAnswer_protoFree hin hv
    case top => simp [tagClause] at hq
    case source => simp [tagClause] at hq
    -- Another clause's members are no objects, whose answer is `false`, or
    -- objects whose answer is unknown.
    all_goals
      cases v with
      | objAt fs code =>
        exfalso
        have hs := semWithArgs_shape (by simp) (by simp) hv
        simp only [tagClause] at hq
        rw [← hs] at hq
        cases code with
        | graph _ _ _ _ _ kind _ => cases kind <;> simp [valueShape, tagShape] at hq
        | _ => simp [valueShape, tagShape] at hq
      | _ => rfl
  all_goals rfl

/-- An answered test's values read no prototype. -/
theorem answers_protoFree {G : NormalGraph ι} {A tag q n W v}
    (hq : Answers G A tag q) (hv : meaning G A n W v) : protoFree tag v = true := by
  obtain ⟨c, hc, hv', -⟩ := (expand_sem G A hq.1 n W v).mp hv
  exact tagClause_protoFree (hq.2 c hc) hv'

/-- An answered test's own answer is the answer of a weaker observation too:
the one that may only say the object reads a prototype. -/
theorem answers_weak {G : NormalGraph ι} {A tag q n W v}
    (hq : Answers G A tag q) (hv : meaning G A n W v)
    (ho : tagHolds tag v = q' ∨ protoFree tag v = false) : q' = q := by
  rcases ho with ho | ho
  · exact ho.symm.trans (answers_sound hq hv)
  · rw [answers_protoFree hq hv] at ho; cases ho

/-- What an answered test observes needs no prototype, so the heap does not
change it. -/
theorem answers_heap {G : NormalGraph ι} {A tag q n W v} (h : Heap)
    (hq : Answers G A tag q) (hv : meaning G A n W v) : tagHoldsIn h tag v = q := by
  obtain ⟨c, hc, hv', -⟩ := (expand_sem G A hq.1 n W v).mp hv
  rw [tagHoldsIn_of_protoFree (tagClause_protoFree (hq.2 c hc) hv')]
  exact answers_sound hq hv

end Verification.ProgramTyping
