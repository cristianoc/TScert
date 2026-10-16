import Verification.Programs.CallableObjects
import Verification.Programs.ObjectMerge
import Verification.Programs.ComputedKey
import Verification.Types.PositiveCertificates

/-!
# Program typing over positive recursive types

Types are finite unions of graph labels. Constructor rules inspect a singleton
expanded clause; subsumption is justified by the existing checked certificates.
The typing judgement is syntactic. Semantic environments enter only its soundness
proof, not its rules.
-/
namespace Verification.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower
open CallEffects (Arrow RestArrow MethodArrow MethodRestArrow Contract Effect PromiseWith)
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


export PositiveRules (readsFrom freeMapOf closureFuel)

/-! ### The built-in prototype type

The array invariant reads `ArrayProto` at one fixed assignment
(`ParameterInterpretation.builtinsAt`); a type reading no parameter row means the
same at every assignment, which a rule relating the invariant to a type checks
of the built-in prototype type. -/

/-- The built-in prototype type reads no parameter row: a checked free map of
the rows it reaches gives it none. -/
def builtinsFree [DecidableEq ι] (G : NormalGraph ι) (P : Ty ι) : Bool :=
  let D := readsFrom G closureFuel P
  let V := freeMapOf G D closureFuel []
  FreeOk G D V && P.all fun l => D.contains l && (fv V l).isEmpty

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

/-- **Graph code at a signature.** Code of `arity` whose body is the graph of
the node lists `E`, `K`, entered at `start`, with captures at `Cs`, meets the
signature `row` when every run of it started from an environment meeting the
frame the row describes (`codeFrame`: with a rest, its store at `store`) is
safe at the row's result. The graph checker establishes this
(`GraphCode.goto_safe`); a code-creating rule takes it as a premise. -/
def GraphCodeSpec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : Arrow (Ty ι)) (store : Option (Ty ι) := none) : Prop :=
  arity ≤ row.arguments.length ∧
  ∀ n W h L, EnvOk G (codeFrame arity row Cs store) (envOf L .nul) n W → WorldAdm W →
    HeapOk n W h → CallArguments.Values L →
      SafePost (excOf G) (meaning G row.result) (row.effect.post h) n W h (.goto E K start L .nul)

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
    SafePost (excOf G) (meaning G row.result) (row.effect.post heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) :=
  hs.2 j U heap _ (frame_envOk hs.1 hvs (Nat.le_of_lt hj) hx hr ha) hu hh (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (meaning_value hr).1
    · rcases List.mem_append.mp hv with hv | hv
      · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl
          (ArgsT_values (fun A hA => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hA); exact meaning_valOnly G a) ha.2.1) v hv
      · exact hvalues v hv)

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
  have hsafe := graph_invoke hspec hvs hvalues hj hx hu hh
    (args := args.take s.arguments.1.length) hr
    (by simpa [RestArrow.mapWith, Contract.map, RestArrow.fixed] using ha.1)
  have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
      CallArguments.parameters arity args := by
    rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
      Nat.min_eq_left hle, CallArguments.parameters_take]
  rw [hp] at hsafe
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
step binds there, so the body entered is the one the padded list enters. -/
theorem construct_safe {B : Fam} (xs : List (Fam × Tm)) (Us : List Fam)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    (hUA : ∀ A ∈ Us, Adm A)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (ctorsT Ξ [(xs.map Prod.fst ++ Us, B)]) n W heap f)
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
      hc.2 _ (List.mem_singleton_self _) k (Nat.lt_succ_self k) (trunc k (Nat.le_succ k) V)
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

/-! ## Binary operators

One rule types every binary operator (`arith`): each pair of operand clauses
must make the operator answer (`binop`) for every pair of their members, all
with one kind of result. Arithmetic takes two numbers or two bigints, never one
of each; a bigint divisor (of `/` or `%`) must exclude zero, and a bigint exponent be
non-negative, since those throw. `+` also takes a string and a primitive other
than a symbol, in either order, and concatenates. A relational operator takes
two numeric operands, of either kind, or two strings. -/

/-- The kind of value an operator yields. -/
inductive OpResult where
  | num | bigint | bool | str
  deriving DecidableEq, Repr

def numberClause : Clause α → Bool
  | .num | .numLit _ => true
  | _ => false

def bigintClause : Clause α → Bool
  | .bigint | .bigintLit _ => true
  | _ => false

def stringClause : Clause α → Bool
  | .str | .strLit _ => true
  | _ => false

/-- Primitives `ToNumeric` converts to a number or a bigint without running
code (`relNumeric`): numbers, bigints, Booleans, `null` and `undefined`. -/
def numericClause : Clause α → Bool
  | .num | .numLit _ | .bigint | .bigintLit _ | .bool | .boolLit _ | .nul | .undef => true
  | _ => false

/-- Primitives `ToString` converts without running code (`primString`):
every primitive but a symbol. -/
def printableClause : Clause α → Bool
  | .str | .strLit _ | .num | .numLit _ | .bigint | .bigintLit _
  | .bool | .boolLit _ | .nul | .undef => true
  | _ => false

/-- A clause of primitives only, which strict equality compares by content. -/
def primitiveClause : Clause α → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _
  | .bigint | .bigintLit _ | .symbol => true
  | _ => false

@[nospecialize] def nullishClause : Clause α → Bool
  | .nul | .undef => true
  | _ => false

/-- Clauses whose members are JavaScript objects, including callable objects. -/
@[nospecialize] def objectClause : Clause α → Bool
  | .refs .. | .dict .. | .arrs .. | .callable .. | .ctors .. => true
  | _ => false

/-- What an operator yields on members of two clauses, when it answers or
throws for every pair of them. Strict equality answers where either clause
is of primitives or of objects, which carry their identity. Two bigints give a bigint for every arithmetic
operator: a division or remainder by zero or a negative exponent throws a `RangeError`
(`binopThrows`), which is an outcome, not a wrong value, so no divisor or
exponent condition is needed. -/
def opResult (op : Arith) (c d : Clause α) : Option OpResult :=
  if op = .looseEq then
    (if primitiveClause c && primitiveClause d || nullishClause c || nullishClause d ||
       objectClause c && objectClause d
     then some .bool else none)
  else if op = .eq then
    (if primitiveClause c || primitiveClause d || objectClause c || objectClause d
     then some .bool else none)
  else if op.relational then
    if numericClause c && numericClause d || stringClause c && stringClause d
    then some .bool else none
  else if op == .add && (stringClause c && printableClause d || printableClause c && stringClause d)
  then some .str
  else if numberClause c && numberClause d then some .num
  else if bigintClause c && bigintClause d then some .bigint
  else none

/-- The values of a result kind. -/
def OpResult.holds : OpResult → Val → Prop
  | .num, v => ∃ x, v = .num x
  | .bigint, v => ∃ i, v = .bigint i
  | .bool, v => v = .tru ∨ v = .fls
  | .str, v => ∃ s, v = .str s

theorem numberClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : numberClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ x, v = .num x := by
  cases c <;> simp [numberClause] at hc
  · exact hv
  · exact ⟨_, hv⟩

theorem bigintClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : bigintClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ i, v = .bigint i := by
  cases c <;> simp [bigintClause] at hc
  · exact hv
  · exact ⟨_, hv⟩

theorem stringClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : stringClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ s, v = .str s := by
  cases c <;> simp [stringClause] at hc
  · exact hv
  · exact ⟨_, hv⟩

/-- A member of a printable clause converts by `ToString`. -/
theorem printableClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : printableClause c = true) (hv : semWithArgs Ξ X P c n W v) : ∃ t, primString v = some t := by
  cases c <;> simp [printableClause] at hc <;> simp only [semWithArgs] at hv
  all_goals first
    | (rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩)
    | (obtain ⟨_, rfl⟩ := hv; exact ⟨_, rfl⟩)
    | (subst hv; exact ⟨_, rfl⟩)
    | (split at hv <;> subst hv <;> exact ⟨_, rfl⟩)

theorem primitiveClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : primitiveClause c = true) (hv : semWithArgs Ξ X P c n W v) : isPrim v = true := by
  cases c <;> simp [primitiveClause] at hc <;> simp only [semWithArgs] at hv
  all_goals first
    | (rcases hv with rfl | rfl <;> rfl)
    | (obtain ⟨_, rfl⟩ := hv; rfl)
    | (subst hv; rfl)
    | (split at hv <;> subst hv <;> rfl)
    | (simp only [nulT, undefT, boolT, numT, strT, bigintT, symbolT] at hv;
       first | (subst hv; rfl) | (rcases hv with rfl | rfl <;> rfl) | (obtain ⟨_, rfl⟩ := hv; rfl))

/-- A member of a numeric clause converts by `ToNumeric` to a number or a bigint. -/
theorem numericClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : numericClause c = true) (hv : semWithArgs Ξ X P c n W v) :
    ∃ x, relNumeric v = some x ∧ ((∃ y, x = .num y) ∨ ∃ i, x = .bigint i) := by
  cases c <;> simp [numericClause] at hc <;> simp only [semWithArgs] at hv
  all_goals first
    | (rcases hv with rfl | rfl <;> exact ⟨_, rfl, by simp⟩)
    | (obtain ⟨_, rfl⟩ := hv; exact ⟨_, rfl, by simp⟩)
    | (subst hv; exact ⟨_, rfl, by simp⟩)
    | (split at hv <;> subst hv <;> exact ⟨_, rfl, by simp⟩)

/-- Two operands `ToNumeric` converts compare to a Boolean. -/
theorem relationalValue_numeric {op : Arith} {v w x y : Tm}
    (hx : relNumeric v = some x) (hy : relNumeric w = some y)
    (hxk : (∃ u, x = .num u) ∨ ∃ i, x = .bigint i) (hyk : (∃ u, y = .num u) ∨ ∃ i, y = .bigint i) :
    ∃ q, relationalValue op v w = some (boolVal q) := by
  have hnum : relationalValue op v w = numericRelation op x y := by
    unfold relationalValue
    split
    · simp [relNumeric] at hx
    · simp [hx, hy]
  rw [hnum]
  rcases hxk with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases hyk with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
    exact ⟨_, rfl⟩

theorem nullishClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : nullishClause c = true) (hv : semWithArgs Ξ X P c n W v) : isNullish v = true := by
  cases c <;> simp [nullishClause] at hc <;> simp only [semWithArgs] at hv
  all_goals subst hv; rfl

theorem looseEquals_some {v w : Tm} (hv : isVal v = true) (hw : isVal w = true)
    (h : (isPrim v && isPrim w || isNullish v || isNullish w) = true) :
    ∃ q, looseEquals v w = some q := by
  unfold looseEquals
  simp only [hv, hw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hp : (isPrim v && isPrim w) = true
  · exact ⟨primitiveEquals v w, by simp [hp]⟩
  · have hn : (isNullish v || isNullish w) = true := by simpa [hp] using h
    exact ⟨false, by simp [hp, hn]⟩

theorem objectClause_member {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : objectClause c = true) (hv : semWithArgs Ξ X P c n W v) :
    ∃ fs code oid, v = .objAt fs code oid := by
  cases c with
  | refs | dict => obtain ⟨fs, oid, h, _⟩ := hv.1.1; exact ⟨fs, .absent, oid, h⟩
  | callable => obtain ⟨fs, code, oid, h, _⟩ := hv.1.1.1; exact ⟨fs, code, oid, h⟩
  | arrs => obtain ⟨fs, code, oid, h, _⟩ := hv.1.1; exact ⟨fs, code, oid, h⟩
  | ctors => obtain ⟨fs, _, _, _, _, _, _, oid, h, _⟩ := hv.1.1.1; exact ⟨fs, _, oid, h⟩
  | _ => simp [objectClause] at hc

/-- Strict equality answers when one operand is a primitive or an object. -/
theorem strictEquals_some {v w : Tm} (hv : isVal v = true) (hw : isVal w = true)
    (h : (isPrim v || isPrim w) = true ∨ (∃ fs code oid, v = .objAt fs code oid) ∨
      (∃ fs code oid, w = .objAt fs code oid)) :
    ∃ q, strictEquals v w = some q := by
  unfold strictEquals
  simp only [hv, hw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hp : (isPrim v || isPrim w) = true
  · exact ⟨sameValue v w, by simp [hp]⟩
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  have hp' : isPrim v = false ∧ isPrim w = false := by simpa using hp
  rcases h with h | ⟨fs, code, oid, rfl⟩ | ⟨fs, code, oid, rfl⟩
  · exact absurd h hp
  · cases w <;> simp_all [isPrim, isVal]
  · cases v <;> simp_all [isPrim, isVal]

/-- `+` of a string and a printable value, in either order, is a string. -/
theorem add_string {s : String} {w : Tm} {t : String} (ht : primString w = some t) :
    binop .add (.str s) w = some (.str (s ++ t)) ∧ binop .add w (.str s) = some (.str (t ++ s)) := by
  cases w <;> simp [primString] at ht <;> subst ht <;> simp [binop, primString, Arith.relational]
  all_goals rfl

theorem boolVal_holds (q : Bool) : OpResult.holds .bool (boolVal q) := by
  cases q <;> simp [OpResult.holds, boolVal]

/-- **The classification is sound**: on members of the two clauses the
operator answers, with a value of the kind it names, or throws. -/
theorem opResult_sound {X : α → Fam} {P : α → ArgFam} {op : Arith} {c d : Clause α} {r n W v w}
    (h : opResult op c d = some r) (hv : semWithArgs Ξ X P c n W v) (hw : semWithArgs Ξ X P d n W w) :
    (∃ z, binop op v w = some z ∧ r.holds z) ∨ binopThrows op v w = true := by
  unfold opResult at h
  by_cases hloose : op = .looseEq
  · subst hloose
    simp only [↓reduceIte] at h
    split at h
    · rename_i hp
      cases h
      have answer : ∃ q, looseEquals v w = some q := by
        rcases Bool.or_eq_true_iff.mp hp with hp | ho
        · apply looseEquals_some (semWithArgs_value hv).1 (semWithArgs_value hw).1
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hp ⊢
          rcases hp with (⟨hc, hd⟩ | hc) | hd
          · exact .inl (.inl ⟨primitiveClause_member hc hv, primitiveClause_member hd hw⟩)
          · exact .inl (.inr (nullishClause_member hc hv))
          · exact .inr (nullishClause_member hd hw)
        · simp only [Bool.and_eq_true] at ho
          obtain ⟨hc, hd⟩ := ho
          obtain ⟨fs, code, oid, rfl⟩ := objectClause_member hc hv
          obtain ⟨gs, other, oid', rfl⟩ := objectClause_member hd hw
          exact ⟨oid == oid', by simp [looseEquals, strictEquals, isVal, isPrim, isNullish]⟩
      obtain ⟨q, hq⟩ := answer
      exact .inl ⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩
    · cases h
  simp only [hloose, ↓reduceIte] at h
  by_cases heq : op = .eq
  · subst heq
    simp only [↓reduceIte] at h
    split at h
    · rename_i hp
      cases h
      have hval := (semWithArgs_value hv).1
      have wval := (semWithArgs_value hw).1
      simp only [Bool.or_eq_true] at hp
      obtain ⟨q, hq⟩ := strictEquals_some hval wval (by
        rcases hp with ((hp | hp) | hp) | hp
        · exact .inl (by simp [primitiveClause_member hp hv])
        · exact .inl (by simp [primitiveClause_member hp hw])
        · exact .inr (.inl (objectClause_member hp hv))
        · exact .inr (.inr (objectClause_member hp hw)))
      exact .inl ⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩
    · cases h
  simp only [heq, ↓reduceIte] at h
  by_cases hrel : op.relational = true
  · simp only [hrel, ↓reduceIte] at h
    split at h
    · rename_i hops
      cases h
      rcases Bool.or_eq_true_iff.mp hops with hops | hops
      · rcases Bool.and_eq_true_iff.mp hops with ⟨hc, hd⟩
        obtain ⟨x, hx, hxk⟩ := numericClause_member hc hv
        obtain ⟨y, hy, hyk⟩ := numericClause_member hd hw
        obtain ⟨q, hq⟩ := relationalValue_numeric (op := op) hx hy hxk hyk
        exact .inl ⟨boolVal q, by simp [binop, hloose, hrel, heq, hq], boolVal_holds _⟩
      · rcases Bool.and_eq_true_iff.mp hops with ⟨hc, hd⟩
        obtain ⟨x, rfl⟩ := stringClause_member hc hv
        obtain ⟨y, rfl⟩ := stringClause_member hd hw
        exact .inl ⟨boolVal (relationHolds op (some (unitsOrder (utf16Units x) (utf16Units y)))),
          by simp [binop, hloose, hrel, heq, relationalValue], boolVal_holds _⟩
    · cases h
  · simp only [hrel, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i hops
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hops
      obtain ⟨hadd, (⟨hc, hd⟩ | ⟨hc, hd⟩)⟩ := hops <;>
        obtain rfl : op = .add := by cases op <;> first | rfl | exact absurd hadd (by decide)
      · obtain ⟨x, rfl⟩ := stringClause_member hc hv
        obtain ⟨t, ht⟩ := printableClause_member hd hw
        exact .inl ⟨_, (add_string ht).1, _, rfl⟩
      · obtain ⟨t, ht⟩ := printableClause_member hc hv
        obtain ⟨y, rfl⟩ := stringClause_member hd hw
        exact .inl ⟨_, (add_string ht).2, _, rfl⟩
    split at h
    · rename_i hops
      cases h
      rcases Bool.and_eq_true_iff.mp hops with ⟨hc, hd⟩
      obtain ⟨x, rfl⟩ := numberClause_member hc hv
      obtain ⟨y, rfl⟩ := numberClause_member hd hw
      exact .inl ⟨.num (arithBits op x y), by simp [binop, hloose, hrel, heq], _, rfl⟩
    · split at h
      · rename_i _ hops
        cases h
        simp only [Bool.and_eq_true] at hops
        obtain ⟨hc, hd⟩ := hops
        obtain ⟨x, rfl⟩ := bigintClause_member hc hv
        obtain ⟨y, rfl⟩ := bigintClause_member hd hw
        cases hz : bigintArith op x y with
        | some z => exact .inl ⟨.bigint z, by simp [binop, hloose, hrel, heq, hz], z, rfl⟩
        | none =>
          refine .inr ?_
          cases op <;> simp [Arith.relational] at hrel heq hloose <;> simp [bigintArith] at hz <;>
            simp [binopThrows, hz]
      · cases h

/-- Two operand types an operator answers for, pair by pair, with one kind
of result. -/
def Operands (G : NormalGraph ι) (op : Arith) (A B : Ty ι) (r : OpResult) : Prop :=
  G.plainTy A = true ∧ G.plainTy B = true ∧
    ∀ c ∈ expand G A, ∀ d ∈ expand G B, opResult op c d = some r

/-- A result type holding every value of the kind: the number, bigint or
string family, or both Booleans. -/
def OpResult.covers (G : NormalGraph ι) (N : Ty ι) : OpResult → Prop
  | .num => Represents G N .num
  | .bigint => Represents G N .bigint
  | .bool => (.boolLit true) ∈ expand G N ∧ (.boolLit false) ∈ expand G N
  | .str => Represents G N .str

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (A B : Ty ι) (r : OpResult) :
    Decidable (Operands G op A B r) := by unfold Operands; infer_instance

instance [DecidableEq ι] (G : NormalGraph ι) (N : Ty ι) (r : OpResult) :
    Decidable (r.covers G N) := by
  cases r <;> unfold OpResult.covers <;> unfold Represents <;> infer_instance

/-- The kind a pair of operand types gives, read from their first clauses;
`Operands` then checks every pair. -/
def operandsResult (G : NormalGraph ι) (op : Arith) (A B : Ty ι) : Option OpResult :=
  match expand G A, expand G B with
  | c :: _, d :: _ => opResult op c d
  | _, _ => none

/-- The operand types give one kind of result, pair by pair, and the result
type holds every value of it. -/
def ClauseOperatorTypes (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) : Prop :=
  match operandsResult G op A B with
  | some r => Operands G op A B r ∧ r.covers G N
  | none => False

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) :
    Decidable (ClauseOperatorTypes G op A B N) := by
  unfold ClauseOperatorTypes; split <;> infer_instance

/-- A clause whose members decide an equality operator against any value:
primitives or objects for strict equality, nullish values for loose. -/
def decidingClause (op : Arith) (c : Clause α) : Bool :=
  (decide (op = .eq) && sourceClause c) ||
    (decide (op = .looseEq) && nullishClause c)

/-- An operand type every clause of which decides the equality operator. -/
def EqualityDecided (G : NormalGraph ι) (op : Arith) (X : Ty ι) : Prop :=
  G.plainTy X = true ∧ ∀ c ∈ expand G X, decidingClause op c = true

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (X : Ty ι) :
    Decidable (EqualityDecided G op X) := by unfold EqualityDecided; infer_instance

/-- A member of a deciding clause compared with any value, in either order,
gives a Boolean. -/
theorem decidingClause_sound {X : α → Fam} {P : α → ArgFam} {op : Arith} {c : Clause α} {n W v w}
    (hc : decidingClause op c = true) (hv : semWithArgs Ξ X P c n W v) (hw : isVal w = true) :
    (∃ z, binop op v w = some z ∧ OpResult.bool.holds z) ∧
      (∃ z, binop op w v = some z ∧ OpResult.bool.holds z) := by
  have hval := (semWithArgs_value hv).1
  simp only [decidingClause, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
  · have hk : (isPrim v = true) ∨ ∃ fs code oid, v = .objAt fs code oid := by
      have hj := (sourceClause_sound hc hv).1
      cases v <;> simp_all [isSourceVal, isPrim]
    obtain ⟨q, hq⟩ := strictEquals_some hval hw (by
      rcases hk with hk | hk
      · exact .inl (by simp [hk])
      · exact .inr (.inl hk))
    obtain ⟨q', hq'⟩ := strictEquals_some hw hval (by
      rcases hk with hk | hk
      · exact .inl (by simp [hk])
      · exact .inr (.inr hk))
    exact ⟨⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩,
      ⟨boolVal q', by simp [binop, hq'], boolVal_holds _⟩⟩
  · have hn := nullishClause_member hc hv
    obtain ⟨q, hq⟩ := looseEquals_some hval hw (by simp [hn])
    obtain ⟨q', hq'⟩ := looseEquals_some hw hval (by simp [hn])
    exact ⟨⟨boolVal q, by simp [binop, hq], boolVal_holds _⟩,
      ⟨boolVal q', by simp [binop, hq'], boolVal_holds _⟩⟩

/-- The operator rule's premise on the types: the operand types give one kind
of result, pair by pair; or one operand's type decides the equality operator
whatever the other's value, a type parameter's included. The result type
holds every value of the kind. -/
def OperatorTypes (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) : Prop :=
  ClauseOperatorTypes G op A B N ∨
    ((EqualityDecided G op A ∨ EqualityDecided G op B) ∧ OpResult.bool.covers G N)

instance [DecidableEq ι] (G : NormalGraph ι) (op : Arith) (A B N : Ty ι) :
    Decidable (OperatorTypes G op A B N) := by unfold OperatorTypes; infer_instance

/-! ## Variadic functions

A variadic body finds the actuals past its fixed parameters in a fresh array in
slot 0. The array's type is an object whose one field holds a store of any
length at the element type; a spread reads a store whose every position's type
is among the element type's labels, and `undefined` must be among them when the
store may have a hole. -/

/-- The variadic signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def restSigs (G : NormalGraph ι) (F : Ty ι) : List (RestArrow (Ty ι)) :=
  match expand G F with
  | [.arrs _ S] | [.callable _ _ _ S] => S
  | _ => []

theorem restsT_of_restSigs {G : NormalGraph ι} {F : Ty ι} {s} (hs : s ∈ restSigs G F) {n W v}
    (hv : meaning G F n W v) :
    CallEffects.restsT (excOf G) [s.mapWith (meaning G) (argMeaning G)] n W v := by
  unfold restSigs at hs
  split at hs
  · rename_i L S hF
    have hv' := ((represents_raw hF n W v) hv).2
    exact CallEffects.restsT_select hv' (List.mem_map_of_mem hs)
  · rename_i P Ps L S hF
    have hv' := ((represents_raw hF n W v) hv).2
    exact CallEffects.restsT_select hv' (List.mem_map_of_mem hs)
  · cases hs

/-- The member a type's one object clause names by a key: a host-relative
method, whose contract holds when it is invoked on the object it is read from. -/
def memberOf (G : NormalGraph ι) (O : Ty ι) (k : PropKey) : Option (MethodMembers.Sig (Ty ι)) :=
  match expand G O with
  | [.refs _ _ _ _ ms _] | [.dict _ _ _ _ _ ms _ _] => ms.find? (·.key == k)
  | _ => none

/-- The quantified signatures of the member of key `k` of `O`: the schemes a
generic method's member bound to its host meets (`bindScheme`). -/
def memberSchemes (G : NormalGraph ι) (O : Ty ι) (k : PropKey) : List (Ty ι) :=
  ((memberOf G O k).map (·.schemes)).getD []

/-- A fixed signature covered by one of a member's: each claimed parameter
within the member's, and the member's result within the claimed one, by
checked proofs. The claimed types may be other rows for the same types, such as
a producer's copy of a declared array type. -/
def CoveredCallUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι))
    (c : MethodArrow (Ty ι)) : Prop :=
  q.arguments.length = c.arguments.length ∧
    (∀ x ∈ q.arguments.zip c.arguments, ∃ p, PositiveCertificates.checkUsing G images x.1 x.2 p = true) ∧
    (∃ p, PositiveCertificates.checkUsing G images c.result q.result p = true) ∧ c.effect.covers q.effect = true

/-- Parameters each within the member's, as families. -/
theorem CoveredCallUsing.params [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} :
    ∀ {Ds Cs : List (Ty ι)}, Ds.length = Cs.length →
      (∀ x ∈ Ds.zip Cs, ∃ p, PositiveCertificates.checkUsing G images x.1 x.2 p = true) →
      ArgsLe (Ds.map (meaning G)) (Cs.map (meaning G))
  | [], [], _, _ => .nil
  | D :: Ds, C :: Cs, hl, h => by
    obtain ⟨p, hp⟩ := h (D, C) (by simp)
    exact .cons (PositiveCertificates.acceptedUsing hp)
      (CoveredCallUsing.params (by simpa using hl) fun x hx => h x (by simp [hx]))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A variadic signature covered by one of a member's with as many fixed
parameters: each claimed fixed parameter within the member's, the claimed
rest within the member's, and the member's result within the claimed one, by
checked proofs. As for `CoveredCallUsing`, the claimed types may be other
rows for the same types, such as a producer's copy of a declared array type
at the rest. -/
def CoveredRestUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : RestArrow (Ty ι))
    (c : MethodRestArrow (Ty ι)) : Prop :=
  q.arguments.1.length = c.arguments.1.length ∧
    (∀ x ∈ q.arguments.1.zip c.arguments.1, ∃ p, PositiveCertificates.checkUsing G images x.1 x.2 p = true) ∧
    (∃ p, PositiveCertificates.checkUsing G images q.arguments.2 c.arguments.2 p = true) ∧
    (∃ p, PositiveCertificates.checkUsing G images c.result q.result p = true) ∧ c.effect.covers q.effect = true

/-- A checked proof is an inclusion of argument lists too: the argument
component of the two types' meanings. -/
theorem argsAcceptedUsing [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {S T proof}
    (h : PositiveCertificates.checkUsing G images S T proof = true) (n W vs)
    (hv : argMeaning G S n W vs) : argMeaning G T n W vs :=
  PositiveCertificates.checkUsing_sound h G.env n W (.inr vs) hv

/-- Pointwise wider fixed parameters and a wider rest admit every list the
narrower ones do. -/
theorem ArgsRest_mono {Qs Ps : List Fam} {E E' : ArgFam} {j : Nat} {W : WorldT j} (h : ArgsLe Qs Ps)
    (he : ∀ vs, E j W vs → E' j W vs) {args : List Tm}
    (ha : ArgsRest Qs E j W args) : ArgsRest Ps E' j W args := by
  obtain ⟨hs, hr⟩ := ha
  rw [ArgsLe_length h] at hs hr
  exact ⟨ArgsShort_mono h hs, he _ hr⟩

/-- A member of a host's type is found by the member's key on the host, whose
contract implies the member's signatures invoked on that host. -/
theorem memberOf_at {G : NormalGraph ι} {O : Ty ι} {k : PropKey} {m : MethodMembers.Sig (Ty ι)}
    (hm : memberOf G O k = some m) {n W v} (hv : meaning G O n W v) :
    m.key = k ∧ MethodMembers.memberT (excOf G) (MethodMembers.Member.of (meaning G) (argMeaning G) m) n W v := by
  unfold memberOf at hm
  split at hm
  all_goals try contradiction
  all_goals
    rename_i ms hO
    have hmem := List.mem_of_find?_eq_some hm
    have hkey : m.key = k := by simpa using List.find?_some hm
    have hs := represents_raw (show Represents G O _ from hO) n W v hv
    exact ⟨hkey, MethodMembers.methodT_at (List.mem_map_of_mem hmem)
      (by first | exact hs.2.2.2.1 | exact hs.2.2.2.2.1)⟩

/-- **Reading along the chain.** A key held `d` prototypes up is read in `d`
delegation steps, each one level down, then from its location, whose contract
implies `A`. -/
theorem along_read_safe {A : Fam} (hval : ValOnly A) (key : PropKey) :
    ∀ (d : Nat) {n : Nat} {W : WorldT n} {h : Heap} {v : Val}, WorldAdm W → HeapOk n W h →
      MethodMembers.along key A d n W v → Safe Ξ A n W h (.readAt key v)
  | 0, n, W, h, _, hw, hh, ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ => read_view_rule_ext hval n W h l hw hh hf hl hag
  | d + 1, n, W, h, _, hw, hh, ⟨flds, oid, rfl, hmiss, hp⟩ => by
    obtain ⟨pf, lp, cp, oid', hρ, hpf, hlp, hpag⟩ := hp
    cases hρ
    cases n with
    | zero => trivial
    | succ q =>
      obtain ⟨pv, hpv, hmem⟩ := hh.2 lp cp hlp
      have hU := WorldAdm_trunc (Nat.le_succ q) hw
      have hH := HeapOk_trunc q W h hh
      exact Or.inr ⟨trunc q (Nat.le_succ q) W, h, .readAt key pv, WExt_refl _,
        hU, .readProto hmiss hpf hpv, hH,
        along_read_safe hval key d hU hH (hpag q (by omega) _ (WExt_refl _) pv (hmem q (by omega)))⟩

/-- **Reading a member.** The read finds the key on the host, or, some steps
later, on an object along the host's prototype chain; either way the value
read meets the member's signatures invoked on the host. -/
theorem member_read_safe {m : MethodMembers.Member} {n : Nat} {W : WorldT n} {h : Heap} {v : Val}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hm : MethodMembers.memberT Ξ m n W v) :
    Safe Ξ (MethodMembers.onHost Ξ v m) n W h (.readAt m.key v) := by
  have hval : ValOnly (MethodMembers.onHost Ξ v m) := fun _ _ _ hv => hv.1.1.val
  obtain ⟨d, hd⟩ := hm
  exact along_read_safe hval m.key d hw hh hd

/-- The fixed signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def callSigs (G : NormalGraph ι) (F : Ty ι) : List (Arrow (Ty ι)) :=
  match expand G F with
  | [.arrs L _] | [.callable _ _ L _] => L
  | _ => []

theorem callsT_of_callSigs {G : NormalGraph ι} {F : Ty ι} {p} (hp : p ∈ callSigs G F) {n W v}
    (hv : meaning G F n W v) :
    CallEffects.callsT (excOf G) [p.map (meaning G)] n W v := by
  unfold callSigs at hp
  split at hp
  · rename_i L S hF
    have hv' := ((represents_raw hF n W v) hv).1
    exact CallEffects.callsT_select hv' (List.mem_map_of_mem hp)
  · rename_i P Ps L S hF
    have hv' := ((represents_raw hF n W v) hv).1.2
    exact CallEffects.callsT_select hv' (List.mem_map_of_mem hp)
  · cases hp

/-- Saved slots, in order, at the contracts the environment gives them. -/
theorem ArgsT_slots {G : NormalGraph ι} {Γ ρ n W} (he : EnvOk G Γ ρ n W) :
    ∀ {slots : List Nat} {Ps : List (Ty ι)}, slots.map (Γ[·]?) = Ps.map some →
      ArgsT (Ps.map (meaning G)) n W (slots.map ρ)
  | [], [], _ => trivial
  | i :: slots, P :: Ps, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨he.2 _ _ h.1, ArgsT_slots he h.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The type of the store a variadic body receives for a rest type: the rest's
one tuple contract, as a writable store, since the store is fresh. -/
def RestStore (G : NormalGraph ι) (S P : Ty ι) : Prop :=
  match expand G P, expand G S with
  | [.pack T []], [.list U []] => U = { T with readonly := false, presence := U.presence }
  | _, _ => False

/-- A store type whose elements a spread passes at `E`. -/
def SpreadsInto (G : NormalGraph ι) (S E : Ty ι) : Prop :=
  match expand G S with
  | [.list T []] =>
      (∀ A ∈ T.required ++ T.optional ++ T.rest.toList, ∀ i ∈ A, i ∈ E) ∧
      (T.presence ≠ .sparse ∨ ∃ i ∈ E, Represents G [i] .undef)
  | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (S P : Ty ι) : Decidable (RestStore G S P) := by
  unfold RestStore; split <;> (try dsimp only [Represents]) <;> infer_instance

instance [DecidableEq ι] (G : NormalGraph ι) (S E : Ty ι) : Decidable (SpreadsInto G S E) := by
  unfold SpreadsInto; split <;> (try dsimp only [Represents]) <;> infer_instance

/-- An actual as a call writes it: itself, or a spread of it. -/
def spreadTerm (p : Bool × Tm) : Tm := if p.1 then .spread p.2 else p.2

theorem instantiate_spreadTerm (d : Nat) (ρ : Env) (p : Bool × Tm) :
    instantiate d ρ (spreadTerm p) = spreadTerm (p.1, instantiate d ρ p.2) := by
  rcases p with ⟨_ | _, t⟩ <;> simp [spreadTerm, instantiate]

theorem positionTy_eq (T : Tuple (Ty ι)) (i : Nat) :
    positionTy T i = PositiveNormalization.Tuple.position T i := by
  rcases hr : T.required[i]? with _ | A <;>
    rcases ho : T.optional[i - T.required.length]? with _ | B <;>
    simp [positionTy, PositiveNormalization.Tuple.position, hr, ho]

theorem positionTy_mem {T : Tuple (Ty ι)} {i : Nat} {A : Ty ι} (h : positionTy T i = some A) :
    A ∈ T.required ++ T.optional ++ T.rest.toList := by
  unfold positionTy at h
  split at h
  · rename_i B hB; cases h; simp [List.mem_of_getElem? hB]
  · split at h
    · rename_i B hB; cases h; simp [List.mem_of_getElem? hB]
    · split at h
      · simp [h]
      · cases h

theorem undef_of_label {G : NormalGraph ι} {E : Ty ι} {i : ι} (hi : i ∈ E)
    (hr : Represents G [i] .undef) (j : Nat) (U : WorldT j) : meaning G E j U .undef := by
  obtain ⟨i', hi', hv⟩ := (represents_back hr j U .undef) rfl
  simp only [List.mem_singleton] at hi'
  rw [hi'] at hv
  exact ⟨i, hi, hv⟩

theorem spreadsInto_sound {G : NormalGraph ι} {S E : Ty ι} (h : SpreadsInto G S E) :
    RestCalls.Spreads (meaning G S) (meaning G E) := by
  unfold SpreadsInto at h
  split at h
  · rename_i T hS
    have hl := RestCalls.listT_spreads (T := tupleFams (meaning G) T) (E := meaning G E)
      (by
        intro i A hA
        rw [positionFam_tupleFams] at hA
        obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp hA
        rintro n W v ⟨k, hk, hv⟩
        exact ⟨k, h.1 A' (positionTy_mem hA') k hk, hv⟩)
      (by
        intro hs j U
        rcases h.2 with hd | ⟨i, hi, hr⟩
        · simp [tupleFams] at hs; simp [hs] at hd
        · exact undef_of_label hi hr j U)
    intro n W heap v hh hv
    exact hl n W heap v hh ((represents_raw hS n W v) hv).1
  · exact h.elim

/-- A prefix covering a signature's first fixed positions, then its element
past them: its first positions are the signature's, the rest the element. -/
theorem prefix_take_drop {α : Type} (Ps : List α) (k : Nat) (E : α) :
    (Ps.take k ++ List.replicate (k - Ps.length) E).take Ps.length = Ps.take k ∧
    (Ps.take k ++ List.replicate (k - Ps.length) E).drop Ps.length =
      List.replicate (k - Ps.length) E := by
  by_cases hk : k ≤ Ps.length
  · have h0 : k - Ps.length = 0 := by omega
    rw [h0, List.replicate_zero, List.append_nil]
    refine ⟨List.take_of_length_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega)⟩
  · rw [List.take_of_length_le (show Ps.length ≤ k by omega)]
    simp

/-- **Allocating the rest store.** A store of the actuals past the fixed ones
meets a rest-store type when the actuals as one pack meet the rest type. -/
theorem restStore_safe {G : NormalGraph ι} {S P : Ty ι} (hS : RestStore G S P)
    {n : Nat} {W : WorldT n} {h : Heap} {extra : List Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (he : argMeaning G P n W extra) (hvals : CallArguments.Values extra) :
    Safe (excOf G) (meaning G S) n W h (.arrLit extra) := by
  unfold RestStore at hS
  split at hS
  · rename_i T U hP hR
    let T' := { T with presence := U.presence }
    have hpos : ∀ i B, positionFam (tupleFams (meaning G) T') i = some B → Adm B := by
      intro i B hB
      rw [PositiveNormalization.positionFam_tupleFams] at hB
      obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hB
      exact meaning_adm G b
    have hposv : ∀ i B, positionFam (tupleFams (meaning G) T') i = some B → ValOnly B := by
      intro i B hB
      rw [PositiveNormalization.positionFam_tupleFams] at hB
      obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hB
      exact meaning_valOnly G b
    have hfit : ArgumentContracts.Fits (tupleFams (meaning G) T') n W extra := by
      exact (mixed_pack_args hP).mp he
    have := RestCalls.argument_alloc_safe (Ξ := excOf G) hpos hposv hw hh hfit hvals
    apply Safe_mono n _ W h _ this
    intro k _ V v hv
    apply (represents_back hR k V v)
    refine ⟨?_, by simp⟩
    have heq : tupleFams (meaning G) U = {tupleFams (meaning G) T' with readonly := false} := by
      rw [hS]; rfl
    rw [heq]
    exact hv
  · exact hS.elim


/-- **Invoking graph code with a rest.** A call at a variadic signature
whose fixed parameters are the code's first collects the actuals past them
into a fresh store, which meets the rest's store type, and runs the code from
the frame the signature describes with that store in slot 0. -/
theorem graphRest_invoke {G : NormalGraph ι} {arity E K start Cs A vs n W}
    {s : RestArrow (Ty ι)}
    (hs : GraphCodeSpec G arity E K start Cs s.fixed (some A))
    (hk : s.arguments.1.length = arity) (harr : RestStore G A s.arguments.2)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (_hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs)
    {j : Nat} (hj : j < n) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G s.receiver j U r)
    {args : List Tm} (hvals : CallArguments.Values args)
    (ha : ArgsRest (s.arguments.1.map (meaning G)) (argMeaning G s.arguments.2) j U args) :
    SafePost (excOf G) (meaning G s.result) (s.effect.post heap) j U heap (CallArguments.graphEntry arity E K start vs true r args) := by
  obtain ⟨hshort, hpack⟩ := ha
  simp only [List.length_map, hk] at hshort hpack
  have hle : arity ≤ s.fixed.arguments.length := by simp [RestArrow.fixed, hk]
  have hframe := frame_envOk (row := s.fixed) hle hvs (Nat.le_of_lt hj) hx
    hr (args := args.take arity) (by simpa [RestArrow.fixed] using hshort)
  rw [CallArguments.parameters_take] at hframe
  have hclosed : ∀ v ∈ r :: CallArguments.parameters arity args ++ vs, Scoped 0 v := by
    intro v hm
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
    have := hframe.1 i
    unfold envOf at this
    rw [List.getD_eq_getElem?_getD, hi] at this
    exact this
  unfold CallArguments.graphEntry
  have hstore : SafePost (excOf G) (meaning G A) (fun heap' _ => heap.IsPrefix heap')
      j U heap (.arrLit (args.drop arity)) := by
    apply HeapObservations.one_step rfl rfl (.arrAlloc (fun a hm => hvals a (List.mem_of_mem_drop hm)))
      ⟨args.drop arity, rfl⟩ (restStore_safe harr hu hh hpack (fun a hm => hvals a (List.mem_of_mem_drop hm)))
  apply HeapObservations.bind (.letE · _) .letC .letC j U heap _ hu hh hstore
  intro i hi V hy hv heap' a hh' hval harr' hprefix
  cases i with
  | zero => trivial
  | succ p =>
    apply HeapObservations.bind_value hval hv hh'
    have hsub : subst 0 a (.goto E K start (.var 0 :: r :: CallArguments.parameters arity args ++ vs)
        .nul) = .goto E K start (a :: r :: CallArguments.parameters arity args ++ vs) .nul := by
      have hmap : (r :: CallArguments.parameters arity args ++ vs).map (subst 0 a) =
          r :: CallArguments.parameters arity args ++ vs := by
        rw [List.map_congr_left (g := id) (fun v hm => subst_above (hclosed v hm) (Nat.le_refl 0) a),
          List.map_id]
      show Tm.goto E K start (substArgs 0 a (.var 0 :: (r :: CallArguments.parameters arity args ++ vs)))
        (subst 0 a .nul) = _
      rw [substArgs_eq_map, List.map_cons, hmap]
      rfl
    rw [hsub]
    have hUV : WExt (trunc (p + 1) hi U) V := hy
    have henv := (hframe.transfer (p + 1) hi V hUV).push harr'
    have henv' : EnvOk G (codeFrame arity s.fixed Cs (some A))
        (envOf (a :: r :: CallArguments.parameters arity args ++ vs) .nul) (p + 1) V := by
      have he : push a (envOf (r :: CallArguments.parameters arity args ++ vs) .nul) =
          envOf (a :: r :: CallArguments.parameters arity args ++ vs) .nul := by
        funext i; cases i <;> rfl
      rw [← he]; exact henv
    apply HeapObservations.weaken (fun heap'' v hp => s.effect.post_prefix hprefix hp)
    exact hs.2 p _ heap' _ (henv'.transfer p (Nat.le_succ p) _ (WExt_refl _))
      (WorldAdm_trunc _ hv) (HeapOk_trunc p V heap' hh') (by
        intro v hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hval
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact (meaning_value hr).1
          · rcases List.mem_append.mp hm with hm | hm
            · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl hvals v hm
            · exact hvalues v hm)

/-- **Graph code with a rest meets its variadic signatures**: the actuals past
its fixed parameters are collected, not discarded (`restsT_of_graph` is the
fixed-arity case, which discards them). -/
theorem restsT_of_graphRest {G : NormalGraph ι} {arity E K start Cs vs n W} {kind : Invoke}
    {S : List (RestArrow (Ty ι))} {As : List (Ty ι)} (fs : List (PropKey × Nat)) (hkind : kind ≠ .construct)
    (hb : ∀ s ∈ S, KindBinds G kind s.receiver)
    (hs : ∀ q ∈ S.zip As, q.1.arguments.1.length = arity ∧ RestStore G q.2 q.1.arguments.2 ∧
      GraphCodeSpec G arity E K start Cs q.1.fixed (some q.2))
    (hlen : S.length = As.length)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W (.objAt fs (.graph arity E K start vs kind true) oid) := by
  refine ⟨⟨fs, _, _, rfl, callable_of_kind hkind, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj U hx hu heap hh r hrv hr args hvals ha
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  have hbind := hb s hsm j U r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsm
  have hiA : i < As.length := hlen ▸ hi
  have hz : (S[i], As[i]) ∈ S.zip As :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
      ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiA⟩)
  obtain ⟨hk, harr, hspec⟩ := hs _ hz
  exact ⟨_, .graph hrv hvals hbind,
    graphRest_invoke hspec hk harr hvs hsc hvalues hj hx hu hh hr hvals ha⟩

/-- **The signatures graph code offers.** Code without a rest meets each
fixed signature and, discarding the actuals past its parameters, each
variadic one, all at their rows (`offerRows`); code with a rest offers no
fixed signature, and meets each variadic one from the frame with the store of
the further actuals, whose type `As` lists in the signatures' order. -/
def CodeOffers (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (rest : Bool) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) (As : List (Ty ι)) : Prop :=
  match rest with
  | false => ∀ p ∈ offerRows L S, GraphCodeSpec G arity E K start Cs p
  | true => L = [] ∧ S.length = As.length ∧ ∀ q ∈ S.zip As, q.1.arguments.1.length = arity ∧
      RestStore G q.2 q.1.arguments.2 ∧
      GraphCodeSpec G arity E K start Cs q.1.fixed (some q.2)

/-- The arity and rest-store requirements of a code offer. -/
def CodeOffersShape (G : NormalGraph ι) (arity : Nat) (rest : Bool)
    (L : List (Arrow (Ty ι))) (S : List (RestArrow (Ty ι))) (As : List (Ty ι)) : Prop :=
  match rest with
  | false => True
  | true => L = [] ∧ S.length = As.length ∧ ∀ q ∈ S.zip As,
      q.1.arguments.1.length = arity ∧ RestStore G q.2 q.1.arguments.2

/-- Whether code of kind `kind` may offer a signature whose receiver is `R`:
`call` code any; `sloppy` code one whose type is of clause rows, each an
object clause, so that it admits objects only (`kindOffers_binds`); construct
code no call signature. -/
@[nospecialize] def kindOffers (G : NormalGraph ι) (kind : Invoke) (R : Ty ι) : Bool :=
  match kind with
  | .call => true
  | .sloppy => G.plainTy R && (expand G R).all objectClause
  | .construct => false

/-- A receiver type `kindOffers` admits for a kind is one the kind binds. -/
theorem kindOffers_binds {G : NormalGraph ι} {kind : Invoke} {R : Ty ι}
    (h : kindOffers G kind R = true) : KindBinds G kind R := by
  intro j U r hr
  cases kind with
  | call => rfl
  | construct => simp [kindOffers] at h
  | sloppy =>
    simp only [kindOffers, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨c, hc, hv, -⟩ := (expand_sem G R h.1 j U r).mp hr
    obtain ⟨fs, code, oid, rfl⟩ := objectClause_member (h.2 c hc) hv
    rfl

/-- The signatures code of kind `kind` offers: it has `[[Call]]`, and binds
every receiver of each (`kindOffers`). -/
def KindOffers (G : NormalGraph ι) (kind : Invoke) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) : Prop :=
  kind ≠ .construct ∧ ∀ p ∈ offerRows L S, kindOffers G kind p.receiver = true

instance [DecidableEq ι] (G : NormalGraph ι) (kind : Invoke) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) : Decidable (KindOffers G kind L S) := by
  unfold KindOffers; infer_instance

/-- Graph code with captured values meets the signatures it offers. -/
theorem offers_sem {G : NormalGraph ι} {arity E K start Cs rest vs n W} {kind : Invoke}
    {L : List (Arrow (Ty ι))} {S : List (RestArrow (Ty ι))}
    {As : List (Ty ι)} (fs : List (PropKey × Nat))
    (hk : KindOffers G kind L S)
    (ho : CodeOffers G arity E K start Cs rest L S As)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.callsT (excOf G) (L.map (Arrow.map (meaning G))) n W
        (.objAt fs (.graph arity E K start vs kind rest) oid) ∧
      CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W (.objAt fs (.graph arity E K start vs kind rest) oid) := by
  obtain ⟨hkind, hrows⟩ := hk
  have hbL : ∀ p ∈ L, KindBinds G kind p.receiver :=
    fun p hp => kindOffers_binds (hrows p (List.mem_append_left _ hp))
  have hbS : ∀ s ∈ S, KindBinds G kind s.receiver :=
    fun s hs => kindOffers_binds (hrows _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)))
  cases rest with
  | false =>
    exact ⟨callsT_of_graph _ hkind hbL (fun p hp => ho p (List.mem_append_left _ hp)) hvs hsc hvalues,
      restsT_of_graph _ hkind hbS (fun s hs => ho _
        (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩))) hvs hsc hvalues⟩
  | true =>
    obtain ⟨rfl, hlen, hs⟩ := ho
    exact ⟨⟨⟨fs, _, _, rfl, callable_of_kind hkind, by simpa [Scoped] using hsc⟩, by simp⟩,
      restsT_of_graphRest fs hkind hbS hs hlen hvs hsc hvalues⟩

/-- **A class value's graph code** meets each construct signature it was
checked at with `undefined` for its receiver: `new` enters it so. -/
theorem ctorsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {U : Ty ι}
    {L : List (List (Ty ι) × Ty ι)} (fs : List (PropKey × Nat))
    (hs : ∀ p ∈ L, GraphCodeSpec G arity E K start Cs ⟨U, p.1, p.2, .unrestricted⟩)
    (hu : Represents G U .undef)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    ctorsT (excOf G) (L.map fun p => (p.1.map (meaning G), meaning G p.2)) n W
      (.objAt fs (.graph arity E K start vs .construct) oid) := by
  refine ⟨⟨fs, _, _, _, _, _, _, _, rfl, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj V hx hv heap hh args _ ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  refine ⟨_, ⟨fs, _, _, _, rfl, rfl, rfl⟩, ?_⟩
  exact HeapObservations.erase (graph_invoke (row := ⟨U, p.1, p.2, .unrestricted⟩) (hs p hp) hvs hvalues hj hx hv hh
    ((represents_back hu j V _) rfl) (ArgsShort_of_exact ha))

/-- The row a class's graph code is checked at for a variadic construct
signature with fixed parameters `Qs` and element rest `El`: the fixed
parameters, then each further position the code binds at `El` or `undefined`,
which construction binds where the list is shorter. -/
def ctorRestParams (arity : Nat) (Qs : List (Ty ι)) (El U : Ty ι) : List (Ty ι) :=
  Qs ++ List.replicate (arity - Qs.length) (El ++ U)

/-- A list of members of `D`, cut to `r` positions, is admitted by `r`
positions at `D` when `D` admits `undefined`. -/
theorem ArgsShort_replicate {D : Fam} {j : Nat} {W : WorldT j} {r : Nat} {xs : List Tm}
    (hx : ∀ x ∈ xs, D j W x) (hu : D j W .undef) :
    ArgsShort (List.replicate r D) j W (xs.take r) := by
  refine ⟨by simp; omega, ?_, ?_⟩
  · apply ArgsT_of_getElem? (by simp)
    intro i A a hA ha
    simp only [List.take_replicate, List.getElem?_replicate] at hA
    split at hA
    · cases hA; exact hx a (List.mem_of_mem_take (List.mem_of_getElem? ha))
    · cases hA
  · intro A hA
    rw [List.drop_replicate] at hA
    rw [List.eq_of_mem_replicate hA]; exact hu

/-- Graph code of a class meets a variadic construct signature with an
element rest when it meets the row `ctorRestParams` gives: construction binds
the fixed actuals, then further ones up to its arity, padding with `undefined`,
and discards the rest. -/
theorem ctorRestsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {U : Ty ι}
    {S : List (List (Ty ι) × Ty ι × Ty ι)} (fs : List (PropKey × Nat))
    (hs : ∀ s ∈ S, ∃ El, restElem G s.2.1 = some El ∧
      GraphCodeSpec G arity E K start Cs ⟨U, ctorRestParams arity s.1 El U, s.2.2, .unrestricted⟩)
    (hu : Represents G U .undef)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    ctorRestsT (excOf G) (S.map fun s => (s.1.map (meaning G), argMeaning G s.2.1, meaning G s.2.2)) n W
      (.objAt fs (.graph arity E K start vs .construct) oid) := by
  refine ⟨⟨fs, _, _, _, _, _, _, _, rfl, by simpa [Scoped] using hsc⟩, ?_⟩
  intro q hq j hj V hx hv heap hh args _ ha
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  obtain ⟨El, hel, hspec⟩ := hs s hsm
  obtain ⟨hlen, hfix, hext⟩ := ha
  have hlenQ : (s.1.map (meaning G)).length = s.1.length := by simp
  rw [hlenQ] at hlen hfix hext
  have hel' := (restElem_args hel).mp hext
  let D : Ty ι := El ++ U
  have hD : ∀ x ∈ args.drop s.1.length, meaning G D j V x :=
    fun x hx => (meaning_append G El U j V x).mpr (Or.inl (hel' x hx))
  have hDu : meaning G D j V .undef :=
    (meaning_append G El U j V _).mpr (Or.inr ((represents_back hu j V _) rfl))
  have hshort := ArgsShort_prefix hfix
    (ArgsShort_replicate (r := arity - s.1.length) hD hDu)
  have hle : arity ≤ (ctorRestParams arity s.1 El U).length := hspec.1
  have hm : (ctorRestParams arity s.1 El U).length = s.1.length + (arity - s.1.length) := by
    simp [ctorRestParams]
  have hargs' : args.take s.1.length ++ (args.drop s.1.length).take (arity - s.1.length) =
      args.take (s.1.length + (arity - s.1.length)) := by
    rw [List.take_add]
  rw [hargs'] at hshort
  have hsafe := graph_invoke (row := ⟨U, ctorRestParams arity s.1 El U, s.2.2, .unrestricted⟩) hspec hvs
    hvalues hj hx hv hh ((represents_back hu j V _) rfl)
    (args := args.take (s.1.length + (arity - s.1.length)))
    (by simpa [ctorRestParams, List.map_append, List.map_replicate] using hshort)
  have hp : CallArguments.parameters arity (args.take (s.1.length + (arity - s.1.length))) =
      CallArguments.parameters arity args := by
    rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
      Nat.min_eq_left (by omega), CallArguments.parameters_take]
  rw [hp] at hsafe
  exact ⟨_, ⟨fs, _, _, _, rfl, rfl, rfl⟩, HeapObservations.erase hsafe⟩

/-- The parts a variadic call writes past its fixed actuals fit its rest. With
a spread among them, the rest is an element rest, each plain part at its
element and each spread spreading into it. Without one, the rest is a pack of
one tuple contract, and the parts are at its positions, within its bounds. -/
def RestParts (G : NormalGraph ι) (P : Ty ι) (parts : List (Bool × Ty ι)) : Prop :=
  if parts.any (·.1) then
    match restElem G P with
    | some E => ∀ p ∈ parts, if p.1 then SpreadsInto G p.2 E else p.2 = E
    | none => False
  else
    match expand G P with
    | [.pack T []] => T.required.length ≤ parts.length ∧
        (T.rest = none → parts.length ≤ T.required.length + T.optional.length) ∧
        ∀ i ∈ List.range parts.length, positionTy T i = (parts[i]?).map (·.2)
    | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (P : Ty ι) (parts : List (Bool × Ty ι)) :
    Decidable (RestParts G P parts) := by
  unfold RestParts
  split
  · split <;> infer_instance
  · split <;> infer_instance

/-- Plain actuals at the positions of a rest's one tuple contract, within its
bounds, form a pack of the rest. -/
theorem restParts_pack {G : NormalGraph ι} {P : Ty ι} {T : Tuple (Ty ι)}
    (hP : expand G P = [.pack T []]) {Qs : List (Ty ι)}
    (hreq : T.required.length ≤ Qs.length)
    (hbound : T.rest = none → Qs.length ≤ T.required.length + T.optional.length)
    (hpos : ∀ i ∈ List.range Qs.length, positionTy T i = Qs[i]?)
    {k : Nat} {W : WorldT k} {extra : List Tm} (ha : ArgsT (Qs.map (meaning G)) k W extra) :
    argMeaning G P k W extra := by
  have hlen : extra.length = Qs.length := by simpa using ArgsT_length ha
  refine (mixed_pack_args hP).mpr ⟨by simpa [tupleFams, hlen] using hreq,
    by simpa [tupleFams, hlen] using hbound, ?_⟩
  intro i u B hu hB
  have hi : i < Qs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hu).1
  rw [PositiveNormalization.positionFam_tupleFams] at hB
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hB
  have hq : Qs[i]? = some b := by
    rw [← hpos i (List.mem_range.mpr hi), positionTy_eq]
    exact hb
  exact ArgsT_getElem? (A := meaning G b) ha (by simp [List.getElem?_map, hq]) hu

theorem ArgStep_append {h h' : Heap} {args args' : List Tm} (rest : List Tm)
    (s : CallArguments.ArgStep h args h' args') :
    CallArguments.ArgStep h (args ++ rest) h' (args' ++ rest) := by
  induction s with
  | head hs => exact .head hs
  | tail hv _ ih => exact .tail hv ih

/-- **A variadic call with a spread.** The callee, the receiver, the fixed
actuals, then the further parts run left to right; the call meets the
signature's result. Each further actual is at the element contract `E`, and
actuals at `E` form a pack of the rest `P`. -/
theorem rest_call_safe {Rc : Fam} {Ps : List Fam} {E R : Fam} {P : ArgFam}
    (hRc : Adm Rc)
    (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A) (hE : Adm E) (hEv : ValOnly E)
    (hP : Adm P) (hEP : ∀ k W xs, (∀ e ∈ xs, E k W e) → P k W xs)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps) (parts : List (Option Fam × Tm))
    (hS : ∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (restsT Ξ [(Rc, Ps, P, R)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r)
    (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) (hp : ∀ p ∈ parts, FutureSafe Ξ (p.1.getD E) n W p.2) :
    Safe Ξ R n W heap (.invoke f r (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) := by
  apply bind (fun f => .invoke f r (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) Step.callL Raises.callL
    n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply bind (fun r => .invoke v r (xs.map Prod.snd ++ parts.map RestCalls.partTerm))
    (Step.callRecv hv) (Raises.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv (args ++ parts.map RestCalls.partTerm))
    (fun hs => (CallArguments.Prepare.args hv hrv (ArgStep_append _ hs)).step)
    (fun hr => (hr.append _).invoke hv hrv) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  apply RestCalls.spread_parts_safe hE hEv hv hrv parts k V heap'' args hS hv' hok'
    (ArgsT_values hAv hargs) (fun p hm => ((hp p hm).transfer hj hxU).transfer hk hy)
  intro i hi X hz hX heap3 extra hh3 hext
  have hUX : WExt (trunc i (Nat.le_trans hi hk) U) X := by
    apply WExt_trans _ hz
    simpa only [trunc_trunc] using WExt_trunc hi hy
  have hfX := (restsT_adm _).mono i _ X hUX v
    ((restsT_adm _).down_le j i (Nat.le_trans hi hk) U v hfun)
  have hrX := hRc.mono i _ X hUX rv (hRc.down_le j i (Nat.le_trans hi hk) U rv hrm)
  exact RestCalls.call_elim_rest (s := (Rc, Ps, P, R)) (by simp) hRc hA hAv hP hrv hrX hfX
    (ArgsT_transfer hA hargs i hi X hz) (hEP i X extra hext) (fun e he => hEv i X e (hext e he))
    hX hh3

/-- Every label of `A` is the packed binder `t`, or a meet row of it: each
value of `A` is one of `t`'s. -/
def PackedBy (G : NormalGraph ι) (A : Ty ι) (t : ι) : Prop :=
  G.parameterKinds t = some .packed ∧
    ∀ l ∈ A, l = t ∨ (G.params l = false ∧ G.schemes l = none ∧ (G.meets l).map Prod.fst = some t)

instance [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (t : ι) : Decidable (PackedBy G A t) := by
  unfold PackedBy; infer_instance

/-- A value of a packed binder, or of a meet row of it, is packable by the
binder's argument lists. -/
theorem packedBy_sound {G : NormalGraph ι} {A : Ty ι} {t : ι} (hp : PackedBy G A t)
    {n W v} (hv : meaning G A n W v) : Packable (argMeaning G [t]) n W v := by
  obtain ⟨hk, hA⟩ := hp
  have hparam : G.params t = true := by simp [NormalGraph.params, hk]
  have hpart : ∀ {m U u}, (mixedParameters G).value t (G.env.1 t) m U u →
      Packable (argMeaning G [t]) m U u := by
    intro m U u h
    simp only [mixedParameters, hk, selectParameter] at h
    rcases h with ⟨h, _⟩ | ⟨_, _, h⟩
    · cases h
    · refine Packable_mono ?_ h
      intro j U' vs hvs
      exact ⟨t, List.mem_singleton_self t, by simpa [NormalGraph.listParam, hk] using hvs⟩
  obtain ⟨l, hl, hv⟩ := hv
  rcases hA l hl with rfl | ⟨hlp, hls, hm'⟩
  · change qDenoteWithArgs G (mixedParameters G) (G.env, l) n W v at hv
    rw [qDenoteWithArgs_unfold] at hv
    simp only [qLayerWithArgs, hparam, ite_true] at hv
    exact hpart hv
  obtain ⟨⟨t', cs⟩, hm, ht⟩ := Option.map_eq_some_iff.mp hm'
  cases ht
  change qDenoteWithArgs G (mixedParameters G) (G.env, l) n W v at hv
  rw [qDenoteWithArgs_unfold] at hv
  simp only [qLayerWithArgs, hlp, hls, hm, Bool.false_eq_true, ite_false] at hv
  rw [partSemWithArgs_param hparam] at hv
  exact hpart hv.1.1

/-- **A spread of a packed value.** The callee, the receiver and the fixed
actuals run, then the operand; its store is read and spread, a step each, and
the elements form a list of the rest `P`, which the operand's values are
packable by (`Packable`). -/
theorem packed_call_safe {Rc : Fam} {Ps : List Fam} {R V : Fam} {P : ArgFam}
    (hRc : Adm Rc) (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A)
    (hP : Adm P) (hPv : ∀ n W vs, P n W vs → CallArguments.Values vs)
    (hVP : ∀ n W v, V n W v → Packable P n W v)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps)
    {n W heap f r a} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (restsT Ξ [(Rc, Ps, P, R)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r) (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) (ha : FutureSafe Ξ V n W a) :
    Safe Ξ R n W heap (.invoke f r (xs.map Prod.snd ++
      [.spread (.readAt CallArguments.arrayStoreField a)])) := by
  let tail := fun (t : Tm) => [Tm.spread (.readAt CallArguments.arrayStoreField t)]
  apply bind (fun f => .invoke f r (xs.map Prod.snd ++ tail a)) Step.callL Raises.callL
    n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply bind (fun r => .invoke v r (xs.map Prod.snd ++ tail a))
    (Step.callRecv hv) (Raises.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv (args ++ tail a))
    (fun hs => (CallArguments.Prepare.args hv hrv (ArgStep_append _ hs)).step)
    (fun hr => (hr.append _).invoke hv hrv) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V' hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  have hvals := ArgsT_values hAv hargs
  have hkU : WExt (trunc k (Nat.le_trans hk hj) W) V' := by
    apply WExt_trans _ hy
    simpa only [trunc_trunc] using WExt_trunc hk hxU
  apply RestCalls.ctx_bind (A := V) (fun t => .invoke v rv (args ++ tail t))
    (fun s => RestCalls.call_lift hv hrv hvals (.spreadC (.readC s)))
    (fun s => RestCalls.call_raise hv hrv hvals (.spreadC (.readC s))) k V' heap'' a hv' hok'
    ((ha.transfer (Nat.le_trans hk hj) hkU) k (Nat.le_refl _) V'
      (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
  intro i hi X hz hX heap3 av hok3 hav hva
  have hfX := (restsT_adm _).mono i _ X hz v ((restsT_adm _).down_le k i hi V' v
    ((restsT_adm _).mono k _ V' hy v ((restsT_adm _).down_le j k hk U v hfun)))
  have hrX := hRc.mono i _ X hz rv (hRc.down_le k i hi V' rv
    (hRc.mono k _ V' hy rv (hRc.down_le j k hk U rv hrm)))
  have hargsX := ArgsT_transfer hA hargs i hi X hz
  cases i with
  | zero => trivial
  | succ i =>
    obtain ⟨fs, c, oid, l, ls, vs, rfl, hl, hls, hrd, hvs⟩ :=
      hVP (i + 1) X av hva i (Nat.le_refl _) X (by rw [trunc_id]; exact WExt_refl _) heap3 hok3
    cases i with
    | zero =>
      refine Or.inr ⟨trunc 0 (Nat.le_succ 0) X, heap3, _, WExt_refl _, WorldAdm_trunc _ hX,
        RestCalls.call_lift hv hrv hvals (.spreadC (.readField hl hls)), HeapOk_trunc 0 X heap3 hok3, trivial⟩
    | succ m =>
      let X1 := trunc (m + 1) (Nat.le_succ (m + 1)) X
      refine Or.inr ⟨X1, heap3, _, WExt_refl _, WorldAdm_trunc _ hX,
        RestCalls.call_lift (rest := []) hv hrv hvals (.spreadC (.readField hl hls)),
        HeapOk_trunc (m + 1) X heap3 hok3, ?_⟩
      have hvsv := hPv _ _ _ (hvs m (by omega))
      let X2 := trunc m (Nat.le_succ m) X1
      refine Or.inr ⟨X2, heap3, .invoke v rv (args ++ vs), WExt_refl _,
        WorldAdm_trunc _ (WorldAdm_trunc _ hX),
        by simpa using Step.callSpread (pre := args) (post := []) hv hrv rfl hvals hrd,
        HeapOk_trunc m X1 heap3 (HeapOk_trunc (m + 1) X heap3 hok3), ?_⟩
      have hle : ∀ {F : Fam}, Adm F → ∀ u, F (m + 2) X u → F m X2 u := fun hF u h =>
        hF.down m X1 u (hF.down (m + 1) X u h)
      have hPm : P m X2 vs := by
        have := hvs m (by omega)
        simpa only [X2, X1, trunc_trunc] using this
      exact RestCalls.call_elim_rest (s := (Rc, Ps, P, R)) (by simp) hRc hA hAv hP hrv
        (hle hRc rv hrX) (hle (restsT_adm _) v hfX)
        (ArgsT_transfer hA hargsX m (by omega) X2 (by simp only [X2, X1, trunc_trunc]; exact WExt_refl _))
        hPm hvsv (WorldAdm_trunc _ (WorldAdm_trunc _ hX))
        (HeapOk_trunc m X1 heap3 (HeapOk_trunc (m + 1) X heap3 hok3))

/-- **A variadic call writing no spread.** The callee, the receiver and every
actual run left to right; the fixed ones meet the signature's parameters, less
trailing ones `Us` the call omits, each admitting `undefined`, and the further
ones, at `Qs`, form a pack of the rest `P`. A call that omits a fixed position
writes no further actual. -/
theorem pack_call_safe {Rc : Fam} {Ps Us Qs : List Fam} {R : Fam} {P : ArgFam}
    (hRc : Adm Rc) (hA : ∀ A ∈ Ps ++ Qs, Adm A) (hAv : ∀ A ∈ Ps ++ Qs, ValOnly A)
    (hUA : ∀ A ∈ Us, Adm A)
    (hpack : ∀ k W extra, ArgsT Qs k W extra → P k W extra)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps ++ Qs) (hshort : Us = [] ∨ Qs = [])
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (restsT Ξ [(Rc, Ps ++ Us, P, R)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r) (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe Ξ A n W .undef) :
    Safe Ξ R n W heap (.invoke f r (xs.map Prod.snd)) := by
  apply bind (fun f => .invoke f r (xs.map Prod.snd)) Step.callL Raises.callL n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply bind (fun r => .invoke v r (xs.map Prod.snd)) (Step.callRecv hv) (Raises.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv args)
    (fun hs => (CallArguments.Prepare.args hv hrv hs).step) (fun hr => hr.invoke hv hrv) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  cases k with
  | zero => trivial
  | succ k =>
    let X := trunc k (Nat.le_succ k) V
    have hX : WorldAdm X := WorldAdm_trunc _ hv'
    have hhX : HeapOk k X heap'' := HeapOk_trunc k V heap'' hok'
    have hfV := (restsT_adm _).mono (k + 1) _ V hy v
      ((restsT_adm _).down_le j (k + 1) hk U v hfun)
    have hrV := hRc.down k V rv (hRc.mono (k + 1) _ V hy rv (hRc.down_le j (k + 1) hk U rv hrm))
    have hargsX := ArgsT_transfer hA hargs k (Nat.le_succ k) X (WExt_refl _)
    have hsplit := ArgsT_take_drop Ps.length hargsX
    simp only [List.take_append_of_le_length (Nat.le_refl _),
      List.take_length, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
      List.nil_append] at hsplit
    have hacc : ArgsRest (Ps ++ Us) P k X args := by
      rcases hshort with rfl | rfl
      · have := ArgsRest_of_exact_extra (Ps := Ps) hsplit.1 (hpack k X _ hsplit.2)
        simpa only [List.append_nil, List.take_append_drop] using this
      · have hundef : ∀ A ∈ Us, A k X .undef := by
          intro A hA'
          have := safe_value_mem rfl
            (((hu A hA').transfer hj hxU).transfer hk hy (k + 1) (Nat.le_refl _) V
              (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
          exact (hUA A hA').down k V _ this
        simp only [List.append_nil] at hargsX
        have hshortX : ArgsShort (Ps ++ Us) k X args :=
          ArgsShort_of_pad (pad := List.replicate Us.length .undef)
            (fun a hm => List.eq_of_mem_replicate hm)
            (ArgsT_append hargsX (ArgsT_undef hundef))
        have hl : args.length ≤ (Ps ++ Us).length := hshortX.1
        refine ⟨by rwa [List.take_of_length_le hl], ?_⟩
        rw [List.drop_eq_nil_of_le hl]
        exact hpack k X [] trivial
    obtain ⟨body, hi, hsafe⟩ := hfV.2 (Rc, Ps ++ Us, P, R) (by simp) k (Nat.lt_succ_self k) X
      (WExt_refl _) hX heap'' hhX rv hrv hrV args (ArgsT_values hAv hargsX) hacc
    exact Or.inr ⟨X, heap'', body, WExt_refl _, hX, hi.step heap'', hhX, hsafe⟩

/-- **Eliminating a variadic construct signature.** A ready construction whose
fixed actuals meet the parameters and whose further ones form a pack of the
rest takes one step to the class's body, safe at the result. -/
theorem ctor_elim_rest {Ps : List Fam} {P : ArgFam} {R : Fam}
    (hA : ∀ A ∈ Ps, Adm A) (hP : Adm P)
    {n W v args extra heap} (hf : ctorRestsT Ξ [(Ps, P, R)] n W v)
    (ha : ArgsT Ps n W args) (he : P n W extra) (hvals : CallArguments.Values (args ++ extra))
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe Ξ R n W heap (.construct v (args ++ extra)) := by
  cases n with
  | zero => trivial
  | succ k =>
    have hl := ArgsT_length ha
    have hrest : CtorRest Ps P k (trunc k (Nat.le_succ k) W) (args ++ extra) := by
      refine ⟨by simp; omega, ?_, ?_⟩
      · rw [List.take_left' hl]
        exact ArgsT_transfer hA ha k (Nat.le_succ k) _ (WExt_refl _)
      · rw [List.drop_left' hl]
        exact hP.down k W extra he
    obtain ⟨result, ⟨fs, c, enter, oid, rfl, hc', rfl⟩, hsafe⟩ :=
      hf.2 _ (List.mem_singleton_self _) k (Nat.lt_succ_self k) (trunc k (Nat.le_succ k) W)
        (WExt_refl _) (WorldAdm_trunc _ hw) heap (HeapOk_trunc k W heap hh) _ hvals hrest
    exact Or.inr ⟨trunc k (Nat.le_succ k) W, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
      CallArguments.construction_step hc' hvals heap, HeapOk_trunc k W heap hh, hsafe⟩

/-- **A variadic construction with a spread.** The constructor, the fixed
actuals, then the further parts run left to right, each spread read where it
is written; each further actual is at the element contract `E`, and actuals at
`E` form a pack of the rest `P`. -/
theorem construct_rest_safe {Ps : List Fam} {E R : Fam} {P : ArgFam}
    (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A) (hE : Adm E) (hEv : ValOnly E)
    (hP : Adm P) (hEP : ∀ k W xs, (∀ e ∈ xs, E k W e) → P k W xs)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps) (parts : List (Option Fam × Tm))
    (hS : ∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (ctorRestsT Ξ [(Ps, P, R)]) n W heap f)
    (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) (hp : ∀ p ∈ parts, FutureSafe Ξ (p.1.getD E) n W p.2) :
    Safe Ξ R n W heap (.construct f (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) := by
  apply bind (fun f => .construct f (xs.map Prod.snd ++ parts.map RestCalls.partTerm))
    Step.constructL Raises.constructL n W heap f hw hh hf
  intro j hj U hxU hu heap' v hok hv hfun
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .construct v (args ++ parts.map RestCalls.partTerm))
    (fun hs => CallArguments.Step.constructArgs hv (ArgStep_append _ hs))
    (fun hr => (hr.append _).construct hv) hu hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  apply RestCalls.parts_safe hE hEv (Tm.construct v)
    (fun hp s => CallArguments.Step.constructArgs hv (CallArguments.keep_prefix hp (.head s)))
    (fun hp s => .constructArg hv (prefix_position hp).1 (prefix_position hp).2 s)
    (fun hp hr => .constructSpread hv rfl hp hr)
    parts k V heap'' args hS hv' hok' (ArgsT_values hAv hargs)
    (fun p hm => ((hp p hm).transfer hj hxU).transfer hk hy)
  intro i hi X hz hX heap3 extra hh3 hext
  have hUX : WExt (trunc i (Nat.le_trans hi hk) U) X := by
    apply WExt_trans _ hz
    simpa only [trunc_trunc] using WExt_trunc hi hy
  have hfX := (ctorRestsT_adm _).mono i _ X hUX v
    ((ctorRestsT_adm _).down_le j i (Nat.le_trans hi hk) U v hfun)
  exact ctor_elim_rest hA hP hfX (ArgsT_transfer hA hargs i hi X hz) (hEP i X extra hext)
    (by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact ArgsT_values hAv hargs a ha
      · exact hEv i X a (hext a ha)) hX hh3

/-- **A variadic construction writing no spread.** The constructor and every
actual run left to right; the fixed ones meet the signature's parameters and
the further ones, at `Qs`, form a pack of the rest `P`. -/
theorem construct_pack_safe {Ps Qs : List Fam} {R : Fam} {P : ArgFam}
    (hA : ∀ A ∈ Ps ++ Qs, Adm A) (hAv : ∀ A ∈ Ps ++ Qs, ValOnly A) (hP : Adm P)
    (hpack : ∀ k W extra, ArgsT Qs k W extra → P k W extra)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps ++ Qs)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (ctorRestsT Ξ [(Ps, P, R)]) n W heap f)
    (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) :
    Safe Ξ R n W heap (.construct f (xs.map Prod.snd)) := by
  apply bind (fun f => .construct f (xs.map Prod.snd)) Step.constructL Raises.constructL n W heap f hw hh hf
  intro j hj U hxU hu heap' v hok hv hfun
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (Tm.construct v) (fun hs => CallArguments.Step.constructArgs hv hs) (fun hr => hr.construct hv) hu hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  obtain ⟨h1, h2⟩ := ArgsT_take_drop Ps.length hargs
  simp only [List.take_append_of_le_length (Nat.le_refl _), List.take_length,
    List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append] at h1 h2
  have hfV := (ctorRestsT_adm _).mono k _ V hy v ((ctorRestsT_adm _).down_le j k hk U v hfun)
  have := ctor_elim_rest (fun A h => hA A (List.mem_append_left _ h)) hP hfV h1 (hpack k V _ h2)
    (by rw [List.take_append_drop]; exact ArgsT_values hAv hargs) hv' hok'
  rwa [List.take_append_drop] at this

/-- **A fresh store of values at `E`.** Allocated, the values meet the
contract `E` at every position, under any readonly flag and presence mode:
every position holds a location of its own. -/
theorem fresh_store_safe {E : Fam} (ro : Bool) (presence : ArrayPresence) (hE : Adm E) (hEv : ValOnly E)
    {n : Nat} {W : WorldT n} {h : Heap} {vs : List Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hvs : ∀ e ∈ vs, E n W e) :
    Safe Ξ (listT ⟨[], [], some E, ro, presence⟩) n W h (.arrLit vs) := by
  apply arr_alloc_rule (As := List.replicate vs.length E)
    (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact hE)
    (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact hEv)
    n W h vs (by simp) (fun v hm => hEv n W v (hvs v hm)) hw hh
    (by
      intro q hq
      rw [List.eq_of_mem_replicate (List.of_mem_zip hq).1]
      exact hvs q.2 (List.of_mem_zip hq).2)
  intro k hk X hy hl
  have := listT_alloc (n := k) (W := X) (T := ⟨[], [], some E, ro, presence⟩)
    (As := List.replicate vs.length E) (base := h.length)
    (by simp) (by simp)
    (by
      intro i A hA
      have := (List.getElem?_eq_some_iff.mp hA)
      simp only [List.getElem_replicate] at this
      rw [← this.2]
      simp [positionFam])
    hl
  simpa using this

/-- The named fields and readonly views of an object of one record operand:
a record's, or a dictionary's, whose named members hold beside its index. -/
def namedMembers : Clause α → Option (List (PropKey × α) × List (PropKey × α))
  | .refs fs [] vs _ _ _ => some (fs, vs)
  | .dict fs [] vs _ _ _ _ _ => some (fs, vs)
  | _ => none

/-- A value of a type with named members holds each named field as a cell of
its contract and each view as a location whose contents meet its bound. -/
theorem namedMembers_sem {G : NormalGraph ι} {A : Ty ι} {c : Clause (Ty ι)}
    {fs vs : List (PropKey × Ty ι)} (hr : Represents G A c)
    (hc : namedMembers c = some (fs, vs)) {n W v} (h : meaning G A n W v) :
    recT (ReferenceConjunctions.famsOf (meaning G) fs) n W v ∧
      viewsT (ReferenceConjunctions.famsOf (meaning G) vs) n W v := by
  have hs := (represents_raw hr n W v) h
  match c, hc with
  | .refs _ [] _ _ _ _, rfl => exact ⟨hs.1.1, hs.2.1⟩
  | .dict _ [] _ _ _ _ _ _, rfl => exact ⟨hs.1.1, hs.2.1⟩

/-- A clause with named members is a record's or a dictionary's, which the
builtins's invariant applies to. -/
theorem namedMembers_carriesInvariant {c : Clause α} {fs vs : List (PropKey × α)}
    (hc : namedMembers c = some (fs, vs)) : c.carriesInvariant = true := by
  match c, hc with
  | .refs _ [] _ _ _ _, rfl => rfl
  | .dict _ [] _ _ _ _ _ _, rfl => rfl

/-- **`length`, read where the object may be an array**: an array's is its
store's length, any other object's its own property's. -/
def lengthRead (i : Nat) : Tm :=
  .ite (.test .isArray (.var i)) (.lenOf (.readAt CallArguments.arrayStoreField (.var i)))
    (.readAt lengthKey (.var i))

/-- Whether a clause's members exclude the number `w`. -/
def rejectsNum (w : UInt64) (c : Clause α) : Bool :=
  match c with
  | .numLit b => b != w
  | c => tagClause .isNum c == some false

theorem rejectsNum_sound {Ξ : Fam} {S : α → Fam} {P : α → ArgFam} {w : UInt64} {c : Clause α}
    (h : rejectsNum w c = true) {n W} : ¬ semWithArgs Ξ S P c n W (.num w) := by
  intro hv
  unfold rejectsNum at h
  split at h
  · simp only [bne_iff_ne, ne_eq] at h
    simp only [semWithArgs, Tm.num.injEq] at hv
    exact h hv.symm
  · have := tagClause_sound (beq_iff_eq.mp h) hv
    simp [tagHolds] at this

/-- A number no value of the type is, where one is found among the first
few: one more than its numeric singletons. -/
@[nospecialize] def numWitness (G : NormalGraph ι) (A : Ty ι) : Option UInt64 :=
  if G.plainTy A then
    ((List.range ((expand G A).length + 1)).map Nat.toUInt64).find? fun w =>
      (expand G A).all (rejectsNum w)
  else none

theorem numWitness_sound {G : NormalGraph ι} {A : Ty ι} {w : UInt64} (h : numWitness G A = some w)
    {n W} : ¬ meaning G A n W (.num w) := by
  intro hv
  unfold numWitness at h
  split at h
  · rename_i hp
    have hall := List.find?_some h
    simp only [List.all_eq_true] at hall
    obtain ⟨c, hc, hcv, -⟩ := (expand_sem G A hp n W _).mp hv
    exact rejectsNum_sound (hall c hc) hcv
  · cases h

/-- **A `length` view met at its own location**: its type excludes a number,
so the view's array alternative (`arrayLenT`, which needs every number) does
not hold, and the view is at the object's own location. -/
@[nospecialize] def lengthExcluded (G : NormalGraph ι) (A : Ty ι) : Bool := (numWitness G A).isSome

/-- Whether a type's `length` is a view an array may meet (`lenView` reads
it): its one record or dictionary clause names `length` among its views, not
among its fields, at a type excluding no number found. -/
@[nospecialize] def lengthViewed (G : NormalGraph ι) (B : Ty ι) : Bool :=
  match expand G B with
  | [c] => match namedMembers c with
    | some (fs, vs) => (fs.lookup lengthKey).isNone &&
        match vs.lookup lengthKey with
        | some A => !lengthExcluded G A
        | none => false
    | none => false
  | _ => false

variable [DecidableEq ι]

/-- Subsumption checked at the body's assignment. A qualified body can use
its enclosing descriptor evidence here; structural subtyping retains its
independent, universally quantified checker. -/
structure BodySubtyping (G : NormalGraph ι) where
  check : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool
  sound : ∀ {A B proof}, check A B proof = true → FamLe (meaning G A) (meaning G B)

@[nospecialize] def BodySubtyping.ordinary (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) : BodySubtyping G where
  check := PositiveCertificates.checkUsing G images
  sound := PositiveCertificates.acceptedUsing

/-- Constructor views avoid any semantic normalization assumption. -/
inductive HasTyWith (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (subtyping : BodySubtyping G) : List (Ty ι) → Tm → Ty ι → Prop where
  | var : Γ[i]? = some A → HasTyWith G images subtyping Γ (.var i) A
  | nul : Represents G A .nul → HasTyWith G images subtyping Γ .nul A
  | undef : Represents G A .undef → HasTyWith G images subtyping Γ .undef A
  | tru : Represents G A .bool → HasTyWith G images subtyping Γ .tru A
  | fls : Represents G A .bool → HasTyWith G images subtyping Γ .fls A
  | truLit : Represents G A (.boolLit true) → HasTyWith G images subtyping Γ .tru A
  | flsLit : Represents G A (.boolLit false) → HasTyWith G images subtyping Γ .fls A
  | numLit : Represents G A (.numLit b) → HasTyWith G images subtyping Γ (.num b) A
  /-- Every number is a number, as every Boolean is a Boolean. Without this a
  literal claimed at the family rather than at its own singleton has no rule. -/
  | num : Represents G A .num → HasTyWith G images subtyping Γ (.num b) A
  /-- A bigint, at its own singleton or at the family, as a number is. -/
  | bigintLit : Represents G A (.bigintLit i) → HasTyWith G images subtyping Γ (.bigint i) A
  | bigint : Represents G A .bigint → HasTyWith G images subtyping Γ (.bigint i) A
  | strLit : Represents G A (.strLit s) → HasTyWith G images subtyping Γ (.str s) A
  | str : Represents G A .str → HasTyWith G images subtyping Γ (.str s) A
  /-- **Graph code.** A function whose body is a control-flow graph, as a
  function body is: the code meets each signature it offers (`CodeOffers`:
  each checked by the graph checker, `GraphCodeSpec`; with a rest, from the
  frame holding the store of the further actuals), with its captures, slots
  of this context, at the types the code was checked with. Its kind binds
  the receivers of every signature it offers (`KindOffers`): sloppy code
  offers signatures whose receivers are objects. -/
  | funGraph {Γ : List (Ty ι)} {F : Ty ι} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {arity start : Nat} {E : List Tm}
      {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {As : List (Ty ι)} :
      Represents G F (.arrs L S) →
      KindOffers G kind L S →
      CodeOffers G arity E K start (caps.map Prod.fst) rest L S As →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeFn (.graph arity E K start (caps.map fun c => .var c.2) kind rest) .nul) F
  /-- **A generic closure.** The code meets each signature at every permitted
  assignment of the scheme's binders. Its captures are slots whose types read
  none of those binders (`FreeOk`), so they mean the same at every instantiation.
  Arity and rest-store formation are checked independently of the assignment. -/
  | funScheme {Γ : List (Ty ι)} {j : ι} {s : SchemeRow ι} {arity start : Nat} {E : List Tm}
      {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {As : List (Ty ι)} :
      G.params j = false → G.schemes j = some s → s.construct = false →
      KindOffers G kind s.signatures s.variadic →
      (∀ η Bs, Bs.length = s.binders.length → G.domain.allowed s Bs →
        CodeOffers (reassign G (assign η s.binders Bs)) arity E K start
          (caps.map Prod.fst) rest s.signatures s.variadic As) →
      CodeOffersShape G arity rest s.signatures s.variadic As →
      capturesFree G s (caps.map Prod.fst) = true →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeFn (.graph arity E K start (caps.map fun c => .var c.2) kind rest) .nul) [j]
  /-- **A class value.** Construct-only graph code, checked at each construct
  signature from the frame with `undefined` for the receiver `new` passes, and
  at each variadic one with an element rest `El` at the row `ctorRestParams`
  gives: the further positions it binds at `El` or `undefined`; allocated with
  its code field and its static fields, named by the program, as a callable
  object's bag is. -/
  | ctorGraph {Γ : List (Ty ι)} {F U : Ty ι} {L : List (List (Ty ι) × Ty ι)}
      {S : List (List (Ty ι) × Ty ι × Ty ι)} {arity start : Nat}
      {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {parts : List (PropKey × Ty ι × Tm)} :
      Represents G F (.ctors L S (parts.map fun p => (p.1, p.2.1)) []) → Represents G U .undef →
      (codeField :: parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      (∀ p ∈ L, GraphCodeSpec G arity E K start (caps.map Prod.fst) ⟨U, p.1, p.2, .unrestricted⟩) →
      (∀ s ∈ S, ∃ El, restElem G s.2.1 = some El ∧ GraphCodeSpec G arity E K start (caps.map Prod.fst)
        ⟨U, ctorRestParams arity s.1 El U, s.2.2, .unrestricted⟩) →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeAt (.graph arity E K start (caps.map fun c => .var c.2) .construct)
        (codeField :: parts.map Prod.fst) (.nul :: parts.map fun p => p.2.2)) F
  /-- **A callable object.** The bag is allocated as a record's is, its fields
  named by the program, with graph code that meets the signatures it offers,
  as a function's does. -/
  | callableGraph {Γ : List (Ty ι)} {F : Ty ι} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {arity start : Nat} {E : List Tm}
      {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {As : List (Ty ι)}
      {parts : List (PropKey × Ty ι × Tm)} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] L S) →
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      KindOffers G kind L S →
      CodeOffers G arity E K start (caps.map Prod.fst) rest L S As →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeAt (.graph arity E K start (caps.map fun c => .var c.2) kind rest)
        (parts.map Prod.fst) (parts.map fun p => p.2.2)) F
  /-- `new f(args)`: `f` at a construct signature, each actual at its
  parameter, whatever static fields its class states. As a call may, `new`
  may omit trailing positions whose contracts admit `undefined`, the value the
  machine binds there. -/
  | construct {Γ : List (Ty ι)} {f : Tm} {F B : Ty ι} {L : List (List (Ty ι) × Ty ι)}
      {S : List (List (Ty ι) × Ty ι × Ty ι)} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)}
      {a : List (PropKey × Ty ι)} {bs : List (List (PropKey × Ty ι))} {vs : List (PropKey × Ty ι)} :
      HasTyWith G images subtyping Γ f F → Represents G F (.ctors L S a bs vs) → (xs.map Prod.fst ++ Us, B) ∈ L →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) →
      HasTyWith G images subtyping Γ (.construct f (xs.map Prod.snd)) B
  /-- **A variadic construction.** `new f(args)` at a variadic construct
  signature: the fixed actuals at its parameters, then parts that fit its
  rest (`RestParts`), as a variadic call's do. -/
  | constructRest {Γ : List (Ty ι)} {f : Tm} {F P B : Ty ι} {L : List (List (Ty ι) × Ty ι)}
      {S : List (List (Ty ι) × Ty ι × Ty ι)} {xs : List (Ty ι × Tm)} {parts : List (Bool × Ty ι × Tm)}
      {a : List (PropKey × Ty ι)} {bs : List (List (PropKey × Ty ι))} {vs : List (PropKey × Ty ι)} :
      HasTyWith G images subtyping Γ f F → Represents G F (.ctors L S a bs vs) → (xs.map Prod.fst, P, B) ∈ S →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      RestParts G P (parts.map fun p => (p.1, p.2.1)) →
      HasTyWith G images subtyping Γ (.construct f (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2))) B
  /-- A call writes the actuals it writes, and passes the receiver `r`, typed
  at the selected signature's receiver. `Us` are the trailing positions the
  signature declares and this call omits; each admits `undefined`, which is
  the value the machine binds there. `Us = []` is the exact-arity call. -/
  | callCallable {effect : Effect} {Γ : List (Ty ι)} {f r : Tm} {F Rt B : Ty ι} {P : List (PropKey × Ty ι)}
      {Ps : List (List (PropKey × Ty ι))} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTyWith G images subtyping Γ f F → Represents G F (.callable P Ps L S) →
      ⟨Rt, xs.map Prod.fst ++ Us, B, effect⟩ ∈ L → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) →
      HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd)) B
  /-- A field of a value with code: a callable object's bag field, or a
  class value's static field. -/
  | readCallable {c : Clause (Ty ι)} : HasTyWith G images subtyping Γ a F → Represents G F c →
      c.bag = some (P, Ps) → (f, A) ∈ P →
      HasTyWith G images subtyping Γ (.readAt f a) A
  /-- A readonly static field of a class value: a view of its own field. -/
  | readBagView {c : Clause (Ty ι)} : HasTyWith G images subtyping Γ a F → Represents G F c →
      (f, A) ∈ c.bagViews → HasTyWith G images subtyping Γ (.readAt f a) A
  | writeCallable {c : Clause (Ty ι)} : HasTyWith G images subtyping Γ a F → Represents G F c →
      c.bag = some (P, Ps) → (f, A) ∈ P →
      HasTyWith G images subtyping Γ b A → Represents G N .nul → HasTyWith G images subtyping Γ (.writeAt f a b) N
  | app {effect : Effect} {Γ : List (Ty ι)} {f r : Tm} {F Rt B : Ty ι} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTyWith G images subtyping Γ f F → Represents G F (.arrs L S) →
      ⟨Rt, xs.map Prod.fst ++ Us, B, effect⟩ ∈ L → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) →
      HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd)) B
  | letE : HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping (A :: Γ) b B → HasTyWith G images subtyping Γ (.letE a b) B
  /-- **Allocation.** One object, one fresh location per named field. The field
  names are distinct, which is what makes the object a map from them. Its own
  keys are exactly those names, so any bound admitting them holds of it. -/
  | alloc {parts : List (PropKey × Ty ι × Tm)} {ks : List KeyBound} :
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      Represents G Ref (.refs (parts.map fun p => (p.1, p.2.1)) [] [] [] [] ks) →
      (∀ K ∈ ks, ∀ p ∈ parts, K.admits p.1 = true) →
      allocBuiltins G (parts.map fun p => (p.1, p.2.1)) = true →
      HasTyWith G images subtyping Γ (.makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2)) Ref
  /-- **Allocation at a dictionary.** A literal allocated directly at a
  dictionary type: its fields are the clause's first operand, with no key the
  model keeps for its prototype, and each field whose key an index's class may
  admit is at exactly that index's type. The object owns no other key, so each
  index holds of it, writable ones included, and it lacks each optional field
  the clause states, which a key added at a writable index's contract keeps
  (the field at that contract, or none meets it). No own-key bound is stated,
  since code holding the dictionary may add keys. -/
  | allocDict {parts : List (PropKey × Ty ι × Tm)} {ix cs : List (IndexKeys × Ty ι)}
      {os : List (OptionalField (Ty ι))} :
      (parts.map Prod.fst).Nodup → CallArguments.protoField ∉ parts.map Prod.fst →
      CallArguments.arrayStoreField ∉ parts.map Prod.fst →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      Represents G Ref (.dict (parts.map fun p => (p.1, p.2.1)) [] [] ix os [] [] cs) →
      (∀ p ∈ parts, ∀ y ∈ ix ++ cs, y.1.may p.1 = true → p.2.1 = y.2) →
      (∀ o ∈ os, o.key ∉ parts.map Prod.fst) →
      (∀ o ∈ os, ∀ y ∈ cs, y.1.may o.key = true → o.type = y.2 ∨ PositiveRules.Uninhabited G y.2) →
      HasTyWith G images subtyping Γ (.makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2)) Ref
  /-- A named field, of a record or of a dictionary, reads at its contract. -/
  | read : HasTyWith G images subtyping Γ a Ref → Represents G Ref c → namedMembers c = some (fs, vs) →
      (f, A) ∈ fs → HasTyWith G images subtyping Γ (.readAt f a) A
  /-- A view field reads at its bound: a capability, never a write permission.
  A view of `length` is read so where its type excludes a number, so that no
  array meets it (`lengthExcluded`). -/
  | readView : HasTyWith G images subtyping Γ a Ref → Represents G Ref c → namedMembers c = some (fs, vs) →
      (f, A) ∈ vs → (f ≠ lengthKey ∨ lengthExcluded G A = true) → HasTyWith G images subtyping Γ (.readAt f a) A
  /-- **`length` through a view.** A view of `length` admits an array, whose
  `length` is its store's: the read tests the slot's value, and reads an
  array's store length, a number the view's type holds, or any other object's
  own `length` location. -/
  | lenView {Γ : List (Ty ι)} {i : Nat} {Ref A : Ty ι} {c : Clause (Ty ι)} {fs vs : List (PropKey × Ty ι)} :
      Γ[i]? = some Ref → Represents G Ref c → namedMembers c = some (fs, vs) → (lengthKey, A) ∈ vs →
      PositiveRules.numIn G A = true →
      HasTyWith G images subtyping Γ (lengthRead i) A
  /-- **A read through the prototype.** A key one of the object's key bounds
  does not admit is not its own, so the read continues at the prototype, which the
  object holds under the reserved key at `P`; the prototype's field or view
  for the key gives the type. -/
  | readProto {a : Tm} {Ref P : Ty ι} {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
      {ms : List (MethodMembers.Sig (Ty ι))} {ks : List KeyBound} {K : KeyBound}
      {gs ws : List (PropKey × Ty ι)} {os' : List (OptionalField (Ty ι))}
      {ms' : List (MethodMembers.Sig (Ty ι))}
      {ks' : List KeyBound} {f : PropKey} {A : Ty ι} :
      HasTyWith G images subtyping Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → K ∈ ks → K.admits f = false →
      (CallArguments.protoField, P) ∈ fs ++ vs → Represents G P (.refs gs [] ws os' ms' ks') →
      (f, A) ∈ gs ++ ws.filter (·.1 != lengthKey) → HasTyWith G images subtyping Γ (.readAt f a) A
  /-- An optional field, writable or readonly, reads at its type or, where the
  object lacks the key, as `undefined`. -/
  | readOptional {a : Tm} {Ref : Ty ι} {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
      {ms : List (MethodMembers.Sig (Ty ι))} {ks : List KeyBound} {f : PropKey} {r : Bool}
      {A U : Ty ι} :
      HasTyWith G images subtyping Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → ⟨f, r, A⟩ ∈ os →
      Represents G U .undef → inheritedKey f = false → HasTyWith G images subtyping Γ (.readAt f a) (A ++ U)
  /-- A dictionary read may miss even when every present value has type `A`.
  An index says nothing of a key its class does not admit, so a key is read
  through one only where its class surely admits it: any string key through
  a string index, a canonical numeric one ("0", "1.5") through a number
  index, a symbol key through a symbol index. -/
  | readDict {f : PropKey} {K : IndexKeys} : HasTyWith G images subtyping Γ a Ref →
      Represents G Ref (.dict fs [] vs ix os ms ks cs) →
      (K, A) ∈ ix → K.surely f = true → Represents G U .undef → inheritedKey f = false →
      HasTyWith G images subtyping Γ (.readAt f a) (A ++ U)
  /-- A computed key of the key clause of a class within the index's reads
  through it: a string through a string index, a number through a number
  index or a string one, a symbol through a symbol index. -/
  | indexDict {K KK : IndexKeys} : HasTyWith G images subtyping Γ a Ref → Represents G Ref (.dict fs [] vs ix os ms ks cs) →
      HasTyWith G images subtyping Γ key Kt → Represents G Kt (keyClause KK) → KK.within K = true →
      (K, A) ∈ ix → Represents G U .undef → KK ≠ .strings →
      HasTyWith G images subtyping Γ (.indexAt a key) (A ++ U)
  | write : HasTyWith G images subtyping Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → (f, A) ∈ fs →
      HasTyWith G images subtyping Γ b A → Represents G N .nul → HasTyWith G images subtyping Γ (.writeAt f a b) N
  /-- A binary operator needs operand types it answers for, pair by pair
  (`Operands`), and yields the family of its result kind: no singleton, since
  the result's value is not typed. -/
  | arith : HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping Γ b B → OperatorTypes G op A B N →
      HasTyWith G images subtyping Γ (.arith op a b) N
  /-- A literal allocates a store: one fresh location per element, each
  under the position's contract of the tuple the store is claimed at, whose
  bounds the element count respects. -/
  | arrLit {Γ : List (Ty ι)} {L : Ty ι} {T : Tuple (Ty ι)} {xs : List (Ty ι × Tm)} :
      Represents G L (.list T []) → T.required.length ≤ xs.length →
      (T.rest = none → xs.length ≤ T.required.length + T.optional.length) →
      (∀ p ∈ xs.zipIdx, positionTy T p.2 = some p.1.1) →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → HasTyWith G images subtyping Γ (.arrLit (xs.map Prod.snd)) L
  /-- A required position, named by a literal index, reads at its contract. -/
  | elem {Γ : List (Ty ι)} {a i : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → HasTyWith G images subtyping Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → T.required[k]? = some A → HasTyWith G images subtyping Γ (.elemAt a i) A
  /-- An optional or rest position, named by a literal index, reads at its
  contract or `undefined`: it may be a hole or past the end. -/
  | elemOpt {Γ : List (Ty ι)} {a i : Tm} {L I A U : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → HasTyWith G images subtyping Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → T.required[k]? = none → positionTy T k = some A →
      Represents G U .undef → HasTyWith G images subtyping Γ (.elemAt a i) (A ++ U)
  /-- Any numeric index into a homogeneous array reads an element or
  `undefined`; no index is in bounds by type alone. -/
  | elemAny {Γ : List (Ty ι)} {a i : Tm} {L I E U : Ty ι} {ro : Bool} {presence : ArrayPresence} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list ⟨[], [], some E, ro, presence⟩ []) → HasTyWith G images subtyping Γ i I →
      Answers G I .isNum true → Represents G U .undef → HasTyWith G images subtyping Γ (.elemAt a i) (E ++ U)
  /-- A write at a literal index into a position the contract names keeps the
  contract: into the element's location, or a fresh one the store records.
  The index is at most the required length, so the write is in bounds or
  appends at the end: it never leaves a hole, and the store stays dense. -/
  | setElem {Γ : List (Ty ι)} {a i v : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → HasTyWith G images subtyping Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → positionTy T k = some A → k ≤ T.required.length →
      T.readonly = false → HasTyWith G images subtyping Γ v A → HasTyWith G images subtyping Γ (.setElem a i v) L
  | len {Γ : List (Ty ι)} {a : Tm} {L N : Ty ι} {T : Tuple (Ty ι)} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → Represents G N .num → HasTyWith G images subtyping Γ (.lenOf a) N
  /-- A string's own `length` is a number. -/
  | lenStr {Γ : List (Ty ι)} {a : Tm} {S N : Ty ι} :
      HasTyWith G images subtyping Γ a S → Answers G S .isStr true → Represents G N .num → HasTyWith G images subtyping Γ (.lenOf a) N
  /-- A string read at any numeric index is a string, or `undefined` past its
  end or at a key that is not an index. -/
  | elemStr {Γ : List (Ty ι)} {a i : Tm} {S I T U : Ty ι} :
      HasTyWith G images subtyping Γ a S → Answers G S .isStr true → HasTyWith G images subtyping Γ i I → Answers G I .isNum true →
      Represents G T .str → Represents G U .undef → HasTyWith G images subtyping Γ (.elemAt a i) (T ++ U)
  /-- A tag test whose answer the operand's type does not settle is still a
  Boolean: its type holds both literals. -/
  | test : HasTyWith G images subtyping Γ a A → (.boolLit true) ∈ expand G B → (.boolLit false) ∈ expand G B →
      HasTyWith G images subtyping Γ (.test k a) B
  | ifBool : HasTyWith G images subtyping Γ c C → Answers G C .isBool true →
      HasTyWith G images subtyping Γ t A → HasTyWith G images subtyping Γ e A → HasTyWith G images subtyping Γ (.ite c t e) A
  /-- The condition still evaluates; its singleton type selects the reachable arm. -/
  | ifKnown : HasTyWith G images subtyping Γ c C → Represents G C (.boolLit q) →
      HasTyWith G images subtyping Γ (if q then t else e) A → HasTyWith G images subtyping Γ (.ite c t e) A
  | ifBoolVar : Γ[i]? = some C → Answers G C .isBool true →
      Represents G T (.boolLit true) → Represents G F (.boolLit false) →
      HasTyWith G images subtyping (Γ.set i T) t A → HasTyWith G images subtyping (Γ.set i F) e A →
      HasTyWith G images subtyping Γ (.ite (.var i) t e) A
  | ifTag : Γ[i]? = some A → Answers G A tag q →
      (q = true → HasTyWith G images subtyping Γ u B) → (q = false → HasTyWith G images subtyping Γ e B) →
      HasTyWith G images subtyping Γ (.ite (.test tag (.var i)) u e) B
  /-- Eliminate a finite union in one immutable environment slot. Every member
  must establish the same term and result, without changing other bindings. -/
  | unionVar : Γ[i]? = some C →
      (∀ a ∈ C, HasTyWith G images subtyping (Γ.set i [a]) t A) → HasTyWith G images subtyping Γ t A
  /-- **A literal with spreads.** `[a, ...s, b]` allocates a fresh store of
  its parts' values in order: each plain part at the element type `E`, each
  spread the elements of the store it evaluates to, read where it is written,
  which spread into `E`. The store's length is not known, so its contract is
  `E` at every position. -/
  | arrParts {Γ : List (Ty ι)} {T E : Ty ι} {ro : Bool} {presence : ArrayPresence}
      {parts : List (Bool × Ty ι × Tm)} :
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      (∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E) →
      Represents G T (.list ⟨[], [], some E, ro, presence⟩ []) →
      HasTyWith G images subtyping Γ (.arrLit (parts.map fun p => spreadTerm (p.1, p.2.2))) T
  /-- **A variadic call.** The fixed actuals meet the selected signature's
  parameters, less trailing ones `Us` the call omits, each admitting
  `undefined`, and a call that omits a fixed position writes nothing further.
  The further parts fit the rest (`RestParts`): with a spread, each part is at
  the element rest's element or spreads into it; without one, the parts are
  at the positions of the rest's tuple contract. The signature may be a
  function's or a callable object's. -/
  | callRest {effect : Effect} {Γ : List (Ty ι)} {f r : Tm} {F Rt : Ty ι}
      {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} {P B : Ty ι} {parts : List (Bool × Ty ι × Tm)} :
      HasTyWith G images subtyping Γ f F → ⟨Rt, (xs.map Prod.fst ++ Us, P), B, effect⟩ ∈ restSigs G F → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) → (Us = [] ∨ parts = []) →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      RestParts G P (parts.map fun p => (p.1, p.2.1)) →
      HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2))) B
  /-- **A spread of a packed value.** A call at a variadic signature whose
  rest admits a packed binder `t`'s argument lists, after its fixed actuals,
  spreads the store of a value of `t`, or of a meet row of it: its elements
  are one of `t`'s lists. -/
  | callPacked {effect : Effect} {Γ : List (Ty ι)} {f r a : Tm} {F Rt A B P : Ty ι}
      {xs : List (Ty ι × Tm)} {t : ι} :
      HasTyWith G images subtyping Γ f F → ⟨Rt, (xs.map Prod.fst, P), B, effect⟩ ∈ restSigs G F →
      t ∈ P → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → HasTyWith G images subtyping Γ a A → PackedBy G A t →
      HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd ++
        [.spread (.readAt CallArguments.arrayStoreField a)])) B
  /-- **A bound function.** `.bind` saved its target, receiver and prefix in
  slots; allocation stores those values, as they are, in a forwarding
  descriptor with no fields. The result takes the positions the target's
  selected signature has after the prefix, with any receiver: the one it is
  later called with is dropped for the saved one. -/
  | bindE {effect : Effect} {Γ : List (Ty ι)} {F T Rt R Rc : Ty ι} {t r : Nat} {slots : List Nat}
      {Ps Ds : List (Ty ι)} :
      Γ[t]? = some T → ⟨Rt, Ps ++ Ds, R, effect⟩ ∈ callSigs G T →
      Γ[r]? = some Rt → slots.map (Γ[·]?) = Ps.map some →
      Represents G F (.arrs [⟨Rc, Ds, R, effect⟩] []) →
      HasTyWith G images subtyping Γ (.makeAt (.bound (.var t) (.var r) (slots.map .var)) [] []) F
  /-- **A bound variadic function.** As `bindE`, for a variadic signature of
  the target whose rest is an element rest: the prefix takes its first fixed
  positions, and past them the element; the result is the positions left, then
  the rest, at any receiver. -/
  | bindRestE {effect : Effect} {Γ : List (Ty ι)} {F T Rt E El R Rc : Ty ι} {t r : Nat} {slots : List Nat}
      {Ps Qs : List (Ty ι)} :
      Γ[t]? = some T → ⟨Rt, (Ps, E), R, effect⟩ ∈ restSigs G T → restElem G E = some El →
      Γ[r]? = some Rt → slots.map (Γ[·]?) = Qs.map some →
      Qs = Ps.take slots.length ++ List.replicate (slots.length - Ps.length) El →
      Represents G F (.arrs [] [⟨Rc, (Ps.drop slots.length, E), R, effect⟩]) →
      HasTyWith G images subtyping Γ (.makeAt (.bound (.var t) (.var r) (slots.map .var)) [] []) F
  /-- **A member bound to its host.** The member is read from the object in a
  slot, before anything else runs, and bound to that same object: the bound
  function meets the member's signatures whatever receiver it is later given,
  and each fixed or variadic signature one of them covers. The host's type is
  within each type the member's host must meet, by checked proofs. This is how
  a method call `o.m(args)` keeps JavaScript's order, reading the member before
  the actuals, while the member's contract stays host-relative. -/
  | bindMember {Γ : List (Ty ι)} {F O : Ty ι} {i : Nat} {k : PropKey}
      {m : MethodMembers.Sig (Ty ι)} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} :
      Γ[i]? = some O → memberOf G O k = some m → Represents G F (.arrs L S) →
      (∀ q ∈ L, ∃ c ∈ m.calls, CoveredCallUsing G images q c) →
      (∀ s ∈ S, ∃ c ∈ m.rests, CoveredRestUsing G images s c) →
      (∀ T ∈ m.receivers, ∃ p, PositiveCertificates.checkUsing G images O T p = true) →
      HasTyWith G images subtyping Γ (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) F
  /-- **A member bound to its host, at its quantified signatures.** As
  `bindMember`, the member is read from the object in a slot and bound to that
  same object; a generic method's signatures are a scheme the bound function
  meets, whatever receiver it is later given. A call names its instance below
  the scheme. -/
  | bindScheme {Γ : List (Ty ι)} {F O : Ty ι} {i : Nat} {k : PropKey}
      {m : MethodMembers.Sig (Ty ι)} :
      Γ[i]? = some O → memberOf G O k = some m → F ∈ m.schemes → expand G F = [] →
      HasTyWith G images subtyping Γ (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) F
  /-- `throw a` has every type: it never produces a value, and a throw is an
  outcome safety admits. Its operand runs first and must produce a
  JavaScript value. -/
  | throw : SourceValues G A → HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping Γ (.throw a) B
  /-- **An allocation from parts.** The accumulator, then the source; the
  result is what `MergeOk` states each pair of their clauses gives: a fresh
  plain object holding the accumulator's own fields and, over them, the own
  enumerable data properties the source has when it is copied, less the
  dropped keys (`ObjectMerge.merge_values_safe`). -/
  | merge {d : List PropKey} {a b : Tm} {A B R : Ty ι} :
      HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping Γ b B → ObjectMerge.MergeOk G d A B R = true →
      HasTyWith G images subtyping Γ (.merge d a b) R
  /-- **An allocation at a computed key.** The key, then the initializer; the
  result is the one-key object `KeyedOk` states each clause of the key's type
  gives: the one field a literal key names, or the dictionary over the class
  of a family's keys, writable at the initializer's type
  (`ComputedKey.keyed_values_safe`). -/
  | makeKey {k a : Tm} {K A R : Ty ι} :
      HasTyWith G images subtyping Γ k K → HasTyWith G images subtyping Γ a A →
      ComputedKey.KeyedOk G K A R = true →
      HasTyWith G images subtyping Γ (.makeKey k a) R
  | sub : HasTyWith G images subtyping Γ t A → subtyping.check A B cert = true → HasTyWith G images subtyping Γ t B

/-- Body typing with the ordinary checker as its default. -/
abbrev HasTyUsing (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (Γ : List (Ty ι)) (t : Tm) (A : Ty ι)
    (subtyping : BodySubtyping G := BodySubtyping.ordinary G images) : Prop :=
  HasTyWith G images subtyping Γ t A

namespace HasTyUsing
export HasTyWith (var nul undef tru fls truLit flsLit numLit num bigintLit bigint strLit str funGraph funScheme ctorGraph callableGraph construct constructRest callCallable readCallable readBagView writeCallable app letE alloc allocDict read readView lenView readProto readOptional readDict indexDict write arith arrLit elem elemOpt elemAny setElem len lenStr elemStr test ifBool ifKnown ifBoolVar ifTag unionVar arrParts callRest callPacked bindE bindRestE bindMember bindScheme throw merge makeKey sub)
end HasTyUsing

/-- A type reading none of a scheme's binders means the same at every
instantiation of them (`agree_freeWith`). -/
theorem meaning_assign_free {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) {bs : List ι} {A : Ty ι}
    (hA : ∀ l ∈ A, l ∈ D ∧ ∀ p ∈ fv V l, p ∉ bs) (As : List MixedFamily) {n W v}
    (h : meaning G A n W v) : meaning (reassign G (assign G.env bs As)) A n W v := by
  obtain ⟨l, hl, hv⟩ := h
  refine ⟨l, hl, ?_⟩
  change qDenoteWithArgs G (mixedParameters G) (assign G.env bs As, l) n W v
  rw [agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF) _ G.env l (hA l hl).1
    (fun p hp => by rw [assign_nmem G.env bs As ((hA l hl).2 p hp)])]
  exact hv

omit [DecidableEq ι] in
/-- **Captured values.** Slots of a context meeting it, each safe at the type
its code was checked with, hold closed values meeting those types in every
later world: what graph code captures when it is created. -/
theorem captures_sem {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n}
    {h : Heap} {caps : List (Ty ι × Nat)} (he : EnvOk G Γ ρ n W)
    (hlt : ∀ c ∈ caps, c.2 < Γ.length)
    (ih : ∀ c ∈ caps, Safe (excOf G) (meaning G c.1) n W h (ρ c.2))
    {j : Nat} (hj : j < n) {V : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) V) :
    (∀ v ∈ caps.map (fun c => ρ c.2), Scoped 0 v) ∧
      EnvOk G (caps.map Prod.fst) (envOf (caps.map fun c => ρ c.2) .nul) j V ∧
      ∀ c ∈ caps, meaning G c.1 j V (ρ c.2) := by
  have hvals : ∀ c ∈ caps, isVal (ρ c.2) = true ∧ Scoped 0 (ρ c.2) := by
    intro c hc
    obtain ⟨B, hB⟩ : ∃ B, Γ[c.2]? = some B :=
      ⟨_, List.getElem?_eq_getElem (hlt c hc)⟩
    exact meaning_value (he.2 _ _ hB)
  have hcapv : ∀ c ∈ caps, meaning G c.1 j V (ρ c.2) := by
    intro c hc
    cases n with
    | zero => omega
    | succ p =>
      have hm := safe_value_mem (hvals c hc).1 (ih c hc)
      exact (meaning_adm G c.1).mono j _ V hx _
        ((meaning_adm G c.1).down_le (p+1) j (Nat.le_of_lt hj) W _ hm)
  have hsc : ∀ v ∈ caps.map (fun c => ρ c.2), Scoped 0 v := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    exact (hvals c hc).2
  refine ⟨hsc, ?_, hcapv⟩
  apply EnvOk.envOf_nul hsc (by simp)
  intro i A hA v hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hA hv
  obtain ⟨c, hc, rfl⟩ := hA
  obtain ⟨c', hc', rfl⟩ := hv
  cases hc.symm.trans hc'
  exact hcapv c (List.mem_of_getElem? hc)

/-- Every derivation is safe in every admissible world and satisfying heap. -/
theorem HasTyUsing.sound {G : NormalGraph ι} {images : PositiveCertificates.InstanceImageCheck G}
    {subtyping : BodySubtyping G} {Γ t A}
    (ht : HasTyUsing G images (subtyping := subtyping) Γ t A) :
    ∀ n W h ρ, EnvOk G Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (excOf G) (meaning G A) n W h (instantiate 0 ρ t) := by
  induction ht with
  | var hi =>
    intro n W h ρ he hw hh
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact value_safe _ _ _ _ _ (meaning_value (he.2 _ _ hi)).1 (he.2 _ _ hi)
  | nul hr | undef hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | tru hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) (Or.inl rfl))
  | fls hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) (Or.inr rfl))
  | truLit hr | flsLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | numLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | @num _ _ b hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) ⟨b, rfl⟩)
  | bigintLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | @bigint _ _ i hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) ⟨i, rfl⟩)
  | strLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | @str _ _ s hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) ⟨s, rfl⟩)
  | @funGraph Γ F L S arity start E K caps kind rest As hr hkind hspec hlt hcap ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map]
    apply makeFn_rule nulT_adm nulT_valOnly n W h _ .nul rfl hw hh rfl
    intro j hj V hx
    obtain ⟨hsc, henv, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ih c hc n W h ρ he hw hh) hj hx
    have ho := offers_sem (oid := h.length + 1) [(codeField, h.length)] hkind hspec henv hsc (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1)
    exact (represents_back hr j V _) ⟨ho.1, ho.2⟩
  | @funScheme Γ i s arity start E K caps kind rest Ss hp hq hcon hkind hspec _hshape hcf hlt hcap ih =>
    obtain ⟨hF, hfree⟩ := capturesFree_sound hcf
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map]
    apply makeFn_rule nulT_adm nulT_valOnly n W h _ .nul rfl hw hh rfl
    intro j hj U hx
    obtain ⟨hsc, -, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ih c hc n W h ρ he hw hh) hj hx
    let vs := caps.map fun c => ρ c.2
    -- The captures, at every instantiation of the scheme's binders: their
    -- types read none of them.
    have henv : ∀ As : List MixedFamily,
        EnvOk (reassign G (assign G.env s.binders As)) (caps.map Prod.fst) (envOf vs .nul) j U := by
      intro As
      apply EnvOk.envOf_nul hsc (by simp)
      intro k A hA v hv
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hA hv
      obtain ⟨c, hc, rfl⟩ := hA
      obtain ⟨c', hc', rfl⟩ := hv
      cases hc.symm.trans hc'
      exact meaning_assign_free hF (hfree c.1 (List.mem_map_of_mem (List.mem_of_getElem? hc))) As
        (hcapv c (List.mem_of_getElem? hc))
    have hsig : ∀ As : List MixedFamily, As.length = s.binders.length →
        G.domain.allowed s As → instanceTWithArgs (excOf G) (fun η S => mixedValues G η S) G.env s As (graphArguments G) j U
          (Tm.fnObj h.length (.graph arity E K start vs kind rest)) := by
      intro As hlen hal
      have ho := offers_sem (G := reassign G (assign G.env s.binders As)) (oid := h.length + 1)
        [(codeField, h.length)] hkind
        (hspec G.env As hlen hal) (henv As) hsc (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1)
      simp only [instanceTWithArgs, sigsT, hcon, Bool.false_eq_true, if_false]
      exact ⟨ho.1, ho.2⟩
    refine ⟨i, List.mem_singleton_self i, ?_⟩
    change qDenoteWithArgs G (mixedParameters G) (G.env, i) j U _
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hp, hq, Bool.false_eq_true, if_false]
    refine ⟨?_, fun q hq As hlen hal _ => (instanceTWithArgs_adm _ _ _ _ _).down_le j q hq U _ (hsig As hlen hal)⟩
    simp only [Callee, hcon, Bool.false_eq_true, if_false]
    exact ⟨_, _, _, rfl, callable_of_kind hkind.1, by simpa [Scoped, vs, instantiate] using hsc⟩
  | @ctorGraph Γ F U L S arity start E K caps parts hr hu hnd hp hspec hrest hlt hcap ih ihc =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, List.map_cons, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.graph arity E K start (caps.map fun c => ρ c.2) .construct)
        (codeField :: parts.map Prod.fst) (.nul :: args))
      (fun hs => CallArguments.Step.makeArgs (.tail rfl hs)) (fun hr => (CallArguments.ArgRaises.tail rfl hr).make)
      hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu' heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlenA := ArgsT_length hargs
    apply make_fields_rule (As := nulT :: parts.map fun p => meaning G p.2.1)
      (by
        intro A hA'
        rcases List.mem_cons.mp hA' with rfl | hA'
        · exact nulT_adm
        · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by
        intro A hA'
        rcases List.mem_cons.mp hA' with rfl | hA'
        · exact nulT_valOnly
        · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap (.graph arity E K start (caps.map fun c => ρ c.2) .construct) _ (.nul :: args) hnd
      (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · rfl
        · exact ArgsT_values
            (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
            hargs v hv)
      hu' hok
      (by
        intro q hq
        simp only [List.zip_cons_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · rfl
        · exact ArgsT_zip hargs q hq)
    intro k' hk' V hy hrec
    have hWV : WExt (trunc k' (by omega) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hk') hx
    obtain ⟨hsc, henv, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ihc c hc n W h ρ he hw hh) (by omega) hWV
    have hvals : CallArguments.Values (caps.map fun c => ρ c.2) := by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1
    have hc := ctorsT_of_graph (oid := heap.length + (.nul :: args).length)
      (slots heap.length (codeField :: parts.map Prod.fst)) hspec hu henv hsc hvals
    have hcr := ctorRestsT_of_graph (oid := heap.length + (.nul :: args).length)
      (slots heap.length (codeField :: parts.map Prod.fst)) hrest hu henv hsc hvals
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    have hbag : recT (ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))) k' V
        (.objAt (slots heap.length (codeField :: parts.map Prod.fst)) .absent
          (heap.length + (.nul :: args).length)) := by
      obtain ⟨flds, oid, he', hall⟩ := hrec
      refine ⟨flds, oid, he', fun f T hm => hall f T ?_⟩
      rw [hfam] at hm
      simp only [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hm
    exact (represents_back hr k' V _)
      ⟨⟨hc, hcr⟩, ⟨⟨_, _, _, rfl, rfl, hbag⟩, by simp⟩, CallableConjunctions.views_nil⟩
  | @callableGraph Γ F L S arity start E K caps kind rest As parts hr hnd hp hkind hspec hlt hcap ih ihc =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.graph arity E K start (caps.map fun c => ρ c.2) kind rest)
        (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) (fun hr => hr.make) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlenA := ArgsT_length hargs
    apply make_fields_rule (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap (.graph arity E K start (caps.map fun c => ρ c.2) kind rest) _ args hnd
      (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k' hk' V hy hrec
    have hWV : WExt (trunc k' (by omega) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hk') hx
    obtain ⟨hsc, henv, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ihc c hc n W h ρ he hw hh) (by omega) hWV
    have ho := offers_sem (oid := heap.length + args.length) (slots heap.length (parts.map Prod.fst)) hkind hspec henv hsc (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1)
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    exact (represents_back hr k' V _)
      ⟨⟨⟨⟨_, _, _, rfl, rfl, by rw [hfam]; exact hrec⟩, by simp⟩, ho.1⟩, ho.2⟩
  | @construct Γ f F B L S xs Us a bs vs hf hr hp hx hu ihf ihx ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := construct_safe (Ξ := excOf G) (B := meaning G B)
      (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)) (Us.map (meaning G))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      hw hh (f := instantiate 0 ρ f) ?_ ?_ ?_
    · simpa only [List.map_map, Function.comp_def] using hs
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map, Function.comp_def, List.map_append] using
        ctorsT_select ((represents_raw hr k U v) hv).1.1
          (List.mem_map.mpr ⟨(xs.map Prod.fst ++ Us, B), hp,
            by simp [List.map_append, List.map_map, Function.comp_def]⟩)
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact ihx q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @constructRest Γ f F P B L S xs parts a bs vs hf hr hmem hx hp hparts ihf ihx ihp =>
    intro n W h ρ he hw hh
    have hfF : Safe (excOf G) (ctorRestsT (excOf G) [(xs.map fun p => meaning G p.1, argMeaning G P, meaning G B)])
        n W h (instantiate 0 ρ f) := by
      apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k _ U v hv
      have hc := ((represents_raw hr k U v) hv).1.2
      refine ⟨hc.1, fun q hq => ?_⟩
      rw [List.mem_singleton] at hq
      subst hq
      exact hc.2 _ (List.mem_map.mpr ⟨(xs.map Prod.fst, P, B), hmem,
        by simp [List.map_map, Function.comp_def]⟩)
    unfold RestParts at hparts
    split at hparts
    · -- A spread: the rest is an element rest.
      rename_i hany
      split at hparts
      · rename_i E hel
        have hterm : instantiate 0 ρ (.construct f
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .construct (instantiate 0 ρ f)
              ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
              (parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
                instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p _
          rcases p with ⟨_ | _, A, t⟩ <;> rfl
        have hpart : ∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E :=
          fun p hp' => hparts (p.1, p.2.1) (List.mem_map_of_mem hp')
        rw [hterm]
        apply construct_rest_safe (Ps := xs.map fun p => meaning G p.1)
          (E := meaning G E) (P := argMeaning G P) (R := meaning G B)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q.1)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q.1)
          (meaning_adm G E) (meaning_valOnly G E) (argMeaning_adm G P)
          (fun k W xs hxs => (restElem_args hel).mpr hxs)
          _ (by simp [List.map_map, Function.comp_def]) _
          (by
            intro q hq S hS
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
            rcases p with ⟨_ | _, A, t⟩
            · simp at hS
            · simp only [if_true, Option.some.injEq] at hS
              subst hS
              have := hpart _ hp'
              simp only [if_true] at this
              exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
          hw hh hfF
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          rcases p with ⟨_ | _, A, t⟩
          · have hA : A = E := by simpa using hpart _ hp'
            subst hA
            exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
    · -- No spread: the parts are at the positions of the rest's tuple contract.
      rename_i hany
      split at hparts
      · rename_i T hPT
        obtain ⟨hreq, hbound, hpos⟩ := hparts
        simp only [List.any_map, List.any_eq_true, not_exists, not_and, Function.comp_def,
          Bool.not_eq_true] at hany
        have hterm : instantiate 0 ρ (.construct f
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .construct (instantiate 0 ρ f)
              ((xs.map (fun p => (meaning G p.1, instantiate 0 ρ p.2)) ++
                parts.map (fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))).map Prod.snd) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p hp'
          simp [spreadTerm, hany p hp']
        rw [hterm]
        apply construct_pack_safe (Ps := xs.map fun p => meaning G p.1)
          (Qs := parts.map fun p => meaning G p.2.1)
          (P := argMeaning G P) (R := meaning G B)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_adm G _)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_valOnly G _)
          (argMeaning_adm G P)
          (fun k W extra ha => restParts_pack hPT (Qs := parts.map (·.2.1))
            (by simpa using hreq) (by simpa using hbound)
            (by
              intro i hi
              have := hpos i (by simpa using hi)
              simpa [List.getElem?_map, Option.map_map, Function.comp_def] using this)
            (by simpa [List.map_map, Function.comp_def] using ha))
          _ (by simp [List.map_map, Function.comp_def])
          hw hh hfF
        · intro q hq j hj U hxU hu heap hok
          rcases List.mem_append.mp hq with hq | hq <;> obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          · exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
  | @callCallable effect Γ f r F Rt B P Ps L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (Ξ := excOf G) (Rc := meaning G Rt) (B := meaning G B) (f := instantiate 0 ρ f)
      (r := instantiate 0 ρ r)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (meaning_adm G Rt) (meaning_valOnly G Rt)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa [Arrow.map, Contract.map, Arrow.plain, List.map_map, List.map_append, Function.comp_def] using
        CallEffects.callsT_erase (CallEffects.callsT_select (((represents_raw hr k U v) hv).1.2) (List.mem_map_of_mem hp))
    · intro j hj U hx hu' heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @readCallable Γ a Ref P Ps f A c ha hr hc hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact bag_read (meaning_valOnly G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      (bag_sem hc ((represents_raw hr j U v) ha')).1 hu hok
  | @readBagView Γ a Ref f A c ha hr hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, code, oid, l, c', rfl, hf, hl, hag⟩ :=
      CallableConjunctions.views_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
        (bagViews_sem ((represents_raw hr j U v) ha') (List.ne_nil_of_mem hm))
    exact read_view_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @writeCallable Γ a Ref P Ps f A b N c ha hr hc hm hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 Raises.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.writeAt f av) (Step.writeC2 hav) (Raises.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    apply Safe_mono k (fun i _ X v hval => (represents_back hn i X v) hval)
    exact bag_write (meaning_adm G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      (bag_sem hc ((represents_raw hr k V av) ha'')).1 hb' hbval hv hok'
  | @app effect Γ f r F Rt B L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (Ξ := excOf G) (Rc := meaning G Rt) (B := meaning G B) (f := instantiate 0 ρ f)
      (r := instantiate 0 ρ r)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (meaning_adm G Rt) (meaning_valOnly G Rt)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa [Arrow.map, Contract.map, Arrow.plain, List.map_map, List.map_append, Function.comp_def] using
        CallEffects.callsT_erase (CallEffects.callsT_select ((represents_raw hr k U v) hv).1 (List.mem_map_of_mem hp))
    · intro j hj U hx hu' heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @letE Γ a A b B ha hb iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .letE a (instantiate 1 ρ b)) Step.letC Raises.letC n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    cases j with
    | zero => trivial
    | succ k =>
      apply let_rule _ _ hav k U heap hu hok
      rw [instantiate_beta ρ he.1]
      have he' := ((he.transfer (k+1) hj U hx).push ha').transfer k (Nat.le_succ k)
        (trunc k (Nat.le_succ k) U) (WExt_refl _)
      exact ihb k _ heap (push av ρ) he' (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @alloc Γ Ref parts ks hnd hp hr hbound hreal ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt .absent (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) (fun hr => hr.make) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply make_fields_rule
      (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap .absent _ args hnd (by simpa using hlen.symm) (by simpa using hlen.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hrec
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    have hrec' := hrec
    rw [← hfam] at hrec'
    refine (represents_sem hr k V _).mpr ⟨⟨⟨hrec', by simp⟩, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      ⟨by simpa [ReferenceConjunctions.famsOf] using optT_nil, MethodMembers.methodT_nil _ _ _,
        fun K hK => ownKeysT_slots fun n hn => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
          exact hbound K hK p hp⟩⟩, ?_⟩
    have hinv := allocBuiltins_sound hreal (by simpa [List.map_map, Function.comp_def] using hnd)
      (.refs (parts.map fun p => (p.1, p.2.1)) [] [] [] [] ks) (base := heap.length) (k := k) (V := V)
      (by simpa [List.map_map, Function.comp_def] using hrec)
    simpa [List.map_map, Function.comp_def] using hinv
  | @allocDict Γ Ref parts ix cs os hnd hproto hstore hp hr hix habs _ ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt .absent (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) (fun hr => hr.make) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply make_fields_rule
      (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap .absent _ args hnd (by simpa using hlen.symm) (by simpa using hlen.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hrec
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    -- The object owns exactly the fields, each at its part's type.
    have hown : ∀ f l, (slots heap.length (parts.map Prod.fst)).lookup f = some l →
        ∃ T, (f, T) ∈ (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      intro f l hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (slots_lookup_mem hl)
      exact ⟨meaning G p.2.1, by
        rw [← hfam]; exact List.mem_map.mpr ⟨(p.1, p.2.1), List.mem_map_of_mem hp, rfl⟩⟩
    have hnp := slots_lookup_none (base := heap.length) hproto
    have hcell : ∀ y ∈ ix ++ cs,
        dictCellT y.1 (meaning G y.2) k V (.objAt (slots heap.length (parts.map Prod.fst)) .absent (heap.length + args.length)) := by
      intro y hy
      refine dictCellT_of_recT hrec hown hnp fun f T hT hk => ?_
      rw [← hfam] at hT
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hT
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      cases hqe
      rw [hix p hp y hy (IndexKeys.may_of_admits hk)]
      exact fun _ _ _ _ => Iff.rfl
    have hrec' := hrec
    rw [← hfam] at hrec'
    refine (represents_sem hr k V _).mpr ⟨⟨⟨hrec', by simp⟩,
      fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      ⟨fun y hy => dictCellT_view (hcell y (List.mem_append_left _ hy)),
        fun y hy => hcell y (List.mem_append_right _ hy)⟩,
      ⟨_, _, rfl, fun _ _ _ => hnp, fun o ho l hl => by
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        rw [show (OptionalField.map (meaning G) o').key = o'.key from rfl,
          slots_lookup_none (habs o' ho')] at hl
        cases hl⟩, MethodMembers.methodT_nil _ _ _,
      fun K hK => by simp at hK⟩, builtinInvariant_of_lookup (slots_lookup_none hstore)⟩
  | @read Γ a Ref c fs vs f A ha hr hc hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, l, c, oid', rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) (namedMembers_sem hr hc ha').1
    exact read_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @readView Γ a Ref c fs vs f A ha hr hc hm hlen ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    have hviews := (namedMembers_sem hr hc ha').2
    have hmA : (f, meaning G A) ∈ ReferenceConjunctions.famsOf (meaning G) vs :=
      ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩
    cases j with
    | zero => trivial
    | succ j =>
      obtain ⟨flds, l, c, oid', rfl, hf, hl, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr (j + 1))
          (oid : Nat), v = .objAt flds .absent oid ∧ flds.lookup f = some l ∧ lookup U l = some c ∧
          ∀ (i : Nat) (hi : i < j + 1) (W' : WorldT i) (u : Val), c i hi W' u → meaning G A i W' u := by
        rcases hlen with hlen | hex
        · exact viewsT_at hmA hlen hviews
        · rcases hviews f _ hmA with hv1 | ⟨-, -, hall⟩
          · exact viewT_at (List.mem_singleton_self _) hv1
          · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hex
            exact absurd (hall 0 (by omega) (ofList []) w) (numWitness_sound hw)
      exact read_view_rule (meaning_valOnly G A) (j + 1) U heap l hu hok hf hl hag
  | @lenView Γ i Ref A c fs vs hi hr hc hm hnum =>
    intro n W h ρ henv hw hh
    have hval := (meaning_value (henv.2 i Ref hi)).1
    simp only [lengthRead, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ n =>
      cases n with
      | zero =>
        exact Or.inr ⟨trunc 0 (by omega) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
          .iteC (.testV hval), HeapOk_trunc 0 W h hh, trivial⟩
      | succ k =>
        have henv' := henv.transfer k (by omega) _ (WExt_refl _)
        have hv := henv'.2 i Ref hi
        have hw' : WorldAdm (trunc k (by omega) W) := WorldAdm_trunc _ hw
        have hh' : HeapOk k (trunc k (by omega) W) h := by
          simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh)
        obtain ⟨hsem, hinv⟩ := (represents_sem hr k _ (ρ i)).mp hv
        obtain ⟨hrec, hviews⟩ := namedMembers_sem hr hc hv
        obtain ⟨flds, oid, hρ, -⟩ := hrec
        apply ite_test_rule .isArray (ρ i) hval _ _ k W h hw hh
        · -- An array: its store is a list, whose length the view's type holds.
          intro ht
          rw [hρ] at ht ⊢
          have hst : (flds.lookup CallArguments.arrayStoreField).isSome = true := ht
          have hinv' := hinv
          rw [hρ] at hinv'
          obtain ⟨l, c', hf, hl, hag⟩ := builtinInvariant_store (namedMembers_carriesInvariant hc) hinv' hst
          apply bind Tm.lenOf Step.lenC Raises.lenC k _ h _ hw' hh'
            (read_view_rule (A := fun _ _ u => ∃ ls, u = .arr ls) (fun _ _ _ ⟨ls, he⟩ => by subst he; rfl)
              k _ h l hw' hh' hf hl hag)
          intro j _ U _ hu heap av hok _ ⟨ls, hav⟩
          subst hav
          exact len_rule j U heap hu hok (fun m U' => numIn_sound hnum G.env _)
        · -- Any other object: no store, so the view is at its own location.
          intro hf
          rw [hρ] at hf ⊢
          have hf2 : (flds.lookup CallArguments.arrayStoreField).isSome = false := hf
          have hns : flds.lookup CallArguments.arrayStoreField = none := by
            cases hl : flds.lookup CallArguments.arrayStoreField with
            | none => rfl
            | some l => rw [hl] at hf2; cases hf2
          rw [hρ] at hviews
          obtain ⟨flds', l, c', oid', he', hf', hl, hag⟩ :=
            viewsT_at_plain (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) hns hviews
          cases he'
          exact read_view_rule (meaning_valOnly G A) k _ h l hw' hh' hf' hl hag
  | @readProto Γ a Ref P fs vs os ms ks K gs ws os' ms' ks' f A ha hr hK hf hpr hP hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    have hs := (represents_raw hr j U v) ha'
    have hloc : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr j) (oid : Nat), v = .objAt flds .absent oid ∧
        flds.lookup CallArguments.protoField = some l ∧ lookup U l = some c ∧
        ∀ (i : Nat) (hi : i < j) (V : WorldT i) (u : Val), c i hi V u → meaning G P i V u := by
      rcases List.mem_append.mp hpr with hpr | hpr
      · obtain ⟨flds, l, c, oid', he, hf', hl, hag⟩ :=
          recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨P, hpr, rfl⟩) hs.1.1
        exact ⟨flds, l, c, oid', he, hf', hl, fun i hi V u hu => (hag i hi V u).mp hu⟩
      · exact viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨P, hpr, rfl⟩) (by decide) hs.2.1
    obtain ⟨flds, l, c, oid, rfl, hpf, hl, hag⟩ := hloc
    have hmiss := ownKeysT_lookup (hs.2.2.2.2 K hK) hf
    apply read_proto_rule j U heap l hu hok hmiss hpf hl hag
    intro i V h' hV hh' u hu
    have hp := (represents_raw hP i V u) hu
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨flds', l', c', oid'', rfl, hf', hl', hag'⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) hp.1.1
      exact read_rule (meaning_valOnly G A) i V h' l' hV hh' hf' hl' hag'
    · obtain ⟨hm, hml⟩ := List.mem_filter.mp hm
      obtain ⟨flds', l', c', oid'', rfl, hf', hl', hag'⟩ :=
        viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) (by simpa using hml) hp.2.1
      exact read_view_rule (meaning_valOnly G A) i V h' l' hV hh' hf' hl' hag'
  | @readOptional Γ a Ref fs vs os ms ks f r A U ha hr hm hUnd _ ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj V hx hv heap v hok hval ha'
    have hs := (represents_raw hr j V v) ha'
    obtain ⟨flds, oid, rfl, _⟩ := hs.1.1
    apply Safe_mono j (fun k _ X u hu => (meaning_append G A U k X u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_back hUnd k X u) h)))) V heap _
      (read_optional_rule (meaning_valOnly G A) j V heap hv hok
        (optT_no_proto (List.mem_map_of_mem hm) hs.2.2.1)
        (fun l hl => by
          obtain ⟨c, hc, hag⟩ := optT_present (List.mem_map_of_mem hm) hs.2.2.1 hl
          exact ⟨c, hc, fun i hi U u hu => (hag i hi U u).1 hu⟩))

  | @readDict Γ a Ref fs vs ix os ms ks cs A U f K ha hr hm hsure hUnd _ ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj V hx hv heap v hok hval ha'
    have hd := ((represents_raw hr j V v) ha').2.2.1.1 (K, A) hm
    obtain ⟨flds, oid, rfl, _⟩ := ((represents_raw hr j V v) ha').1.1
    apply Safe_mono j (fun k _ X u hu => (meaning_append G A U k X u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_back hUnd k X u) h)))) V heap _
      (read_dict_rule (meaning_valOnly G A) j V heap hv hok (IndexKeys.surely_admits hsure) hd)
  | @indexDict Γ a Ref fs vs ix os ms ks cs key Kt A U K KK ha hr hk hStr hwithin hm hUnd _ iha ihk =>
    intro n W h ρ he hw hh
    apply bind (fun v => .indexAt v (instantiate 0 ρ key)) Step.indexC1 Raises.indexC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj V hx hv heap av hok hav ha'
    apply bind (Tm.indexAt av) (Step.indexC2 hav) (Raises.indexC2 hav) j V heap _ hv hok
      (ihk j V heap ρ (he.transfer j hj V hx) hv hok)
    intro k hk X hy hX heap' kv hok' hkv hk'
    have ha'' := (meaning_adm G Ref).mono k _ X hy av
      ((meaning_adm G Ref).down_le j k hk V av ha')
    obtain ⟨f, hkey, hadmits⟩ := keyClause_admits ((represents_raw hStr k X kv) hk')
    have hd := dictViewT_within hwithin (((represents_raw hr k X av) ha'').2.2.1.1 (K, A) hm)
    obtain ⟨flds, oid, rfl, _⟩ := ((represents_raw hr k X av) ha'').1.1
    apply Safe_mono k (fun i _ Y u hu => (meaning_append G A U i Y u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_back hUnd i Y u) h)))) X heap' _
      (index_dict_rule (meaning_valOnly G A) k X heap' hX hok' hkey hadmits hd)
  | @arrLit Γ L T xs hr hreq hbound hpos hx ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd
        = xs.map fun x => instantiate 0 ρ x.2 := by simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.1)
      (fun args => .arrLit args) (fun hs => CallArguments.Step.arrArgs hs) (fun hr => hr.arrLit) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.fst
        = xs.map fun p => meaning G p.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply arr_alloc_rule (As := xs.map fun p => meaning G p.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.1)
      j U heap args hlen.symm
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hl
    refine (represents_back hr k V _) ⟨?_, by simp⟩
    rw [hlen]
    apply listT_alloc
    · simpa [tupleFams] using hreq
    · intro hn
      simp only [tupleFams, List.length_map, Option.map_eq_none_iff] at hn ⊢
      exact hbound hn
    · intro i A hA
      rw [positionFam_tupleFams]
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hA
      obtain ⟨p, hp, rfl⟩ := hA
      have := hpos (p, i) (by simpa [List.mem_zipIdx_iff_getElem?] using hp)
      simp [this]
    · exact hl
  | @elem Γ a i L I A T b k ha hr hi hI hk hA iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U heap _ hu hok
      (ihi j U heap ρ (he.transfer j hj U hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U av ha')
    obtain ⟨ls, rfl, -, -, -, hreq, -, -⟩ := ((represents_raw hr m V av) ha'').1
    simp only [tupleFams, List.getElem?_map] at hreq
    have hb : iv = .num b := (represents_raw hI m V iv) hi'
    subst hb
    obtain ⟨l, c, hl, hw', hag⟩ := hreq k (meaning G A) (by simp [hA])
    exact elem_read_rule (meaning_valOnly G A) m V heap' l hv hok' (by simp [elemLoc, hk, hl]) hw'
      (fun j hj U u => (hag j hj U u).1)
  | @elemOpt Γ a i L I A U T b k ha hr hi hI hk hnone hA hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U' av ha')
    obtain ⟨ls, rfl, -, -, -, -, hopt, hrest⟩ := ((represents_raw hr m V av) ha'').1
    simp only [tupleFams, List.length_map, List.getElem?_map] at hopt hrest
    have hb : iv = .num b := (represents_raw hI m V iv) hi'
    subst hb
    have hundef : ∀ m' (U'' : WorldT m'), meaning G (A ++ U) m' U'' .undef := fun m' U'' =>
      (meaning_append G A U m' U'' _).mpr (Or.inr ((represents_back hU m' U'' _) rfl))
    cases hloc : elemLoc ls b with
    | none => exact elem_absent_rule m V heap' hv hok' hloc hundef
    | some l =>
      have hl : ls[k]? = some (some l) := by
        simp only [elemLoc, hk, Option.bind_some] at hloc
        cases hls : ls[k]? with
        | none => simp [hls] at hloc
        | some o => cases o with
          | none => simp [hls] at hloc
          | some l' => simp [hls] at hloc; subst hloc; rfl
      have hpos := hA
      simp only [positionTy, hnone] at hpos
      have key : ∃ c : Ctr m, lookup V l = some c ∧
          ∀ (j : Nat) (hj : j < m) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (meaning G A j W' u) := by
        split at hpos
        · rename_i hopt'
          cases hpos
          have hk' : T.required.length + (k - T.required.length) = k := by
            have := (List.getElem?_eq_none_iff.mp hnone); omega
          exact hopt (k - T.required.length) (meaning G A) l
            (by simp [hopt']) (by rw [hk']; exact hl)
        · split at hpos
          · rename_i hge
            obtain ⟨E, c, hE, hw', hag⟩ := hrest k l hge hl
            simp only [Option.map_eq_some_iff] at hE
            obtain ⟨e, he, rfl⟩ := hE
            rw [he] at hpos
            cases hpos
            exact ⟨c, hw', hag⟩
          · cases hpos
      obtain ⟨c, hw', hag⟩ := key
      apply Safe_mono m (fun m' _ U'' u hu => (meaning_append G A U m' U'' u).mpr (Or.inl hu))
      exact elem_read_rule (meaning_valOnly G A) m V heap' l hv hok' hloc hw' (fun j hj U u => (hag j hj U u).1)
  | @elemAny Γ a i L I E U ro presence ha hr hi hq hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U' av ha')
    obtain ⟨ls, rfl, -, -, -, -, -, hrest⟩ := ((represents_raw hr m V av) ha'').1
    have hnum := answers_sound hq hi'
    obtain ⟨b, rfl⟩ : ∃ b, iv = .num b := by
      cases iv <;> simp [tagHolds] at hnum; exact ⟨_, rfl⟩
    have hundef : ∀ m' (U'' : WorldT m'), meaning G (E ++ U) m' U'' .undef := fun m' U'' =>
      (meaning_append G E U m' U'' _).mpr (Or.inr ((represents_back hU m' U'' _) rfl))
    cases hloc : elemLoc ls b with
    | none => exact elem_absent_rule m V heap' hv hok' hloc hundef
    | some l =>
      obtain ⟨k, hk, hl⟩ : ∃ k, indexOfBits b = some k ∧ ls[k]? = some (some l) := by
        simp only [elemLoc] at hloc
        cases hkb : indexOfBits b with
        | none => simp [hkb] at hloc
        | some k =>
          simp only [hkb, Option.bind_some] at hloc
          cases hls : ls[k]? with
          | none => simp [hls] at hloc
          | some o => cases o with
            | none => simp [hls] at hloc
            | some l' => simp [hls] at hloc; subst hloc; exact ⟨k, rfl, hls⟩
      obtain ⟨E', c, hE, hw', hag⟩ := hrest k l (by simp [tupleFams]) hl
      simp only [tupleFams, List.map_nil, Option.map_some, Option.some.injEq] at hE
      subst hE
      apply Safe_mono m (fun m' _ U'' u hu => (meaning_append G E U m' U'' u).mpr (Or.inl hu))
      exact elem_read_rule (meaning_valOnly G E) m V heap' l hv hok' hloc hw' (fun j hj U u => (hag j hj U u).1)
  | @setElem Γ a i v L I A T b k ha hr hi hI hk hA hkle hro hv iha ihi ihv =>
    intro n W h ρ he hw hh
    apply bind (fun a => .setElem a (instantiate 0 ρ i) (instantiate 0 ρ v)) Step.setC1 Raises.setC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (fun i => .setElem av i (instantiate 0 ρ v)) (Step.setC2 hav) (Raises.setC2 hav) j U heap _ hu hok
      (ihi j U heap ρ (he.transfer j hj U hx) hu hok)
    intro m hm V hy hvw heap' iv hok' hival hi'
    apply bind (.setElem av iv) (Step.setC3 hav hival) (Raises.setC3 hav hival) m V heap' _ hvw hok'
      (ihv m V heap' ρ ((he.transfer j hj U hx).transfer m hm V hy) hvw hok')
    intro p hp X hz hxw heap'' vv hok'' hvval hv'
    have hav' := (meaning_adm G L).mono p _ X hz av ((meaning_adm G L).down_le m p hp V av
      ((meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U av ha')))
    have hlist := ((represents_raw hr p X av) hav').1
    obtain ⟨ls, rfl, -, hlen, -, hreq, hopt, hrest⟩ := hlist
    simp only [tupleFams, List.length_map, List.getElem?_map] at hreq hopt hrest hlen
    have rwContract : ∀ P Q : Prop, SlotContract T.readonly P Q ↔ (P ↔ Q) := by
      intro P Q; simp [SlotContract, hro, iff_def]
    simp only [rwContract] at hreq hopt hrest
    have hb : iv = .num b := (meaning_adm G I).mono p _ X hz iv ((meaning_adm G I).down_le m p hp V iv hi')
      |> (represents_raw hI p X iv)
    subst hb
    have hkeep : ∀ j' (hj' : j' < p) (U' : WorldT j'), WExt (trunc j' (Nat.le_of_lt hj') X) U' →
        meaning G L j' U' (.arr ls) := fun j' hj' U' hx' =>
      (meaning_adm G L).mono j' _ U' hx' _ ((meaning_adm G L).down_le p j' (by omega) X _ hav')
    cases hloc : elemLoc ls b with
    | some l =>
      have hl : ls[k]? = some (some l) := by
        simp only [elemLoc, hk, Option.bind_some] at hloc
        cases hls : ls[k]? with
        | none => simp [hls] at hloc
        | some o => cases o with
          | none => simp [hls] at hloc
          | some l' => simp [hls] at hloc; subst hloc; rfl
      have key : ∃ c : Ctr p, lookup X l = some c ∧
          ∀ (j : Nat) (hj : j < p) (W' : WorldT j) (u : Val), c j hj W' u ↔ meaning G A j W' u := by
        have hpos := hA
        simp only [positionTy] at hpos
        split at hpos
        · rename_i hreq'
          cases hpos
          obtain ⟨l', c, hl', hw', hag⟩ := hreq k (meaning G A) (by simp [hreq'])
          cases Option.some.inj (Option.some.inj (hl.symm.trans hl'))
          exact ⟨c, hw', hag⟩
        · rename_i hnone
          split at hpos
          · rename_i hopt'
            cases hpos
            have hk' : T.required.length + (k - T.required.length) = k := by
              have := (List.getElem?_eq_none_iff.mp hnone); omega
            exact hopt (k - T.required.length) (meaning G A) l
              (by simp [hopt']) (by rw [hk']; exact hl)
          · split at hpos
            · rename_i hge
              obtain ⟨E, c, hE, hw', hag⟩ := hrest k l hge hl
              simp only [Option.map_eq_some_iff] at hE
              obtain ⟨e, he, rfl⟩ := hE
              rw [he] at hpos
              cases hpos
              exact ⟨c, hw', hag⟩
            · cases hpos
      obtain ⟨c, hw', hag⟩ := key
      exact set_present_rule (meaning_adm G A) p X heap'' l vv hvval hxw hok'' hloc hw' hag hv' hkeep
    | none =>
      apply set_grow_rule (meaning_adm G A) (meaning_valOnly G A) p X heap'' vv hvval hxw hok'' hk hloc hv'
      intro j' hj' U' hx' hm'
      refine (represents_back hr j' U' _) ⟨?_, by simp⟩
      have hold := ((represents_raw hr j' U' _) (hkeep j' hj' U' hx')).1
      apply listT_grow hold
      · rw [positionFam_tupleFams, hA]; rfl
      · simp only [elemLoc, hk, Option.bind_some] at hloc; exact hloc
      · omega
      · exact hm'
  | @len Γ a L N T ha hr hn ih =>
    intro n W h ρ he hw hh
    apply bind Tm.lenOf Step.lenC Raises.lenC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    obtain ⟨ls, rfl, -⟩ := ((represents_raw hr j U av) ha').1
    exact len_rule j U heap hu hok (fun m U' => (represents_back hn m U' _) ⟨_, rfl⟩)
  | @lenStr Γ a S N ha hs hn ih =>
    intro n W h ρ he hw hh
    apply bind Tm.lenOf Step.lenC Raises.lenC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    have hstr := answers_sound hs ha'
    obtain ⟨s, rfl⟩ : ∃ s, av = .str s := by
      cases av <;> simp [tagHolds] at hstr; exact ⟨_, rfl⟩
    exact len_str_rule j U heap hu hok (fun m U' => (represents_back hn m U' _) ⟨_, rfl⟩)
  | @elemStr Γ a i S I T U ha hs hi hq hT hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G S).mono m _ V hy av ((meaning_adm G S).down_le j m hm U' av ha')
    have hstr := answers_sound hs ha''
    obtain ⟨s, rfl⟩ : ∃ s, av = .str s := by
      cases av <;> simp [tagHolds] at hstr; exact ⟨_, rfl⟩
    have hnum := answers_sound hq hi'
    obtain ⟨b, rfl⟩ : ∃ b, iv = .num b := by
      cases iv <;> simp [tagHolds] at hnum; exact ⟨_, rfl⟩
    exact elem_str_rule m V heap' hv hok'
      (fun m' U'' t => (meaning_append G T U m' U'' _).mpr (Or.inl ((represents_back hT m' U'' _) ⟨t, rfl⟩)))
      (fun m' U'' => (meaning_append G T U m' U'' _).mpr (Or.inr ((represents_back hU m' U'' _) rfl)))
  | @test Γ a A B k ha ht hf ih =>
    intro n W h ρ he hw hh
    apply bind (.test k) Step.testC Raises.testC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    cases j with
    | zero => trivial
    | succ p =>
      apply Safe_mono (p+1) (fun m _ X v hv => ?_) U heap _ (test_value_safe k av hav p U heap hu hok)
      rcases hv with rfl | rfl
      · exact expand_sem_mpr ⟨_, expand_sub ht, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
      · exact expand_sem_mpr ⟨_, expand_sub hf, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
  | @merge Γ d a b A B R ha hb hm iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .merge d a (instantiate 0 ρ b)) Step.mergeC1 Raises.mergeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.merge d av) (Step.mergeC2 hav) (Raises.mergeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G A).mono k _ V hy av ((meaning_adm G A).down_le j k hk U av ha')
    exact ObjectMerge.merge_values_safe hm hv hok' ha'' hb'
  | @makeKey Γ k a K A R hk ha hm ihk iha =>
    intro n W h ρ he hw hh
    apply bind (fun k => .makeKey k (instantiate 0 ρ a)) Step.makeKeyC1 Raises.makeKeyC1 n W h _ hw hh
      (ihk n W h ρ he hw hh)
    intro j hj U hx hu heap kv hok hkv hk'
    apply bind (.makeKey kv) (Step.makeKeyC2 hkv) (Raises.makeKeyC2 hkv) j U heap _ hu hok
      (iha j U heap ρ (he.transfer j hj U hx) hu hok)
    intro i hi V hy hv heap' av hok' haval ha'
    have hk'' := (meaning_adm G K).mono i _ V hy kv ((meaning_adm G K).down_le j i hi U kv hk')
    exact ComputedKey.keyed_values_safe hm hv hok' hk'' ha'
  | @arith Γ a A b B op N ha hb hopt iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .arith op a (instantiate 0 ρ b)) Step.arithC1 Raises.arithC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.arith op av) (Step.arithC2 hav) (Raises.arithC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G A).mono k _ V hy av ((meaning_adm G A).down_le j k hk U av ha')
    rcases hopt with hopt | ⟨hdec, hn⟩
    case inr =>
      have hres : ∃ z, binop op av bv = some z ∧ OpResult.bool.holds z := by
        rcases hdec with ⟨hp, hall⟩ | ⟨hp, hall⟩
        · obtain ⟨c, hc, hca, -⟩ := (expand_sem G A hp k V av).mp ha''
          exact (decidingClause_sound (hall c hc) hca hbval).1
        · obtain ⟨d, hd, hdb, -⟩ := (expand_sem G B hp k V bv).mp hb'
          exact (decidingClause_sound (hall d hd) hdb hav).2
      obtain ⟨z, hz, hr⟩ := hres
      refine arith_value_safe op av bv z hz k V heap' hv hok' (fun m U => ?_)
      rcases hr with rfl | rfl
      · exact expand_sem_mpr ⟨_, expand_sub hn.1, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
      · exact expand_sem_mpr ⟨_, expand_sub hn.2, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
    unfold ClauseOperatorTypes at hopt
    split at hopt
    case h_2 => exact hopt.elim
    rename_i r _
    obtain ⟨hops, hn⟩ := hopt
    obtain ⟨c, hc, hca, -⟩ := (expand_sem G A hops.1 k V av).mp ha''
    obtain ⟨d, hd, hdb, -⟩ := (expand_sem G B hops.2.1 k V bv).mp hb'
    rcases opResult_sound (hops.2.2 c hc d hd) hca hdb with ⟨z, hz, hr⟩ | hthrow
    case inr => exact arith_throw_safe op av bv hthrow k V heap' hv hok' (builtinExc_errors G _)
    refine arith_value_safe op av bv z hz k V heap' hv hok' (fun m U => ?_)
    cases r with
    | num => obtain ⟨x, rfl⟩ := hr; exact (represents_back hn m U _) ⟨x, rfl⟩
    | bigint => obtain ⟨i, rfl⟩ := hr; exact (represents_back hn m U _) ⟨i, rfl⟩
    | str => obtain ⟨s, rfl⟩ := hr; exact (represents_back hn m U _) ⟨s, rfl⟩
    | bool =>
      rcases hr with rfl | rfl
      · exact expand_sem_mpr ⟨_, expand_sub hn.1, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
      · exact expand_sem_mpr ⟨_, expand_sub hn.2, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
  | @write Γ a Ref fs vs os ms ks f A b N ha hr hm hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 Raises.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.writeAt f av) (Step.writeC2 hav) (Raises.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    obtain ⟨flds, l, c, oid', rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) ((represents_raw hr k V av) ha'').1.1
    apply Safe_mono k (fun i _ X v hval => (represents_back hn i X v) hval)
    exact write_rule (meaning_adm G A) k V heap' l bv hbval hv hok' hf hl hag hb'
  | @ifBool Γ c C t A e hc hbool ht he ihc iht ihe =>
    intro n W h ρ henv hw hh
    apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC Raises.iteC
      n W h _ hw hh (ihc n W h ρ henv hw hh)
    intro j hj U hx hu heap v hok hv ha
    have hb := answers_sound hbool ha
    have shape : v = .tru ∨ v = .fls := by cases v <;> simp_all [tagHolds]
    rcases shape with rfl | rfl
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
          WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
          WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
        exact ihe k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @ifKnown Γ c C q t e A hc hq ht ihc iht =>
    intro n W h ρ henv hw hh
    apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC Raises.iteC
      n W h _ hw hh (ihc n W h ρ henv hw hh)
    intro j hj U hx hu heap v hok hv ha
    have hvalue := (represents_raw hq j U v) ha
    cases q <;> simp only [semWithArgs] at hvalue <;> subst v
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
          WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
          WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @ifBoolVar Γ i C T F t A e hi hb hT hF ht he iht ihe =>
    intro n W h ρ henv hw hh
    have hshape := answers_sound hb (henv.2 i C hi)
    have shape : ρ i = .tru ∨ ρ i = .fls := by
      cases hv : ρ i <;> simp_all [tagHolds]
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ k =>
      rcases shape with hv | hv
      · have refined := henv.refine hi (represents_back hT (k+1) W (ρ i) rfl (by simp [hv, semWithArgs]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ t,WExt_refl _,
          WorldAdm_trunc _ hw,.iteT,HeapOk_trunc k W h hh,?_⟩
        exact iht k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
      · have refined := henv.refine hi (represents_back hF (k+1) W (ρ i) rfl (by simp [hv, semWithArgs]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ e,WExt_refl _,
          WorldAdm_trunc _ hw,.iteF,HeapOk_trunc k W h hh,?_⟩
        exact ihe k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    intro n W h ρ henv hw hh
    have hval := (meaning_value (henv.2 i A hi)).1
    have htag := answers_heap h hq (henv.2 i A hi)
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ n =>
      cases n with
      | zero =>
        exact Or.inr ⟨trunc 0 (by omega) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
          .iteC (.testV hval), HeapOk_trunc 0 W h hh, trivial⟩
      | succ k =>
        apply ite_test_rule tag (ρ i) hval _ _ k W h hw hh
        · intro ht
          exact iht (htag.symm.trans ht) k _ h ρ
            (henv.transfer k (by omega) _ (WExt_refl _))
            (WorldAdm_trunc _ hw) (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh))
        · intro he
          exact ihe (htag.symm.trans he) k _ h ρ
            (henv.transfer k (by omega) _ (WExt_refl _))
            (WorldAdm_trunc _ hw) (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh))
  | @unionVar Γ i C t A hi ht ih =>
    intro n W h ρ henv hw hh
    obtain ⟨a, ha, hv⟩ := henv.2 i C hi
    apply ih a ha n W h ρ (henv.refine hi ?_) hw hh
    exact ⟨a, by simp, hv⟩
  | @arrParts Γ T E ro presence parts hp hparts hr ih =>
    intro n W h ρ he hw hh
    have hterm : instantiate 0 ρ (.arrLit (parts.map fun p => spreadTerm (p.1, p.2.2)))
        = .arrLit ((parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
            instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
      simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
        instantiate_spreadTerm]
      congr 1
      apply List.map_congr_left
      intro p _
      rcases p with ⟨_ | _, A, t⟩ <;> rfl
    rw [hterm]
    apply RestCalls.store_parts_safe (meaning_adm G E) (meaning_valOnly G E) _ n W h
      (by
        intro q hq S hS
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
        rcases p with ⟨_ | _, A, t⟩
        · simp at hS
        · simp only [if_true, Option.some.injEq] at hS
          subst hS
          have := hparts _ hp'
          simp only [if_true] at this
          exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
      hw hh
      (by
        intro q hq j hj U hxU hu heap hok
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
        rcases p with ⟨_ | _, A, t⟩
        · have hA : A = E := by simpa using hparts _ hp'
          subst hA
          exact ih _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · exact ih _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok)
    intro j _ U _ hu heap extra hok hex
    apply Safe_mono j _ U heap _
      (fresh_store_safe ro presence (meaning_adm G E) (meaning_valOnly G E) hu hok hex)
    intro k _ V v hv
    exact (represents_back hr k V v) ⟨by simpa [tupleFams] using hv, by simp⟩
  | @callPacked effect Γ f r a F Rt A B P xs t hf hmem htP hrt hx ha hpk ihf ihrt ihx iha =>
    intro n W h ρ he hw hh
    have hfF : Safe (excOf G) (restsT (excOf G) [(meaning G Rt, (xs.map Prod.fst).map (meaning G), argMeaning G P,
        meaning G B)]) n W h (instantiate 0 ρ f) :=
      Safe_mono n (fun m _ U v hv => CallEffects.restsT_erase (restsT_of_restSigs hmem hv)) W h _
        (ihf n W h ρ he hw hh)
    have hterm : instantiate 0 ρ (.invoke f r (xs.map Prod.snd ++
          [.spread (.readAt CallArguments.arrayStoreField a)])) =
        .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
          ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
            [.spread (.readAt CallArguments.arrayStoreField (instantiate 0 ρ a))]) := by
      simp [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    rw [hterm]
    apply packed_call_safe (Rc := meaning G Rt) (Ps := (xs.map Prod.fst).map (meaning G))
      (R := meaning G B) (V := meaning G A) (P := argMeaning G P)
      (meaning_adm G Rt)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      (argMeaning_adm G P)
      (fun n W vs hvs v hv => ((graphArguments_valid G G.env _ (fun S => meaning_valueFam G S) P).2
        n W vs hvs v hv).1)
      (fun n W v hv => Packable_mono (fun m U vs ⟨i, hi, h'⟩ => ⟨i, by
        rw [List.mem_singleton] at hi; subst hi; exact htP, h'⟩) (packedBy_sound hpk hv))
      _ (by simp [List.map_map, Function.comp_def]) hw hh hfF
    · intro j hj U hxU hu heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
    · intro q hq j hj U hxU hu heap hok
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
      exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
    · intro j hj U hxU hu heap hok
      exact iha j U heap ρ (he.transfer j hj U hxU) hu hok
  | @callRest effect Γ f r F Rt xs Us P B parts hf hmem hrt hx hu hshort hp hparts
      ihf ihrt ihx ihu ihp =>
    intro n W h ρ he hw hh
    have hfF : Safe (excOf G) (restsT (excOf G) [(meaning G Rt, (xs.map Prod.fst ++ Us).map (meaning G), argMeaning G P,
        meaning G B)]) n W h (instantiate 0 ρ f) :=
      Safe_mono n (fun m _ U v hv => CallEffects.restsT_erase (restsT_of_restSigs hmem hv)) W h _ (ihf n W h ρ he hw hh)
    unfold RestParts at hparts
    split at hparts
    · -- A spread: the rest is an element rest.
      rename_i hany
      split at hparts
      · rename_i E hel
        have hUs : Us = [] := by
          rcases hshort with h | h
          · exact h
          · subst h; simp at hany
        subst hUs
        have hterm : instantiate 0 ρ (.invoke f r
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
              ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
              (parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
                instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p _
          rcases p with ⟨_ | _, A, t⟩ <;> rfl
        have hpart : ∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E :=
          fun p hp' => hparts (p.1, p.2.1) (List.mem_map_of_mem hp')
        rw [hterm]
        apply rest_call_safe (Rc := meaning G Rt) (Ps := xs.map fun p => meaning G p.1)
          (E := meaning G E) (P := argMeaning G P) (R := meaning G B)
          (meaning_adm G Rt)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q.1)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q.1)
          (meaning_adm G E) (meaning_valOnly G E) (argMeaning_adm G P)
          (fun k W xs hxs => (restElem_args hel).mpr hxs)
          _ (by simp [List.map_map, Function.comp_def]) _
          (by
            intro q hq S hS
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
            rcases p with ⟨_ | _, A, t⟩
            · simp at hS
            · simp only [if_true, Option.some.injEq] at hS
              subst hS
              have := hpart _ hp'
              simp only [if_true] at this
              exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
          hw hh (by simpa [List.map_map, Function.comp_def] using hfF)
        · intro j hj U hxU hu heap hok
          exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          rcases p with ⟨_ | _, A, t⟩
          · have hA : A = E := by simpa using hpart _ hp'
            subst hA
            exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
    · -- No spread: the parts are at the positions of the rest's tuple contract.
      rename_i hany
      split at hparts
      · rename_i T hPT
        obtain ⟨hreq, hbound, hpos⟩ := hparts
        simp only [List.any_map, List.any_eq_true, not_exists, not_and, Function.comp_def,
          Bool.not_eq_true] at hany
        have hterm : instantiate 0 ρ (.invoke f r
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
              ((xs.map (fun p => (meaning G p.1, instantiate 0 ρ p.2)) ++
                parts.map (fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))).map Prod.snd) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p hp'
          simp [spreadTerm, hany p hp']
        rw [hterm]
        apply pack_call_safe (Rc := meaning G Rt) (Ps := xs.map fun p => meaning G p.1)
          (Us := Us.map (meaning G)) (Qs := parts.map fun p => meaning G p.2.1)
          (P := argMeaning G P) (R := meaning G B)
          (meaning_adm G Rt)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_adm G _)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_valOnly G _)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
          (fun k W extra ha => restParts_pack hPT (Qs := parts.map (·.2.1))
            (by simpa using hreq) (by simpa using hbound)
            (by
              intro i hi
              have := hpos i (by simpa using hi)
              simpa [List.getElem?_map, Option.map_map, Function.comp_def] using this)
            (by simpa [List.map_map, Function.comp_def] using ha))
          _ (by simp [List.map_map, Function.comp_def])
          (by rcases hshort with h | h <;> simp [h])
          hw hh (by simpa [List.map_map, Function.comp_def] using hfF)
        · intro j hj U hxU hu heap hok
          exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          rcases List.mem_append.mp hq with hq | hq <;> obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          · exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro A hA j hj U hxU hu' heap hok
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
          exact ihu q hq j U heap ρ (he.transfer j hj U hxU) hu' hok
      · exact hparts.elim
  | @bindE effect Γ F T Rt R Rc t r saved Ps Ds ht hsig hr hpre hF =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ m =>
      have hcall := callsT_of_callSigs hsig (he.2 t T ht)
      simp only [Arrow.map, Contract.map, List.map_append] at hcall
      have hpv := ArgsT_slots he hpre
      apply make_empty_rule (meaning_adm G F) (m + 1) W h _ hw hh
      intro oid
      have hbound := CallEffects.callsT_bound (Rc := meaning G Rc) (fs := []) (oid := oid)
        (meaning_adm G Rt) (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        hcall (meaning_value (he.2 r Rt hr)).1 (he.1 r) (he.2 r Rt hr) hpv
        (ArgsT_values (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q) hpv)
        (by intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact he.1 q)
      exact (represents_back hF (m + 1) _ _) ⟨by simpa [Arrow.map, RestArrow.mapWith, Contract.map] using hbound, hbound.1, by simp⟩
  | @bindRestE effect Γ F T Rt E El R Rc t r saved Ps Qs ht hsig hel hr hpre hQs hF =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ m =>
      have hrest := restsT_of_restSigs hsig (he.2 t T ht)
      have hpv := ArgsT_slots he hpre
      subst hQs
      have hlen : (saved.map ρ).length = saved.length := List.length_map _
      have hvals := ArgsT_values (by
        intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q) hpv
      have hsplit := ArgsT_take_drop Ps.length hpv
      rw [← List.map_take, ← List.map_drop, (prefix_take_drop Ps saved.length El).1,
        (prefix_take_drop Ps saved.length El).2, List.map_replicate] at hsplit
      have hpv' : ArgsT ((Ps.map (meaning G)).take (saved.map ρ).length) (m + 1) W
          ((saved.map ρ).take (Ps.map (meaning G)).length) := by
        simpa [List.map_take, hlen] using hsplit.1
      have hext : ∀ j (hj : j ≤ m + 1) (U : WorldT j), WExt (trunc j hj W) U →
          ∀ ys, argMeaning G E j U ys →
            argMeaning G E j U ((saved.map ρ).drop (Ps.map (meaning G)).length ++ ys) := by
        intro j hj U hx ys hy
        refine mixed_restElem_append hel (fun u hu => ?_) hy
        have hu' := ArgsT_replicate_all hsplit.2 u (by simpa using hu)
        exact (meaning_adm G El).transfer hu' j hj U hx
      apply make_empty_rule (meaning_adm G F) (m + 1) W h _ hw hh
      intro oid
      have hbound := CallEffects.restsT_bound (Rc := meaning G Rc) (fs := []) (oid := oid)
        (meaning_adm G Rt) (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        (argMeaning_adm G E) hrest (meaning_value (he.2 r Rt hr)).1 (he.1 r) (he.2 r Rt hr) hpv'
        hext hvals (by intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact he.1 q)
      refine (represents_back hF (m + 1) _ _) ⟨⟨hbound.1, by simp⟩, ?_⟩
      simpa [RestArrow.mapWith, Contract.map, List.map_drop, hlen] using hbound
  | @bindMember Γ F O i k m L S hi hmo hF hL hS hR =>
    intro n W h ρ he hw hh
    obtain ⟨hkey, hmem⟩ := memberOf_at hmo (he.2 i O hi)
    have hscope : Scoped 0 (ρ i) := he.1 i
    have hvalρ : isVal (ρ i) = true := (meaning_value (he.2 i O hi)).1
    have hterm : instantiate 0 ρ
        (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) =
        .letE (.readAt k (ρ i)) (.makeAt (.bound (.var 0) (ρ i) []) [] []) := by
      simp [instantiate, instantiateArgs_eq_map]
    rw [hterm]
    have hread : Safe (excOf G) (MethodMembers.onHost (excOf G) (ρ i) (MethodMembers.Member.of (meaning G) (argMeaning G) m))
        n W h (.readAt k (ρ i)) := by
      have := member_read_safe hw hh hmem
      rwa [show (MethodMembers.Member.of (meaning G) (argMeaning G) m).key = k from hkey] at this
    apply bind (fun a => Tm.letE a (.makeAt (.bound (.var 0) (ρ i) []) [] [])) Step.letC Raises.letC
      n W h _ hw hh hread
    intro j hj U hx hu h' u hok hval hon
    cases j with
    | zero => trivial
    | succ p =>
      apply let_rule _ u hval p U h' hu hok
      have hsub : subst 0 u (.makeAt (.bound (.var 0) (ρ i) []) [] []) =
          .makeAt (.bound u (ρ i) []) [] [] := by
        simp [subst, substArgs_eq_map, subst_above hscope (Nat.zero_le 0)]
      rw [hsub]
      cases p with
      | zero => trivial
      | succ q =>
        -- The host is in each type the member's host must meet.
        have hO : meaning G O (q + 2) U (ρ i) :=
          (meaning_adm G O).mono _ _ _ hx _ ((meaning_adm G O).down_le n (q + 2) hj W _ (he.2 i O hi))
        have hhost : MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)) (q + 2) U (ρ i) := by
          refine ⟨rfl, fun T hT => ?_⟩
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hT
          obtain ⟨pr, hpr⟩ := hR t ht
          exact PositiveCertificates.acceptedUsing hpr _ U _ hO
        have hRadm : Adm (MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G))) :=
          MethodMembers.hostIn_adm _ fun A hA => by
            obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b
        apply make_empty_rule (meaning_adm G F) (q + 1) _ h' _ (WorldAdm_trunc _ hu)
          (HeapOk_trunc (q + 1) U h' hok)
        intro oid
        refine (meaning_adm G F).down_le (q + 2) (q + 1) (by omega) U _ ?_
        have hinv : Invocable (.objAt [] (.bound u (ρ i) []) oid) :=
          ⟨[], _, _, rfl, rfl, by simp only [Scoped, scopedArgs_iff]; exact ⟨hon.1.1.scoped, hscope, by simp⟩⟩
        have hcalls : CallEffects.callsT (excOf G) (L.map (Arrow.map (meaning G)))
            (q + 2) U (.objAt [] (.bound u (ρ i) []) oid) := by
          refine CallEffects.callsT_of_signatures hinv fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨c, hc, hlen, hps, ⟨pr, hpr⟩, heff⟩ := hL y hy
          have hc' := CallEffects.callsT_select hon.1 (List.mem_map_of_mem (List.mem_map_of_mem hc))
          have hle := CoveredCallUsing.params hlen hps
          have ht : CallEffects.callsT (excOf G) [⟨MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)), y.arguments.map (meaning G), meaning G y.result, y.effect⟩]
              (q + 2) U u :=
            ⟨hc'.1, fun p hp => by
              cases List.mem_singleton.mp hp
              exact (hc'.2 _ (List.mem_singleton_self _)).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
                (fun _ _ _ args ha => ArgsShort_mono hle ha)
                (fun m _ V w hw => PositiveCertificates.acceptedUsing hpr m V w hw)⟩
          exact CallEffects.callsT_bound (Ps := []) (oid := oid) hRadm (by simp)
            (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b)
            ht hvalρ hscope hhost trivial (by simp [CallArguments.Values]) (by simp)
        have hrests : CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) (q + 2) U (.objAt [] (.bound u (ρ i) []) oid) := by
          refine CallEffects.restsT_of_signatures hinv fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨c, hc, hlen, hps, ⟨pe, hpe⟩, ⟨pr, hpr⟩, heff⟩ := hS y hy
          have hc' := CallEffects.restsT_select hon.2.1 (List.mem_map_of_mem (List.mem_map_of_mem hc))
          have hle := CoveredCallUsing.params hlen hps
          have ht : CallEffects.restsT (excOf G) [⟨MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)), (y.arguments.1.map (meaning G), argMeaning G y.arguments.2),
              meaning G y.result, y.effect⟩] (q + 2) U u :=
            ⟨hc'.1, fun p hp => by
              cases List.mem_singleton.mp hp
              exact (hc'.2 _ (List.mem_singleton_self _)).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
                (fun _ _ _ args ha => ArgsRest_mono hle (fun vs hv => argsAcceptedUsing hpe _ _ vs hv) ha)
                (fun m _ V w hw => PositiveCertificates.acceptedUsing hpr m V w hw)⟩
          have hb := CallEffects.restsT_bound (Rc := meaning G y.receiver) (pre := []) (fs := []) (oid := oid)
            hRadm
            (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b)
            (argMeaning_adm G _)
            (show CallEffects.restsT (excOf G) [⟨MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)), (y.arguments.1.map (meaning G), argMeaning G y.arguments.2),
              meaning G y.result, y.effect⟩] (q + 2) U u from ht)
            hvalρ hscope hhost (by simp only [List.take_nil, List.take_zero, List.length_nil]; exact trivial)
            (fun _ _ _ _ ys hys => by simpa using hys)
            (by simp [CallArguments.Values]) (by simp)
          simpa [RestArrow.mapWith, Contract.map] using hb
        exact represents_back hF (q + 2) U _ rfl ⟨hcalls, hrests⟩
  | @bindScheme Γ F O i k m hi hmo hF _ =>
    intro n W h ρ he hw hh
    obtain ⟨hkey, hmem⟩ := memberOf_at hmo (he.2 i O hi)
    have hscope : Scoped 0 (ρ i) := he.1 i
    have hterm : instantiate 0 ρ
        (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) =
        .letE (.readAt k (ρ i)) (.makeAt (.bound (.var 0) (ρ i) []) [] []) := by
      simp [instantiate, instantiateArgs_eq_map]
    rw [hterm]
    have hread : Safe (excOf G) (MethodMembers.onHost (excOf G) (ρ i) (MethodMembers.Member.of (meaning G) (argMeaning G) m))
        n W h (.readAt k (ρ i)) := by
      have := member_read_safe hw hh hmem
      rwa [show (MethodMembers.Member.of (meaning G) (argMeaning G) m).key = k from hkey] at this
    apply bind (fun a => Tm.letE a (.makeAt (.bound (.var 0) (ρ i) []) [] [])) Step.letC Raises.letC
      n W h _ hw hh hread
    intro j hj U hx hu h' u hok hval hon
    cases j with
    | zero => trivial
    | succ p =>
      apply let_rule _ u hval p U h' hu hok
      have hsub : subst 0 u (.makeAt (.bound (.var 0) (ρ i) []) [] []) =
          .makeAt (.bound u (ρ i) []) [] [] := by
        simp [subst, substArgs_eq_map, subst_above hscope (Nat.zero_le 0)]
      rw [hsub]
      cases p with
      | zero => trivial
      | succ q =>
        -- The member bound to its host meets each of its schemes.
        apply make_empty_rule (meaning_adm G F) (q + 1) _ h' _ (WorldAdm_trunc _ hu)
          (HeapOk_trunc (q + 1) U h' hok)
        intro oid
        exact (meaning_adm G F).down_le (q + 2) (q + 1) (by omega) U _
          (hon.2.2 oid _ (List.mem_map_of_mem hF))
  | throw hA ha iha =>
    intro n W h ρ he hw hh
    apply bind Tm.throw Step.throwC Raises.throwC n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact thrown_safe _ _ _ _ ⟨v, .throwV hv (hA.sound ha'), (meaning_value ha').2, hA.exc ha'⟩
  | sub ht hc ih =>
    intro n W h ρ he hw hh
    exact Safe_mono n (fun k _ V v hv => subtyping.sound hc k V v hv)
      W h _ (ih n W h ρ he hw hh)

#print axioms bind_list
#print axioms HasTyUsing.sound
#print axioms dictCellT_of_recT
#print axioms meaning_assign_free
#print axioms tagClause_sound
#print axioms SourceValues.sound
#print axioms opResult_sound
#print axioms builtinsFree_meaning
#print axioms storeTy_sound
#print axioms allocBuiltins_sound

end Verification.ProgramTyping
