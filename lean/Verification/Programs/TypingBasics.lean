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

/-- The roles a typed allocation or write gives contents: a storage
position's tag (`StorageRole`), or an element of a store, whose cell is an
element cell (E). -/
inductive PayloadRole where
  | stored (s : StorageRole)
  | element
  deriving DecidableEq, Repr

/-- **The sort of a role's contents** (the Tolerant frames note, §2): a
field, a cell and an element hold source values, a store slot a store. -/
def PayloadRole.sort : PayloadRole → ValueSort
  | .stored .field | .stored .cell | .element => .source
  | .stored .arrayStore | .stored .viewStore => .store

/-- **Payload compatibility**: `Payload(F|C|E, A) ⟺ A ⊆ V`,
`Payload(S, A) ⟺ A ⊆ S`, the category checked by `tyIn`. -/
def Payload (G : NormalGraph ι) (r : PayloadRole) (A : Ty ι) : Prop := tyIn G r.sort A = true

instance (G : NormalGraph ι) (r : PayloadRole) (A : Ty ι) : Decidable (Payload G r A) := by
  unfold Payload; infer_instance

/-- A compatible payload's values are of its role's sort. -/
theorem Payload.sound {G : NormalGraph ι} {r : PayloadRole} {A : Ty ι} (h : Payload G r A)
    {n W v} (hv : meaning G A n W v) : r.sort.Holds v :=
  tyIn_sound (G.sorted G.env) h hv

/-- **A stored payload's values meet its tag's category** (`StorageRole.Holds`),
from which an allocation's concrete role follows. -/
theorem Payload.stored {G : NormalGraph ι} {s : StorageRole} {A : Ty ι} (h : Payload G (.stored s) A)
    {n W v} (hv : meaning G A n W v) : s.Holds v := by
  have := h.sound hv
  cases s <;> simp_all [PayloadRole.sort, PositiveNormalization.ValueSort.Holds, StorageRole.Holds]

/-- **An element payload's values are an element cell's contents** (`Cat .elem`). -/
theorem Payload.element {G : NormalGraph ι} {A : Ty ι} (h : Payload G .element A)
    {n W v} (hv : meaning G A n W v) : Cat .elem v :=
  (h.sound hv).1

/-- A type's category reads no assignment. -/
theorem tyIn_reassign {G : NormalGraph ι} (η : MixedAssignment ι) {q : ValueSort} {A : Ty ι} :
    tyIn (reassign G η) q A = tyIn G q A := rfl

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

/-- The parts of an allocation whose keys a list of stable keys names
(`b = true`), which the clause it meets states as views, or leaves
(`b = false`), its contract fields (POSITIVE-TYPES.md, "Records"). -/
def stablePart {α : Type} (st : List PropKey) (b : Bool) (ps : List (PropKey × α)) : List (PropKey × α) :=
  ps.filter fun p => st.contains p.1 == b

@[simp] theorem stablePart_nil_false {α : Type} (ps : List (PropKey × α)) : stablePart [] false ps = ps := by
  simp [stablePart]

@[simp] theorem stablePart_nil_true {α : Type} (ps : List (PropKey × α)) : stablePart [] true ps = [] := by
  simp [stablePart]

/-- The family a stable field's location is allocated with: its contract's
values that are the value it is initialized with. -/
def singleT (A : Fam) (v : Val) : Fam := fun j W u => A j W u ∧ u = v

theorem singleT_adm {A : Fam} (hA : Adm A) (v : Val) : Adm (singleT A v) :=
  ⟨fun n W u h => ⟨hA.down n W u h.1, h.2⟩, fun n W W' hx u h => ⟨hA.mono n W W' hx u h.1, h.2⟩⟩

theorem singleT_valOnly {A : Fam} (hA : ValOnly A) (v : Val) : ValOnly (singleT A v) :=
  fun j W a h => hA j W a h.1

/-- A part of a list is at some position of a list of its length. -/
theorem exists_mem_zip_left {α β : Type} : ∀ {l : List α} {m : List β} {a : α},
    l.length = m.length → a ∈ l → ∃ b, (a, b) ∈ l.zip m
  | [], _, _, _, h => by cases h
  | _ :: _, [], _, hl, _ => by simp at hl
  | x :: l, y :: m, a, hl, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := exists_mem_zip_left (by simpa using hl) h
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- A pair of a zip, its first component mapped, beside a function of the
pair, is a pair of the zip of the mapped list with the mapped zip. -/
theorem mem_zip_map_zip {α β γ δ : Type} (f : α → γ) (g : α × β → δ) : ∀ {l : List α} {m : List β} {q : α × β},
    q ∈ l.zip m → (f q.1, g q) ∈ (l.map f).zip ((l.zip m).map g)
  | [], _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: l, y :: m, q, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_zip_map_zip f g h)

/-- Zipping a mapped zip with its second list pairs each image with its
second component. -/
theorem zip_map_zip_snd {α β δ : Type} (g : α × β → δ) : ∀ {l : List α} {m : List β},
    l.length = m.length → ((l.zip m).map g).zip m = (l.zip m).map fun q => (g q, q.2)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, y :: m, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact zip_map_zip_snd g (by simpa using h)

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

/-- The role a claim's storage positions give a key's location: its position's
role, `field` for a key no position of the claim names (a stable key, which
the claim reads as a view). -/
def allocRole {α : Type} (fs : List (Stored α)) (k : PropKey) : StorageRole :=
  ((fs.find? (·.1 == k)).map (·.2.1)).getD .field

theorem allocBuiltins_sound [DecidableEq ι] {G : NormalGraph ι} {parts : List (PropKey × Ty ι)}
    {r : PropKey → StorageRole}
    (hok : allocBuiltins G parts = true) (_hnd : (parts.map Prod.fst).Nodup) (c : Clause (Ty ι))
    {k : Nat} {V : WorldT k} {base : Nat}
    (hrec : recT ((parts.map Prod.fst).zip (parts.map fun p => (r p.1, meaning G p.2))) k V
      (.objAt (slots base (parts.map Prod.fst)) .absent oid)) :
    builtinInvariant G (builtinValues G) c k V (.objAt (slots base (parts.map Prod.fst)) .absent oid) := by
  have hmem : ∀ p ∈ parts, (p.1, r p.1, meaning G p.2) ∈
      (parts.map Prod.fst).zip (parts.map fun p => (r p.1, meaning G p.2)) := by
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
  · have h := CallEffects.Effect.below_promise h
    simp only [CallEffects.Effect.promiseBelow, decide_eq_true_eq] at h
    have hlen : q.param < (CallArguments.parameters arity args ++ vs).length := by
      have := CallEffects.Effect.parameters_length arity args
      simp [this]; omega
    simp only [framePromised, envOf, CallEffects.Effect.promised, List.append_assoc,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlen, Option.getD_some]

/-- The precondition a signature states of the call's values, read at a
frame: code collecting no rest finds the receiver and its parameters at the
call's positions (`CallEffects.Effect.pre_frame`); code collecting one
assumes none. -/
def PreAt (e : CallEffects.Effect) (store : Option (Ty ι)) (L : List Tm) (h : Heap) : Prop :=
  store = none → ∀ F ∈ e.pre, F.HoldsAt ⟨envOf L .nul, h⟩ (envOf L .nul) h

/-- The receiver and bound parameters of a call occur in its entry frame,
following the optional rest store and preceding the captures. Actuals past
`arity` have no parameter slot. -/
@[nospecialize] def FrameValues (arity : Nat) (store : Option (Ty ι)) (L : List Tm)
    (r : Tm) (args : List Tm) : Prop :=
  ∃ pre captures, pre.length = frameOffset store - 1 ∧
    L = pre ++ r :: CallArguments.parameters arity args ++ captures

/-- **Graph code at a signature.** Code of `arity` whose body is the graph of
the node lists `E`, `K`, entered at `start`, with captures at `Cs`, meets the
signature `row` when every run of it started from an environment meeting the
frame the row describes (`codeFrame`: with a rest, its store at `store`) is
safe at the row's result, a promise's about the parameter it names. Its effect
is guaranteed at the receiver and actuals matching that frame (`FrameValues`).
The graph
checker establishes this (`GraphCode.goto_safe`); a code-creating rule takes
it as a premise. -/
def GraphCodeSpec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : Arrow (Ty ι)) (store : Option (Ty ι) := none) : Prop :=
  arity ≤ row.arguments.length ∧ row.effect.below arity = true ∧
  ∀ n W h L, EnvOk G (codeFrame arity row Cs store) (envOf L .nul) n W → WorldAdm W →
    HeapOk n W h → RefsOk W (.goto E K start L .nul) → CallArguments.Values L → PreAt row.effect store L h →
    ∀ r args, FrameValues arity store L r args →
      HeapObservations.SafePostExc (excOf G)
        (row.effect.result (meaning G row.result) (framePromised row.effect (frameOffset store) L))
        (row.effect.post r args h) (row.effect.excPost r args h)
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

/-- The captures' frame with the invoked object after them, its self entry:
the captures' slots keep their values, and the code's types state none past
them. -/
theorem EnvOk.withSelf {G : NormalGraph ι} {Cs : List (Ty ι)} {vs : List Tm} {n W x}
    (h : EnvOk G Cs (envOf vs .nul) n W) (hlen : Cs.length ≤ vs.length) (hx : Scoped 0 x) :
    EnvOk G Cs (envOf (vs ++ [x]) .nul) n W := by
  refine ⟨fun i => ?_, fun i A hA => ?_⟩
  · show Scoped 0 ((vs ++ [x]).getD i .nul)
    rcases getD_mem_or (vs ++ [x]) i .nul with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨k, hk⟩ := List.getElem_of_mem hm
        have := h.1 k
        simp only [envOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk.1, Option.getD_some, hk.2] at this
        exact this
      · rw [List.mem_singleton.mp hm]; exact hx
    · rw [hm]; trivial
  · have hi : i < Cs.length := (List.getElem?_eq_some_iff.mp hA).1
    have := h.2 i A hA
    show meaning G A n W ((vs ++ [x]).getD i .nul)
    have hv : i < vs.length := by omega
    simpa [envOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hv] using this

/-- The captures' frame extended by the self entry at its type. -/
theorem EnvOk.withSelfAt {G : NormalGraph ι} {Cs : List (Ty ι)} {vs : List Tm} {n W x} {F : Ty ι}
    (h : EnvOk G Cs (envOf vs .nul) n W) (hlen : Cs.length = vs.length) (hx : Scoped 0 x)
    (hF : meaning G F n W x) : EnvOk G (Cs ++ [F]) (envOf (vs ++ [x]) .nul) n W := by
  have h' := h.withSelf (Nat.le_of_eq hlen) hx
  refine ⟨h'.1, fun i A hA => ?_⟩
  rw [List.getElem?_append] at hA
  split at hA
  · exact h'.2 i A hA
  · rename_i hi
    have hlt := (List.getElem?_eq_some_iff.mp hA).1
    simp only [List.length_singleton] at hlt
    have hiv : i = vs.length := by omega
    subst hiv
    rw [← hlen, Nat.sub_self] at hA
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
    subst hA
    show meaning G F n W ((vs ++ [x]).getD vs.length .nul)
    simpa using hF

theorem Values.withSelf {vs : List Tm} {x : Tm} (h : CallArguments.Values vs) (hx : isVal x = true) :
    CallArguments.Values (vs ++ [x]) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h v hv
  · rw [List.mem_singleton.mp hv]; exact hx

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

/-- **Graph code's node expressions and captures** are among its object's
references. -/
theorem graph_code_refs {k : Nat} {U : WorldT k} {fs : List (PropKey × Nat)} {arity : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start : Nat} {caps : List Tm}
    {kind : Invoke} {rest : Bool} {oid : Nat}
    (hc : RefsOk U (.objAt fs (.graph arity E K start caps kind rest) oid)) :
    (∀ e ∈ E, RefsOk U e) ∧ ∀ a ∈ caps, RefsOk U a :=
  ⟨fun e he x hx =>
    hc x (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr (.inl ⟨e, he, hx⟩)),
   fun a ha x hx =>
    hc x (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr (.inr ⟨a, ha, hx⟩))⟩

/-- **A graph run's entry refers to what its call does**: the code's node
expressions, the receiver, the bound parameters (actuals or `undefined`) and
the frame's further values. -/
theorem goto_entry_refs {k : Nat} {U : WorldT k} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {start arity : Nat} {vs : List Tm}
    {r : Tm} {args : List Tm} (hE : ∀ e ∈ E, RefsOk U e) (hvs : ∀ a ∈ vs, RefsOk U a) (hr : RefsOk U r)
    (ha : ∀ a ∈ args, RefsOk U a) :
    RefsOk U (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) := by
  intro x hx
  simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (⟨e, he, hxe⟩ | ⟨a, hal, hxa⟩) | hx
  · exact hE e he x hxe
  · rcases hal with hal | hal
    · rcases List.mem_cons.mp hal with rfl | hal
      · exact hr x hxa
      · rcases Kinds.parameters_mem hal with hal | rfl
        · exact ha a hal x hxa
        · simp [refs] at hxa
    · exact hvs a hal x hxa
  · simp at hx

/-- **Invoking graph code.** A call with a receiver and an admitted list runs
the code from the frame its signature describes: the actuals it takes, padded
with `undefined`, then the captures. -/
theorem graph_invoke {G : NormalGraph ι} {arity E K start Cs row vs n W}
    (hs : GraphCodeSpec G arity E K start Cs row) (hvs : EnvOk G Cs (envOf vs .nul) n W) (hvalues : CallArguments.Values vs)
    {j : Nat} (hj : j < n) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args)
    (hq : ∀ F ∈ row.effect.pre, F.HoldsAt ⟨CallEffects.callEnv r args, heap⟩ (CallEffects.callEnv r args) heap)
    (hgo : RefsOk U (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul)) :
    HeapObservations.SafePostExc (excOf G) (row.effect.result (meaning G row.result) (row.effect.promised args))
      (row.effect.post r args heap) (row.effect.excPost r args heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) := by
  have hsafe := hs.2.2 j U heap _ (frame_envOk hs.1 hvs (Nat.le_of_lt hj) hx hr ha) hu hh hgo (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (meaning_value hr).1
    · rcases List.mem_append.mp hv with hv | hv
      · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl
          (ArgsT_values (fun A hA => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hA); exact meaning_valOnly G a) ha.2.1) v hv
      · exact hvalues v hv)
    (fun _ F hF => (CallEffects.Effect.pre_frame hs.2.1 hF r args vs .nul heap).mp (hq F hF))
    r args ⟨[], vs, rfl, rfl⟩
  have hp := framePromised_params hs.2.1 [r] args vs
  simp only [List.length_singleton, List.singleton_append] at hp
  rw [show frameOffset (none : Option (Ty ι)) = 1 from rfl, hp] at hsafe
  exact hsafe

/-- **Invoking graph code from a frame at the call's own level.** As
`graph_invoke`, with the captures' frame met where the call runs: what a
recursive closure needs, its self entry meeting its type only below the level
its creation is proved at. -/
theorem graph_invoke_at {G : NormalGraph ι} {arity E K start Cs row vs}
    (hs : GraphCodeSpec G arity E K start Cs row) {j : Nat} {U : WorldT j}
    (hvs : EnvOk G Cs (envOf vs .nul) j U) (hvalues : CallArguments.Values vs)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args)
    (hq : ∀ F ∈ row.effect.pre, F.HoldsAt ⟨CallEffects.callEnv r args, heap⟩ (CallEffects.callEnv r args) heap)
    (hgo : RefsOk U (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul)) :
    HeapObservations.SafePostExc (excOf G) (row.effect.result (meaning G row.result) (row.effect.promised args))
      (row.effect.post r args heap) (row.effect.excPost r args heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) := by
  have hx : WExt (trunc j (Nat.le_refl j) U) U := by rw [trunc_id]; exact WExt_refl U
  have hsafe := hs.2.2 j U heap _ (frame_envOk hs.1 hvs (Nat.le_refl j) hx hr ha) hu hh hgo (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (meaning_value hr).1
    · rcases List.mem_append.mp hv with hv | hv
      · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl
          (ArgsT_values (fun A hA => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hA); exact meaning_valOnly G a) ha.2.1) v hv
      · exact hvalues v hv)
    (fun _ F hF => (CallEffects.Effect.pre_frame hs.2.1 hF r args vs .nul heap).mp (hq F hF))
    r args ⟨[], vs, rfl, rfl⟩
  have hp := framePromised_params hs.2.1 [r] args vs
  simp only [List.length_singleton, List.singleton_append] at hp
  rw [show frameOffset (none : Option (Ty ι)) = 1 from rfl, hp] at hsafe
  exact hsafe

/-- Graph code with captured values meets its fixed signatures, where its
kind binds each signature's receivers. -/
theorem callsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {kind : Invoke}
    {L : List (Arrow (Ty ι))} (fs : List (PropKey × Nat)) (hk : kind ≠ .construct)
    (hb : ∀ p ∈ L, KindBinds G kind p.receiver)
    (hs : ∀ p ∈ L, GraphCodeSpec G arity E K start Cs p) (hvs : EnvOk G Cs (envOf vs .nul) n W)
    (hlen : Cs.length ≤ vs.length)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.callsT (excOf G) (L.map (Arrow.map (meaning G))) n W
      (.objAt fs (.graph arity E K start vs kind) oid) := by
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind) oid) := by simpa [Scoped] using hsc
  refine ⟨⟨fs, _, _, rfl, callable_of_kind hk, hself⟩, ?_⟩
  intro q hq j hj U hx hu heap hh hvr r hrv hr hrr args hvals har ha hreq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  -- Graph code states no element write (`Effect.below_write`): its view
  -- write is vacuous, and its postcondition is its heap postcondition.
  exact ⟨_, .graph hrv hvals (hb p hp j U r hr), HeapObservations.SafePostExcW.weaken
    (fun _ _ _ _ h => CallEffects.Effect.postW_of_post (CallEffects.Effect.below_write (hs p hp).2.1) h)
    (fun _ _ _ h => h) (graph_invoke (hs p hp) (hvs.withSelf hlen hself)
    (Values.withSelf hvalues rfl) hj hx hu hh hr ha (fun F hF => hreq.2 F hF)
    (goto_entry_refs (graph_code_refs hvr).1 (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact (graph_code_refs hvr).2 a ha
      · rw [List.mem_singleton.mp ha]; exact hvr) hrr har))⟩

/-- Graph code of fixed arity meets a variadic signature whose fixed
parameters cover it and whose fixed part it meets: the further actuals are
discarded. -/
theorem restsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {kind : Invoke}
    {S : List (RestArrow (Ty ι))} (fs : List (PropKey × Nat)) (hk : kind ≠ .construct)
    (hb : ∀ s ∈ S, KindBinds G kind s.receiver)
    (hs : ∀ s ∈ S, GraphCodeSpec G arity E K start Cs s.fixed)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hlen : Cs.length ≤ vs.length)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W (.objAt fs (.graph arity E K start vs kind) oid) := by
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind) oid) := by simpa [Scoped] using hsc
  refine ⟨⟨fs, _, _, rfl, callable_of_kind hk, hself⟩, ?_⟩
  intro q hq j hj U hx hu heap hh hvr r hrv hr hrr args hvals har ha hreq
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  have hspec := hs s hsm
  have hle : arity ≤ s.arguments.1.length := hspec.1
  have hbelow : s.fixed.effect.below arity = true := hspec.2.1
  have hsafe := graph_invoke hspec (hvs.withSelf hlen hself) (Values.withSelf hvalues rfl) hj hx hu hh
    (args := args.take s.arguments.1.length) hr
    (by simpa [RestArrow.mapWith, Contract.map, RestArrow.fixed] using ha.1)
    (fun F hF => (CallEffects.Effect.pre_take hbelow hle hF r args heap).mpr
      (hreq.2 F (by simpa [RestArrow.mapWith, Contract.map, RestArrow.fixed] using hF)))
    (goto_entry_refs (graph_code_refs hvr).1 (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact (graph_code_refs hvr).2 a ha
      · rw [List.mem_singleton.mp ha]; exact hvr) hrr (fun a ha => har a (List.mem_of_mem_take ha)))
  have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
      CallArguments.parameters arity args := by
    rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
      Nat.min_eq_left hle, CallArguments.parameters_take]
  rw [hp, CallEffects.Effect.promised_take (e := s.fixed.effect) hbelow hle] at hsafe
  exact ⟨_, .graph hrv hvals (hb s hsm j U r hr), HeapObservations.SafePostExcW.weaken
    (fun _ _ _ _ h => CallEffects.Effect.postW_of_post (CallEffects.Effect.below_write hbelow)
      (CallEffects.Effect.post_args (CallEffects.Effect.below_ensures hbelow)
      (CallEffects.Effect.below_grows hbelow) (CallEffects.Effect.below_write hbelow) (CallEffects.Effect.below_regions hbelow) h))
      (fun _ _ _ h => CallEffects.Effect.excPost_args (CallEffects.Effect.below_regions hbelow) h) hsafe⟩

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

/-- A list context's references are its frame's and its entries'. -/
def ListCtxRefs (C : List Tm → Tm) : Prop :=
  ∀ (args : List Tm) (r : Ref), r ∈ refs (C args) ↔ r ∈ refs (C []) ∨ ∃ a ∈ args, r ∈ refs a

theorem ListCtxRefs.cons {C : List Tm → Tm} (hC : ListCtxRefs C) (v : Tm) :
    ListCtxRefs (fun args => C (v :: args)) := by
  intro args r
  simp only
  rw [hC (v :: args) r, hC [v] r]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp]
  constructor
  · rintro (h | h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨v, rfl, h⟩)
    · exact .inr h
  · rintro ((h | ⟨a, rfl, h⟩) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

theorem ListCtxRefs.ok {C : List Tm → Tm} (hC : ListCtxRefs C) {k : Nat} {W : WorldT k} {args : List Tm}
    (h0 : RefsOk W (C [])) (ha : ∀ a ∈ args, RefsOk W a) : RefsOk W (C args) := by
  intro r hr
  rcases (hC args r).mp hr with hr | ⟨a, hm, hr⟩
  · exact h0 r hr
  · exact ha a hm r hr

theorem ListCtxRefs.frame {C : List Tm → Tm} (hC : ListCtxRefs C) {k : Nat} {W : WorldT k} {args : List Tm}
    (h : RefsOk W (C args)) : RefsOk W (C []) ∧ ∀ a ∈ args, RefsOk W a :=
  ⟨fun r hr => h r ((hC args r).mpr (.inl hr)), fun a ha r hr => h r ((hC args r).mpr (.inr ⟨a, ha, hr⟩))⟩

/-- Compose left-to-right argument evaluation with a continuation over the
resulting values. Earlier values retain their types across later heap
effects; the continuation receives the list's references valid. -/
theorem bind_list {B : Fam} (xs : List (Fam × Tm))
    (hA : ∀ p ∈ xs, Adm p.1) (C : List Tm → Tm)
    (lift : ∀ {h args h' args'}, CallArguments.ArgStep h args h' args' → Step h (C args) h' (C args'))
    (raise : ∀ {args v}, CallArguments.ArgRaises args v → Raises (C args) v)
    (hC : ListCtxRefs C)
    {n W heap} (hw : WorldAdm W) (hh : HeapOk n W heap) (href : RefsOk W (C (xs.map Prod.snd)))
    (ht : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2)
    (hk : ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ heap args, HeapOk j U heap → ArgsT (xs.map Prod.fst) j U args → RefsOk U (C args) →
        Safe Ξ B j U heap (C args)) :
    Safe Ξ B n W heap (C (xs.map Prod.snd)) := by
  induction xs generalizing n C heap with
  | nil =>
    exact hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap [] hh trivial href
  | cons p xs ih =>
    have hfr := hC.frame href
    apply Safe_bind (fun a => C (a :: xs.map Prod.snd)) (fun hs => lift (.head hs)) (fun hr => raise (.head hr))
      (fun t r => by
        simp only
        rw [hC (t :: _) r, hC (.undef :: _) r]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr (.inr h))
        · rintro (h | h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · simp [refs] at h
          · exact .inr (.inr h))
      n W heap p.2 hw hh
      (hC.ok hfr.1 (fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [RefsOk, refs]
        · exact hfr.2 a (List.mem_cons_of_mem _ ha)))
      (ht p (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh)
    intro j hj U hx hu heap' v hok hv ha hvr
    have hxW : ∀ {t}, RefsOk W t → RefsOk U t := fun h => RefsOk_mono hx (RefsOk_trunc _ h)
    apply ih (fun q hq => hA q (by simp [hq])) (fun args => C (v :: args))
      (fun hs => lift (.tail hv hs)) (fun hr => raise (.tail hv hr)) (hC.cons v) hu hok
      (hC.ok (hxW hfr.1) (fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hvr
        · exact hxW (hfr.2 a (List.mem_cons_of_mem _ ha))))
      (fun q hq => (ht q (by simp [hq])).transfer hj hx)
    intro k hk' V hy hv' heap'' args hok' hargs hrefs
    have hworld : WExt (trunc k (Nat.le_trans hk' hj) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc hk' hx
    apply hk k (Nat.le_trans hk' hj) V hworld hv' heap'' (v :: args) hok' _ hrefs
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
    (hu : ∀ A ∈ Us, FutureSafe Ξ A n W .undef) (href : RefsOk W (.construct f (xs.map Prod.snd))) :
    Safe Ξ B n W heap (.construct f (xs.map Prod.snd)) := by
  have hargsr := (RefsOk_construct.mp href).2
  apply Safe_bind (fun f => .construct f (xs.map Prod.snd)) Step.constructL Raises.constructL (by ctx_refs)
    n W heap f hw hh (RefsOk_construct.mpr ⟨RefsOk_undef, hargsr⟩) hf
  intro j hj U hx hw' heap' v hok hv hctor hvr
  apply bind_list xs hA (Tm.construct v) (fun hs => CallArguments.Step.constructArgs hv hs)
    (fun hr => hr.construct hv) (fun args r => by simp [refs, refsArgs_eq]) hw' hok
    (RefsOk_construct.mpr ⟨hvr, fun a ha => RefsOk_mono hx (RefsOk_trunc _ (hargsr a ha))⟩)
    (fun p hp => (ha p hp).transfer hj hx)
  intro k hk V hz hv' heap3 args hok3 hargs hrefs
  cases k with
  | zero => exact hrefs
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
    obtain ⟨hvr', har'⟩ := RefsOk_construct.mp hrefs
    obtain ⟨result, ⟨fs, c, enter, oid, rfl, hc', rfl⟩, hsafe⟩ :=
      (hc.2 _ (List.mem_singleton_self _)).erase he k (Nat.lt_succ_self k) (trunc k (Nat.le_succ k) V)
        (WExt_refl _) (WorldAdm_trunc _ hv') heap3 (HeapOk_trunc k V heap3 hok3) (RefsOk_trunc _ hvr') _ hpvals
        (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact RefsOk_trunc _ (har' a ha)
          · rw [hpad a ha]; exact RefsOk_undef)
        (ArgsT_transfer hAm hall k (Nat.le_succ k) _ (WExt_refl _))
    rw [CallArguments.construction_pad hc' _ _ hpad] at hsafe
    exact ⟨hrefs, Or.inr ⟨trunc k (Nat.le_succ k) V, heap3, _, WExt_refl _, WorldAdm_trunc _ hv',
      CallArguments.construction_step hc' hvals heap3, HeapOk_trunc k V heap3 hok3, hsafe⟩⟩

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
    (hu : ∀ A ∈ Us, FutureSafe Ξ A n W .undef) (href : RefsOk W (.invoke f r (xs.map Prod.snd))) :
    Safe Ξ B n W heap (.invoke f r (xs.map Prod.snd)) := by
  obtain ⟨-, hrr, hargsr⟩ := RefsOk_invoke.mp href
  apply Safe_bind (fun f => .invoke f r (xs.map Prod.snd)) Step.callL Raises.callL (by ctx_refs) n W heap f hw hh
    (RefsOk_invoke.mpr ⟨RefsOk_undef, hrr, hargsr⟩) hf
  intro j hj U hx hw' heap' v hok hv hfun hvr
  have hxW : ∀ {t}, RefsOk W t → RefsOk U t := fun h => RefsOk_mono hx (RefsOk_trunc _ h)
  apply Safe_bind (fun r => .invoke v r (xs.map Prod.snd)) (Step.callRecv hv) (Raises.callRecv hv) (by ctx_refs)
    j U heap' r hw' hok (RefsOk_invoke.mpr ⟨hvr, RefsOk_undef, fun a ha => hxW (hargsr a ha)⟩)
    ((hr.transfer hj hx) j (Nat.le_refl _) U (by rw [trunc_id]; exact WExt_refl _) hw' heap' hok)
  intro i hi X hy hX heap'' rv hok'' hrv hrm hrvr
  apply bind_list xs hA (Tm.invoke v rv)
    (fun hs => (CallArguments.Prepare.args hv hrv hs).step) (fun hr => hr.invoke hv hrv)
    (fun args r => by simp [refs, refsArgs_eq, or_assoc]) hX hok''
    (RefsOk_invoke.mpr ⟨RefsOk_mono hy (RefsOk_trunc _ hvr), hrvr,
      fun a ha => RefsOk_mono hy (RefsOk_trunc _ (hxW (hargsr a ha)))⟩)
    (fun p hp => ((ha p hp).transfer hj hx).transfer hi hy)
  intro k hk V hz hv' heap3 args hok3 hargs hrefs
  cases k with
  | zero => exact hrefs
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
      (ArgsT_append hargs (ArgsT_undef hundef)) hv' hok3 hrefs

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

/-- Whether a label's clauses are exactly the literal `e`. -/
def rowIs (G : NormalGraph ι) (l : ι) (e : Clause (List ι)) : Bool :=
  match G l, e with
  | [.numLit b'], .numLit b => b' == b
  | [.strLit s'], .strLit s => s' == s
  | _, _ => false

theorem rowIs_sound {G : NormalGraph ι} {l : ι} {e : Clause (List ι)} (h : rowIs G l e = true) :
    G l = [e] := by
  unfold rowIs at h
  split at h <;> simp_all

/-- The label of the graph whose row is the literal `e`, checked. -/
def elementLabel (G : NormalGraph ι) (e : Clause (List ι)) : Option ι :=
  let key : Option LitKey := match e with
    | .numLit b => some (.num b)
    | .strLit s => some (.str s)
    | _ => none
  (key.bind G.literal).filter (rowIs G · e)

theorem elementLabel_sound {G : NormalGraph ι} {e : Clause (List ι)} {l : ι}
    (h : elementLabel G e = some l) : G l = [e] := by
  unfold elementLabel at h
  exact rowIs_sound (Option.filter_eq_some_iff.mp h).2

theorem mapM_mem {f : α → Option β} : ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
    ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], ys, _, x, hx => by cases hx
  | x' :: xs, ys, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨z, hz, hfz⟩ := mapM_mem hys x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

/-- The literals a clause holds: a number's or a string's, or a tag set's. -/
def litsOf : Clause α → Option (List LitKey)
  | .numLit b => some [.num b]
  | .strLit s => some [.str s]
  | .numIn bs => some (bs.map .num)
  | .strIn ss => some (ss.map .str)
  | _ => none

/-- A literal's one value. -/
def litVal : LitKey → Val
  | .num b => .num b
  | .str s => .str s

theorem litVal_inj {x y : LitKey} (h : litVal x = litVal y) : x = y := by
  cases x <;> cases y <;> simp_all [litVal]

theorem litsOf_sem {c : Clause α} {ks : List LitKey} (h : litsOf c = some ks) {Ξ : Fam} {X : α → Fam}
    {P : α → ArgFam} {n W v} : semWithArgs Ξ X P c n W v ↔ ∃ x ∈ ks, v = litVal x := by
  cases c <;> simp [litsOf] at h <;> subst h <;> simp only [semWithArgs, List.mem_map,
    List.mem_singleton, exists_eq_left, litVal]
  · exact ⟨fun ⟨b, hb, hv⟩ => ⟨.num b, ⟨b, hb, rfl⟩, hv⟩, fun ⟨_, ⟨b, hb, rfl⟩, hv⟩ => ⟨b, hb, hv⟩⟩
  · exact ⟨fun ⟨b, hb, hv⟩ => ⟨.str b, ⟨b, hb, rfl⟩, hv⟩, fun ⟨_, ⟨b, hb, rfl⟩, hv⟩ => ⟨b, hb, hv⟩⟩

theorem litsOf_carries {c : Clause α} {ks : List LitKey} (h : litsOf c = some ks) :
    c.carriesInvariant = false := by
  cases c <;> simp [litsOf] at h <;> rfl

/-- The literals of a list of clauses, where each is `litsOf`'s. -/
def litsAll : List (Clause α) → Option (List LitKey)
  | [] => some []
  | c :: cs => do
    let ks ← litsOf c
    let rest ← litsAll cs
    pure (ks ++ rest)

theorem litsAll_sem {G : NormalGraph ι} : ∀ {cs : List (Clause (List ι))} {ks : List LitKey},
    litsAll cs = some ks → ∀ {n W v}, setSem (clauseSem G) cs n W v ↔ ∃ x ∈ ks, v = litVal x
  | [], ks, h, n, W, v => by
    simp only [litsAll, Option.some.injEq] at h
    subst h
    simp [setSem]
  | c :: cs, ks, h, n, W, v => by
    simp only [litsAll, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨k1, h1, rest, h2, rfl⟩ := h
    have ih := litsAll_sem (G := G) h2 (n := n) (W := W) (v := v)
    have hc : clauseSem G c n W v ↔ ∃ x ∈ k1, v = litVal x :=
      ⟨fun hv => (litsOf_sem h1).mp hv.1,
       fun hv => ⟨(litsOf_sem h1).mpr hv, builtinInvariant_of_withoutInvariant (litsOf_carries h1) n W v⟩⟩
    simp only [setSem, List.mem_cons, exists_eq_or_imp, List.mem_append] at ih hc ⊢
    rw [hc]
    constructor
    · rintro (⟨x, hx, rfl⟩ | hr)
      · exact ⟨x, .inl hx, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := ih.mp hr
        exact ⟨x, .inr hx, rfl⟩
    · rintro ⟨x, hx | hx, rfl⟩
      · exact .inl ⟨x, hx, rfl⟩
      · exact .inr (ih.mpr ⟨x, hx, rfl⟩)

/-- The literals a type of clause rows holds, where each of its clauses is
a literal or a tag set. -/
def fieldLits (G : NormalGraph ι) (A : Ty ι) : Option (List LitKey) :=
  if G.plainTy A then litsAll (expand G A) else none

/-- A type `fieldLits` reads means exactly its literals' values, at every
level. -/
theorem fieldLits_sem {G : NormalGraph ι} {A : Ty ι} {ks : List LitKey} (h : fieldLits G A = some ks)
    (n W v) : meaning G A n W v ↔ ∃ x ∈ ks, v = litVal x := by
  unfold fieldLits at h
  split at h
  · rename_i hp
    rw [expand_sem G A hp]
    exact litsAll_sem h
  · cases h

/-- The fields of a clause of one record operand: a record's or a
dictionary's. -/
def recordFields : Clause α → Option (List (Stored α))
  | .refs fs [] _ _ _ _ _ => some fs
  | .dict fs [] _ _ _ _ _ _ _ => some fs
  | _ => none

theorem recordFields_rec {c : Clause α} {fs : List (Stored α)} (h : recordFields c = some fs)
    {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {n W v} (hs : semWithArgs Ξ X P c n W v) :
    recT (ReferenceConjunctions.famsOf X fs) n W v := by
  match c, h with
  | .refs _ [] _ _ _ _ _, rfl => exact hs.1.1
  | .dict _ [] _ _ _ _ _ _ _, rfl => exact hs.1.1

/-- Whether a list of fields names one key at two disjoint literal sets,
the first nonempty. -/
def litClash (G : NormalGraph ι) (fs : List (Stored (Ty ι))) : Bool :=
  fs.any fun p => fs.any fun q => decide (p.1 = q.1) && match fieldLits G p.2.2, fieldLits G q.2.2 with
    | some (x :: xs), some ys => (x :: xs).all fun z => !ys.contains z
    | _, _ => false

/-- **A record clause no value meets.** One field named twice, at two
disjoint literal sets (the meet `{ k: "id" } & { k: "optional" }`): the
field's one location holds one contract, which would have to agree with
both at every lower level, so no object at a level above `0` meets it. -/
def conflicting (G : NormalGraph ι) (c : Clause (Ty ι)) : Bool :=
  match recordFields c with
  | some fs => litClash G fs
  | none => false

theorem conflicting_empty {G : NormalGraph ι} {A : Ty ι} {c : Clause (Ty ι)}
    (hc : conflicting G c = true) (hr : Represents G A c) {k W v} : ¬ meaning G A (k + 1) W v := by
  intro hv
  have hs := represents_raw hr (k + 1) W v hv
  unfold conflicting at hc
  split at hc
  · rename_i fs hfs
    have hrec := recordFields_rec hfs hs
    obtain ⟨⟨f, s, B⟩, hp, hany⟩ := List.any_eq_true.mp hc
    obtain ⟨⟨f', s', C⟩, hq, hpq⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpq
    obtain ⟨rfl, hlit⟩ := hpq
    split at hlit
    · rename_i x xs ys hx hy
      have hxy : x ∉ ys := by
        have := (List.all_eq_true.mp hlit) x List.mem_cons_self
        simpa using this
      obtain ⟨flds, l, c1, oid, rfl, hf, hl, hag⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨B, hp, rfl⟩) hrec
      obtain ⟨flds', l', c2, oid', he, hf', hl', hag'⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨C, hq, rfl⟩) hrec
      cases he
      have hll : l = l' := Option.some.inj (hf.symm.trans hf')
      subst hll
      have hcc : c1 = c2 := Option.some.inj (hl.symm.trans hl')
      subst hcc
      let W0 : WorldT 0 := trunc 0 (by omega) W
      have h1 : c1 0 (by omega) W0 (litVal x) :=
        (hag 0 (by omega) W0 (litVal x)).mpr ((fieldLits_sem hx 0 W0 _).mpr ⟨x, List.mem_cons_self, rfl⟩)
      obtain ⟨y, hy', he⟩ := (fieldLits_sem hy 0 W0 _).mp ((hag' 0 (by omega) W0 (litVal x)).mp h1)
      exact hxy (litVal_inj he ▸ hy')
    · simp at hlit
  · cases hc

/-- The labels a union eliminates into (`unionVar`): each label, a tag set
split into its elements' labels where the graph holds a label for each
(HOST-FAMILIES.md, "Tag sets"); none for a label whose one clause is
`conflicting`, which holds no value a step can still reach. -/
def labelMembers (G : NormalGraph ι) (a : ι) : List ι :=
  match G a with
  | [c] => if conflicting G c then [] else
    if c.elements.length == 1 then [a] else (c.elements.mapM (elementLabel G)).getD [a]
  | _ => [a]

def members (G : NormalGraph ι) (C : Ty ι) : Ty ι := C.flatMap (labelMembers G)

/-- A member of a union is a member of one of its members, at every level
above `0`, where a `conflicting` label holds no value. -/
theorem members_sound {G : NormalGraph ι} {C : Ty ι} {n W v} (hv : meaning G C (n + 1) W v) :
    ∃ a ∈ members G C, meaning G [a] (n + 1) W v := by
  obtain ⟨a, ha, hav⟩ := hv
  unfold members
  by_cases hconf : ∃ c, G a = [c] ∧ conflicting G c = true
  · obtain ⟨c, hrow, hc⟩ := hconf
    have hplain : G.plain a = true := NormalGraph.plain_of_clauses (c := c) (by simp [hrow])
    have hr : Represents G [a] c := by
      simp [Represents, expand, NormalGraph.plainTy, hplain, clausesOf, hrow]
    exact absurd ⟨a, by simp, hav⟩ (conflicting_empty hc hr)
  have hnc : ∀ c, G a = [c] → conflicting G c = false := fun c hrow => by
    cases h : conflicting G c
    · rfl
    · exact absurd ⟨c, hrow, h⟩ hconf
  by_cases hsplit : ∃ c ls, G a = [c] ∧ (c.elements.length == 1) = false ∧ c.elements.mapM (elementLabel G) = some ls
  · obtain ⟨c, ls, hrow, hlen, hls⟩ := hsplit
    have hplain : G.plain a = true := NormalGraph.plain_of_clauses (c := c) (by simp [hrow])
    have hpt : G.plainTy [a] = true := by simp [NormalGraph.plainTy, hplain]
    obtain ⟨c', hc', hcv⟩ := (expand_sem G [a] hpt (n + 1) W v).mp ⟨a, by simp, hav⟩
    have hcc : c' = c := by simpa [expand, hpt, clausesOf, hrow] using hc'
    subst hcc
    obtain ⟨e, he, hev⟩ := rowSem_elements G _ _ _ hcv
    obtain ⟨l, hl, hel⟩ := mapM_mem hls e he
    have hlr := elementLabel_sound hel
    have hlp : G.plain l = true :=
      NormalGraph.plain_of_clauses (c := e) (show e ∈ G l by rw [hlr]; exact List.mem_singleton_self e)
    have hlt : G.plainTy [l] = true := by simp [NormalGraph.plainTy, hlp]
    refine ⟨l, List.mem_flatMap.mpr ⟨a, ha, by simp [labelMembers, hrow, hnc c' hrow, hlen, hls, hl]⟩, ?_⟩
    exact (expand_sem G [l] hlt (n + 1) W v).mpr ⟨e, by simp [expand, hlt, clausesOf, hlr], hev⟩
  · refine ⟨a, List.mem_flatMap.mpr ⟨a, ha, ?_⟩, ⟨a, by simp, hav⟩⟩
    unfold labelMembers
    split
    · rename_i c hrow
      rw [if_neg (by simp [hnc c hrow])]
      split
      · simp
      · rename_i hlen
        cases hm : c.elements.mapM (elementLabel G) with
        | none => simp
        | some ls => exact absurd ⟨c, ls, hrow, by simpa using hlen, hm⟩ hsplit
    · simp

/-- The one answer every element gives, if they agree. -/
def uniform (bs : List Bool) : Option Bool :=
  if bs.all id then some true else if bs.all (!·) then some false else none

theorem uniform_mem {bs : List Bool} {q : Bool} (h : uniform bs = some q) {x : Bool} (hx : x ∈ bs) :
    x = q := by
  unfold uniform at h
  split at h
  · rename_i ha; cases h; simpa using List.all_eq_true.mp ha x hx
  · split at h
    · rename_i _ ha; cases h; simpa using List.all_eq_true.mp ha x hx
    · cases h

/-- A tag set answers a test where all its elements do (HOST-FAMILIES.md,
"Tag sets"). -/
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
  | .numEq bits, .numIn S => uniform (S.map fun value => numberEqual value bits)
  | .strEq s, .strIn S => uniform (S.map fun t => s == t)
  | .truthy, .numIn S => uniform (S.map numberTruthy)
  | .truthy, .strIn S => uniform (S.map fun t => t != "")
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
  case numEq.numIn bits S =>
    obtain ⟨b, hb, rfl⟩ := hv
    exact uniform_mem hq (List.mem_map.mpr ⟨b, hb, rfl⟩)
  case strEq.strIn s S =>
    obtain ⟨t, ht, rfl⟩ := hv
    exact uniform_mem hq (List.mem_map.mpr ⟨t, ht, rfl⟩)
  case truthy.numIn S =>
    obtain ⟨b, hb, rfl⟩ := hv
    exact uniform_mem hq (List.mem_map.mpr ⟨b, hb, rfl⟩)
  case truthy.strIn S =>
    obtain ⟨t, ht, rfl⟩ := hv
    exact uniform_mem hq (List.mem_map.mpr ⟨t, ht, rfl⟩)
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
    case refs a bs vs os ms ks st =>
      have hin : inAnswer k (Clause.refs a bs vs os ms ks st) = some q := by simpa [tagClause] using hq
      exact inAnswer_protoFree hin hv
    case dict a bs vs ds os ms ks cs st =>
      have hin : inAnswer k (Clause.dict a bs vs ds os ms ks cs st) = some q := by simpa [tagClause] using hq
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
