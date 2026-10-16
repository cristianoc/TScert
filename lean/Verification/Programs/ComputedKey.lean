import Verification.Programs.ObjectMerge

/-!
# Allocation at a key known only at run time

`Tm.makeKey k a` evaluates `k`, then `a`, then allocates one fresh plain
object owning one property, at the key `ToPropertyKey` gives `k`'s value
(`propertyKey`), holding `a`'s value. Its type is, for each clause of the
key's type, the object that clause's keys give (`keyedClause`): at a literal
key, the record of that one field, its keys among it; at a key of a class
(every string, every number, every symbol), the dictionary over the class,
writable at the initializer's type. A key-adding write at a key known only at
run time is the copy of the object with this allocation over it (`merge`).

The key is never one the model keeps for itself (`Unreserved`, `keyed_key`): a string
is spelled by `escapeKey`, which moves every such spelling
(`reservedSpelling_escapeKey`), a number's `ToString` begins with a digit, a
minus sign, `NaN` or `Infinity` (`numberToString_shape`), and a symbol is no
string. So the object holds no prototype and is no array, by construction.
-/
namespace Verification.ComputedKey
open PositiveNormalization PositiveGraphs PositiveRules Tower

variable {ι : Type}

/-- The keys the model keeps for itself that a dictionary's bound excludes:
the array store's and the prototype's, which no key of a class added by code
holding the object can be (`KeyBound.keeps`). -/
def modelKeys : List PropKey := [arrayStoreKey, CallArguments.protoField]

/-- The dictionary over the class `K`, writable at `A`, owning neither the
array store nor a prototype, of no other part. -/
def classDict (K : IndexKeys) (A : List ι) : Clause (List ι) :=
  .dict [] [] [] [(K, A)] [] [] [⟨false, modelKeys⟩] [(K, A)]

/-- The record of the one field `f` at `A`, owning `f` alone. -/
def oneField (f : PropKey) (A : List ι) : Clause (List ι) :=
  .refs [(f, A)] [] [] [] [] [⟨true, [f]⟩]

/-- The object an allocation at a key of clause `c`, holding a value of `A`,
is of: the one field a literal key names, or the dictionary over the class of
every key of a family. No other clause holds a key. -/
def keyedClause (c : Clause (List ι)) (A : List ι) : Option (Clause (List ι)) :=
  match c with
  | .strLit s => some (oneField (.str (escapeKey s)) A)
  | .numLit b => some (oneField (.str (numberToString b)) A)
  | .symbolLit i => some (oneField (.sym i) A)
  | .str => some (classDict .strings A)
  | .num => some (classDict .numeric A)
  | .symbol => some (classDict .symbols A)
  | _ => none

/-- **The rule's premise.** Every clause of the key's type `K` holds keys,
and the object each gives at the initializer's type `A` is a clause of the
result `R`. -/
def KeyedOk [DecidableEq ι] (G : NormalGraph ι) (K A R : List ι) : Bool :=
  G.plainTy K && (expand G K).all fun c => match keyedClause c A with
    | some d => (expand G R).contains d
    | none => false

/-! ### The key is none the model keeps for itself -/

theorem reservedSpelling_head {cs : List Char} (h : reservedSpelling cs = true) :
    cs.head? = some '[' := by
  unfold reservedSpelling at h
  split at h <;> simp_all

theorem digitLead_unreserved {cs : List Char} (h : digitLead cs = true) :
    reservedSpelling cs = false := by
  cases hr : reservedSpelling cs
  · rfl
  · have hh := reservedSpelling_head hr
    cases cs with
    | nil => simp at hh
    | cons c rest =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp [digitLead] at h

theorem numberToString_unreserved (b : UInt64) : reservedSpelling (numberToString b).toList = false := by
  rcases numberToString_shape b with h | h | h | h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · exact digitLead_unreserved h

/-- A key the model does not keep for itself: neither the prototype's nor the
array store's. -/
def Unreserved (f : PropKey) : Prop :=
  f ≠ CallArguments.protoField ∧ f ≠ CallArguments.arrayStoreField

theorem unreserved_str {s : String} (h : reservedSpelling s.toList = false) : Unreserved (.str s) := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · have hs : s = "[[proto]]" := by
      simpa [CallArguments.protoField] using he
    subst hs; exact absurd h (by decide)
  · have hs : s = "[]" := by
      simpa [CallArguments.arrayStoreField, arrayStoreKey] using he
    subst hs; exact absurd h (by decide)

theorem unreserved_sym (i : Nat) : Unreserved (.sym i) := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · simp [CallArguments.protoField] at he
  · simp [CallArguments.arrayStoreField, arrayStoreKey] at he

/-- Where a value of the key's clause converts to, and that the keyed object
owns it: the one field, or a key the class admits. -/
theorem keyed_key {G : NormalGraph ι} {c d : Clause (List ι)} {A : List ι}
    (hk : keyedClause c A = some d) {n W v} (hv : semWithArgs (excOf G) (meaning G) (argMeaning G) c n W v) :
    ∃ f, propertyKey v = some f ∧ Unreserved f ∧
      (d = oneField f A ∨ ∃ K, d = classDict K A ∧ K.Admits f) := by
  match c, hk with
  | .str, hk =>
    cases hk
    obtain ⟨s, rfl⟩ := hv
    exact ⟨_, rfl, unreserved_str (reservedSpelling_escapeKey s), .inr ⟨.strings, rfl, trivial⟩⟩
  | .strLit s, hk =>
    cases hk
    simp only [semWithArgs] at hv; subst hv
    exact ⟨_, rfl, unreserved_str (reservedSpelling_escapeKey s), .inl rfl⟩
  | .num, hk =>
    cases hk
    obtain ⟨b, rfl⟩ := hv
    exact ⟨_, rfl, unreserved_str (numberToString_unreserved b),
      .inr ⟨.numeric, rfl, numeric_admits_number b⟩⟩
  | .numLit b, hk =>
    cases hk
    simp only [semWithArgs] at hv; subst hv
    exact ⟨_, rfl, unreserved_str (numberToString_unreserved b), .inl rfl⟩
  | .symbol, hk =>
    cases hk
    obtain ⟨i, rfl⟩ := hv
    exact ⟨_, rfl, unreserved_sym i, .inr ⟨.symbols, rfl, trivial⟩⟩
  | .symbolLit i, hk =>
    cases hk
    simp only [semWithArgs] at hv; subst hv
    exact ⟨_, rfl, unreserved_sym i, .inl rfl⟩

/-- **An allocation at a computed key of two values is safe at a result the
rule states.** The key converts, running no code, to a key the model does not
keep for itself; the object allocated there is of the clause the key's clause
gives. -/
theorem keyed_values_safe [DecidableEq ι] {G : NormalGraph ι} {K A R : List ι}
    (hk : KeyedOk G K A R = true) {n : Nat} {W : WorldT n} {h : Heap} {kv av : Val}
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hkv : meaning G K n W kv) (hav : meaning G A n W av) :
    Safe (excOf G) (meaning G R) n W h (.makeKey kv av) := by
  cases n with
  | zero => trivial
  | succ p =>
  simp only [KeyedOk, Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨hpK, hall⟩ := hk
  obtain ⟨c, hc, hcv, -⟩ := (expand_sem G K hpK _ _ _).mp hkv
  have hd := hall c hc
  cases hkc : keyedClause c A with
  | none => rw [hkc] at hd; cases hd
  | some d =>
  rw [hkc] at hd
  have hdR : d ∈ expand G R := List.mem_of_elem_eq_true hd
  obtain ⟨f, hf, ⟨hnp, hns⟩, hshape⟩ := keyed_key hkc hcv
  have hadmA : Adm (meaning G A) := setSem_adm (normalDenote_adm G) _
  have hval : isVal av = true := ObjectMerge.meaning_isVal hav
  have hav' : meaning G A p (trunc p (Nat.le_succ p) W) av :=
    hadmA.down_le (p + 1) p (Nat.le_succ p) W av hav
  refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .makeAt .absent [f] [av], WExt_refl _,
    WorldAdm_trunc _ hadm, Step.makeKeyV hval hf, HeapOk_trunc p W h hok, ?_⟩
  apply make_fields_rule (As := [meaning G A]) (by simpa using hadmA)
    (fun B hB => by
      rw [List.mem_singleton.mp hB]
      exact fun _ _ _ ⟨_, _, h⟩ => (normalDenote_value h).1) p _ h .absent [f] [av] (by simp) rfl rfl (by simpa using hval) (WorldAdm_trunc _ hadm)
    (HeapOk_trunc p W h hok) (by simpa using hav')
  intro j hj U hx hrec
  have hown : ∀ g l, (slots h.length [f]).lookup g = some l → ∃ T, (g, T) ∈ [f].zip [meaning G A] := by
    intro g l hl
    have := slots_lookup_mem hl
    simp only [List.mem_singleton] at this
    subst this
    exact ⟨meaning G A, by simp⟩
  have hproto := slots_lookup_none (base := h.length) (ns := [f]) (f := CallArguments.protoField)
    (by simp only [List.mem_singleton]; exact fun he => hnp he.symm)
  have hstore := slots_lookup_none (base := h.length) (ns := [f]) (f := CallArguments.arrayStoreField)
    (by simp only [List.mem_singleton]; exact fun he => hns he.symm)
  refine (expand_sem G R (plain_of_mem_expand hdR) j U _).mpr
    ⟨d, hdR, ?_, builtinInvariant_of_lookup hstore⟩
  rcases hshape with rfl | ⟨K, rfl, hKf⟩
  · simp only [oneField, semWithArgs]
    refine ⟨⟨by simpa [ReferenceConjunctions.famsOf] using hrec, by simp⟩,
      fun g T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      by simpa using optT_nil, MethodMembers.methodT_nil _ _ _,
      fun B hB => ?_⟩
    simp only [List.mem_singleton] at hB
    subst hB
    exact ownKeysT_slots fun g hg => by simp_all [KeyBound.admits]
  · have hcell : dictCellT K (meaning G A) j U (.objAt (slots h.length [f]) .absent (h.length + 1)) :=
      dictCellT_of_recT hrec hown hproto fun g T hT _ => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton, Prod.mk.injEq] at hT
        obtain ⟨-, rfl⟩ := hT
        exact fun _ _ _ _ => Iff.rfl
    simp only [classDict, semWithArgs]
    refine ⟨⟨⟨_, _, rfl, fun g T hm => by simp [ReferenceConjunctions.famsOf] at hm⟩, by simp⟩,
      fun g T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      ⟨fun y hy => ?_, fun y hy => ?_⟩, by simpa using optT_nil, MethodMembers.methodT_nil _ _ _,
      fun B hB => ?_⟩
    · simp only [List.mem_singleton] at hy; subst hy; exact dictCellT_view hcell
    · simp only [List.mem_singleton] at hy; subst hy; exact hcell
    · simp only [List.mem_singleton] at hB
      subst hB
      refine ownKeysT_slots fun g hg => ?_
      simp only [List.mem_singleton] at hg
      subst hg
      have h1 : g ≠ arrayStoreKey := hns
      have h2 : g ≠ CallArguments.protoField := hnp
      simp [KeyBound.admits, modelKeys, h1, h2]

#print axioms keyed_values_safe

end Verification.ComputedKey
