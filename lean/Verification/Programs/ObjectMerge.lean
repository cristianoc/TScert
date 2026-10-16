import Verification.Programs.CallableObjects
import Verification.Types.PositiveCertificates

/-!
# Allocation from parts

An object literal with spreads, `{ a: e, ...x, b: f }`, is a chain of merges
(`Tm.merge`) from a fresh accumulator: each copies what its source owns now
onto a fresh object (`mergeParts`). This module states what a merge's result
is known to hold, clause by clause, from what its two operands' types say
(`MergeClause`), and proves it (`merge_values_safe`).

The facts are about keys. For the source (`b`), a key is *never* copied when
it is dropped or reserved, or when a key bound excludes it and, if it could be
an array index, excludes the array store too; it is *surely* copied at a type
when the source's type names it as a field or view; and whatever is copied
under it is *within* a type when, besides, its optional field or index says so
and it cannot come from an array's store. The accumulator (`a`) is read the
same way, all its keys but the store's copied. A result field is surely there
at its type: the source's, or the accumulator's where whatever the source
copies over it is within the type. A result's optional field is within its
type on both sides, and the result then has no prototype. A result's key
bound admits every key either side may give. A result may also state an
index (`DictOk`): whatever either side gives under a key its class admits is
within its type, which both sides say through an index or their exact keys
(`classWithinA`, `Src.classWithin`).
-/
namespace Verification.ObjectMerge
open PositiveNormalization PositiveGraphs PositiveRules Tower

variable {ι : Type}

/-! ### Lookups through the copy -/

theorem lookup_append {β : Type} (xs ys : List (PropKey × β)) (k : PropKey) :
    (xs ++ ys).lookup k = (xs.lookup k).or (ys.lookup k) := by
  induction xs with
  | nil => simp [List.lookup]
  | cons p xs ih =>
    obtain ⟨g, x⟩ := p
    by_cases hk : k = g
    · subst hk; simp [List.lookup]
    · have : (k == g) = false := by simpa using hk
      simp [List.lookup, this, ih]

theorem lookup_filter_key {β : Type} (p : PropKey → Bool) (fs : List (PropKey × β)) (k : PropKey) :
    (fs.filter (fun q => p q.1)).lookup k = if p k then fs.lookup k else none := by
  induction fs with
  | nil => simp [List.lookup]
  | cons q fs ih =>
    obtain ⟨g, x⟩ := q
    by_cases hk : k = g
    · subst hk
      by_cases hp : p k <;> simp [hp, List.lookup, ih]
    · have : (k == g) = false := by simpa using hk
      by_cases hp : p g <;> simp [hp, List.lookup, this, ih]

theorem lookup_map_snd {β γ : Type} (f : β → γ) (fs : List (PropKey × β)) (k : PropKey) :
    (fs.map fun q => (q.1, f q.2)).lookup k = (fs.lookup k).map f := by
  induction fs with
  | nil => simp [List.lookup]
  | cons q fs ih =>
    obtain ⟨g, x⟩ := q
    by_cases hk : k = g
    · subst hk; simp [List.lookup]
    · have : (k == g) = false := by simpa using hk
      simp [List.lookup, this, ih]

theorem any_key_iff {β : Type} (b : List (PropKey × β)) (k : PropKey) :
    b.any (·.1 == k) = true ↔ k ∈ b.map Prod.fst := by
  simp only [List.any_eq_true, beq_iff_eq, List.mem_map]

theorem lookup_eq_none {β : Type} : ∀ {b : List (PropKey × β)} {k : PropKey},
    k ∉ b.map Prod.fst → b.lookup k = none
  | [], _, _ => rfl
  | (g, x) :: b, k, h => by
    have hg : k ≠ g := fun he => h (by simp [he])
    have : (k == g) = false := by simpa using hg
    simp only [List.lookup, this]
    exact lookup_eq_none (fun hm => h (by simp [hm]))

theorem lookup_isSome {β : Type} : ∀ {b : List (PropKey × β)} {k : PropKey},
    k ∈ b.map Prod.fst → ∃ v, b.lookup k = some v
  | [], _, h => by simp at h
  | (g, x) :: b, k, h => by
    by_cases hg : k = g
    · subst hg; exact ⟨x, by simp [List.lookup]⟩
    · have : (k == g) = false := by simpa using hg
      simp only [List.lookup, this]
      exact lookup_isSome (by simpa [hg] using h)

/-- What a merged list gives under a key: the source's, else the
accumulator's. -/
theorem lookup_mergeData (a b : List (PropKey × Tm)) (k : PropKey) :
    (mergeData a b).lookup k = (b.lookup k).or (a.lookup k) := by
  unfold mergeData
  rw [lookup_append, lookup_filter_key (fun k => !b.any (·.1 == k))]
  by_cases hk : k ∈ b.map Prod.fst
  · obtain ⟨v, hv⟩ := lookup_isSome hk
    have : b.any (·.1 == k) = true := (any_key_iff b k).mpr hk
    simp [this, hv]
  · have : b.any (·.1 == k) = false := by
      cases h : b.any (·.1 == k)
      · rfl
      · exact absurd ((any_key_iff b k).mp h) hk
    simp [this, lookup_eq_none hk]

theorem mergeData_nodup {a b : List (PropKey × Tm)} (ha : (a.map Prod.fst).Nodup)
    (hb : (b.map Prod.fst).Nodup) : ((mergeData a b).map Prod.fst).Nodup := by
  unfold mergeData
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨ha.sublist (List.Sublist.map _ List.filter_sublist), hb, ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have := (List.mem_filter.mp hp).2
  rw [Bool.not_eq_true', ← Bool.not_eq_true] at this
  exact this ((any_key_iff b p.1).mpr hy)

/-- No index key a store's copy writes is the store key: an index key is the
decimal spelling of a natural number. -/
theorem index_key_not_store (i : Nat) : PropKey.str (toString i) ≠ arrayStoreKey := by
  intro h
  have hs : toString i = "[]" := by simpa [arrayStoreKey] using h
  have hm : '[' ∈ Nat.toDigits 10 i := by
    rw [← Nat.toList_repr]
    change '[' ∈ (toString i).toList
    rw [hs]
    decide
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm
  revert this
  decide

/-- **A merge allocates no store.** The accumulator's fields are copied but its
store, and a source gives its copied keys and its elements' index keys, none
of which is the store key: an object a merge allocates is no array. -/
theorem mergeParts_store {h : List Tm} {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hp : mergeParts h d a b = some ps) : ∀ e ∈ ps, e.1 ≠ arrayStoreKey := by
  simp only [mergeParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨pa, ha, qb, hb, he⟩ := hp
  cases he
  intro e he
  rcases mem_mergeData he with he | he
  · unfold ownAll at ha
    split at ha
    · cases ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (mem_firstKeys he)
      have := (List.mem_filter.mp hr).2
      simp only [bne_iff_ne, ne_eq] at this
      exact this
    · cases ha
  · have he := (List.mem_filter.mp he).1
    unfold ownData at hb
    split at hb
    · cases hb
      rcases List.mem_append.mp (mem_firstKeys he) with he | he
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
        have := (List.mem_filter.mp hr).2
        intro hk
        change r.1 = arrayStoreKey at hk
        rw [hk] at this
        simp [arrayStoreKey, copiedKey] at this
      · unfold storeData at he
        split at he
        · split at he
          · obtain ⟨q, -, hq⟩ := List.mem_filterMap.mp he
            obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hq
            exact index_key_not_store _
          · simp at he
        · simp at he
    · cases hb
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp (mem_firstKeys he)
      exact index_key_not_store _
    all_goals first | (simp at he; done) | (cases hb; simp at he; done) | (cases hb; done)

/-- In a list naming each key once, an entry is what its key looks up. -/
theorem lookup_of_mem {β : Type} : ∀ {ps : List (PropKey × β)}, (ps.map Prod.fst).Nodup →
    ∀ {k : PropKey} {v : β}, (k, v) ∈ ps → ps.lookup k = some v
  | [], _, _, _, h => by simp at h
  | (g, x) :: ps, hnd, k, v, h => by
    rw [List.map_cons] at hnd
    rcases List.mem_cons.mp h with he | hm
    · cases he; simp [List.lookup]
    · have hg : k ≠ g := by
        intro he; subst he
        exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨(k, v), hm, rfl⟩)
      have : (k == g) = false := by simpa using hg
      simp only [List.lookup, this]
      exact lookup_of_mem (List.nodup_cons.mp hnd).2 hm

theorem mem_of_lookup {β : Type} : ∀ {ps : List (PropKey × β)} {k : PropKey} {v : β},
    ps.lookup k = some v → (k, v) ∈ ps
  | [], _, _, h => by simp [List.lookup] at h
  | (g, x) :: ps, k, v, h => by
    by_cases hk : k = g
    · subst hk; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have : (k == g) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-! ### What the copy reads from an object -/

/-- A key an array's store gives: its index, spelled in decimal. -/
def indexKey : PropKey → Bool
  | .str s => s.toList.all Char.isDigit
  | .sym _ => false

theorem indexKey_toString (n : Nat) : indexKey (.str (toString n)) = true := by
  simp only [indexKey, List.all_eq_true]
  intro c hc
  rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

/-- A store's copied entries are under index keys. -/
theorem storeData_lookup_none {h : List Tm} {fs : List (PropKey × Nat)} {k : PropKey}
    (hk : indexKey k = false ∨ fs.lookup arrayStoreKey = none) : (storeData h fs).lookup k = none := by
  unfold storeData
  rcases hk with hk | hk
  · split
    · split
      · rename_i ls _
        cases hl : (ls.zipIdx.filterMap fun p => p.1.map fun m => (PropKey.str (toString p.2), heapVal h m)).lookup k with
        | none => rfl
        | some v =>
          exfalso
          obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp (mem_of_lookup hl)
          obtain ⟨m, -, he⟩ := Option.map_eq_some_iff.mp hp
          cases he
          rw [indexKey_toString] at hk
          cases hk
      · rfl
    · rfl
  · rw [hk]; rfl

/-- What the source's copy gives under a key: its own field's value if it has
one the copy takes, else an array element. -/
theorem ownData_lookup {h : List Tm} {fs : List (PropKey × Nat)} {qs : List (PropKey × Tm)}
    {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) (k : PropKey) :
    qs.lookup k = ((if copiedKey k then fs.lookup k else none).map (heapVal h)).or
      ((storeData h fs).lookup k) := by
  simp only [ownData, Option.some.injEq] at hq
  subst hq
  rw [lookup_firstKeys, lookup_append]
  congr 1
  rw [show (fs.filter (copiedKey ·.1)).map (fun p => (p.1, heapVal h p.2))
      = (fs.filter (copiedKey ·.1)).map (fun q => (q.1, heapVal h q.2)) from rfl,
    lookup_map_snd, lookup_filter_key (fun k => copiedKey k)]

theorem ownData_nodup {h : List Tm} {v : Tm} {qs : List (PropKey × Tm)} (hq : ownData h v = some qs) :
    (qs.map Prod.fst).Nodup := by
  unfold ownData at hq
  split at hq
  · cases hq; exact firstKeys_nodup _
  · cases hq; exact firstKeys_nodup _
  all_goals (cases hq <;> simp)

theorem ownAll_lookup {h : List Tm} {fs : List (PropKey × Nat)} {ps : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fs .absent oid) = some ps) (k : PropKey) :
    ps.lookup k = (if k != arrayStoreKey then fs.lookup k else none).map (heapVal h) := by
  simp only [ownAll, Option.some.injEq] at hp
  subst hp
  rw [lookup_firstKeys, lookup_map_snd, lookup_filter_key (fun k => k != arrayStoreKey)]

theorem ownAll_nodup {h : List Tm} {v : Tm} {ps : List (PropKey × Tm)} (hp : ownAll h v = some ps) :
    (ps.map Prod.fst).Nodup := by
  unfold ownAll at hp
  split at hp
  · cases hp; exact firstKeys_nodup _
  · cases hp


/-! ### What a clause says of a merge's operand -/

variable [DecidableEq ι]

/-- `A`'s labels are among `T`'s, so every value of `A` is one of `T`. -/
def inLabels (A T : List ι) : Bool := A.all (· ∈ T)

theorem inLabels_sound {G : NormalGraph ι} {A T : List ι} (h : inLabels A T = true)
    {n : Nat} {W : WorldT n} {v : Val} (hv : meaning G A n W v) : meaning G T n W v := by
  obtain ⟨i, hi, hv⟩ := hv
  exact ⟨i, List.all_eq_true.mp h i hi |> of_decide_eq_true, hv⟩

/-- A store type whose elements are within `T`: each clause a store's, the
positions of its first tuple contract within `T`. -/
def storeIn (G : NormalGraph ι) (S T : List ι) : Bool :=
  G.plainTy S && (expand G S).all fun c => match c with
    | .list a _ => a.operands.all (inLabels · T)
    | _ => false

/-- A store of such a type is a possibly sparse store of `T`. -/
theorem storeIn_sound {G : NormalGraph ι} {S T : List ι} (h : storeIn G S T = true)
    {m : Nat} {U : WorldT m} {s : Val} (hs : meaning G S m U s) : builtinStoreT (meaning G T) m U s := by
  simp only [storeIn, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨c, hc, hv, -⟩ := (expand_sem G S h.1 m U s).mp hs
  have hl := h.2 c hc
  cases c with
  | list a bs =>
    have hin : ∀ B ∈ a.operands, inLabels B T = true := by simpa only [List.all_eq_true] using hl
    refine listT_builtinStore (fun A hA j W' u hu => ?_) hv.1
    simp only [tupleFams] at hA
    rcases hA with hA | hA | hA
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact inLabels_sound (hin B (by simp [Tuple.operands, hB])) hu
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact inLabels_sound (hin B (by simp [Tuple.operands, hB])) hu
    · obtain ⟨B, hB, he⟩ := Option.map_eq_some_iff.mp hA; subst he
      exact inLabels_sound (hin B (by simp [Tuple.operands, hB])) hu
  | _ => simp at hl

omit [DecidableEq ι] in
theorem meaning_isVal {G : NormalGraph ι} {A : List ι} {n : Nat} {W : WorldT n} {v : Val}
    (h : meaning G A n W v) : isVal v = true := by
  obtain ⟨_, _, h⟩ := h
  exact (normalDenote_value h).1

/-- Some bound excludes the key: no object under the bounds owns it. -/
def excludes (ks : List KeyBound) (k : PropKey) : Bool := ks.any fun K => !K.admits k

theorem excludes_lookup {ks : List KeyBound} {k : PropKey} (h : excludes ks k = true)
    {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    (hb : ∀ K ∈ ks, ownKeysT K n W (.objAt fs .absent oid)) : fs.lookup k = none := by
  obtain ⟨K, hK, hn⟩ := List.any_eq_true.mp h
  exact ownKeysT_lookup (hb K hK) (by simpa using hn)

/-- A string key, which an index signature speaks of. -/
def strKey : PropKey → Bool
  | .str _ => true
  | .sym _ => false

/-- The part of a plain-object clause a merge reads: its fields and views,
its optional fields, its index types (views and writable ones alike), its key
bounds, and whether it states no prototype, as an index does. -/
structure Obj (ι : Type) where
  named : List (PropKey × List ι)
  optional : List (OptionalField (List ι))
  indexes : List (IndexKeys × List ι)
  bounds : List KeyBound
  plain : Bool

def objOf : Clause (List ι) → Option (Obj ι)
  | .refs a bs vs os _ ks => some ⟨(a :: bs).flatten ++ vs.filter (·.1 != lengthKey), os, [], ks, false⟩
  | .dict a bs vs ds os _ ks cs => some ⟨(a :: bs).flatten ++ vs.filter (·.1 != lengthKey), os, ds ++ cs, ks, !(ds ++ cs).isEmpty⟩
  | _ => none

/-- A clause whose values own no enumerable property: `null`, `undefined`,
Booleans, numbers, bigints and symbols. A spread of one copies nothing. -/
def emptyClause : Clause (List ι) → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .bigint | .bigintLit _ | .symbol
  | .symbolLit _ => true
  | _ => false

/-- What the semantics of a plain-object clause gives a merge. -/
structure ObjFacts (G : NormalGraph ι) (o : Obj ι) (n : Nat) (W : WorldT n)
    (fs : List (PropKey × Nat)) : Prop where
  named : ∀ p ∈ o.named, ∃ (l : Nat) (c : Ctr n), fs.lookup p.1 = some l ∧ lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → meaning G p.2 j U u
  optional : ∀ q ∈ o.optional, ∀ l, fs.lookup q.key = some l → ∃ c : Ctr n, lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → meaning G q.type j U u
  indexes : ∀ x ∈ o.indexes, ∀ (f : PropKey) l, x.1.Admits f → fs.lookup f = some l → ∃ c : Ctr n,
    lookup W l = some c ∧ ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → meaning G x.2 j U u
  bounds : ∀ K ∈ o.bounds, ∀ oid, ownKeysT K n W (.objAt fs .absent oid)
  plain : o.plain = true → fs.lookup CallArguments.protoField = none
  /-- An array's own fields at canonical numeric keys hold what its store's
  elements do (the built-in `numericOwn`). -/
  numeric : ∀ S T, (CallArguments.arrayStoreField, S) ∈ o.named → storeIn G S T = true →
    G.builtins.isSome = true → ∀ key l, IndexKeys.numeric.Admits key → fs.lookup key = some l →
    ∃ c : Ctr n, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j + 1 < n) (U : WorldT j) (u : Val), c j (by omega) U u → meaning G T j U u

/-- An array of a builtins-checked clause holds, at its own canonical numeric
keys, what its store's elements hold. -/
theorem numeric_of_inv {G : NormalGraph ι} {c : Clause (List ι)} (hc : c.carriesInvariant = true)
    {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)} {oid : Nat}
    (hinv : builtinInvariant G (builtinValues G) c n W (.objAt fs .absent oid)) {S T : List ι}
    (hσ : ∃ (l : Nat) (c' : Ctr n), fs.lookup CallArguments.arrayStoreField = some l ∧ lookup W l = some c' ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c' j hj U u → meaning G S j U u)
    (hst : storeIn G S T = true) (hr : G.builtins.isSome = true) :
    ∀ key l, IndexKeys.numeric.Admits key → fs.lookup key = some l →
      ∃ c : Ctr n, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j + 1 < n) (U : WorldT j) (u : Val), c j (by omega) U u → meaning G T j U u := by
  intro key l hkey hl
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hr
  unfold builtinInvariant at hinv
  rw [hr'] at hinv
  simp only [hc, ite_true] at hinv
  obtain ⟨lσ, cσ, hlσ, hcσ, hagσ⟩ := hσ
  obtain ⟨-, -, ls, cs, hls, hcs, hk⟩ := hinv fs oid rfl (by simp [hlσ])
  rw [hls] at hlσ; cases hlσ
  rw [hcs] at hcσ; cases hcσ
  obtain ⟨c, hcw, hag⟩ := hk key l hkey hl
  exact ⟨c, hcw, fun j hj U u hu => hag j hj U u hu (meaning G T)
    fun U' s hs => storeIn_sound hst (hagσ (j + 1) hj U' s hs)⟩

theorem objFacts_of_sem {G : NormalGraph ι} {c : Clause (List ι)} {o : Obj ι} (ho : objOf c = some o)
    {n : Nat} {W : WorldT n} {v : Val} (hv : clauseSem G c n W v) :
    ∃ fs oid, v = .objAt fs .absent oid ∧ ObjFacts G o n W fs := by
  obtain ⟨hv, hinv⟩ := hv
  unfold objOf at ho
  split at ho
  · rename_i a bs vs os ms ks
    cases ho
    obtain ⟨hr, hw, hopt, -, hb⟩ := hv
    obtain ⟨fs, oid, rfl, -⟩ := hr.1
    refine ⟨fs, oid, rfl, ⟨fun p hp => ?_, fun q hq l hl => ?_, fun x hx => by simp at hx,
      fun K hK => ownKeysT_reid (hb K hK),
      fun hp => by simp at hp, fun S T hS hst hrl => numeric_of_inv rfl hinv (by
        obtain ⟨fs', l, c, oid', he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw _ hS
        cases he; exact ⟨l, c, hl, hc, hag⟩) hst hrl⟩⟩
    · obtain ⟨fs', l, c, oid', he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw p hp
      cases he
      exact ⟨l, c, hl, hc, hag⟩
    · obtain ⟨fs', oid', he, -, hall⟩ := hopt
      cases he
      obtain ⟨c, hc, hag⟩ := hall _ (List.mem_map_of_mem hq) l hl
      exact ⟨c, hc, fun j hj U u hu => (hag j hj U u).1 hu⟩
  · rename_i a bs vs ds os ms ks cs
    cases ho
    obtain ⟨hr, hw, ⟨hd, hcs⟩, hopt, -, hb⟩ := hv
    obtain ⟨fs, oid, rfl, -⟩ := hr.1
    have hview : ∀ x ∈ ds ++ cs, dictViewT x.1 (meaning G x.2) n W (.objAt fs .absent oid) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hd x hx
      · exact dictCellT_view (hcs x hx)
    refine ⟨fs, oid, rfl, ⟨fun p hp => ?_, fun q hq l hl => ?_, fun x hx f l hk hl => ?_,
      fun K hK => ownKeysT_reid (hb K hK),
      fun hp => ?_, fun S T hS hst hrl => numeric_of_inv rfl hinv (by
        obtain ⟨fs', l, c, oid', he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw _ hS
        cases he; exact ⟨l, c, hl, hc, hag⟩) hst hrl⟩⟩
    · obtain ⟨fs', l, c, oid', he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw p hp
      cases he
      exact ⟨l, c, hl, hc, hag⟩
    · obtain ⟨fs', oid', he, -, hall⟩ := hopt
      cases he
      obtain ⟨c, hc, hag⟩ := hall _ (List.mem_map_of_mem hq) l hl
      exact ⟨c, hc, fun j hj U u hu => (hag j hj U u).1 hu⟩
    · exact dictViewT_present (hview x hx) hk hl
    · cases hne : ds ++ cs with
      | nil => rw [hne] at hp; simp at hp
      | cons x _ => exact dictViewT_no_proto (hview x (by rw [hne]; exact List.mem_cons_self))
  · cases ho

omit [DecidableEq ι] in
theorem emptyClause_ownData {G : NormalGraph ι} {c : Clause (List ι)} (he : emptyClause c = true)
    {n : Nat} {W : WorldT n} {v : Val} (hv : clauseSem G c n W v) (h : List Tm) :
    ownData h v = some [] ∧ isVal v = true := by
  obtain ⟨hv, -⟩ := hv
  cases c <;> simp [emptyClause] at he <;> simp only [semWithArgs] at hv
  · subst hv; exact ⟨rfl, rfl⟩
  · rcases hv with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · rename_i b; subst hv; cases b <;> exact ⟨rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩


/-- The part of a function or class clause a merge's source reads: a
function's own enumerable properties are whatever was assigned to it, a
class value's its static fields, of which its type states the bag's fields,
if any, and no bound. -/
def codeOf : Clause (List ι) → Option (Obj ι)
  | .arrs _ _ => some ⟨[], [], [], [], false⟩
  | .callable a bs _ _ =>
    some ⟨(a :: bs).flatten.filter (·.1 != CallArguments.arrayStoreField), [], [], [], false⟩
  | .ctors _ _ a bs vs =>
    some ⟨((a :: bs).flatten ++ vs).filter (·.1 != CallArguments.arrayStoreField), [], [], [], false⟩
  | _ => none

/-- A bag's fields hold their contracts on the object the bag is of. -/
theorem bagFacts_of_sem {G : NormalGraph ι} {c : Clause (List ι)} {a : List (PropKey × List ι)}
    {bs : List (List (PropKey × List ι))} (hc : c.bag = some (a, bs)) {vs : List (PropKey × List ι)}
    {n : Nat} {W : WorldT n} {v : Val} (hv : semWithArgs (excOf G) (meaning G) (argMeaning G) c n W v)
    (hvs : CallableConjunctions.viewsT (ReferenceConjunctions.famsOf (meaning G) vs) n W v) :
    ∃ fs code oid, v = .objAt fs code oid ∧
      ObjFacts G ⟨((a :: bs).flatten ++ vs).filter (·.1 != CallArguments.arrayStoreField), [], [], [], false⟩
        n W fs := by
  obtain ⟨⟨fs, code, oid, rfl, -, ha⟩, hbs⟩ := bag_sem hc hv
  refine ⟨fs, code, oid, rfl, ⟨fun p hp => ?_, fun q hq => by simp at hq,
    fun x hx => by simp at hx, fun K hK => by simp at hK, fun hp => by simp at hp,
    fun S T hS => absurd (List.mem_filter.mp hS).2 (by simp)⟩⟩
  replace hp := (List.mem_filter.mp hp).1
  -- A view's field is the object's own, within the view's contract.
  by_cases hpv : p ∈ vs
  · obtain ⟨flds, code', oid', l, c, he, hl, hc, hag⟩ :=
      CallableConjunctions.views_at (ReferenceConjunctions.mem_famsOf.mpr ⟨p.2, hpv, rfl⟩) hvs
    cases he
    exact ⟨l, c, hl, hc, hag⟩
  replace hp : p ∈ (a :: bs).flatten := (List.mem_append.mp hp).resolve_right hpv
  -- The field is one of an operand's, whose bag is over the same fields.
  have hrec : ∀ B ∈ a :: bs, recT (ReferenceConjunctions.famsOf (meaning G) B) n W (.objAt fs .absent oid) := by
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ha
    · obtain ⟨fs', code', oid', he, -, hr⟩ := hbs _ (List.mem_map_of_mem hB)
      cases he
      exact hr
  obtain ⟨B, hB, hpB⟩ := List.mem_flatten.mp hp
  obtain ⟨flds, l, c, oid', he, hl, hc, hag⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨p.2, hpB, rfl⟩) (hrec B hB)
  cases he
  exact ⟨l, c, hl, hc, fun j hj U u hu => (hag j hj U u).mp hu⟩

/-- What the semantics of a function or class clause gives a merge's
source: an object with code, whose bag's fields hold their contracts. -/
theorem codeFacts_of_sem {G : NormalGraph ι} {c : Clause (List ι)} {o : Obj ι} (ho : codeOf c = some o)
    {n : Nat} {W : WorldT n} {v : Val} (hv : clauseSem G c n W v) :
    ∃ fs code oid, v = .objAt fs code oid ∧ ObjFacts G o n W fs := by
  obtain ⟨hv, -⟩ := hv
  cases c <;> simp only [codeOf, Option.some.injEq, reduceCtorEq] at ho <;> subst ho
  · obtain ⟨⟨⟨fs, code, oid, rfl, -, -⟩, -⟩, -⟩ := hv
    exact ⟨fs, code, oid, rfl, ⟨fun p hp => by simp at hp, fun q hq => by simp at hq,
      fun x hx => by simp at hx, fun K hK => by simp at hK, fun hp => by simp at hp,
      fun S T hS => by simp at hS⟩⟩
  · obtain ⟨⟨fs, code, oid, rfl, -, -⟩, -⟩ := bag_sem (P := argMeaning G) (c := .callable _ _ _ _) rfl hv
    simpa using bagFacts_of_sem (vs := []) rfl hv CallableConjunctions.views_nil
  · exact bagFacts_of_sem rfl hv hv.2.2

/-- The source side of a merge: values owning no enumerable property, a
string, which owns its code units at its indices, or an object, a plain one,
a function or a class. -/
inductive Src (ι : Type) where
  | prim
  | str
  | obj (o : Obj ι)

/-- A clause of strings. -/
def stringClause : Clause (List ι) → Bool
  | .str | .strLit _ => true
  | _ => false

def srcOf (c : Clause (List ι)) : Option (Src ι) :=
  if emptyClause c then some .prim else
  if stringClause c then some .str else
    match objOf c with
    | some o => some (.obj o)
    | none => (codeOf c).map .obj

/-- The source never gives the key: it is dropped or a reserved string key,
or a bound excludes it and, if an array could give it as an index, the store
too. A symbol key the model's copy does not take, JavaScript's takes where
the source owns it enumerable: only a bound says it never does. -/
def Src.never : Src ι → List PropKey → PropKey → Bool
  | .prim, _, _ => true
  | .str, d, k => d.contains k || !indexKey k
  | .obj o, d, k => d.contains k || (strKey k && !copiedKey k) ||
      (excludes o.bounds k && (!indexKey k || excludes o.bounds arrayStoreKey))

/-- The source surely gives the key, at a value within `T`: its type names it. -/
def Src.sure : Src ι → List PropKey → PropKey → List ι → Bool
  | .prim, _, _, _ => false
  | .str, _, _, _ => false
  | .obj o, d, k, T => !d.contains k && copiedKey k && o.named.any fun p => p.1 == k && inLabels p.2 T

/-- Whatever the source gives under the key is within `T`. -/
def Src.within : Src ι → List PropKey → PropKey → List ι → Bool
  | .prim, _, _, _ => true
  | .str, d, k, _ => (Src.str : Src ι).never d k
  | .obj o, d, k, T => (Src.obj o).never d k || (Src.obj o).sure d k T ||
      ((o.optional.any fun q => q.key == k && inLabels q.type T) ||
        (o.indexes.any fun x => x.1.surely k && inLabels x.2 T)) &&
        (!indexKey k || excludes o.bounds arrayStoreKey)

/-- The accumulator never gives the key: it is the store's, or excluded, or
the prototype of an object its index says has none. -/
def Obj.neverA (o : Obj ι) (k : PropKey) : Bool :=
  k == arrayStoreKey || excludes o.bounds k || (o.plain && k == CallArguments.protoField)

def Obj.sureA (o : Obj ι) (k : PropKey) (T : List ι) : Bool :=
  k != arrayStoreKey && o.named.any fun p => p.1 == k && inLabels p.2 T

def Obj.withinA (o : Obj ι) (k : PropKey) (T : List ι) : Bool :=
  o.neverA k || o.sureA k T ||
    (k != arrayStoreKey && ((o.optional.any fun q => q.key == k && inLabels q.type T) ||
      (o.indexes.any fun x => x.1.surely k && inLabels x.2 T)))

/-! ### What a side gives under the keys of an index class

A result with an index states what every present key its class admits holds,
so each side must say that of every such key it may give: through an index
of a class containing it, or by listing its own keys (an `among` bound) and
typing each the class may admit. -/

/-- Whatever the accumulator gives under a key the class `K` admits is within
`T`. -/
def Obj.classWithinA (o : Obj ι) (K : IndexKeys) (T : List ι) : Bool :=
  o.named.all (fun p => !K.may p.1 || inLabels p.2 T) &&
  o.optional.all (fun q => !K.may q.key || inLabels q.type T) &&
  (o.indexes.any (fun x => K.within x.1 && inLabels x.2 T) ||
   o.bounds.any fun B => B.among && B.keys.all fun x =>
     !K.may x || x == arrayStoreKey || o.named.any (·.1 == x) || o.optional.any (·.key == x))

/-- A type holding every string: one of its clauses is the string family. -/
def strIn (G : NormalGraph ι) (T : List ι) : Bool :=
  (expand G T).any fun c => match c with | .str => true | _ => false

omit [DecidableEq ι] in
theorem strIn_sound {G : NormalGraph ι} {T : List ι} (h : strIn G T = true) (n : Nat) (W : WorldT n)
    (u : String) : meaning G T n W (.str u) := by
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp h
  cases c <;> simp at hs
  exact expand_sem_mpr ⟨.str, expand_sub hc, ⟨u, rfl⟩, builtinInvariant_of_withoutInvariant rfl _ _ _⟩

/-- A type none of whose members is an array's store: every clause is a
primitive's or a plain object's. A string index at such a type rules out the
store key, `[]`, which is a string. -/
def noStore (G : NormalGraph ι) (T : List ι) : Bool :=
  G.plainTy T && (expand G T).all fun c => match c with
    | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _
    | .bigint | .bigintLit _ | .symbol | .symbolLit _ | .refs .. | .dict .. => true
    | _ => false

omit [DecidableEq ι] in
theorem noStore_sound {G : NormalGraph ι} {T : List ι} (h : noStore G T = true)
    {n : Nat} {W : WorldT n} {ls : List (Option Nat)} : ¬ meaning G T n W (.arr ls) := by
  intro hm
  simp only [noStore, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨c, hc, hs, -⟩ := (expand_sem G T h.1 _ _ _).mp hm
  have hw := h.2 c hc
  cases c with
  | nul => simp only [semWithArgs, nulT] at hs; cases hs
  | undef => simp only [semWithArgs, undefT] at hs; cases hs
  | bool => simp only [semWithArgs, boolT] at hs; rcases hs with h1 | h1 <;> cases h1
  | boolLit b => simp only [semWithArgs] at hs; cases b <;> cases hs
  | num => simp only [semWithArgs, numT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | numLit _ => simp only [semWithArgs] at hs; cases hs
  | str => simp only [semWithArgs, strT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | strLit _ => simp only [semWithArgs] at hs; cases hs
  | bigint => simp only [semWithArgs, bigintT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | bigintLit _ => simp only [semWithArgs] at hs; cases hs
  | symbol => simp only [semWithArgs, symbolT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | symbolLit _ => simp only [semWithArgs] at hs; cases hs
  | refs a bs vs os ms ks =>
    simp only [semWithArgs, ReferenceConjunctions.refsT, recT] at hs
    obtain ⟨⟨⟨_, _, h1, -⟩, -⟩, -⟩ := hs; cases h1
  | dict a bs vs ds os ms ks cs =>
    simp only [semWithArgs, ReferenceConjunctions.refsT, recT] at hs
    obtain ⟨⟨⟨_, _, h1, -⟩, -⟩, -⟩ := hs; cases h1
  | arrs L S => simp at hw
  | callable a bs L S => simp at hw
  | top | source => simp at hw
  | list a bs => simp at hw
  | ctors L S => simp at hw
  | pack a bs => simp at hw

/-- Whatever the source gives under a key the class `K` admits is within `T`.
The symbol class admits none of the string keys the model's copy gives;
JavaScript's copy also gives the source's own enumerable symbol-keyed
properties, so the source's type says what it holds there, by a symbol index
within `T` or by listing its keys, none a symbol. Otherwise the source owns no
store whose elements it would give under index keys, and each key it copies
is typed. -/
def Src.classWithinPlain (G : NormalGraph ι) : Src ι → List PropKey → IndexKeys → List ι → Bool
  | .prim, _, _, _ => true
  | .str, _, K, T => K == .symbols || strIn G T
  | .obj o, d, K, T => if K == .symbols then
    o.indexes.any (fun x => x.1 == .symbols && inLabels x.2 T) ||
      o.bounds.any (fun B => B.among && B.keys.all fun x => strKey x)
    else
    (excludes o.bounds arrayStoreKey || o.indexes.any (fun x => x.1 == .strings && noStore G x.2)) &&
    o.named.all (fun p => !K.may p.1 || d.contains p.1 || !copiedKey p.1 || inLabels p.2 T) &&
    o.optional.all (fun q => !K.may q.key || d.contains q.key || !copiedKey q.key || inLabels q.type T) &&
    (o.indexes.any (fun x => K.within x.1 && inLabels x.2 T) ||
     o.bounds.any fun B => B.among && B.keys.all fun x =>
       !K.may x || d.contains x || !copiedKey x || o.named.any (·.1 == x) || o.optional.any (·.key == x))

/-- An array source under the canonical numeric keys: its store's elements
are within `T`, and so, by the built-ins' invariant (`numericOwn`), are its own
fields there. -/
def Src.arrayRoute (G : NormalGraph ι) : Src ι → IndexKeys → List ι → Bool
  | .obj o, K, T => K == .numeric && G.builtins.isSome &&
      o.named.any fun p => p.1 == CallArguments.arrayStoreField && storeIn G p.2 T
  | _, _, _ => false

/-- Whatever the source gives under a key the class `K` admits is within `T`:
by its type's statements (`classWithinPlain`), or, under the canonical
numeric keys, as an array (`arrayRoute`). -/
def Src.classWithin (G : NormalGraph ι) (sb : Src ι) (d : List PropKey) (K : IndexKeys) (T : List ι) : Bool :=
  sb.arrayRoute G K T || sb.classWithinPlain G d K T

/-! ### The copied values are the types say -/

omit [DecidableEq ι] in
/-- A location's value, at the level below, meets what its contract implies. -/
theorem heap_contract {G : NormalGraph ι} {p : Nat} {W : WorldT (p + 1)} {h : Heap}
    (hok : HeapOk (p + 1) W h) {l : Nat} {c : Ctr (p + 1)} {A : List ι} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < p + 1) (U : WorldT j) (u : Val), c j hj U u → meaning G A j U u) :
    meaning G A p (trunc p (Nat.le_succ p) W) (heapVal h l) := by
  obtain ⟨v, hv, hmem⟩ := hok.2 l c hc
  have hA := hag p (Nat.lt_succ_self p) _ v (hmem p (Nat.lt_succ_self p))
  have : heapVal h l = v := by simp [heapVal, hv, meaning_isVal hA]
  rw [this]; exact hA

theorem heap_contract_within {G : NormalGraph ι} {p : Nat} {W : WorldT (p + 1)} {h : Heap}
    (hok : HeapOk (p + 1) W h) {l : Nat} {c : Ctr (p + 1)} {A T : List ι} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < p + 1) (U : WorldT j) (u : Val), c j hj U u → meaning G A j U u)
    (hw : inLabels A T = true) :
    meaning G T p (trunc p (Nat.le_succ p) W) (heapVal h l) :=
  inLabels_sound hw (heap_contract hok hc hag)

/-- The world a merge's values are read at: one level down. -/
abbrev below {p : Nat} (W : WorldT (p + 1)) : WorldT p := trunc p (Nat.le_succ p) W

/-- An array's element a copy reads is within what its store type's elements
are, at every level below the one after the read: the element sits one
location further than the store. -/
theorem storeData_typed {G : NormalGraph ι} {p : Nat} {W : WorldT (p + 1)} {h : Heap}
    (hok : HeapOk (p + 1) W h) {fs : List (PropKey × Nat)} {S T : List ι} {lσ : Nat} {cσ : Ctr (p + 1)}
    (hl : fs.lookup arrayStoreKey = some lσ) (hc : lookup W lσ = some cσ)
    (hag : ∀ (j : Nat) (hj : j < p + 1) (U : WorldT j) (u : Val), cσ j hj U u → meaning G S j U u)
    (hst : storeIn G S T = true) {k : PropKey} {v : Tm} (hv : (storeData h fs).lookup k = some v) :
    ∀ (j : Nat) (hj : j + 1 < p), meaning G T j (trunc j (by omega) (below W)) v := by
  intro j hj
  obtain ⟨u, hu, hmem⟩ := hok.2 lσ cσ hc
  have hs := storeIn_sound hst (hag p (Nat.lt_succ_self p) _ u (hmem p (Nat.lt_succ_self p)))
  unfold storeData at hv
  simp only [hl] at hv
  rw [hu] at hv
  obtain ⟨ls, rfl, -, -, -, -, -, hrest⟩ := hs
  simp only at hv
  obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp (mem_of_lookup hv)
  obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.mp hqe
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain ⟨i, hi⟩ : ∃ i, ls[i]? = some (some m) ∧ q.2 = i := by
    obtain ⟨x, i⟩ := q
    simp only at hm
    subst hm
    obtain ⟨hil, hie⟩ := List.mem_zipIdx' hq
    exact ⟨i, by rw [List.getElem?_eq_getElem hil, hie], rfl⟩
  obtain ⟨E, c', hE, hc', hag'⟩ := hrest i m (by simp) hi.1
  cases hE
  obtain ⟨c'', hc'', rfl⟩ := lookup_trunc_inv (Nat.le_succ p) W m c' hc'
  obtain ⟨w, hw, hmem'⟩ := hok.2 m c'' hc''
  have hT : meaning G T j (trunc j (by omega) (below W)) w := by
    have := (hag' j (by omega) (trunc j (by omega) (below W)) w).1
    apply this
    show c'' j _ (trunc j _ (trunc p _ W)) w
    rw [trunc_trunc]
    exact hmem' j (by omega)
  have : heapVal h m = w := by simp [heapVal, hw, meaning_isVal hT]
  rw [this]; exact hT

/-- The source's copy under a key, less the dropped keys. -/
theorem srcData_lookup {h : List Tm} {fs : List (PropKey × Nat)} {qs : List (PropKey × Tm)}
    {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) (d : List PropKey) (k : PropKey) :
    (qs.filter fun e => !d.contains e.1).lookup k =
      if d.contains k then none else
        ((if copiedKey k then fs.lookup k else none).map (heapVal h)).or ((storeData h fs).lookup k) := by
  rw [lookup_filter_key (fun k => !d.contains k), ownData_lookup hq]
  by_cases hd : d.contains k <;> simp []

theorem any_named {o : List (PropKey × List ι)} {k : PropKey} {T : List ι}
    (h : (o.any fun p => p.1 == k && inLabels p.2 T) = true) :
    ∃ A, (k, A) ∈ o ∧ inLabels A T = true := by
  obtain ⟨⟨g, A⟩, hm, he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨rfl, hw⟩ := he
  exact ⟨A, hm, hw⟩

theorem indexKey_of_not_copied {k : PropKey} (h : copiedKey k = false) : indexKey k = false := by
  cases k with
  | sym => rfl
  | str s =>
    simp only [copiedKey, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
    rcases h with (rfl | rfl) | rfl <;> decide

theorem src_never {G : NormalGraph ι} {o : Obj ι} {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    (hf : ObjFacts G o n W fs) {h : List Tm} {qs : List (PropKey × Tm)}
    {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) {d : List PropKey} {k : PropKey}
    (hn : (Src.obj o).never d k = true) : (qs.filter fun e => !d.contains e.1).lookup k = none := by
  rw [srcData_lookup hq]
  simp only [Src.never, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hn
  by_cases hd : d.contains k = true
  · rw [if_pos hd]
  · rw [if_neg hd]
    rcases hn with (hd' | ⟨-, hc⟩) | ⟨hx, hi⟩
    · exact absurd hd' hd
    · rw [if_neg (by simp [hc]), Option.map_none, Option.none_or]
      exact storeData_lookup_none (.inl (indexKey_of_not_copied hc))
    · have hl := excludes_lookup (oid := 0) hx (fun K hK => hf.bounds K hK 0)
      rw [show (if copiedKey k = true then fs.lookup k else none) = none by split <;> simp [hl],
        Option.map_none, Option.none_or]
      rcases hi with hi | hs
      · exact storeData_lookup_none (.inl hi)
      · exact storeData_lookup_none (.inr (excludes_lookup (oid := 0) hs (fun K hK => hf.bounds K hK 0)))

theorem src_sure {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) {d : List PropKey}
    {k : PropKey} {T : List ι} (hs : (Src.obj o).sure d k T = true) :
    ∃ v, (qs.filter fun e => !d.contains e.1).lookup k = some v ∧ meaning G T p (below W) v := by
  simp only [Src.sure, Bool.and_eq_true, Bool.not_eq_true'] at hs
  obtain ⟨⟨hd, hc⟩, hn⟩ := hs
  obtain ⟨A, hA, hw⟩ := any_named hn
  obtain ⟨l, c, hl, hcw, hag⟩ := hf.named (k, A) hA
  refine ⟨heapVal h l, ?_, heap_contract_within hok hcw hag hw⟩
  rw [srcData_lookup hq, if_neg (by simpa using hd), if_pos hc, hl]
  rfl

theorem src_within {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) {d : List PropKey}
    {k : PropKey} {T : List ι} (hs : (Src.obj o).within d k T = true) {v : Tm}
    (hv : (qs.filter fun e => !d.contains e.1).lookup k = some v) : meaning G T p (below W) v := by
  simp only [Src.within, Bool.or_eq_true, Bool.and_eq_true] at hs
  rcases hs with (hn | hsure) | ⟨hopt, hidx⟩
  · rw [src_never hf hq hn] at hv; cases hv
  · obtain ⟨v', hv', hm⟩ := src_sure hf hok hq hsure
    rw [hv] at hv'; cases hv'; exact hm
  · rw [srcData_lookup hq] at hv
    by_cases hd : d.contains k = true
    · rw [if_pos hd] at hv; cases hv
    rw [if_neg hd] at hv
    have hstore : (storeData h fs).lookup k = none := by
      simp only [Bool.not_eq_true'] at hidx
      rcases hidx with hi | hs
      · exact storeData_lookup_none (.inl hi)
      · exact storeData_lookup_none (.inr (excludes_lookup (oid := 0) hs (fun K hK => hf.bounds K hK 0)))
    rw [hstore, Option.or_none] at hv
    by_cases hc : copiedKey k = true
    · rw [if_pos hc] at hv
      cases hl : fs.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l =>
        rw [hl] at hv
        cases hv
        rcases hopt with ho | hix
        · obtain ⟨q, hqm, hqe⟩ := List.any_eq_true.mp ho
          simp only [Bool.and_eq_true, beq_iff_eq] at hqe
          obtain ⟨hk, hw⟩ := hqe
          obtain ⟨c, hcw, hag⟩ := hf.optional q hqm l (hk ▸ hl)
          exact heap_contract_within hok hcw hag hw
        · obtain ⟨x, hxm, hxe⟩ := List.any_eq_true.mp hix
          simp only [Bool.and_eq_true] at hxe
          obtain ⟨c, hcw, hag⟩ := hf.indexes x hxm k l (IndexKeys.surely_admits hxe.1) hl
          exact heap_contract_within hok hcw hag hxe.2
    · rw [if_neg hc] at hv; cases hv

/-- What the accumulator's copy gives under a key. -/
theorem acc_never {G : NormalGraph ι} {o : Obj ι} {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    (hf : ObjFacts G o n W fs) {h : List Tm} {ps : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fs .absent oid) = some ps) {k : PropKey}
    (hn : o.neverA k = true) : ps.lookup k = none := by
  rw [ownAll_lookup hp]
  simp only [Obj.neverA, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hn
  rcases hn with (rfl | hx) | ⟨hpl, rfl⟩
  · simp
  · simp [excludes_lookup (oid := 0) hx (fun K hK => hf.bounds K hK 0)]
  · simp [hf.plain hpl]

theorem acc_sure {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {ps : List (PropKey × Tm)} (hp : ownAll h (.objAt fs .absent oid) = some ps)
    {k : PropKey} {T : List ι} (hs : o.sureA k T = true) :
    ∃ v, ps.lookup k = some v ∧ meaning G T p (below W) v := by
  simp only [Obj.sureA, Bool.and_eq_true] at hs
  obtain ⟨hk, hn⟩ := hs
  obtain ⟨A, hA, hw⟩ := any_named hn
  obtain ⟨l, c, hl, hcw, hag⟩ := hf.named (k, A) hA
  refine ⟨heapVal h l, ?_, heap_contract_within hok hcw hag hw⟩
  rw [ownAll_lookup hp, if_pos hk, hl]
  rfl

theorem acc_within {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {ps : List (PropKey × Tm)} (hp : ownAll h (.objAt fs .absent oid) = some ps)
    {k : PropKey} {T : List ι} (hs : o.withinA k T = true) {v : Tm}
    (hv : ps.lookup k = some v) : meaning G T p (below W) v := by
  simp only [Obj.withinA, Bool.or_eq_true, Bool.and_eq_true] at hs
  rcases hs with (hn | hsure) | ⟨hk, hopt⟩
  · rw [acc_never hf hp hn] at hv; cases hv
  · obtain ⟨v', hv', hm⟩ := acc_sure hf hok hp hsure
    rw [hv] at hv'; cases hv'; exact hm
  · rw [ownAll_lookup hp, if_pos hk] at hv
    cases hl : fs.lookup k with
    | none => rw [hl] at hv; cases hv
    | some l =>
      rw [hl] at hv
      cases hv
      rcases hopt with ho | hix
      · obtain ⟨q, hqm, hqe⟩ := List.any_eq_true.mp ho
        simp only [Bool.and_eq_true, beq_iff_eq] at hqe
        obtain ⟨hk', hw⟩ := hqe
        obtain ⟨c, hcw, hag⟩ := hf.optional q hqm l (hk' ▸ hl)
        exact heap_contract_within hok hcw hag hw
      · obtain ⟨x, hxm, hxe⟩ := List.any_eq_true.mp hix
        simp only [Bool.and_eq_true] at hxe
        obtain ⟨c, hcw, hag⟩ := hf.indexes x hxm k l (IndexKeys.surely_admits hxe.1) hl
        exact heap_contract_within hok hcw hag hxe.2

/-- What the accumulator gives under a key its class admits, read through
`classWithinA`. -/
theorem acc_class {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {ps : List (PropKey × Tm)} (hp : ownAll h (.objAt fs .absent oid) = some ps)
    {K : IndexKeys} {T : List ι} (hc : o.classWithinA K T = true) {k : PropKey} (hk : K.Admits k)
    {v : Tm} (hv : ps.lookup k = some v) : meaning G T p (below W) v := by
  have hmay := IndexKeys.may_of_admits hk
  rw [ownAll_lookup hp] at hv
  by_cases hs : (k != arrayStoreKey) = true
  · rw [if_pos hs] at hv
    cases hl : fs.lookup k with
    | none => rw [hl] at hv; cases hv
    | some l =>
      rw [hl] at hv; cases hv
      simp only [Obj.classWithinA, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hnamed, hopt⟩, hroute⟩ := hc
      have typed : (∃ q ∈ o.named, q.1 = k) ∨ (∃ q ∈ o.optional, q.key = k) →
          meaning G T p (below W) (heapVal h l) := by
        rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
        · obtain ⟨l', c, hl', hcw, hag⟩ := hf.named q hq
          rw [hl] at hl'; cases hl'
          have hin : inLabels q.2 T = true := by
            rcases hnamed q hq with h1 | h1
            · rw [hmay] at h1; cases h1
            · exact h1
          exact heap_contract_within hok hcw hag hin
        · obtain ⟨c, hcw, hag⟩ := hf.optional q hq l hl
          have hin : inLabels q.type T = true := by
            rcases hopt q hq with h1 | h1
            · rw [hmay] at h1; cases h1
            · exact h1
          exact heap_contract_within hok hcw hag hin
      rcases hroute with ⟨x, hx, hwithin, hlab⟩ | ⟨B, hB, hamong, hkeys⟩
      · obtain ⟨c, hcw, hag⟩ := hf.indexes x hx k l (IndexKeys.within_admits hwithin hk) hl
        exact heap_contract_within hok hcw hag hlab
      · have hadm := ownKeysT_admits (hf.bounds B hB 0) hl
        have hkB : k ∈ B.keys := by simpa [KeyBound.admits, hamong] using hadm
        rcases hkeys k hkB with ((h1 | h1) | h1) | h1
        · rw [hmay] at h1; cases h1
        · simp [h1] at hs
        · exact typed (.inl h1)
        · exact typed (.inr h1)
  · rw [if_neg hs] at hv; cases hv

/-- The store key is a string key: a string index constrains it. -/
theorem strings_admit_store : IndexKeys.strings.Admits arrayStoreKey := trivial

/-- What the source gives under a key its class admits, read through
`classWithin`. -/
theorem src_class_plain {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) {d : List PropKey}
    {K : IndexKeys} {T : List ι} (hc : (Src.obj o).classWithinPlain G d K T = true) {k : PropKey}
    (hk : K.Admits k) {v : Tm} (hv : (qs.filter fun e => !d.contains e.1).lookup k = some v) :
    meaning G T p (below W) v := by
  have hmay := IndexKeys.may_of_admits hk
  rw [srcData_lookup hq] at hv
  by_cases hd : d.contains k = true
  · rw [if_pos hd] at hv; cases hv
  rw [if_neg hd] at hv
  simp only [Src.classWithinPlain] at hc
  by_cases hsym : K = .symbols
  · subst hsym
    cases k with
    | str s => exact absurd hk (by simp [IndexKeys.Admits])
    | sym i =>
      rw [if_neg (by simp [copiedKey]), Option.map_none, Option.none_or,
        storeData_lookup_none (.inl rfl)] at hv
      cases hv
  · rw [if_neg (by simpa using hsym)] at hc
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hstore, hnamed⟩, hopt⟩, hroute⟩ := hc
    have hnone : (storeData h fs).lookup k = none := by
      rcases hstore with hx | ⟨x, hx, hstr, hns⟩
      · exact storeData_lookup_none (.inr (excludes_lookup (oid := 0) hx (fun K hK => hf.bounds K hK 0)))
      · unfold storeData
        cases hl : fs.lookup arrayStoreKey with
        | none => rfl
        | some l =>
          obtain ⟨c, hcw, hag⟩ := hf.indexes x hx arrayStoreKey l (by rw [hstr]; exact strings_admit_store) hl
          obtain ⟨u, hu, hmem⟩ := hok.2 l c hcw
          have hm := hag p (Nat.lt_succ_self p) _ u (hmem p (Nat.lt_succ_self p))
          simp only [hu]
          cases u with
          | arr ls => exact absurd hm (noStore_sound hns)
          | _ => rfl
    rw [hnone, Option.or_none] at hv
    by_cases hcp : copiedKey k = true
    · rw [if_pos hcp] at hv
      cases hl : fs.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l =>
        rw [hl] at hv; cases hv
        have hd' : d.contains k = false := by simpa using hd
        have typed : (∃ q ∈ o.named, q.1 = k) ∨ (∃ q ∈ o.optional, q.key = k) →
            meaning G T p (below W) (heapVal h l) := by
          rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · obtain ⟨l', c, hl', hcw, hag⟩ := hf.named q hq
            rw [hl] at hl'; cases hl'
            have hin : inLabels q.2 T = true := by
              rcases hnamed q hq with ((h1 | h1) | h1) | h1
              · rw [hmay] at h1; cases h1
              · rw [hd'] at h1; cases h1
              · rw [hcp] at h1; cases h1
              · exact h1
            exact heap_contract_within hok hcw hag hin
          · obtain ⟨c, hcw, hag⟩ := hf.optional q hq l hl
            have hin : inLabels q.type T = true := by
              rcases hopt q hq with ((h1 | h1) | h1) | h1
              · rw [hmay] at h1; cases h1
              · rw [hd'] at h1; cases h1
              · rw [hcp] at h1; cases h1
              · exact h1
            exact heap_contract_within hok hcw hag hin
        rcases hroute with ⟨x, hx, hwithin, hlab⟩ | ⟨B, hB, hamong, hkeys⟩
        · obtain ⟨c, hcw, hag⟩ := hf.indexes x hx k l (IndexKeys.within_admits hwithin hk) hl
          exact heap_contract_within hok hcw hag hlab
        · have hadm := ownKeysT_admits (hf.bounds B hB 0) hl
          have hkB : k ∈ B.keys := by simpa [KeyBound.admits, hamong] using hadm
          rcases hkeys k hkB with ((((h1 | h1) | h1) | h1) | h1)
          · rw [hmay] at h1; cases h1
          · rw [hd'] at h1; cases h1
          · rw [hcp] at h1; cases h1
          · exact typed (.inl h1)
          · exact typed (.inr h1)
    · rw [if_neg hcp] at hv; cases hv

/-- What the source gives under a key its class admits, at every level the
allocation it is copied into is judged at: by `classWithinPlain`, or, for an
array under the canonical numeric keys, by its store's elements and its own
fields there (`arrayRoute`, `storeData_typed`, `ObjFacts.numeric`). -/
theorem src_class {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} {cb : CallCode} (hq : ownData h (.objAt fs cb oid) = some qs) {d : List PropKey}
    {K : IndexKeys} {T : List ι} (hc : (Src.obj o).classWithin G d K T = true) {k : PropKey}
    (hk : K.Admits k) {v : Tm} (hv : (qs.filter fun e => !d.contains e.1).lookup k = some v) :
    ∀ (j : Nat) (hj : j + 1 < p), meaning G T j (trunc j (by omega) (below W)) v := by
  rcases Bool.or_eq_true_iff.mp hc with hr | hc
  · simp only [Src.arrayRoute, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hr
    obtain ⟨⟨rfl, hbuiltins⟩, ⟨σ', S⟩, hS, hσ, hst⟩ := hr
    simp only at hσ
    subst hσ
    obtain ⟨lσ, cσ, hlσ, hcσ, hagσ⟩ := hf.named _ hS
    rw [srcData_lookup hq] at hv
    split at hv
    · cases hv
    cases hown : (if copiedKey k then fs.lookup k else none) with
    | some l =>
      rw [hown] at hv
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at hv
      subst hv
      have hl : fs.lookup k = some l := by
        split at hown
        · exact hown
        · cases hown
      obtain ⟨c, hcw, hag⟩ := hf.numeric S T hS hst hbuiltins k l hk hl
      obtain ⟨u, hu, hmem⟩ := hok.2 l c hcw
      intro j hj
      have hT := hag j (by omega) _ u (hmem j (by omega))
      have : heapVal h l = u := by simp [heapVal, hu, meaning_isVal hT]
      rw [this, below, trunc_trunc]
      exact hT
    | none =>
      rw [hown, Option.map_none, Option.none_or] at hv
      exact storeData_typed hok hlσ hcσ hagσ hst hv
  · intro j hj
    exact (meaning_valueFam G T).1.down_le p j (by omega) (below W) _ (src_class_plain hf hok hq hc hk hv)

/-! ### The rule -/

/-- A result key bound follows from the operands': listing keys, the
accumulator's and the source's own keys are among them (the source owning no
store, so no index), a symbol key the source lists included, which
JavaScript's copy takes where it is enumerable; excluding keys, neither side
gives one. -/
def boundOk (oa : Obj ι) (sb : Src ι) (d : List PropKey) (K : KeyBound) : Bool :=
  if K.among then
    (oa.bounds.any fun Ka => Ka.among && Ka.keys.all fun x => x == arrayStoreKey || K.admits x) &&
    (match sb with
     | .prim => true
     | .str => false
     | .obj ob => ob.bounds.any fun Kb => Kb.among && !Kb.keys.contains arrayStoreKey &&
         Kb.keys.all fun x => (strKey x && !copiedKey x) || d.contains x || K.admits x)
  else K.keys.all fun x => oa.neverA x && sb.never d x

/-- A merge result's fields, optional fields and key bounds. Each field is
surely given within its type: by the source, or by the accumulator where
whatever the source gives is within it too. Each optional field is within its
type on both sides, and then the accumulator gives no prototype, so the
result has none. Each bound admits every key either side may give. -/
def FieldsOk (d : List PropKey) (oa : Obj ι) (sb : Src ι) (fs : List (PropKey × List ι))
    (os : List (OptionalField (List ι))) (ks : List KeyBound) : Bool :=
  decide ((fs.map Prod.fst ++ os.map (·.key)).Nodup) &&
  fs.all (fun p => sb.sure d p.1 p.2 || (oa.sureA p.1 p.2 && sb.within d p.1 p.2)) &&
  os.all (fun q => oa.withinA q.key q.type && sb.within d q.key q.type) &&
  (os.isEmpty || oa.neverA CallArguments.protoField) &&
  ks.all (boundOk oa sb d)

/-- A merge result's index: views (`ds`) and writable ones (`cs`), each at its
type, two whose classes overlap at one type. Whatever either side gives under
a key a class admits is within its type, and the accumulator gives no
prototype. A field or optional field whose key a class may admit is at a
type within that class's, and exactly it where a writable index may admit
it, whose locations hold exactly that type. -/
def DictOk (G : NormalGraph ι) (d : List PropKey) (oa : Obj ι) (sb : Src ι)
    (fs : List (PropKey × List ι)) (os : List (OptionalField (List ι)))
    (ds cs : List (IndexKeys × List ι)) : Bool :=
  !(ds ++ cs).isEmpty &&
  oa.neverA CallArguments.protoField &&
  (ds ++ cs).all (fun x => oa.classWithinA x.1 x.2 && sb.classWithin G d x.1 x.2) &&
  (ds ++ cs).all (fun x => (ds ++ cs).all fun y => !x.1.overlaps y.1 || x.2 == y.2) &&
  fs.all (fun p => cs.all (fun y => !y.1.may p.1 || p.2 == y.2) &&
    ds.all (fun y => !y.1.may p.1 || inLabels p.2 y.2)) &&
  os.all (fun q => cs.all (fun y => !y.1.may q.key || q.type == y.2) &&
    ds.all (fun y => !y.1.may q.key || inLabels q.type y.2))

/-- **A merge's result, clause by clause.** The accumulator is a plain object
and the source a plain object or a value owning no enumerable property; the
result is a record of fields and optional fields with key bounds
(`FieldsOk`), and, where both sides say what they give under an index's
keys, a dictionary (`DictOk`). A writable index lets outside code add keys,
which an own-key bound listing keys, or excluding a key of the index's class,
would deny: each bound of a result with one keeps its writable classes
(`KeyBound.keeps`). -/
def MergeClause (G : NormalGraph ι) (d : List PropKey) (ca cb cr : Clause (List ι)) : Bool :=
  match objOf ca, srcOf cb, cr with
  | some oa, some sb, .refs fs [] [] os [] ks => FieldsOk d oa sb fs os ks
  | some oa, some sb, .dict fs [] [] ds os [] ks cs =>
    FieldsOk d oa sb fs os ks && DictOk G d oa sb fs os ds cs &&
      ks.all (fun K => cs.all fun y => K.keeps y.1)
  | _, _, _ => false

/-- Every pair of the operands' clauses merges into a clause of the result. -/
def MergeOk (G : NormalGraph ι) (d : List PropKey) (A B R : List ι) : Bool :=
  G.plainTy A && G.plainTy B &&
    (expand G A).all fun ca => (expand G B).all fun cb => (expand G R).any fun cr =>
      MergeClause G d ca cb cr

theorem lookup_slots_none {ns : List PropKey} {k : PropKey} (h : k ∉ ns) (base : Nat) :
    (slots base ns).lookup k = none := by
  induction ns generalizing base with
  | nil => rfl
  | cons n ns ih =>
    have hkn : (k == n) = false := by simp only [beq_eq_false_iff_ne]; intro he; exact h (he ▸ List.mem_cons_self)
    simp only [slots, List.lookup, hkn]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm)) _

theorem mem_of_lookup_slots {ns : List PropKey} {k : PropKey} {base l : Nat}
    (h : (slots base ns).lookup k = some l) : k ∈ ns := by
  by_cases hk : k ∈ ns
  · exact hk
  · rw [lookup_slots_none hk] at h
    cases h

open Classical in
/-- The family a merge's allocation stores under an entry: the result's
field type, or its optional field's, or the type of an index of `ix` whose
class admits the key, or, for a key the result does not state, exactly the
value copied. -/
noncomputable def entryFam (G : NormalGraph ι) (fs : List (PropKey × List ι))
    (os : List (OptionalField (List ι))) (ix : List (IndexKeys × List ι)) (e : PropKey × Tm) : Fam :=
  match fs.lookup e.1 with
  | some T => meaning G T
  | none => match os.find? (·.key == e.1) with
    | some q => meaning G q.type
    | none => if h : ∃ x ∈ ix, x.1.Admits e.1 then meaning G (Classical.choose h).2
      else fun _ _ u => u = e.2

omit [DecidableEq ι] in
theorem entryFam_adm (G : NormalGraph ι) (fs os ix) (e : PropKey × Tm) : Adm (entryFam G fs os ix e) := by
  unfold entryFam
  split
  · exact setSem_adm (normalDenote_adm G) _
  · split
    · exact setSem_adm (normalDenote_adm G) _
    · split
      · exact setSem_adm (normalDenote_adm G) _
      · exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

omit [DecidableEq ι] in
/-- An entry's family admits only values when the entry's own value is one. -/
theorem entryFam_valOnly (G : NormalGraph ι) (fs os ix) (e : PropKey × Tm) (hv : isVal e.2 = true) :
    ValOnly (entryFam G fs os ix e) := by
  unfold entryFam
  split
  · exact fun _ _ _ ⟨_, _, h⟩ => (normalDenote_value h).1
  · split
    · exact fun _ _ _ ⟨_, _, h⟩ => (normalDenote_value h).1
    · split
      · exact fun _ _ _ ⟨_, _, h⟩ => (normalDenote_value h).1
      · intro _ _ _ h; rw [h]; exact hv

/-- The entries a merge allocates, read through its two sides. -/
structure Sides (G : NormalGraph ι) (d : List PropKey) (oa : Obj ι) (sb : Src ι)
    (p : Nat) (W : WorldT (p + 1)) (pa qs : List (PropKey × Tm)) : Prop where
  neverA : ∀ k, oa.neverA k = true → pa.lookup k = none
  sureA : ∀ k T, oa.sureA k T = true → ∃ v, pa.lookup k = some v ∧ meaning G T p (below W) v
  withinA : ∀ k T, oa.withinA k T = true → ∀ v, pa.lookup k = some v → meaning G T p (below W) v
  never : ∀ k, sb.never d k = true → qs.lookup k = none
  sure : ∀ k T, sb.sure d k T = true → ∃ v, qs.lookup k = some v ∧ meaning G T p (below W) v
  within : ∀ k T, sb.within d k T = true → ∀ v, qs.lookup k = some v → meaning G T p (below W) v
  /-- A key the source gives is one it copied, not dropped, or an index. -/
  bound : ∀ K ∈ (match sb with | .prim | .str => [] | .obj ob => ob.bounds),
    ∀ k v, qs.lookup k = some v → K.among = true → K.admits arrayStoreKey = false →
      copiedKey k = true ∧ d.contains k = false ∧ K.admits k = true
  /-- A key the accumulator gives is its own, not the store. -/
  boundA : ∀ K ∈ oa.bounds, ∀ k v, pa.lookup k = some v → k ≠ arrayStoreKey ∧ K.admits k = true
  proto : qs.lookup CallArguments.protoField = none
  /-- What either side gives under a key an index class admits. -/
  classA : ∀ K T, oa.classWithinA K T = true → ∀ k v, K.Admits k → pa.lookup k = some v →
    meaning G T p (below W) v
  classB : ∀ K T, sb.classWithin G d K T = true → ∀ k v, K.Admits k → qs.lookup k = some v →
    ∀ (j : Nat) (hj : j + 1 < p), meaning G T j (trunc j (by omega) (below W)) v

theorem proto_not_copied : copiedKey CallArguments.protoField = false := by decide
theorem proto_not_index : indexKey CallArguments.protoField = false := by decide

/-- A plain-object source's copy, read through its clause. -/
theorem sides_obj {G : NormalGraph ι} {d : List PropKey} {oa ob : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fa fb : List (PropKey × Nat)} (hfa : ObjFacts G oa (p + 1) W fa) (hfb : ObjFacts G ob (p + 1) W fb)
    {h : Heap} (hok : HeapOk (p + 1) W h) {pa qs : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fa .absent oid) = some pa) {cb : CallCode} {oidb : Nat}
    (hq : ownData h (.objAt fb cb oidb) = some qs) :
    Sides G d oa (.obj ob) p W pa (qs.filter fun e => !d.contains e.1) where
  neverA _ hn := acc_never hfa hp hn
  sureA _ _ hs := acc_sure hfa hok hp hs
  withinA _ _ hs _ hv := acc_within hfa hok hp hs hv
  never _ hn := src_never hfb hq hn
  sure _ _ hs := src_sure hfb hok hq hs
  within _ _ hs _ hv := src_within hfb hok hq hs hv
  bound K hK k v hv hamong hstore := by
    rw [srcData_lookup hq] at hv
    by_cases hd : d.contains k = true
    · rw [if_pos hd] at hv; cases hv
    rw [if_neg hd] at hv
    have hs : fb.lookup arrayStoreKey = none := ownKeysT_lookup (hfb.bounds K hK 0) hstore
    rw [storeData_lookup_none (.inr hs), Option.or_none] at hv
    by_cases hc : copiedKey k = true
    · rw [if_pos hc] at hv
      cases hl : fb.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨hc, by simpa using hd, ownKeysT_admits (hfb.bounds K hK 0) hl⟩
    · rw [if_neg hc] at hv; cases hv
  boundA K hK k v hv := by
    rw [ownAll_lookup hp] at hv
    by_cases hk : (k != arrayStoreKey) = true
    · rw [if_pos hk] at hv
      cases hl : fa.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨by simpa using hk, ownKeysT_admits (hfa.bounds K hK 0) hl⟩
    · rw [if_neg hk] at hv; cases hv
  proto := by
    rw [srcData_lookup hq]
    split
    · rfl
    · rw [if_neg (by simp [proto_not_copied]), Option.map_none, Option.none_or]
      exact storeData_lookup_none (.inl proto_not_index)
  classA _ _ hc _ _ hk hv := acc_class hfa hok hp hc hk hv
  classB _ _ hc _ _ hk hv := src_class hfb hok hq hc hk hv

/-- A source owning no enumerable property gives nothing. -/
theorem sides_prim {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fa : List (PropKey × Nat)} (hfa : ObjFacts G oa (p + 1) W fa)
    {h : Heap} (hok : HeapOk (p + 1) W h) {pa : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fa .absent oid) = some pa) :
    Sides G d oa .prim p W pa [] where
  neverA _ hn := acc_never hfa hp hn
  sureA _ _ hs := acc_sure hfa hok hp hs
  withinA _ _ hs _ hv := acc_within hfa hok hp hs hv
  never _ _ := rfl
  sure _ _ hs := by simp [Src.sure] at hs
  within _ _ _ _ hv := by simp [List.lookup] at hv
  bound _ hK := by simp at hK
  boundA K hK k v hv := by
    rw [ownAll_lookup hp] at hv
    by_cases hk : (k != arrayStoreKey) = true
    · rw [if_pos hk] at hv
      cases hl : fa.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨by simpa using hk, ownKeysT_admits (hfa.bounds K hK 0) hl⟩
    · rw [if_neg hk] at hv; cases hv
  proto := rfl
  classA _ _ hc _ _ hk hv := acc_class hfa hok hp hc hk hv
  classB _ _ _ _ _ _ hv := by simp [List.lookup] at hv

/-- What a string's copy gives under a key: a code unit, a string, at an
index key. -/
theorem stringData_lookup {s : String} {d : List PropKey} {k : PropKey} {v : Tm}
    (hv : ((firstKeys (stringData s)).filter fun e => !d.contains e.1).lookup k = some v) :
    indexKey k = true ∧ d.contains k = false ∧ ∃ u, v = .str u := by
  have hm := List.mem_filter.mp (mem_of_lookup hv)
  obtain ⟨q, -, he⟩ := List.mem_map.mp (mem_firstKeys hm.1)
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨indexKey_toString _, by simpa using hm.2, _, rfl⟩

/-- A string source gives its code units, each a string, at its index keys. -/
theorem sides_str {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fa : List (PropKey × Nat)} (hfa : ObjFacts G oa (p + 1) W fa)
    {h : Heap} (hok : HeapOk (p + 1) W h) {pa : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fa .absent oid) = some pa) (s : String) :
    Sides G d oa .str p W pa ((firstKeys (stringData s)).filter fun e => !d.contains e.1) where
  neverA _ hn := acc_never hfa hp hn
  sureA _ _ hs := acc_sure hfa hok hp hs
  withinA _ _ hs _ hv := acc_within hfa hok hp hs hv
  never k hn := by
    cases hv : ((firstKeys (stringData s)).filter fun e => !d.contains e.1).lookup k with
    | none => rfl
    | some v =>
      obtain ⟨hi, hd, -⟩ := stringData_lookup hv
      simp only [Src.never, hi, Bool.not_true, Bool.or_false] at hn
      rw [hd] at hn; cases hn
  sure _ _ hs := by simp [Src.sure] at hs
  within k _ hs v hv := by
    obtain ⟨hi, hd, -⟩ := stringData_lookup hv
    simp only [Src.within, Src.never, hi, Bool.not_true, Bool.or_false] at hs
    rw [hd] at hs; cases hs
  bound _ hK := by simp at hK
  boundA K hK k v hv := by
    rw [ownAll_lookup hp] at hv
    by_cases hk : (k != arrayStoreKey) = true
    · rw [if_pos hk] at hv
      cases hl : fa.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨by simpa using hk, ownKeysT_admits (hfa.bounds K hK 0) hl⟩
    · rw [if_neg hk] at hv; cases hv
  proto := by
    cases hv : ((firstKeys (stringData s)).filter fun e => !d.contains e.1).lookup CallArguments.protoField with
    | none => rfl
    | some v => exact absurd (stringData_lookup hv).1 (by rw [proto_not_index]; decide)
  classA _ _ hc _ _ hk hv := acc_class hfa hok hp hc hk hv
  classB K T hc k v hk hv := by
    obtain ⟨hi, -, u, rfl⟩ := stringData_lookup hv
    simp only [Src.classWithin, Src.arrayRoute, Src.classWithinPlain, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hc
    intro j hj
    rcases hc with rfl | hc
    · cases k with
      | str s => exact absurd hk (by simp [IndexKeys.Admits])
      | sym i => simp [indexKey] at hi
    · exact strIn_sound hc _ _ u

theorem admits_among {K : KeyBound} (ha : K.among = true) {k : PropKey} :
    K.admits k = true ↔ k ∈ K.keys := by
  simp [KeyBound.admits, ha]

theorem admits_outside {K : KeyBound} (ha : K.among = false) {k : PropKey} :
    K.admits k = true ↔ k ∉ K.keys := by
  simp [KeyBound.admits, ha]

/-- What the merged entries hold, from the two sides and the clause. -/
theorem result_facts {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι} {p : Nat}
    {W : WorldT (p + 1)} {pa qs : List (PropKey × Tm)} (hs : Sides G d oa sb p W pa qs)
    {fs : List (PropKey × List ι)} {os : List (OptionalField (List ι))} {ks : List KeyBound}
    (hfs : ∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true)
    (hos : ∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true)
    (hpr : (os.isEmpty || oa.neverA CallArguments.protoField) = true)
    (hks : ∀ K ∈ ks, boundOk oa sb d K = true) :
    (∀ q ∈ fs, ∃ v, (mergeData pa qs).lookup q.1 = some v ∧ meaning G q.2 p (below W) v) ∧
    (∀ q ∈ os, ∀ v, (mergeData pa qs).lookup q.key = some v → meaning G q.type p (below W) v) ∧
    (os ≠ [] → (mergeData pa qs).lookup CallArguments.protoField = none) ∧
    (∀ K ∈ ks, ∀ k ∈ (mergeData pa qs).map Prod.fst, K.admits k = true) := by
  refine ⟨fun q hq => ?_, fun q hq v hv => ?_, fun hne => ?_, fun K hK k hk => ?_⟩
  · have h := hfs q hq
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rw [lookup_mergeData]
    rcases h with hsure | ⟨hsa, hw⟩
    · obtain ⟨v, hv, hm⟩ := hs.sure _ _ hsure
      exact ⟨v, by rw [hv]; rfl, hm⟩
    · cases hq' : qs.lookup q.1 with
      | some v => exact ⟨v, rfl, hs.within _ _ hw v hq'⟩
      | none =>
        obtain ⟨v, hv, hm⟩ := hs.sureA _ _ hsa
        exact ⟨v, by rw [Option.none_or, hv], hm⟩
  · have h := hos q hq
    simp only [Bool.and_eq_true] at h
    rw [lookup_mergeData] at hv
    cases hq' : qs.lookup q.key with
    | some w =>
      rw [hq', Option.some_or] at hv; cases hv
      exact hs.within _ _ h.2 _ hq'
    | none =>
      rw [hq', Option.none_or] at hv
      exact hs.withinA _ _ h.1 _ hv
  · have hn : oa.neverA CallArguments.protoField = true := by
      simp only [Bool.or_eq_true, List.isEmpty_iff] at hpr
      rcases hpr with h | h
      · exact absurd h hne
      · exact h
    rw [lookup_mergeData, hs.proto, Option.none_or]
    exact hs.neverA _ hn
  · obtain ⟨v, hv⟩ := lookup_isSome hk
    rw [lookup_mergeData] at hv
    have hb := hks K hK
    unfold boundOk at hb
    split at hb
    · rename_i hamong
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hA, hB⟩ := hb
      cases hq' : qs.lookup k with
      | some w =>
        cases sb with
        | prim => rw [hs.never k rfl] at hq'; cases hq'
        | str => cases hB
        | obj ob =>
          obtain ⟨Kb, hKb, hbits⟩ := List.any_eq_true.mp hB
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hbits
          obtain ⟨⟨hKa, hst⟩, hall⟩ := hbits
          have hstore : Kb.admits arrayStoreKey = false := by
            simp only [KeyBound.admits, hKa, hst]; rfl
          obtain ⟨hc, hd, hadm⟩ := hs.bound Kb hKb k w hq' hKa hstore
          have := hall k ((admits_among hKa).mp hadm)
          simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
          rcases this with (h1 | h1) | h1
          · rw [hc] at h1; cases h1.2
          · rw [hd] at h1; cases h1
          · exact h1
      | none =>
        rw [hq', Option.none_or] at hv
        obtain ⟨Ka, hKa, hbits⟩ := List.any_eq_true.mp hA
        simp only [Bool.and_eq_true, List.all_eq_true] at hbits
        obtain ⟨hKam, hall⟩ := hbits
        obtain ⟨hne, hadm⟩ := hs.boundA Ka hKa k v hv
        have := hall k ((admits_among hKam).mp hadm)
        simp only [Bool.or_eq_true, beq_iff_eq] at this
        rcases this with h1 | h1
        · exact absurd h1 hne
        · exact h1
    · rename_i hamong
      rw [admits_outside (by simpa using hamong)]
      intro hkK
      have := List.all_eq_true.mp hb k hkK
      simp only [Bool.and_eq_true] at this
      rw [hs.never k this.2, Option.none_or, hs.neverA k this.1] at hv
      cases hv

theorem slots_fst_mem {base : Nat} {ns : List PropKey} {q : PropKey × Nat}
    (h : q ∈ slots base ns) : q.1 ∈ ns := by
  induction ns generalizing base with
  | nil => simp [slots] at h
  | cons n ns ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq ι] in
theorem key_unique {os : List (OptionalField (List ι))} (hnd : (os.map (·.key)).Nodup)
    {q q' : OptionalField (List ι)} (hq : q ∈ os) (hq' : q' ∈ os) (hk : q.key = q'.key) : q = q' := by
  induction os with
  | nil => simp at hq
  | cons o os ih =>
    rw [List.map_cons] at hnd
    have hn := List.nodup_cons.mp hnd
    have h1 := List.mem_cons.mp hq
    have h2 := List.mem_cons.mp hq'
    rcases h1 with e1 | m1
    · rcases h2 with e2 | m2
      · rw [e1, e2]
      · exfalso; apply hn.1; rw [← e1, hk]; exact List.mem_map_of_mem m2
    · rcases h2 with e2 | m2
      · exfalso; apply hn.1; rw [← e2, ← hk]; exact List.mem_map_of_mem m1
      · exact ih hn.2 m1 m2

/-- **The merge step, from values.** Once both operands are values, the merge
reads the properties they own now and allocates them: the entries the result
states at their types, the keys its index admits at the index's type, and
every other at exactly the value copied. The result is a record (`cr` a
`refs` clause) or a dictionary over the index `ds`, `cs`, each at its type,
two that admit one key at one type. -/
theorem merge_finish {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι} {p : Nat}
    {W : WorldT (p + 1)} {h : Heap} {va vb : Val} {pa qs : List (PropKey × Tm)}
    (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) (hs : Sides G d oa sb p W pa qs)
    (hpn : (pa.map Prod.fst).Nodup) (hqn : (qs.map Prod.fst).Nodup)
    (hva : isVal va = true) (hvb : isVal vb = true)
    (hparts : mergeParts h d va vb = some (mergeData pa qs))
    {R : List ι} {cr : Clause (List ι)} {fs : List (PropKey × List ι)}
    {os : List (OptionalField (List ι))} {ks : List KeyBound}
    {ds cs : List (IndexKeys × List ι)}
    (hcr : cr ∈ expand G R)
    (hshape : cr = .refs fs [] [] os [] ks ∨ (cr = .dict fs [] [] ds os [] ks cs ∧ ds ++ cs ≠ []))
    (hnd : (fs.map Prod.fst ++ os.map (·.key)).Nodup)
    (hfs : ∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true)
    (hos : ∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true)
    (hpr : (os.isEmpty || oa.neverA CallArguments.protoField) = true)
    (hks : ∀ K ∈ ks, boundOk oa sb d K = true)
    (hov : ∀ x ∈ ds ++ cs, ∀ y ∈ ds ++ cs, ∀ k, x.1.Admits k → y.1.Admits k → x.2 = y.2)
    (hcls : ∀ x ∈ ds ++ cs, ∀ k v, x.1.Admits k → (mergeData pa qs).lookup k = some v →
      ∀ (j : Nat) (hj : j + 1 < p), meaning G x.2 j (trunc j (by omega) (below W)) v)
    (hnp : ds ++ cs ≠ [] → (mergeData pa qs).lookup CallArguments.protoField = none)
    (hfd : ∀ q ∈ fs, (∀ x ∈ cs, x.1.Admits q.1 → q.2 = x.2) ∧
      (∀ x ∈ ds, x.1.Admits q.1 → inLabels q.2 x.2 = true))
    (hod : ∀ q ∈ os, (∀ x ∈ cs, x.1.Admits q.key → q.type = x.2) ∧
      (∀ x ∈ ds, x.1.Admits q.key → inLabels q.type x.2 = true)) :
    Safe (excOf G) (meaning G R) (p + 1) W h (.merge d va vb) := by
  have hnodup := mergeData_nodup hpn hqn
  obtain ⟨hF, hO, hP, hK⟩ := result_facts hs hfs hos hpr hks
  have hfn : (fs.map Prod.fst).Nodup := hnd.sublist (List.sublist_append_left _ _)
  have hon : (os.map (·.key)).Nodup := hnd.sublist (List.sublist_append_right _ _)
  have hdisj : ∀ q ∈ os, fs.lookup q.key = none := by
    intro q hq
    apply lookup_eq_none
    intro hm
    exact (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_map_of_mem hq) rfl
  let ix : List (IndexKeys × List ι) := ds ++ cs
  generalize mergeData pa qs = ps at hparts hnodup hF hO hP hK hcls hnp
  have hvals : ∀ v ∈ ps.map Prod.snd, isVal v = true := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    rcases mergeParts_vals hparts e he with h1 | ⟨-, h2⟩ | ⟨u, h3⟩
    · rw [h1]; rfl
    · exact h2
    · rw [h3]; rfl
  -- The family an entry's location is given, and why its value meets it.
  have hfam : ∀ e ∈ ps, ∀ (j : Nat) (hj : j + 1 < p),
      entryFam G fs os ix e j (trunc j (by omega) (below W)) e.2 := by
    intro e he j hj
    have hl := lookup_of_mem hnodup he
    cases hT : fs.lookup e.1 with
    | some T =>
      simp only [entryFam, hT]
      obtain ⟨v, hv, hm⟩ := hF (e.1, T) (mem_of_lookup hT)
      rw [hl] at hv; cases hv; exact (meaning_valueFam G T).1.down_le p j (by omega) (below W) _ hm
    | none =>
      cases hq : os.find? (·.key == e.1) with
      | some q =>
        simp only [entryFam, hT, hq]
        have hk : q.key = e.1 := by simpa using List.find?_some hq
        exact (meaning_valueFam G q.type).1.down_le p j (by omega) (below W) _
          (hO q (List.mem_of_find?_eq_some hq) e.2 (hk ▸ hl))
      | none =>
        simp only [entryFam, hT, hq]
        split
        · rename_i hadmits
          obtain ⟨hx, hadmK⟩ := Classical.choose_spec hadmits
          exact hcls _ hx e.1 e.2 hadmK hl j hj
        · rfl
  refine Or.inr ⟨below W, h, .makeAt .absent (ps.map Prod.fst) (ps.map Prod.snd), WExt_refl _,
    WorldAdm_trunc _ hadm, Step.mergeV hva hvb hparts, HeapOk_trunc p W h hok, ?_⟩
  apply make_fields_rule_below (As := ps.map (entryFam G fs os ix))
    (fun A hA => by obtain ⟨e, -, rfl⟩ := List.mem_map.mp hA; exact entryFam_adm G fs os ix e)
    (fun A hA => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hA
      exact entryFam_valOnly G fs os ix e (hvals _ (List.mem_map_of_mem he)))
    p (below W) h .absent (ps.map Prod.fst) (ps.map Prod.snd) hnodup (by simp) (by simp) hvals
    (WorldAdm_trunc _ hadm) (HeapOk_trunc p W h hok)
  · intro q hq
    rw [List.zip_map', List.mem_map] at hq
    obtain ⟨e, he, rfl⟩ := hq
    exact hfam e he
  · intro j hj U hx hrec
    -- The pair each entry contributes to the record the allocation meets.
    have hzip : ∀ e ∈ ps, (e.1, entryFam G fs os ix e) ∈
        (ps.map Prod.fst).zip (ps.map (entryFam G fs os ix)) := by
      intro e he
      rw [List.zip_map', List.mem_map]
      exact ⟨e, he, rfl⟩
    -- The location under a key the object owns, and what its contract is.
    have hat : ∀ f l, (slots h.length (ps.map Prod.fst)).lookup f = some l →
        ∃ v c, ps.lookup f = some v ∧ lookup U l = some c ∧
          ∀ i (hi : i < j) (U' : WorldT i) u, c i hi U' u ↔ entryFam G fs os ix (f, v) i U' u := by
      intro f l hl
      have hmem := mem_of_lookup_slots hl
      obtain ⟨v, hv⟩ := lookup_isSome hmem
      have he := mem_of_lookup hv
      obtain ⟨fl, l', c, oid', hfl, hl', hU, hag⟩ := recT_at (hzip _ he) hrec
      cases hfl
      rw [hl] at hl'; cases hl'
      exact ⟨v, c, hv, hU, hag⟩
    have hrefs : ReferenceConjunctions.refsT (ReferenceConjunctions.famsOf (meaning G) fs) [] j U
        (.objAt (slots h.length (ps.map Prod.fst)) .absent (h.length + (ps.map Prod.snd).length)) := by
      refine ⟨⟨_, _, rfl, ?_⟩, by simp⟩
      intro f F hm
      obtain ⟨T, hT, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hm
      obtain ⟨v, hv, -⟩ := hF (f, T) hT
      have he := mem_of_lookup hv
      obtain ⟨fl, l, c, oid', hfl, hl, hU, hag⟩ := recT_at (hzip _ he) hrec
      cases hfl
      have : entryFam G fs os ix (f, v) = meaning G T := by
        simp [entryFam, lookup_of_mem hfn hT]
      exact ⟨l, c, hl, hU, fun i hi U' u => (hag i hi U' u).trans (by rw [this])⟩
    have hviews : viewT (ReferenceConjunctions.famsOf (meaning G) []) j U
        (.objAt (slots h.length (ps.map Prod.fst)) .absent (h.length + (ps.map Prod.snd).length)) := by
      intro f F hm; simp [ReferenceConjunctions.famsOf] at hm
    have hopt : optT (os.map (·.map (meaning G))) j U
        (.objAt (slots h.length (ps.map Prod.fst)) .absent (h.length + (ps.map Prod.snd).length)) := by
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro o ho _
        have hne : os ≠ [] := by
          intro he; subst he; simp at ho
        apply lookup_slots_none
        intro hm
        obtain ⟨v, hv⟩ := lookup_isSome hm
        rw [hP hne] at hv; cases hv
      · intro o ho l hl
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
        obtain ⟨v, c, hv, hU, hag⟩ := hat _ l hl
        have hfind : ∃ q', os.find? (·.key == q.key) = some q' ∧ q' = q := by
          cases hf : os.find? (·.key == q.key) with
          | none =>
            exfalso
            have := List.find?_eq_none.mp hf q hq
            simp at this
          | some q' =>
            refine ⟨q', rfl, key_unique hon (List.mem_of_find?_eq_some hf) hq ?_⟩
            simpa using List.find?_some hf
        obtain ⟨q', hf, rfl⟩ := hfind
        have : entryFam G fs os ix (q'.key, v) = meaning G q'.type := by
          simp only [entryFam, hdisj q' hq, hf]
        refine ⟨c, hU, fun i hi U' u => ?_⟩
        have hiff : c i hi U' u ↔ meaning G q'.type i U' u :=
          (hag i hi U' u).trans (by simp only [OptionalField.map]; rw [this])
        exact ⟨hiff.mp, fun _ => hiff.mpr⟩
    have hbounds : ∀ K ∈ ks, ownKeysT K j U (.objAt (slots h.length (ps.map Prod.fst)) .absent (h.length + (ps.map Prod.snd).length)) := by
      intro K hKm
      exact ⟨_, _, rfl, fun q hq => hK K hKm q.1 (slots_fst_mem hq)⟩
    have hstore : (slots h.length (ps.map Prod.fst)).lookup CallArguments.arrayStoreField = none := by
      apply lookup_slots_none
      intro hm
      obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
      exact mergeParts_store hparts e he hk
    refine (expand_sem G R (plain_of_mem_expand hcr) j U _).mpr
      ⟨_, hcr, ?_, builtinInvariant_of_lookup hstore⟩
    rcases hshape with rfl | ⟨rfl, hne⟩
    · simp only [semWithArgs]
      exact ⟨hrefs, viewsT_of_viewT hviews, hopt, MethodMembers.methodT_nil _ _ _, hbounds⟩
    · simp only [semWithArgs]
      -- What a location under a key an index class admits holds: exactly
      -- the type of a writable index admitting it, and within the index's
      -- type in any case.
      have hkey : ∀ x ∈ ds ++ cs, ∀ f l, (slots h.length (ps.map Prod.fst)).lookup f = some l →
          x.1.Admits f → ∃ c : Ctr j, lookup U l = some c ∧
            ((∀ y ∈ cs, y.1.Admits f →
                ∀ i (hi : i < j) (U' : WorldT i) u, c i hi U' u ↔ meaning G y.2 i U' u) ∧
             ∀ i (hi : i < j) (U' : WorldT i) u, c i hi U' u → meaning G x.2 i U' u) := by
        intro x hx f l hl hxf
        obtain ⟨v, c, hv, hU, hag⟩ := hat f l hl
        refine ⟨c, hU, ?_⟩
        cases hT : fs.lookup f with
        | some T =>
          have hq := hfd (f, T) (mem_of_lookup hT)
          simp only at hq
          have hfam : entryFam G fs os ix (f, v) = meaning G T := by simp [entryFam, hT]
          refine ⟨fun y hy hyf i hi U' u => ?_, fun i hi U' u hc => ?_⟩
          · rw [hag i hi U' u, hfam, hq.1 y hy hyf]
          · rw [hag i hi U' u, hfam] at hc
            rcases List.mem_append.mp hx with hx | hx
            · exact inLabels_sound (hq.2 x hx hxf) hc
            · rw [hq.1 x hx hxf] at hc; exact hc
        | none =>
          cases hf : os.find? (·.key == f) with
          | some q =>
            have hqk : q.key = f := by simpa using List.find?_some hf
            have hq := hod q (List.mem_of_find?_eq_some hf)
            rw [hqk] at hq
            have hfam : entryFam G fs os ix (f, v) = meaning G q.type := by
              simp only [entryFam, hT, hf]
            refine ⟨fun y hy hyf i hi U' u => ?_, fun i hi U' u hc => ?_⟩
            · rw [hag i hi U' u, hfam, hq.1 y hy hyf]
            · rw [hag i hi U' u, hfam] at hc
              rcases List.mem_append.mp hx with hx | hx
              · exact inLabels_sound (hq.2 x hx hxf) hc
              · rw [hq.1 x hx hxf] at hc; exact hc
          | none =>
            have hex : ∃ z ∈ ix, z.1.Admits f := ⟨x, hx, hxf⟩
            obtain ⟨hz, hzf⟩ := Classical.choose_spec hex
            have hfam : entryFam G fs os ix (f, v) = meaning G (Classical.choose hex).2 := by
              simp only [entryFam, hT, hf]
              rw [dif_pos hex]
            refine ⟨fun y hy hyf i hi U' u => ?_, fun i hi U' u hc => ?_⟩
            · rw [hag i hi U' u, hfam, hov _ hz y (List.mem_append_right _ hy) f hzf hyf]
            · rw [hag i hi U' u, hfam, hov _ hz x hx f hzf hxf] at hc; exact hc
      have hnoproto : (slots h.length (ps.map Prod.fst)).lookup CallArguments.protoField = none := by
        apply lookup_slots_none
        intro hm
        obtain ⟨v, hv⟩ := lookup_isSome hm
        rw [hnp hne] at hv; cases hv
      refine ⟨hrefs, viewsT_of_viewT hviews, ⟨fun x hx => ⟨_, _, rfl, hnoproto, fun f l hl hxf => ?_⟩,
        fun x hx => ⟨_, _, rfl, hnoproto, fun f l hl hxf => ?_⟩⟩, hopt, MethodMembers.methodT_nil _ _ _,
        hbounds⟩
      · obtain ⟨c, hU, -, himp⟩ := hkey x (List.mem_append_left _ hx) f l hl hxf
        exact ⟨c, hU, himp⟩
      · obtain ⟨c, hU, hiff, -⟩ := hkey x (List.mem_append_right _ hx) f l hl hxf
        exact ⟨c, hU, hiff x hx hxf⟩

/-- The conditions `FieldsOk` states, as `merge_finish` takes them. -/
theorem fieldsOk_facts {d : List PropKey} {oa : Obj ι} {sb : Src ι} {fs : List (PropKey × List ι)}
    {os : List (OptionalField (List ι))} {ks : List KeyBound} (h : FieldsOk d oa sb fs os ks = true) :
    (fs.map Prod.fst ++ os.map (·.key)).Nodup ∧
    (∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true) ∧
    (∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true) ∧
    (os.isEmpty || oa.neverA CallArguments.protoField) = true ∧
    (∀ K ∈ ks, boundOk oa sb d K = true) := by
  simp only [FieldsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hnd, hfs⟩, hos⟩, hpr⟩, hks⟩ := h
  exact ⟨hnd, hfs, fun q hq => by simpa using hos q hq, hpr, hks⟩

/-- The conditions `DictOk` states, as `merge_finish` takes them. -/
theorem dictOk_facts {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι}
    {fs : List (PropKey × List ι)} {os : List (OptionalField (List ι))}
    {ds cs : List (IndexKeys × List ι)} (h : DictOk G d oa sb fs os ds cs = true) :
    ds ++ cs ≠ [] ∧ oa.neverA CallArguments.protoField = true ∧
      (∀ x ∈ ds ++ cs, oa.classWithinA x.1 x.2 = true ∧ sb.classWithin G d x.1 x.2 = true) ∧
      (∀ x ∈ ds ++ cs, ∀ y ∈ ds ++ cs, ∀ k, x.1.Admits k → y.1.Admits k → x.2 = y.2) ∧
      (∀ q ∈ fs, (∀ x ∈ cs, x.1.Admits q.1 → q.2 = x.2) ∧
        (∀ x ∈ ds, x.1.Admits q.1 → inLabels q.2 x.2 = true)) ∧
      (∀ q ∈ os, (∀ x ∈ cs, x.1.Admits q.key → q.type = x.2) ∧
        (∀ x ∈ ds, x.1.Admits q.key → inLabels q.type x.2 = true)) := by
  simp only [DictOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨hne, hnp⟩, hix⟩, hov⟩, hfs⟩, hos⟩ := h
  refine ⟨hne, hnp, fun x hx => hix x hx, fun x hx y hy k hxk hyk => ?_,
    fun q hq => ⟨fun x hx hxa => ?_, fun x hx hxa => ?_⟩,
    fun q hq => ⟨fun x hx hxa => ?_, fun x hx hxa => ?_⟩⟩
  · rcases hov x hx y hy with h1 | h1
    · exact absurd (IndexKeys.overlaps_of_admits hxk hyk) (by simp [h1])
    · exact h1
  · rcases (hfs q hq).1 x hx with h1 | h1
    · exact absurd (IndexKeys.may_of_admits hxa) (by simp [h1])
    · exact h1
  · rcases (hfs q hq).2 x hx with h1 | h1
    · exact absurd (IndexKeys.may_of_admits hxa) (by simp [h1])
    · exact h1
  · rcases (hos q hq).1 x hx with h1 | h1
    · exact absurd (IndexKeys.may_of_admits hxa) (by simp [h1])
    · exact h1
  · rcases (hos q hq).2 x hx with h1 | h1
    · exact absurd (IndexKeys.may_of_admits hxa) (by simp [h1])
    · exact h1

/-- The two sides of a merge, read through their clauses. -/
theorem merge_sides {G : NormalGraph ι} {d : List PropKey} {ca cb : Clause (List ι)}
    {oa : Obj ι} {sb : Src ι} (hoa : objOf ca = some oa) (hsrc : srcOf cb = some sb)
    {p : Nat} {W : WorldT (p + 1)} {h : Heap} {va vb : Val} (hok : HeapOk (p + 1) W h)
    (hsa : clauseSem G ca (p + 1) W va) (hsb : clauseSem G cb (p + 1) W vb) :
    ∃ pa qs, (pa.map Prod.fst).Nodup ∧ (qs.map Prod.fst).Nodup ∧ isVal va = true ∧
      isVal vb = true ∧ mergeParts h d va vb = some (mergeData pa qs) ∧
      Sides G d oa sb p W pa qs := by
  obtain ⟨fa, oid, rfl, hfa⟩ := objFacts_of_sem hoa hsa
  have hp : ownAll h (.objAt fa .absent oid) = some (firstKeys
      ((fa.filter (·.1 != arrayStoreKey)).map (fun p => (p.1, heapVal h p.2)))) := rfl
  unfold srcOf at hsrc
  split at hsrc
  · rename_i hempty
    cases hsrc
    obtain ⟨hq, hvb⟩ := emptyClause_ownData hempty hsb h
    exact ⟨_, [], ownAll_nodup hp, by simp, rfl, hvb, by simp [mergeParts, hp, hq],
      sides_prim hfa hok hp⟩
  split at hsrc
  · rename_i hne hstr
    cases hsrc
    -- A string: its code units at its indices.
    have hs : ∃ s, vb = .str s := by
      obtain ⟨hsb, -⟩ := hsb
      cases cb <;> simp [stringClause] at hstr
      · obtain ⟨s, rfl⟩ := hsb; exact ⟨s, rfl⟩
      · rename_i s; simp only [semWithArgs] at hsb; exact ⟨s, hsb⟩
    obtain ⟨s, rfl⟩ := hs
    have hq : ownData h (.str s) = some (firstKeys (stringData s)) := rfl
    exact ⟨_, _, ownAll_nodup hp,
      (ownData_nodup hq).sublist (List.Sublist.map _ List.filter_sublist), rfl, rfl,
      by simp [mergeParts, hp, hq], sides_str hfa hok hp s⟩
  · -- A plain object, a function or a class: an object whose own fields the copy reads.
    have hfacts : ∃ ob fb code oidb, sb = .obj ob ∧ vb = .objAt fb code oidb ∧ ObjFacts G ob (p + 1) W fb := by
      split at hsrc
      · rename_i ob hob
        cases hsrc
        obtain ⟨fb, oidb, rfl, hfb⟩ := objFacts_of_sem hob hsb
        exact ⟨ob, fb, .absent, oidb, rfl, rfl, hfb⟩
      · obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.mp hsrc
        obtain ⟨fb, code, oidb, rfl, hfb⟩ := codeFacts_of_sem hob hsb
        exact ⟨ob, fb, code, oidb, rfl, rfl, hfb⟩
    obtain ⟨ob, fb, code, oidb, rfl, rfl, hfb⟩ := hfacts
    have hq : ownData h (.objAt fb code oidb) = some (firstKeys
        ((fb.filter (copiedKey ·.1)).map (fun p => (p.1, heapVal h p.2)) ++ storeData h fb)) := rfl
    exact ⟨_, _, ownAll_nodup hp,
      (ownData_nodup hq).sublist (List.Sublist.map _ List.filter_sublist), rfl, rfl,
      by simp [mergeParts, hp, hq], sides_obj hfa hfb hok hp hq⟩

/-- **A merge of two values is safe at a result the rule states.** -/
theorem merge_values_safe {G : NormalGraph ι} {d : List PropKey} {A B R : List ι}
    (hm : MergeOk G d A B R = true) {n : Nat} {W : WorldT n} {h : Heap} {va vb : Val}
    (hadm : WorldAdm W) (hok : HeapOk n W h) (ha : meaning G A n W va) (hb : meaning G B n W vb) :
    Safe (excOf G) (meaning G R) n W h (.merge d va vb) := by
  cases n with
  | zero => trivial
  | succ p =>
  simp only [MergeOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hm
  obtain ⟨⟨hpA, hpB⟩, hall⟩ := hm
  obtain ⟨ca, hca, hsa⟩ := (expand_sem G A hpA _ _ _).mp ha
  obtain ⟨cb, hcb, hsb⟩ := (expand_sem G B hpB _ _ _).mp hb
  obtain ⟨cr, hcr, hmc⟩ := hall ca hca cb hcb
  unfold MergeClause at hmc
  split at hmc
  · rename_i oa sb fs os ks hoa hsrc
    obtain ⟨pa, qs, hpn, hqn, hva, hvb, hparts, hs⟩ := merge_sides (d := d) hoa hsrc hok hsa hsb
    obtain ⟨hnd, hfs, hos, hpr, hks⟩ := fieldsOk_facts hmc
    exact merge_finish (ds := []) (cs := []) hadm hok hs hpn hqn hva hvb hparts hcr
      (.inl rfl) hnd hfs hos hpr hks (by simp) (by simp) (by simp)
      (fun _ _ => ⟨by simp, by simp⟩) (fun _ _ => ⟨by simp, by simp⟩)
  · rename_i oa sb fs ds os ks cs hoa hsrc
    obtain ⟨pa, qs, hpn, hqn, hva, hvb, hparts, hs⟩ := merge_sides (d := d) hoa hsrc hok hsa hsb
    simp only [Bool.and_eq_true] at hmc
    obtain ⟨⟨hmf, hmd⟩, -⟩ := hmc
    obtain ⟨hnd, hfs, hos, hpr, hks⟩ := fieldsOk_facts hmf
    obtain ⟨hne, hnp, hix, hov, hfd, hod⟩ := dictOk_facts hmd
    refine merge_finish hadm hok hs hpn hqn hva hvb hparts hcr (.inr ⟨rfl, hne⟩) hnd hfs
      hos hpr hks hov ?_ ?_ hfd hod
    · intro x hx k v hk hv
      rw [lookup_mergeData] at hv
      cases hq : qs.lookup k with
      | some w =>
        rw [hq, Option.some_or] at hv; cases hv
        exact hs.classB _ _ (hix x hx).2 k _ hk hq
      | none =>
        rw [hq, Option.none_or] at hv
        intro j hj
        exact (meaning_valueFam G x.2).1.down_le p j (by omega) (below W) _
          (hs.classA _ _ (hix x hx).1 k v hk hv)
    · intro _
      rw [lookup_mergeData, hs.proto, Option.none_or]
      exact hs.neverA _ hnp
  · cases hmc

/-! ### The result a merge is typed at

Untrusted: what extraction proposes for a merge, one clause per pair of the
operands' clauses. `MergeClause` checks it, as any claim. -/

/-- The type a side's field or view states for a key. -/
def Obj.namedType (o : Obj ι) (k : PropKey) : Option (List ι) :=
  (o.named.find? (·.1 == k)).map (·.2)

/-- The types a side may hold under a key it need not own: its optional
field's, and, for a string key, its index types. -/
def Obj.maybeTypes (o : Obj ι) (k : PropKey) : List ι :=
  (o.optional.filter (·.key == k)).flatMap (·.type) ++ (o.indexes.filter (·.1.may k)).flatMap (·.2)

def Obj.keys (o : Obj ι) : List PropKey := o.named.map (·.1) ++ o.optional.map (·.key)

/-- The record a merge of two clauses gives: each key the source surely
copies, at its type; each the accumulator surely has, at its type with what
the source may copy over it; the rest, where both sides' types say what they
may hold, optional; and, when both sides list their keys, the keys listed. -/
def mergeResult (G : NormalGraph ι) (d : List PropKey) (ca cb : Clause (List ι)) :
    Option (Clause (List ι)) := do
  let oa ← objOf ca
  let sb ← srcOf cb
  let bKeys := match sb with | .prim | .str => [] | .obj ob => ob.keys
  let keys := (oa.keys ++ bKeys).eraseDups.filter (· != arrayStoreKey)
  let bNamed (k : PropKey) : Option (List ι) := match sb with
    | .prim | .str => none
    | .obj ob => if !d.contains k && copiedKey k then ob.namedType k else none
  let bMaybe (k : PropKey) : List ι := match sb with
    | .prim | .str => []
    | .obj ob => if !d.contains k && copiedKey k then ob.maybeTypes k else []
  let fields := keys.filterMap fun k =>
    match bNamed k with
    | some T => some (k, T)
    | none => match oa.namedType k with
      | some Ta =>
        let T := (Ta ++ bMaybe k).eraseDups
        if sb.within d k T then some (k, T) else none
      | none => none
  let optional : List (OptionalField (List ι)) :=
    if oa.neverA CallArguments.protoField then keys.filterMap fun k =>
      if fields.any (·.1 == k) then none else
      let T := (oa.maybeTypes k ++ bMaybe k).eraseDups
      if !T.isEmpty && oa.withinA k T && sb.within d k T then some ⟨k, false, T⟩ else none
    else []
  let bound : List KeyBound := match oa.bounds.find? (·.among), sb with
    | some Ka, .prim => [⟨true, Ka.keys.filter (· != arrayStoreKey)⟩]
    | some Ka, .obj ob =>
      match ob.bounds.find? (fun K => K.among && !K.keys.contains arrayStoreKey) with
      | some Kb => [⟨true, (Ka.keys.filter (· != arrayStoreKey) ++
          Kb.keys.filter (fun x => (copiedKey x || !strKey x) && !d.contains x)).eraseDups⟩]
      | none => []
    | some _, .str => []
    | none, _ => []
  -- Without a prototype from the accumulator the result has none, which a
  -- later merge's optional fields need.
  let bound := if oa.neverA CallArguments.protoField && bound.isEmpty
    then [⟨false, [CallArguments.protoField]⟩] else bound
  let record : Clause (List ι) := .refs fields [] [] optional [] bound
  -- Where a side states an index, the result states one over the same
  -- classes, writable, each at what either side and the fields the classes
  -- overlapping it may admit hold, where the rule admits it; otherwise the
  -- record.
  let bIndexes := match sb with | .prim | .str => [] | .obj ob => ob.indexes
  let classes := (oa.indexes.map Prod.fst ++ bIndexes.map Prod.fst).eraseDups
  if classes.isEmpty then pure record else
  let admittedBy (K : IndexKeys) (k : PropKey) := (classes.filter (·.overlaps K)).any (·.may k)
  let typeOf (K : IndexKeys) : List ι :=
    ((oa.indexes.filter (·.1.overlaps K)).flatMap (·.2) ++
      (bIndexes.filter (·.1.overlaps K)).flatMap (·.2) ++
      (fields.filter (admittedBy K ·.1)).flatMap (·.2) ++
      (optional.filter (admittedBy K ·.key)).flatMap (·.type)).eraseDups
  let ix := classes.map fun K => (K, typeOf K)
  let typeAt (k : PropKey) : Option (List ι) := (ix.find? (·.1.may k)).map (·.2)
  let dict : Clause (List ι) :=
    .dict (fields.map fun (k, T) => (k, (typeAt k).getD T)) [] [] ix
      (optional.map fun q => match typeAt q.key with
        | some V => { q with type := V }
        | none => q) []
      (bound.filter fun K => ix.all fun y => K.keeps y.1) ix
  pure (if MergeClause G d ca cb dict then dict else record)

#print axioms merge_values_safe

end Verification.ObjectMerge
