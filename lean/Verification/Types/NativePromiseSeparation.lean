import Verification.Types.PositiveRules

/-! A native Promise application is separated from the stable bound by one
world and value: an object that owns exactly the Promise row's view keys, the
prototype key among them, each at a location with the empty contract. It
belongs to the Promise row, whose views and host-relative methods then hold
vacuously, and every clause of the stable bound excludes it by shape, by a
required view key it lacks, or by an optional key it lacks while it has a
prototype. -/
namespace Verification.NativePromiseSeparation
open PositiveGraphs PositiveRules PositiveNormalization ReferenceConjunctions MethodMembers

/-- Every owned key shares one location. -/
def fields (keys : List PropKey) : List (PropKey × Nat) :=
  keys.map fun k => (k, 0)

theorem fields_lookup (keys : List PropKey) (k : PropKey) (hk : k ∈ keys) :
    (fields keys).lookup k = some 0 := by
  induction keys with
  | nil => cases hk
  | cons q qs ih =>
    simp only [fields, List.map_cons, List.lookup_cons]
    split
    · rfl
    · rename_i hn
      apply ih
      rcases List.mem_cons.mp hk with he | he
      · subst k
        simp at hn
      · exact he

theorem fields_absent (keys : List PropKey) (k : PropKey) (hk : k ∉ keys) :
    (fields keys).lookup k = none := by
  induction keys with
  | nil => rfl
  | cons q qs ih =>
    simp only [fields, List.map_cons, List.lookup_cons]
    have hq : (k == q) = false := beq_false_of_ne (fun h => hk (h ▸ List.mem_cons_self))
    rw [hq]
    exact ih (fun h => hk (List.mem_cons_of_mem _ h))

theorem fields_location (keys : List PropKey) (k : PropKey) (l : Nat)
    (h : (fields keys).lookup k = some l) : l = 0 := by
  by_cases hk : k ∈ keys
  · rw [fields_lookup keys k hk] at h
    cases h
    rfl
  · rw [fields_absent keys k hk] at h
    cases h

/-- The location's contract admits no value, so every implication from it holds. -/
noncomputable def emptyCell : Ctr 1 := fun _ _ _ _ => False
noncomputable def witnessWorld : WorldT 1 := ofList [emptyCell]
def witness (keys : List PropKey) : Val := .objAt (fields keys) .absent 1

theorem witness_cell : lookup witnessWorld 0 = some emptyCell := by
  simp [witnessWorld, lookup]

/-- The keys a row's views name. -/
def viewKeys (vs : List (PropKey × List ι)) : List PropKey := vs.map (·.1)

/-- A member is found at the witness's own location for its key, or one
prototype up; both locations hold the empty contract. -/
theorem witness_member (keys : List PropKey) (proto : CallArguments.protoField ∈ keys)
    (m : Member) : memberT Ξ m 1 witnessWorld (witness keys) := by
  cases hk : (fields keys).lookup m.key with
  | none =>
    refine ⟨1, fields keys, 1, rfl, hk, ?_⟩
    exact ⟨fields keys, 0, emptyCell, 1, rfl, fields_lookup keys _ proto, witness_cell,
      fun _ _ _ _ _ h => h.elim⟩
  | some l =>
    have he := fields_location keys _ l hk
    subst l
    exact ⟨0, fields keys, 0, emptyCell, 1, rfl, hk, witness_cell, fun _ _ _ _ _ h => h.elim⟩

theorem witness_clause (G : NormalGraph ι) (η : MixedAssignment ι)
    (vs : List (PropKey × List ι)) (ms : List (Sig (List ι))) (ks : List KeyBound)
    (proto : CallArguments.protoField ∈ viewKeys vs)
    (admitted : ∀ K ∈ ks, ∀ p ∈ vs, K.admits p.1 = true) :
    semWithArgs Ξ (mixedValues G η) (mixedArgs G η)
      (.refs [] [] vs [] ms ks) 1 witnessWorld (witness (viewKeys vs)) := by
  refine ⟨⟨⟨fields (viewKeys vs), 1, rfl, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [famsOf]
  · simp
  · intro key T hm
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
    cases he
    exact .inl (viewT_single ⟨fields (viewKeys vs), 0, emptyCell, 1, rfl,
      fields_lookup _ _ (List.mem_map.mpr ⟨p, hp, rfl⟩), witness_cell,
      fun _ _ _ _ h => h.elim⟩)
  · exact ⟨fields (viewKeys vs), 1, rfl, by simp, by simp⟩
  · intro m _
    exact witness_member _ proto m
  · intro K hK
    refine ⟨fields (viewKeys vs), 1, rfl, ?_⟩
    intro q hq
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hq
    cases he
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hk
    cases he
    exact admitted K hK p hp

theorem witness_builtins (G : NormalGraph ι) (X : List ι → Fam)
    (keys : List PropKey) (c : Clause (List ι))
    (ha : CallArguments.arrayStoreField ∉ keys) :
    builtinInvariant G X c 1 witnessWorld (witness keys) := by
  exact builtinInvariant_of_lookup (fields_absent keys _ ha)

/-- A stable clause excludes the witness by shape, by a required view key the
witness lacks, or by an optional key it lacks while it has a prototype. -/
def RejectClause (keys : List PropKey) (c : Clause (List ι)) : Prop :=
  (shape c ≠ 2 ∧ shape c ≠ 7) ∨ match c with
  | .refs _ _ views optional _ _ =>
      (∃ p ∈ views, p.1 ∉ keys ∧ p.1 ≠ lengthKey) ∨ ∃ o ∈ optional, o.key ∉ keys
  | _ => False

instance [DecidableEq ι] (keys : List PropKey) (c : Clause (List ι)) :
    Decidable (RejectClause keys c) := by
  unfold RejectClause
  cases c <;> infer_instance

theorem reject_clause (G : NormalGraph ι) (η : MixedAssignment ι)
    (keys : List PropKey) (proto : CallArguments.protoField ∈ keys)
    (c : Clause (List ι)) (hc : RejectClause keys c) :
    ¬ semWithArgs Ξ (mixedValues G η) (mixedArgs G η) c 1 witnessWorld (witness keys) := by
  intro hv
  rcases hc with shape | field
  · have ht : c ≠ .top := by intro h; subst c; exact shape.2 rfl
    have hj : c ≠ .source := by intro h; subst c; exact shape.2 rfl
    exact shape.1 (semWithArgs_shape ht hj hv).symm
  · cases c <;> try exact field.elim
    rename_i a bs views optional methods bounds
    rcases field with ⟨p, hp, hn, hlen⟩ | ⟨o, ho, hn⟩
    · obtain ⟨fs, l, ctr, oid, he, hl, _, _⟩ :=
        viewsT_at (List.mem_map.mpr ⟨p, hp, rfl⟩) hlen hv.2.1
      cases he
      rw [fields_absent keys _ hn] at hl
      cases hl
    · obtain ⟨fs, oid, he, absent, _⟩ := hv.2.2.1
      cases he
      have hp := absent (o.map (mixedValues G η)) (List.mem_map.mpr ⟨o, ho, rfl⟩)
        (fields_absent keys _ hn)
      rw [fields_lookup keys _ proto] at hp
      cases hp

/-- The checked structure: the Promise row's plain record clause, whose views
include the prototype key, whose own-key bounds admit every view key and
whose views exclude the array store, and a stable bound each clause of which
rejects the witness. -/
structure Shape (G : NormalGraph ι) (root : ι) (stable : List ι) where
  views : List (PropKey × List ι)
  methods : List (Sig (List ι))
  bounds : List KeyBound
  plain : G.plain root = true
  row : Clause.refs [] [] views [] methods bounds ∈ G root
  proto : CallArguments.protoField ∈ viewKeys views
  admitted : ∀ K ∈ bounds, ∀ p ∈ views, K.admits p.1 = true
  noArray : CallArguments.arrayStoreField ∉ viewKeys views
  stablePlain : G.plainTy stable = true
  reject : ∀ l ∈ stable, ∀ c ∈ G l, RejectClause (viewKeys views) c

theorem Shape.separate {G : NormalGraph ι} {root : ι} {stable : List ι}
    (shape : Shape G root stable)
    (η θ : MixedAssignment ι) :
    ¬ FamLe (mixedValues G η [root]) (mixedValues G θ stable) := by
  intro sub
  have input : mixedValues G η [root] 1 witnessWorld (witness (viewKeys shape.views)) := by
    refine ⟨root, List.mem_singleton_self _, ?_⟩
    dsimp only
    rw [qDenoteWithArgs_unfold]
    obtain ⟨hp, hs, hm⟩ := NormalGraph.plain_iff.mp shape.plain
    simp only [qLayerWithArgs, hp, hs, hm, Bool.false_eq_true, if_false]
    exact ⟨_, shape.row, witness_clause G η shape.views shape.methods shape.bounds
      shape.proto shape.admitted, witness_builtins G _ _ _ shape.noArray⟩
  obtain ⟨l, hl, hv⟩ := sub 1 witnessWorld _ input
  rw [qDenoteWithArgs_unfold] at hv
  obtain ⟨hp, hs, hm⟩ := NormalGraph.plain_iff.mp (List.all_eq_true.mp shape.stablePlain l hl)
  simp only [qLayerWithArgs, hp, hs, hm, Bool.false_eq_true, if_false] at hv
  obtain ⟨c, hc, hv, _⟩ := hv
  exact reject_clause G θ _ shape.proto c (shape.reject l hl c hc) hv

/-- The source loader supplies a graph-derived witness only after all its
structural obligations have been checked. -/
def check [DecidableEq ι] (G : NormalGraph ι) (root : ι) (stable : List ι) :
    Option (Shape G root stable) := do
  let candidates := (G root).filterMap fun c => match c with
    | .refs [] [] vs [] ms ks => some (vs, ms, ks)
    | _ => none
  let fits := fun (vs : List (PropKey × List ι)) (ks : List KeyBound) =>
    CallArguments.protoField ∈ viewKeys vs ∧ (∀ K ∈ ks, ∀ p ∈ vs, K.admits p.1 = true) ∧
      CallArguments.arrayStoreField ∉ viewKeys vs ∧
      ∀ l ∈ stable, ∀ c ∈ G l, RejectClause (viewKeys vs) c
  let (vs, ms, ks) ← candidates.find? fun r => decide (fits r.1 r.2.2)
  if plain : G.plain root = true then
    if row : Clause.refs [] [] vs [] ms ks ∈ G root then
      if stablePlain : G.plainTy stable = true then
        if h : fits vs ks then
          some ⟨vs, ms, ks, plain, row, h.1, h.2.1, h.2.2.1, stablePlain, h.2.2.2⟩
        else none
      else none
    else none
  else none

#print axioms Shape.separate
end Verification.NativePromiseSeparation
