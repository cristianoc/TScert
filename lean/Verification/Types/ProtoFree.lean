import Verification.Types.PositiveNormalization

/-! Clauses whose members own no prototype.

An object the model allocates for a class instance, a constructed error or an
array owns the prototype key (`CallArguments.protoField`); a plain object
does not. A write of a key some such object holds as a property the model
does not state is lowered only onto a receiver whose claim excludes them
(SOURCE-ELABORATION.md, "Reserved writes"). The test is on clauses, and its
meaning holds for every interpretation of their operands. -/
namespace Verification.ProtoFree
open PositiveNormalization

/-- `v` is an object owning the prototype key. -/
def OwnsProto (v : Val) : Prop :=
  ∃ (flds : List (PropKey × Nat)) (r : CallCode) (oid : Nat),
    v = .objAt flds r oid ∧ (flds.lookup CallArguments.protoField).isSome

/-- A bound that keeps the prototype key out. -/
def excludesProto (b : KeyBound) : Bool := !b.admits CallArguments.protoField

/-- A clause of primitives: no member is an object. -/
def primitive {α : Type} : Clause α → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .numIn _
  | .str | .strLit _ | .strIn _ | .bigint | .bigintLit _ | .symbol | .symbolLit _ => true
  | _ => false

/-- A clause none of whose members owns the prototype key: a primitive, a
dictionary with an index view or a writable index, or a record or
dictionary with a key bound keeping the key out. Optional fields and views
alone constrain no absent key; `top`, `source`, arrays, packs and callable
clauses are not proto-free. -/
def clause {α : Type} (c : Clause α) : Bool :=
  primitive c || match c with
  | .dict _ _ _ ds _ _ ks cs _ => !ds.isEmpty || !cs.isEmpty || ks.any excludesProto
  | .refs _ _ _ _ _ ks _ => ks.any excludesProto
  | _ => false

private theorem ownKeys_excludes {b : KeyBound} (hb : excludesProto b = true) {n W v}
    (h : ownKeysT b n W v) : ¬ OwnsProto v := by
  rintro ⟨flds, r, oid, rfl, hs⟩
  have h' := h
  obtain ⟨_, _, he, _⟩ := h'
  cases he
  rw [ownKeysT_lookup h (by simpa [excludesProto] using hb)] at hs
  simp at hs

private theorem dictView_excludes {K : IndexKeys} {A : Fam} {n W v}
    (h : dictViewT K A n W v) : ¬ OwnsProto v := by
  obtain ⟨flds, oid, he, ⟨hp, _⟩, _⟩ := h
  rintro ⟨flds', r, oid', he', hs⟩
  rw [he'] at he
  cases he
  rw [hp] at hs
  simp at hs

private theorem dictCell_excludes {K : IndexKeys} {s : StorageRole} {A : Fam} {n W v}
    (h : dictCellT K s A n W v) : ¬ OwnsProto v :=
  dictView_excludes (dictCellT_view h)

private theorem bounds_exclude {ks : List KeyBound} (hk : ks.any excludesProto = true) {n W v}
    (h : ∀ K ∈ ks, ownKeysT K n W v) : ¬ OwnsProto v := by
  obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hk
  exact ownKeys_excludes he (h b hb)

private theorem notObj {v : Val} (h : ∀ flds r oid, v ≠ .objAt flds r oid) : ¬ OwnsProto v := by
  rintro ⟨flds, r, oid, he, _⟩
  exact h flds r oid he

/-- **A proto-free clause's members own no prototype**, at every
interpretation of its operands. -/
theorem clause_sound {α : Type} {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {c : Clause α}
    (hc : clause c = true) {n W v} (h : semWithArgs Ξ X P c n W v) : ¬ OwnsProto v := by
  match c, hc, h with
  | .boolLit b, _, h =>
    exact notObj fun _ _ _ he => by
      simp only [semWithArgs] at h; cases b <;> simp at h <;> subst h <;> cases he
  | .nul, _, h | .undef, _, h | .numLit _, _, h | .strLit _, _, h
  | .bigintLit _, _, h | .symbolLit _, _, h =>
    exact notObj fun _ _ _ he => by simp only [semWithArgs, nulT, undefT] at h; subst h; cases he
  | .bool, _, h =>
    exact notObj fun _ _ _ he => by
      simp only [semWithArgs, boolT] at h; rcases h with rfl | rfl <;> cases he
  | .num, _, h | .str, _, h | .bigint, _, h | .symbol, _, h =>
    exact notObj fun _ _ _ he => by
      simp only [semWithArgs, numT, strT, bigintT, symbolT] at h; obtain ⟨_, rfl⟩ := h; cases he
  | .numIn _, _, h | .strIn _, _, h =>
    exact notObj fun _ _ _ he => by
      simp only [semWithArgs] at h; obtain ⟨_, _, rfl⟩ := h; cases he
  | .refs _ _ _ _ _ ks _, hc, h => exact bounds_exclude (by simpa [clause, primitive] using hc) h.2.2.2.2.1
  | .dict _ _ _ ds _ _ ks cs _, hc, h =>
    obtain ⟨_, _, ⟨hd, hcs⟩, _, _, hks, -⟩ := h
    simp only [clause, primitive, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨d, hd'⟩ := List.exists_mem_of_ne_nil ds hc
      exact dictView_excludes (hd d hd')
    · obtain ⟨d, hd'⟩ := List.exists_mem_of_ne_nil cs hc
      exact dictCell_excludes (hcs d hd')
    · exact bounds_exclude hc hks

/-- A list of clauses each proto-free: no member of their union owns a
prototype. -/
theorem list_sound {α : Type} {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {L : List (Clause α)}
    (hL : L.all clause = true) {n W v} (h : semList Ξ X P L n W v) : ¬ OwnsProto v := by
  obtain ⟨c, hc, hv⟩ := h
  exact clause_sound (List.all_eq_true.mp hL c hc) hv

end Verification.ProtoFree
