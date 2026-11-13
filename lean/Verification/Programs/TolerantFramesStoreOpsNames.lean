import Verification.Programs.TolerantFramesStoreOpsBelow
import Verification.Programs.TolerantFramesMergeHolds

/-! # Tolerant frames: the names the eliminations give

The facts `HeapKnowledge.eliminateIndices`, `restateReads` and
`restateStores` derive name only what their inputs name: the eliminated
linear facts keep the terms an input atom states defined (`termDefined`),
under a condition an input atom has; a restatement through reads roots a
term at the cell of a read link. So the names of the facts a store
operation derives are names of the store's facts, and below the pass's
counter where those are (`drop_below`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations HeapKnowledge PositiveGraphs
open Verification.SinglePass (Atom Store State)

/-! ## Renamings name the images -/

theorem bound_mapM_slots {f : Nat → Option Nat} {b b' : Bound} (h : b.mapM f = some b') :
    ∀ y ∈ b'.slots, ∃ x ∈ b.slots, f x = some y := by
  cases b with
  | free t =>
    simp only [Bound.mapM, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    exact Term.mapM_slots ht
  | _ =>
    simp only [Bound.mapM, Option.some.injEq] at h
    subst h
    intro y hy; simp [Bound.slots] at hy

theorem clause_mapVars_vars {V W : Type} {g : V → Option W} :
    ∀ {F : LinearClause V} {F' : LinearClause W}, F.mapVars g = some F' →
      ∀ y ∈ F'.vars, ∃ x ∈ F.vars, g x = some y
  | .atom F, F', h => by
    simp only [LinearClause.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G, hG, rfl⟩ := h
    exact Linear.Fact.mapVars_vars hG
  | .either A B, F', h => by
    simp only [LinearClause.mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨A', hA, B', hB, rfl⟩ := h
    intro y hy
    simp only [LinearClause.vars, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · obtain ⟨x, hx, e⟩ := clause_mapVars_vars hA y hy; exact ⟨x, .inl hx, e⟩
    · obtain ⟨x, hx, e⟩ := clause_mapVars_vars hB y hy; exact ⟨x, .inr hx, e⟩

theorem indexFact_mapM_slots {f : Nat → Option Nat} :
    ∀ {F F' : IndexFact}, F.mapM f = some F' → ∀ y ∈ F'.slots, ∃ x ∈ F.slots, f x = some y := by
  intro F
  induction F with
  | linear L =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.map_eq_some_iff] at h
    obtain ⟨L', hL, rfl⟩ := h
    simp only [IndexFact.slots, List.mem_flatMap] at hy ⊢
    obtain ⟨t', ht', hy⟩ := hy
    obtain ⟨t, ht, e⟩ := Linear.Fact.mapVars_vars hL t' ht'
    obtain ⟨x, hx, ex⟩ := Term.mapM_slots e y hy
    exact ⟨x, ⟨t, ht, hx⟩, ex⟩
  | either A B ihA ihB =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A', hA, B', hB, rfl⟩ := h
    simp only [IndexFact.slots, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · obtain ⟨x, hx, e⟩ := ihA hA y hy; exact ⟨x, .inl hx, e⟩
    · obtain ⟨x, hx, e⟩ := ihB hB y hy; exact ⟨x, .inr hx, e⟩
  | guarded s p t B ih =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s', hs, B', hB, rfl⟩ := h
    simp only [IndexFact.slots, List.mem_cons] at hy ⊢
    rcases hy with rfl | hy
    · exact ⟨s, .inl rfl, hs⟩
    · obtain ⟨x, hx, e⟩ := ih hB y hy; exact ⟨x, .inr hx, e⟩
  | every s p stop body =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s', hs, stop', hst, body', hb, rfl⟩ := h
    simp only [IndexFact.slots] at hy ⊢
    rcases List.mem_cons.mp hy with h1 | hy
    · subst h1; exact ⟨s, List.mem_cons_self .., hs⟩
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨x, hx, e⟩ := Term.mapM_slots hst y hy
      exact ⟨x, List.mem_cons_of_mem _ (List.mem_append_left _ hx), e⟩
    · obtain ⟨C', hC', hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨b', hb', hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨C, hC, hCm⟩ := (IndexFact.mapBody_pairs hb).1 C' hC'
      obtain ⟨b, hb0, hbm⟩ := clause_mapVars_vars hCm b' hb'
      obtain ⟨x, hx, e⟩ := bound_mapM_slots hbm y hy
      exact ⟨x, List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨C, hC, List.mem_flatMap.mpr ⟨b, hb0, hx⟩⟩)), e⟩
  | _ =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    first
    | (obtain ⟨a, ha, rfl⟩ := h
       simp only [IndexFact.slots, List.mem_singleton] at hy
       subst hy
       exact ⟨_, by simp [IndexFact.slots], ha⟩)
    | (obtain ⟨a, ha, b, hb, rfl⟩ := h
       simp only [IndexFact.slots, List.mem_cons, List.mem_nil_iff, or_false] at hy
       rcases hy with rfl | rfl
       · exact ⟨_, by simp [IndexFact.slots], ha⟩
       · exact ⟨_, by simp [IndexFact.slots], hb⟩)
    | (obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
       simp only [IndexFact.slots, List.mem_cons, List.mem_nil_iff, or_false] at hy
       rcases hy with rfl | rfl | rfl
       · exact ⟨_, by simp [IndexFact.slots], ha⟩
       · exact ⟨_, by simp [IndexFact.slots], hb⟩
       · exact ⟨_, by simp [IndexFact.slots], hc⟩)

/-- **A renamed fact names the images of its names.** -/
theorem atom_rename_names {f : Nat → Option Nat} {a b : Atom} (h : a.rename f = some b) :
    ∀ y ∈ b.names, ∃ x ∈ a.names, f x = some y := by
  cases a with
  | cell x | value x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    intro y hy; simp only [Atom.names, List.mem_singleton] at hy ⊢; subst hy; exact ⟨_, rfl, hs⟩
  | link g =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, v, hv, rfl⟩ := h
    intro y hy
    simp only [Atom.names, List.mem_cons, List.mem_nil_iff, or_false] at hy ⊢
    rcases hy with rfl | rfl
    · exact ⟨_, .inl rfl, hc⟩
    · exact ⟨_, .inr rfl, hv⟩
  | elem e =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s, hs, c, hc, rfl⟩ := h
    intro y hy
    simp only [Atom.names, List.mem_cons] at hy ⊢
    rcases hy with rfl | hy
    · exact ⟨_, .inl rfl, hs⟩
    · cases hec : e.cond with
      | none => rw [hec] at hc; cases hc; simp at hy
      | some k =>
        rw [hec] at hc
        cases hk : f k with
        | none => simp [hk] at hc
        | some k' =>
          simp [hk] at hc
          subst hc
          simp only [Option.toList_some, List.mem_singleton] at hy
          subst hy
          exact ⟨k, .inr (by simp), hk⟩
  | index x =>
    simp only [Atom.rename, Option.map_eq_some_iff] at h
    obtain ⟨x', hx, rfl⟩ := h
    unfold HeapKnowledge.mapIndex at hx
    intro y hy
    simp only [Atom.names, List.mem_append] at hy ⊢
    split at hx
    · rename_i F hF hc
      cases hx
      rcases hy with hy | hy
      · obtain ⟨z, hz, e⟩ := indexFact_mapM_slots hF y hy; exact ⟨z, .inl hz, e⟩
      · simp [hc] at hy
    · rename_i F c hF hc
      simp only [Option.map_eq_some_iff] at hx
      obtain ⟨c', hc', rfl⟩ := hx
      rcases hy with hy | hy
      · obtain ⟨z, hz, e⟩ := indexFact_mapM_slots hF y hy; exact ⟨z, .inl hz, e⟩
      · simp only [Option.toList_some, List.mem_singleton] at hy
        subst hy
        exact ⟨c, .inr (by simp [hc]), hc'⟩
    · cases hx
  | sep s =>
    simp only [Atom.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨t, ht, ps, hps, rfl⟩ := h
    intro y hy
    simp only [Atom.names, List.mem_cons, List.mem_map] at hy ⊢
    rcases hy with rfl | ⟨⟨p', fs⟩, hp', rfl⟩
    · exact ⟨_, .inl rfl, ht⟩
    · obtain ⟨⟨p, fs0⟩, hp, hpm⟩ := mapM_mem hps _ hp'
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hpm
      obtain ⟨q, hq, rfl, rfl⟩ := hpm
      exact ⟨p, .inr ⟨_, hp, rfl⟩, hq⟩

/-! ## The eliminations' names -/

/-- `x` is a name an atom of `as` states: of its fact or its condition. -/
def NamedIn (as : List IndexAtom) (x : Nat) : Prop := ∃ a ∈ as, x ∈ (Atom.index a).names

theorem namedIn_of_slots {as : List IndexAtom} {a : IndexAtom} (ha : a ∈ as) {x : Nat} (hx : x ∈ a.fact.slots) :
    NamedIn as x := ⟨a, ha, by simp [Atom.names, hx]⟩

/-- **A term an atom states defined is rooted at a name it states**: each
current slot it reads is named. -/
theorem termDefined_named {as : List IndexAtom} {t : Term} (h : termDefined as t = true) :
    ∀ x ∈ t.slots, NamedIn as x := by
  intro x hx
  obtain ⟨he, rfl⟩ := Term.mem_slots.mp hx
  unfold termDefined at h
  simp only [he, Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h
  rcases h with ⟨-, hk⟩ | ⟨a, ha, -, hf⟩
  · revert hk
    cases t.kind <;> intro hk <;> try (cases hk; done)
    · unfold intSlot at hk
      simp only [List.any_eq_true, Bool.and_eq_true] at hk
      obtain ⟨a, ha, -, hf⟩ := hk
      refine namedIn_of_slots ha ?_
      split at hf
      · rename_i k hk; simp only [beq_iff_eq] at hf; simp [IndexFact.slots, hk, hf]
      · rename_i y n hk; simp only [beq_iff_eq] at hf; simp [IndexFact.slots, hk, hf]
      · rename_i F hk
        simp only [List.contains_iff_mem] at hf
        simp only [hk, IndexFact.slots, List.mem_flatMap]
        exact ⟨_, hf, by simp [Term.slots, Term.value]⟩
      · cases hf
    · simp only [List.any_eq_true, Bool.and_eq_true] at hk
      obtain ⟨a, ha, -, hf⟩ := hk
      refine namedIn_of_slots ha ?_
      split at hf
      · rename_i y n hk; simp only [beq_iff_eq] at hf; simp [IndexFact.slots, hk, hf]
      · cases hf
  · refine namedIn_of_slots ha ?_
    split at hf
    · rename_i F hk
      simp only [List.contains_iff_mem] at hf
      simp only [hk, IndexFact.slots, List.mem_flatMap]
      exact ⟨_, hf, by simp [Term.slots, he]⟩
    · cases hf

theorem namedIn_append {as bs : List IndexAtom} {x : Nat} : NamedIn (as ++ bs) x ↔ NamedIn as x ∨ NamedIn bs x := by
  simp only [NamedIn, List.mem_append]
  constructor
  · rintro ⟨a, ha | ha, hx⟩
    · exact .inl ⟨a, ha, hx⟩
    · exact .inr ⟨a, ha, hx⟩
  · rintro (⟨a, ha, hx⟩ | ⟨a, ha, hx⟩)
    · exact ⟨a, .inl ha, hx⟩
    · exact ⟨a, .inr ha, hx⟩

/-- **The linear elimination names what its input names** (`eliminateLinear`):
a derived fact keeps only terms an input atom states defined, under the
condition of an input atom. -/
theorem eliminateLinear_named {D : List Nat} {as : List IndexAtom} {b : IndexAtom} (hb : b ∈ eliminateLinear D as)
    {x : Nat} (hx : x ∈ (Atom.index b).names) : NamedIn as x := by
  unfold eliminateLinear at hb
  split at hb
  · exact ⟨b, hb, hx⟩
  dsimp only at hb
  split at hb
  · exact ⟨b, hb, hx⟩
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · exact ⟨b, hb, hx⟩
    · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hb
      obtain ⟨-, hk⟩ := List.mem_filter.mp hF
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
      simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, List.mem_flatMap] at hx
      obtain ⟨t, ht, hx⟩ := hx
      exact termDefined_named (hk.2 t ht).2 x hx
  · obtain ⟨⟨c, neg⟩, hg, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hb
    obtain ⟨-, hk⟩ := List.mem_filter.mp hF
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
    simp only [Atom.names, IndexFact.slots, Option.toList_some, List.mem_append, List.mem_flatMap,
      List.mem_singleton] at hx
    rcases hx with ⟨t, ht, hx⟩ | rfl
    · exact termDefined_named (hk.2 t ht).2 x hx
    · obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hg)
      refine ⟨a, ha, ?_⟩
      split at hm
      · rename_i c' F' hc hf
        split at hm
        · cases hm
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, -⟩ := hm
          simp [Atom.names, hc]
      · cases hm

theorem releasePast_named {as : List IndexAtom} {b : IndexAtom} (hb : b ∈ releasePast as) {x : Nat}
    (hx : x ∈ (Atom.index b).names) : NamedIn as x := by
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hb
  split at hm
  · rename_i A k hc hf
    split at hm
    · cases hm
      refine namedIn_of_slots ha ?_
      simp only [Atom.names, Option.toList_none, List.append_nil] at hx
      simp [hf, IndexFact.slots, hx]
    · cases hm
  · cases hm

/-- **The elimination names what its input names** (`eliminateIndices`). -/
theorem eliminateIndices_named {D : List Nat} {as : List IndexAtom} {b : IndexAtom} (hb : b ∈ eliminateIndices D as)
    {x : Nat} (hx : x ∈ (Atom.index b).names) : NamedIn as x := by
  rcases namedIn_append.mp (eliminateLinear_named hb hx) with h | ⟨a, ha, hx⟩
  · exact h
  · split at ha
    · exact releasePast_named ha hx
    · cases ha

theorem atomLinear_slots {f : IndexFact} {F : Linear.Fact Term} (hF : F ∈ atomLinear f) :
    ∀ t ∈ F.vars, ∀ x ∈ t.slots, x ∈ f.slots := by
  cases f with
  | linear G =>
    simp only [atomLinear, List.mem_singleton] at hF; subst hF
    intro t ht x hx; simp only [IndexFact.slots, List.mem_flatMap]; exact ⟨t, ht, hx⟩
  | length y n =>
    simp only [atomLinear, List.mem_cons, List.mem_nil_iff, or_false] at hF
    intro t ht x hx
    rcases hF with rfl | rfl <;>
      simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at ht <;> rcases ht with rfl | rfl <;>
      simp_all [IndexFact.slots, Term.value, Term.length, Term.slots]
  | _ => simp [atomLinear] at hF

theorem liftDropped_slot {dropped : Nat → Bool} {reads : List (Nat × String × Nat)} :
    ∀ n t t', liftDropped dropped reads n t = some t' → t' = t ∨ ∃ r ∈ reads, t'.slot = r.1 := by
  intro n
  induction n with
  | zero => intro t t' h; simp only [liftDropped] at h; split at h <;> simp_all
  | succ n ih =>
    intro t t' h
    simp only [liftDropped] at h
    split at h
    · split at h
      · rename_i c f v hfind
        rcases ih _ _ h with h | h
        · subst h; exact .inr ⟨_, List.mem_of_find?_eq_some hfind, rfl⟩
        · exact .inr h
      · cases h
    · cases h; exact .inl rfl

theorem liftPath_slot {dropped : Nat → Bool} {reads : List (Nat × String × Nat)} :
    ∀ n s p s' p', liftPath dropped reads n (s, p) = some (s', p') → s' = s ∨ ∃ r ∈ reads, s' = r.1 := by
  intro n
  induction n with
  | zero => intro s p s' p' h; simp only [liftPath] at h; split at h <;> simp_all
  | succ n ih =>
    intro s p s' p' h
    simp only [liftPath] at h
    split at h
    · split at h
      · rename_i c f v hfind
        rcases ih _ _ _ _ h with h | h
        · exact .inr ⟨_, List.mem_of_find?_eq_some hfind, h⟩
        · exact .inr h
      · cases h
    · cases h; exact .inl rfl

/-- A name a link states as its cell or value. -/
def LinkNamed (ls : HeapLinks.Links) (x : Nat) : Prop := ∃ g ∈ ls, x = g.cell ∨ x = g.value

/-- **A restatement through reads names its input's names or a read's
cell** (`restateReads`). -/
theorem restateReads_named {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {b : IndexAtom}
    (hb : b ∈ restateReads ls dropped as) {x : Nat} (hx : x ∈ (Atom.index b).names) :
    NamedIn as x ∨ LinkNamed ls x := by
  unfold restateReads at hb
  dsimp only at hb
  split at hb
  · cases hb
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨F, hF, hab⟩ := List.mem_filterMap.mp hb
  split at hab
  · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
    simp only [Atom.names, IndexFact.slots, List.mem_append, List.mem_flatMap] at hx
    rcases hx with ⟨t', ht', hx⟩ | hx
    · obtain ⟨t, ht, e⟩ := Linear.Fact.mapVars_vars hF' t' ht'
      rcases liftDropped_slot _ _ _ e with rfl | ⟨r, hr, e⟩
      · exact .inl (namedIn_of_slots ha (atomLinear_slots hF t' ht x hx))
      · obtain ⟨-, rfl⟩ := Term.mem_slots.mp hx
        obtain ⟨hr, -⟩ := List.mem_filter.mp hr
        obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hr
        split at hgm
        · cases hgm
        · split at hgm
          · cases hgm; exact .inr ⟨g, hg, .inl e⟩
          · cases hgm
    · exact .inl ⟨a, ha, by simp [Atom.names, hx]⟩
  · cases hab

theorem plainRead_cell {ls : HeapLinks.Links} {r : Nat × String × Nat} (hr : r ∈ plainReads ls) : LinkNamed ls r.1 := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hr
  split at hgm
  · cases hgm
  · split at hgm
    · cases hgm; exact ⟨g, hg, .inl rfl⟩
    · cases hgm

/-- **A store restatement through reads names its input's names or a read's
cell** (`restateStores`). -/
theorem restateStores_named {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {b : IndexAtom}
    (hb : b ∈ restateStores ls dropped as) {x : Nat} (hx : x ∈ (Atom.index b).names) :
    NamedIn as x ∨ LinkNamed ls x := by
  unfold restateStores at hb
  dsimp only at hb
  split at hb
  · cases hb
  obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp hb
  have lift : ∀ (u w : Nat) (p q : List String) (c : IndexAtom), u ∈ a.fact.slots → w ∈ a.fact.slots →
      (if dropped (u, p).1 || dropped (w, q).1 then do
        let (x, p) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
          ((plainReads ls).filter fun g => dropped g.2.2).length (u, p)
        let (y, q) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
          ((plainReads ls).filter fun g => dropped g.2.2).length (w, q)
        pure { fact := .storeApart x p y q } else none) = some c →
      ∀ x ∈ (Atom.index c).names, NamedIn as x ∨ LinkNamed ls x := by
    intro u w p q c hu hw hc x hx
    split at hc
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hc
      obtain ⟨⟨x1, p1⟩, h1, ⟨y1, q1⟩, h2, rfl⟩ := hc
      simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hx
      have side : ∀ s s' (pp pp' : List String), s ∈ a.fact.slots →
          liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
            ((plainReads ls).filter fun g => dropped g.2.2).length (s, pp) = some (s', pp') →
          NamedIn as s' ∨ LinkNamed ls s' := by
        intro s s' pp pp' hs hl
        rcases liftPath_slot _ _ _ _ _ hl with e | ⟨r, hr, e⟩
        · exact .inl (namedIn_of_slots ha (e ▸ hs))
        · exact .inr (e ▸ plainRead_cell (List.mem_filter.mp hr).1)
      rcases hx with rfl | rfl
      · exact side _ _ _ _ hu h1
      · exact side _ _ _ _ hw h2
    · cases hc
  split at hab
  · split at hab
    · rename_i u w hf
      exact lift u w [] [] b (by simp [hf, IndexFact.slots]) (by simp [hf, IndexFact.slots]) hab x hx
    · rename_i u p w q hf
      exact lift u w p q b (by simp [hf, IndexFact.slots]) (by simp [hf, IndexFact.slots]) hab x hx
    · cases hab
  · cases hab

end Verification.TolerantFrames
