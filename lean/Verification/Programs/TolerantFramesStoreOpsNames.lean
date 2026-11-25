import Verification.Programs.TolerantFramesStoreOpsBelow
import Verification.Programs.TolerantFramesMergeHolds

/-! # Tolerant frames: the names the eliminations give

The facts `HeapKnowledge.eliminateIndices`, `restateReads` and
`restateSpines` derive name only what their inputs name: the eliminated
linear facts keep the terms an input atom states defined (`termDefined`),
under a condition an input atom has; a restatement through reads roots a
term at the cell of a read link. So the names of the facts a store
operation derives are names of the store's facts, and below the pass's
counter where those are (`drop_below`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations HeapKnowledge PositiveGraphs
open Verification.SinglePass (Atom Store State)

/-! ## Renamings name the images -/

theorem indexShift_mapM_slots {f : Nat → Option Nat} {sh sh' : IndexShift} (h : sh.mapM f = some sh') :
    ∀ y ∈ sh'.slots, ∃ x ∈ sh.slots, f x = some y := by
  cases sh with
  | mk ts off =>
    simp only [IndexShift.mapM, Option.map_eq_some_iff] at h
    obtain ⟨ts', hts, rfl⟩ := h
    intro y hy
    simp only [IndexShift.slots, List.mem_flatMap] at hy ⊢
    obtain ⟨⟨t', c'⟩, ht', hy⟩ := hy
    have hpair : ∀ {a b : Linear.Form Term},
        a.mapM (fun (t, c) => (t.mapM f).map (·, c)) = some b →
        ∀ p ∈ b, ∃ q ∈ a, q.1.mapM f = some p.1 := by
      intro a
      induction a with
      | nil => intro b h0 p hp; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h0; subst h0; cases hp
      | cons q rest ih =>
        intro b h0 p hp
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h0
        obtain ⟨_, ⟨t1, ht1, rfl⟩, rest', hrest, rfl⟩ := h0
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨q, List.mem_cons_self .., ht1⟩
        · obtain ⟨q0, hq0, hm⟩ := ih hrest p hp
          exact ⟨q0, List.mem_cons_of_mem _ hq0, hm⟩
    obtain ⟨q, hq, hqm⟩ := hpair hts (t', c') ht'
    obtain ⟨x, hx, e⟩ := Term.mapM_slots hqm y hy
    exact ⟨x, ⟨q, hq, hx⟩, e⟩

theorem bound_mapM_slots {f : Nat → Option Nat} {b b' : Bound} (h : b.mapM f = some b') :
    ∀ y ∈ b'.slots, ∃ x ∈ b.slots, f x = some y := by
  cases b with
  | free t =>
    simp only [Bound.mapM, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    exact Term.mapM_slots ht
  | parallel s p sh k ep =>
    simp only [Bound.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨s', hs, sh', hsh, rfl⟩ := h
    intro y hy
    simp only [Bound.slots, List.mem_cons] at hy ⊢
    rcases hy with rfl | hy
    · exact ⟨s, .inl rfl, hs⟩
    · obtain ⟨x, hx, e⟩ := indexShift_mapM_slots hsh y hy
      exact ⟨x, .inr hx, e⟩
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

theorem bodyClause_mapM_slots {f : Nat → Option Nat} :
    ∀ {B B' : BodyClause}, B.mapM f = some B' → ∀ y ∈ B'.slots, ∃ x ∈ B.slots, f x = some y
  | .clause F, B', h => by
    simp only [BodyClause.mapM, Option.map_eq_some_iff] at h
    obtain ⟨F', hF, rfl⟩ := h
    intro y hy
    obtain ⟨b', hb', hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨b, hb, hbm⟩ := clause_mapVars_vars hF b' hb'
    obtain ⟨x, hx, e⟩ := bound_mapM_slots hbm y hy
    exact ⟨x, List.mem_flatMap.mpr ⟨b, hb, hx⟩, e⟩
  | .guarded (.self ep) g b, B', h => by
    simp only [BodyClause.mapM, ElemTarget.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, rfl, b', hb, rfl⟩ := h
    intro y hy
    simp only [BodyClause.slots, ElemTarget.slots, List.nil_append] at hy ⊢
    exact bodyClause_mapM_slots hb y hy
  | .guarded (.parallel s p sh ep) g b, B', h => by
    simp only [BodyClause.mapM, ElemTarget.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, ⟨s', hs, sh', hsh, rfl⟩, b', hb, rfl⟩ := h
    intro y hy
    simp only [BodyClause.slots, ElemTarget.slots, List.cons_append, List.mem_cons, List.mem_append] at hy ⊢
    rcases hy with rfl | hy | hy
    · exact ⟨s, .inl rfl, hs⟩
    · obtain ⟨x, hx, e⟩ := indexShift_mapM_slots hsh y hy; exact ⟨x, .inr (.inl hx), e⟩
    · obtain ⟨x, hx, e⟩ := bodyClause_mapM_slots hb y hy; exact ⟨x, .inr (.inr hx), e⟩
  | .either A B, B', h => by
    simp only [BodyClause.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A', hA, B', hB, rfl⟩ := h
    intro y hy
    simp only [BodyClause.slots, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · obtain ⟨x, hx, e⟩ := bodyClause_mapM_slots hA y hy; exact ⟨x, .inl hx, e⟩
    · obtain ⟨x, hx, e⟩ := bodyClause_mapM_slots hB y hy; exact ⟨x, .inr hx, e⟩

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
  | every s p start stop body =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s', hs, start', hstart, stop', hstop, body', hb, rfl⟩ := h
    simp only [IndexFact.slots, List.mem_cons, List.mem_append, List.mem_flatMap] at hy ⊢
    rcases hy with ((rfl | hy) | hy) | ⟨C', hC', hy⟩
    · exact ⟨s, .inl (.inl (.inl rfl)), hs⟩
    · cases hsb : start.base with
      | none =>
        simp only [IndexBound.mapM, hsb, Option.some.injEq] at hstart
        subst hstart; simp [IndexBound.slots, hsb] at hy
      | some t =>
        simp only [IndexBound.mapM, hsb, Option.map_eq_some_iff] at hstart
        obtain ⟨t', ht', rfl⟩ := hstart
        obtain ⟨x, hx, e⟩ := Term.mapM_slots ht' y hy
        exact ⟨x, .inl (.inl (.inr (by simp [IndexBound.slots, hsb, hx]))), e⟩
    · cases hsb : stop.base with
      | none =>
        simp only [IndexBound.mapM, hsb, Option.some.injEq] at hstop
        subst hstop; simp [IndexBound.slots, hsb] at hy
      | some t =>
        simp only [IndexBound.mapM, hsb, Option.map_eq_some_iff] at hstop
        obtain ⟨t', ht', rfl⟩ := hstop
        obtain ⟨x, hx, e⟩ := Term.mapM_slots ht' y hy
        exact ⟨x, .inl (.inr (by simp [IndexBound.slots, hsb, hx])), e⟩
    · obtain ⟨C, hC, hCm⟩ := (IndexFact.mapBody_pairs hb).1 C' hC'
      obtain ⟨x, hx, e⟩ := bodyClause_mapM_slots hCm y hy
      exact ⟨x, .inr ⟨C, hC, hx⟩, e⟩
  | atIndex s p idx g body =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s', hs, idx', hidx, body', hb, rfl⟩ := h
    simp only [IndexFact.slots] at hy ⊢
    rcases List.mem_cons.mp hy with h1 | hy
    · subst h1; exact ⟨s, List.mem_cons_self .., hs⟩
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨x, hx, e⟩ := indexShift_mapM_slots hidx y hy
      exact ⟨x, List.mem_cons_of_mem _ (List.mem_append_left _ hx), e⟩
    · obtain ⟨b', hb', hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨b, hb0, hbm⟩ := clause_mapVars_vars hb b' hb'
      obtain ⟨x, hx, e⟩ := bound_mapM_slots hbm y hy
      exact ⟨x, List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨b, hb0, hx⟩)), e⟩
  | element v a idx =>
    intro F' h y hy
    simp only [IndexFact.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v', hv, a', ha, idx', hidx, rfl⟩ := h
    simp only [IndexFact.slots, List.mem_cons] at hy ⊢
    rcases hy with rfl | rfl | hy
    · exact ⟨v, .inl rfl, hv⟩
    · exact ⟨a, .inr (.inl rfl), ha⟩
    · obtain ⟨x, hx, e⟩ := indexShift_mapM_slots hidx y hy
      exact ⟨x, .inr (.inr hx), e⟩
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
  · have hint : intSlot as t.slot = true → NamedIn as t.slot := by
      intro hi
      unfold intSlot at hi
      simp only [List.any_eq_true, Bool.and_eq_true] at hi
      obtain ⟨a, ha, -, hf⟩ := hi
      refine namedIn_of_slots ha ?_
      split at hf
      · rename_i k hk; simp only [beq_iff_eq] at hf; simp [IndexFact.slots, hk, hf]
      · rename_i y n hk; simp only [beq_iff_eq] at hf; simp [IndexFact.slots, hk, hf]
      · rename_i F hk
        simp only [List.contains_iff_mem] at hf
        simp only [hk, IndexFact.slots, List.mem_flatMap]
        exact ⟨_, hf, by simp [Term.slots, Term.value]⟩
      · cases hf
    revert hk
    cases t.kind <;> intro hk <;> try (cases hk; done)
    · exact hint hk
    · simp only [List.any_eq_true, Bool.and_eq_true] at hk
      obtain ⟨a, ha, -, hf⟩ := hk
      refine namedIn_of_slots ha ?_
      split at hf
      · rename_i y n hk; simp only [beq_iff_eq] at hf; simp [IndexFact.slots, hk, hf]
      · cases hf
    · exact hint (Bool.and_eq_true_iff.mp hk).2
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

theorem bridgeRead_cell {ls : HeapLinks.Links} {r : Nat × String × Nat} (hr : r ∈ bridgeReads ls) : LinkNamed ls r.1 := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hr
  split at hgm
  · cases hgm
  · split at hgm
    · cases hgm; exact ⟨g, hg, .inl rfl⟩
    · cases hgm

theorem restateAtIndex_named {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {b : IndexAtom}
    (hb : b ∈ restateAtIndex ls dropped as) {x : Nat} (hx : x ∈ (Atom.index b).names) :
    NamedIn as x ∨ LinkNamed ls x := by
  have hdropTerm : ∀ {a : IndexAtom}, a ∈ as → ∀ {t t' : Term},
      (∀ z ∈ t.slots, z ∈ a.fact.slots) →
      liftDropped dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
        ((bridgeReads ls).filter fun g => dropped g.2.2).length t = some t' →
      ∀ z ∈ t'.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha t t' hts hl z hz
    rcases liftDropped_slot _ _ _ hl with rfl | ⟨r, hr, e⟩
    · exact .inl (namedIn_of_slots ha (hts z hz))
    · obtain ⟨-, rfl⟩ := Term.mem_slots.mp hz
      exact .inr (e ▸ bridgeRead_cell (List.mem_filter.mp hr).1)
  have hdropShift : ∀ {a : IndexAtom}, a ∈ as → ∀ {sh sh' : IndexShift},
      (∀ z ∈ sh.slots, z ∈ a.fact.slots) →
      liftDroppedShift dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
        ((bridgeReads ls).filter fun g => dropped g.2.2).length sh = some sh' →
      ∀ z ∈ sh'.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha sh sh' hshs hl z hz
    simp only [liftDroppedShift, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨ts', hts', rfl⟩ := hl
    simp only [IndexShift.slots, List.mem_flatMap] at hz
    obtain ⟨⟨t', c'⟩, ht', htz⟩ := hz
    have hmem : ∀ {l1 l2 : Linear.Form Term},
        l1.mapM (fun (t, c) => (liftDropped dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
          ((bridgeReads ls).filter fun g => dropped g.2.2).length t).map (·, c)) = some l2 →
        ∀ p ∈ l2, ∃ q ∈ l1, liftDropped dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
          ((bridgeReads ls).filter fun g => dropped g.2.2).length q.1 = some p.1 := by
      intro l1
      induction l1 with
      | nil => intro l2 h0 p hp; simp at h0; subst h0; cases hp
      | cons hd tl ih =>
        intro l2 h0 p hp
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h0
        obtain ⟨_, ⟨u', hu', rfl⟩, tl', htl', rfl⟩ := h0
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hd, List.mem_cons_self .., hu'⟩
        · obtain ⟨q, hq, hql⟩ := ih htl' p hp
          exact ⟨q, List.mem_cons_of_mem _ hq, hql⟩
    obtain ⟨q, hq, hql⟩ := hmem hts' (t', c') ht'
    exact hdropTerm ha (fun y hy => hshs y (List.mem_flatMap.mpr ⟨q, hq, hy⟩)) hql z htz
  have hdropPath : ∀ {a : IndexAtom}, a ∈ as → ∀ {s s' : Nat} {p p' : List String},
      s ∈ a.fact.slots →
      liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
        ((plainReads ls).filter fun g => dropped g.2.2).length (s, p) = some (s', p') →
      NamedIn as s' ∨ LinkNamed ls s' := by
    intro a ha s s' p p' hs hl
    rcases liftPath_slot _ _ _ _ _ hl with rfl | ⟨r, hr, e⟩
    · exact .inl (namedIn_of_slots ha hs)
    · exact .inr (e ▸ plainRead_cell (List.mem_filter.mp hr).1)
  have habs : ∀ {a : IndexAtom}, a ∈ as → ∀ {r : Nat} {lenSlots : List Nat} {maskSlots : List (Nat × Nat)} {t : Term} {bd : Bound},
      (∀ z ∈ t.slots, z ∈ a.fact.slots) →
      abstractAtElem r lenSlots maskSlots dropped ((bridgeReads ls).filter fun g => dropped g.2.2) t = some bd →
      ∀ z ∈ bd.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha r lenSlots maskSlots t bd hts hab z hz
    unfold abstractAtElem at hab
    split at hab
    · split at hab
      · cases hab; simp [Bound.slots] at hz
      · cases hab; simp [Bound.slots] at hz
    · split at hab
      · cases hab; simp [Bound.slots] at hz
      · split at hab
        · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hab
          simp [Bound.slots] at hz
        · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hab
          exact hdropTerm ha hts ht' z hz
  simp only [restateAtIndex, List.mem_append] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · split at hb
    · cases hb
    · obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp hb
      split at hab
      · split at hab
        · rename_i s p idx g body hf
          split at hab
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hab
            obtain ⟨⟨s', p'⟩, hsp, idx', hidx, body', hbody, rfl⟩ := hab
            simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil] at hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hdropPath ha (by simp [hf, IndexFact.slots]) hsp
            rcases List.mem_append.mp hx with hx | hx
            · exact hdropShift ha (fun z hz => by simp [hf, IndexFact.slots, hz]) hidx x hx
            · obtain ⟨bd', hbd', hzx⟩ := List.mem_flatMap.mp hx
              obtain ⟨bd, hbd, hmap⟩ := LinearClause.mapVars_vars hbody bd' hbd'
              cases bd with
              | free t =>
                obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hmap
                exact hdropTerm ha (fun z hz => by
                  simp only [hf, IndexFact.slots]
                  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨.free t, hbd, hz⟩))) ht' x hzx
              | parallel s1 p1 sh1 k1 ep1 =>
                cases hmap
                exact .inl ⟨a, ha, by
                  simp only [Atom.names, hf, IndexFact.slots]
                  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _
                    (List.mem_flatMap.mpr ⟨Bound.parallel s1 p1 sh1 k1 ep1, hbd, hzx⟩)))⟩
              | index | elem | offset _ | project _ _ => cases hmap; simp [Bound.slots] at hzx
          · cases hab
        · cases hab
      · cases hab
  · split at hb
    · cases hb
    · obtain ⟨⟨r0, x0, j0⟩, hmem, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨be, hbe, hbem⟩ := List.mem_filterMap.mp hmem
      split at hbem
      · split at hbem
        · rename_i r x0' j0' hfe
          split at hbem
          · simp only [Option.some.injEq, Prod.mk.injEq] at hbem
            obtain ⟨rfl, rfl, rfl⟩ := hbem
            split at hb
            · rename_i x' p' idx' hxp hidx
              rcases List.mem_append.mp hb with hml | hb
              · obtain ⟨⟨ms, mask⟩, hmsm, hml⟩ := List.mem_flatMap.mp hml
                split at hml
                · obtain ⟨bm, hbm, hbmm⟩ := List.mem_filterMap.mp hmsm
                  have hmsIn : NamedIn as ms := by
                    split at hbmm
                    · cases hm1 : matchMaskLe r bm.fact with
                      | none => simp [hm1] at hbmm
                      | some q1 =>
                        obtain ⟨ms', mask'⟩ := q1
                        simp only [hm1] at hbmm
                        split at hbmm
                        · simp only [Option.some.injEq, Prod.mk.injEq] at hbmm
                          obtain ⟨rfl, rfl⟩ := hbmm
                          unfold matchMaskLe at hm1
                          split at hm1
                          · rename_i t1 t2 hf1'
                            split at hm1
                            · rename_i hts
                              cases ht2k : t2.kind <;> rw [ht2k] at hm1 <;> simp at hm1
                              obtain ⟨rfl, rfl⟩ := hm1
                              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hts
                              exact namedIn_of_slots hbm (by
                                simp only [hf1', IndexFact.slots, Linear.Fact.vars, List.map_cons, List.map_nil,
                                  List.flatMap_cons, List.mem_append]
                                exact .inl (by simp [Term.slots, hts.1.1.1.1.1]))
                            · cases hm1
                          · cases hm1
                        · cases hbmm
                    · cases hbmm
                  rcases List.mem_cons.mp hml with rfl | hml
                  · simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, LinearClause.vars,
                      Linear.Fact.vars, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, Bound.slots,
                      List.nil_append, List.append_nil] at hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hdropPath hbe (by simp [hfe, IndexFact.slots]) hxp
                    rcases List.mem_append.mp hx with hx | hx
                    · exact hdropShift hbe (fun z hz => by simp [hfe, IndexFact.slots, hz]) hidx x hx
                    · simp only [Term.value, Term.slots, Bool.false_eq_true, ite_false, List.mem_singleton] at hx
                      subst hx; exact .inl hmsIn
                  · simp only [List.mem_singleton] at hml; subst hml
                    simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, LinearClause.vars,
                      Linear.Fact.vars, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, Bound.slots] at hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hdropPath hbe (by simp [hfe, IndexFact.slots]) hxp
                    rcases List.mem_append.mp hx with hx | hx
                    · exact hdropShift hbe (fun z hz => by simp [hfe, IndexFact.slots, hz]) hidx x hx
                    · simp only [Term.value, Term.slots, Bool.false_eq_true, ite_false, List.mem_singleton] at hx
                      subst hx; exact .inl hmsIn
                · cases hml
              · obtain ⟨ba, hba, hab⟩ := List.mem_filterMap.mp hb
                split at hab
                · split at hab
                  · rename_i F hfa
                    split at hab
                    · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
                      simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, LinearClause.vars] at hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hdropPath hbe (by simp [hfe, IndexFact.slots]) hxp
                      rcases List.mem_append.mp hx with hx | hx
                      · exact hdropShift hbe (fun z hz => by simp [hfe, IndexFact.slots, hz]) hidx x hx
                      · obtain ⟨bd', hbd', hzx⟩ := List.mem_flatMap.mp hx
                        obtain ⟨t, ht, hmap⟩ := Linear.Fact.mapVars_vars hF' bd' hbd'
                        exact habs hba (fun z hz => by
                          simp only [hfa, IndexFact.slots, List.mem_flatMap]; exact ⟨t, ht, hz⟩) hmap x hzx
                    · cases hab
                  · rename_i s g F hfa
                    split at hab
                    · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
                      simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, LinearClause.vars] at hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hdropPath hbe (by simp [hfe, IndexFact.slots]) hxp
                      rcases List.mem_append.mp hx with hx | hx
                      · exact hdropShift hbe (fun z hz => by simp [hfe, IndexFact.slots, hz]) hidx x hx
                      · obtain ⟨bd', hbd', hzx⟩ := List.mem_flatMap.mp hx
                        obtain ⟨t, ht, hmap⟩ := Linear.Fact.mapVars_vars hF' bd' hbd'
                        exact habs hba (fun z hz => by
                          simp only [hfa, IndexFact.slots, List.mem_cons, List.mem_flatMap]; exact .inr ⟨t, ht, hz⟩) hmap x hzx
                    · cases hab
                  · cases hab
                · cases hab
            · cases hb
          · cases hbem
        · cases hbem
      · cases hbem
  · split at hb
    · cases hb
    · obtain ⟨be, hbe, hb⟩ := List.mem_flatMap.mp hb
      split at hb
      · split at hb
        · rename_i r x0 j0 hfe
          split at hb
          · split at hb
            · rename_i x' p' idx' hxp hidx
              rcases List.mem_cons.mp hb with rfl | hb
              · simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, LinearClause.vars,
                  Linear.Fact.vars, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, Bound.slots,
                  List.nil_append, List.append_nil] at hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hdropPath hbe (by simp [hfe, IndexFact.slots]) hxp
                rcases List.mem_append.mp hx with hx | hx
                · exact hdropShift hbe (fun z hz => by simp [hfe, IndexFact.slots, hz]) hidx x hx
                · simp only [Term.value, Term.slots, Bool.false_eq_true, ite_false, List.mem_singleton] at hx
                  subst hx; exact .inl (namedIn_of_slots hbe (by simp [hfe, IndexFact.slots]))
              · simp only [List.mem_singleton] at hb; subst hb
                simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil, LinearClause.vars,
                  Linear.Fact.vars, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, Bound.slots] at hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hdropPath hbe (by simp [hfe, IndexFact.slots]) hxp
                rcases List.mem_append.mp hx with hx | hx
                · exact hdropShift hbe (fun z hz => by simp [hfe, IndexFact.slots, hz]) hidx x hx
                · simp only [Term.value, Term.slots, Bool.false_eq_true, ite_false, List.mem_singleton] at hx
                  subst hx; exact .inl (namedIn_of_slots hbe (by simp [hfe, IndexFact.slots]))
            · cases hb
          · cases hb
        · cases hb
      · cases hb
  · obtain ⟨b1, hb1, hb⟩ := List.mem_flatMap.mp hb
    split at hb
    · cases hm1 : matchAtIndexSlotEq dropped b1.fact with
      | none => simp [hm1] at hb
      | some q =>
        obtain ⟨s, p, idx, bd, ms⟩ := q
        simp only [hm1] at hb
        have hbdSlots : bd.slots = [] ∧ s ∈ b1.fact.slots ∧ ∀ z ∈ idx.slots, z ∈ b1.fact.slots := by
          unfold matchAtIndexSlotEq at hm1
          split at hm1
          · rename_i s' p' idx' bd' t' hfeq
            split at hm1
            · rename_i hts
              simp only [Option.some.injEq, Prod.mk.injEq] at hm1
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hm1
              simp only [Bool.and_eq_true] at hts
              have hbd0 : bd'.slots = [] := by
                cases bd' with
                | elem => rfl
                | project _ ep => cases ep with | nil => rfl | cons _ _ => simp [Bound.isDirectProj] at hts
                | _ => simp [Bound.isDirectProj] at hts
              exact ⟨hbd0, by simp [hfeq, IndexFact.slots], fun z hz => by simp [hfeq, IndexFact.slots, hz]⟩
            · cases hm1
          · cases hm1
        split at hb
        · obtain ⟨bf, hbf, hb⟩ := List.mem_filterMap.mp hb
          split at hb
          · rename_i F hff
            split at hb
            · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hb
              simp only [Atom.names, IndexFact.slots, LinearClause.vars] at hx
              rcases List.mem_append.mp hx with hx | hcondX
              · rcases List.mem_cons.mp hx with rfl | hx
                · exact .inl (namedIn_of_slots hb1 hbdSlots.2.1)
                rcases List.mem_append.mp hx with hx | hx
                · exact .inl (namedIn_of_slots hb1 (hbdSlots.2.2 x hx))
                · obtain ⟨bd', hbd', hzx⟩ := List.mem_flatMap.mp hx
                  obtain ⟨t, ht, hmap⟩ := Linear.Fact.mapVars_vars hF' bd' hbd'
                  split at hmap
                  · cases hmap; rw [hbdSlots.1] at hzx; cases hzx
                  · split at hmap
                    · cases hmap
                    · cases hmap
                      exact .inl (namedIn_of_slots hbf (by simp only [hff, IndexFact.slots, List.mem_flatMap]; exact ⟨t, ht, hzx⟩))
              · exact .inl ⟨bf, hbf, by simp [Atom.names, hcondX]⟩
            · cases hb
          · cases hb
        · cases hb
    · cases hb

/-- **A quantified-fact restatement through reads names its input's names or a
read's cell** (`restateEvery`). -/
theorem restateEvery_named {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {b : IndexAtom}
    (hb : b ∈ restateEvery ls dropped as) {x : Nat} (hx : x ∈ (Atom.index b).names) :
    NamedIn as x ∨ LinkNamed ls x := by
  have hdropTerm : ∀ {a : IndexAtom}, a ∈ as → ∀ {t t' : Term},
      (∀ z ∈ t.slots, z ∈ a.fact.slots) →
      liftDropped dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
        ((bridgeReads ls).filter fun g => dropped g.2.2).length t = some t' →
      ∀ z ∈ t'.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha t t' hts hl z hz
    rcases liftDropped_slot _ _ _ hl with rfl | ⟨r, hr, e⟩
    · exact .inl (namedIn_of_slots ha (hts z hz))
    · obtain ⟨-, rfl⟩ := Term.mem_slots.mp hz
      exact .inr (e ▸ bridgeRead_cell (List.mem_filter.mp hr).1)
  have hdropShift : ∀ {a : IndexAtom}, a ∈ as → ∀ {sh sh' : IndexShift},
      (∀ z ∈ sh.slots, z ∈ a.fact.slots) →
      liftDroppedShift dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
        ((bridgeReads ls).filter fun g => dropped g.2.2).length sh = some sh' →
      ∀ z ∈ sh'.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha sh sh' hshs hl z hz
    simp only [liftDroppedShift, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hl
    obtain ⟨ts', hts', rfl⟩ := hl
    simp only [IndexShift.slots, List.mem_flatMap] at hz
    obtain ⟨⟨t', c'⟩, ht', htz⟩ := hz
    have hmem : ∀ {l1 l2 : Linear.Form Term},
        l1.mapM (fun (t, c) => (liftDropped dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
          ((bridgeReads ls).filter fun g => dropped g.2.2).length t).map (·, c)) = some l2 →
        ∀ p ∈ l2, ∃ q ∈ l1, liftDropped dropped ((bridgeReads ls).filter fun g => dropped g.2.2)
          ((bridgeReads ls).filter fun g => dropped g.2.2).length q.1 = some p.1 := by
      intro l1
      induction l1 with
      | nil => intro l2 h0 p hp; simp at h0; subst h0; cases hp
      | cons hd tl ih =>
        intro l2 h0 p hp
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
          Option.pure_def, Option.some.injEq] at h0
        obtain ⟨_, ⟨u', hu', rfl⟩, tl', htl', rfl⟩ := h0
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨hd, List.mem_cons_self, hu'⟩
        · obtain ⟨q, hq, hql⟩ := ih htl' p hp
          exact ⟨q, List.mem_cons_of_mem _ hq, hql⟩
    obtain ⟨q, hq, hql⟩ := hmem hts' (t', c') ht'
    exact hdropTerm ha (fun y hy => hshs y (List.mem_flatMap.mpr ⟨q, hq, hy⟩)) hql z htz
  have hdropPath : ∀ {a : IndexAtom}, a ∈ as → ∀ {s s' : Nat} {p p' : List String},
      s ∈ a.fact.slots →
      liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
        ((plainReads ls).filter fun g => dropped g.2.2).length (s, p) = some (s', p') →
      NamedIn as s' ∨ LinkNamed ls s' := by
    intro a ha s s' p p' hs hl
    rcases liftPath_slot _ _ _ _ _ hl with rfl | ⟨r, hr, e⟩
    · exact .inl (namedIn_of_slots ha hs)
    · exact .inr (e ▸ plainRead_cell (List.mem_filter.mp hr).1)
  have hdropBody : ∀ {a : IndexAtom}, a ∈ as → ∀ {B B' : BodyClause},
      (∀ z ∈ B.slots, z ∈ a.fact.slots) →
      liftDroppedBodyClause dropped ((plainReads ls).filter fun g => dropped g.2.2)
        ((bridgeReads ls).filter fun g => dropped g.2.2) B = some B' →
      ∀ z ∈ B'.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha B
    induction B with
    | clause c =>
      intro B' hBs hmap z hz
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hmap
      simp only [BodyClause.slots, List.mem_flatMap] at hz
      obtain ⟨bd', hbd', hbz⟩ := hz
      obtain ⟨bd, hbd, hbm⟩ := LinearClause.mapVars_vars hc' bd' hbd'
      have hbdS : ∀ y ∈ bd.slots, y ∈ a.fact.slots := fun y hy =>
        hBs y (List.mem_flatMap.mpr ⟨bd, hbd, hy⟩)
      cases bd with
      | parallel s1 p1 sh1 k1 ep1 =>
        simp only [liftDroppedBound, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hbm
        obtain ⟨⟨s1', p1'⟩, hs1, sh1', hsh1, rfl⟩ := hbm
        rcases List.mem_cons.mp hbz with rfl | hbz
        · exact hdropPath ha (hbdS _ List.mem_cons_self) hs1
        · exact hdropShift ha (fun y hy => hbdS y (List.mem_cons_of_mem _ hy)) hsh1 z hbz
      | free t =>
        obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hbm
        exact hdropTerm ha hbdS ht' z hbz
      | index | elem | offset _ | project _ _ => cases hbm; simp [Bound.slots] at hbz
    | guarded t g inner ih =>
      intro B' hBs hmap z hz
      simp only [liftDroppedBodyClause, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmap
      obtain ⟨t', ht', inner', hi', rfl⟩ := hmap
      simp only [BodyClause.slots, List.mem_append] at hz
      rcases hz with hz | hz
      · cases t with
        | self ep => cases ht'; simp [ElemTarget.slots] at hz
        | parallel s1 p1 sh1 ep1 =>
          simp only [liftDroppedTarget, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at ht'
          obtain ⟨⟨s1', p1'⟩, hs1, sh1', hsh1, rfl⟩ := ht'
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hdropPath ha (hBs _ (List.mem_append_left _ List.mem_cons_self)) hs1
          · exact hdropShift ha (fun y hy => hBs y (List.mem_append_left _ (List.mem_cons_of_mem _ hy))) hsh1 z hz
      · exact ih (fun y hy => hBs y (List.mem_append_right _ hy)) hi' z hz
    | either A B ihA ihB =>
      intro B' hBs hmap z hz
      simp only [liftDroppedBodyClause, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmap
      obtain ⟨A', hA', B'', hB'', rfl⟩ := hmap
      simp only [BodyClause.slots, List.mem_append] at hz
      rcases hz with hz | hz
      · exact ihA (fun y hy => hBs y (List.mem_append_left _ hy)) hA' z hz
      · exact ihB (fun y hy => hBs y (List.mem_append_right _ hy)) hB'' z hz
  have hdropBound : ∀ {a : IndexAtom}, a ∈ as → ∀ {b b' : IndexBound},
      (∀ z ∈ b.slots, z ∈ a.fact.slots) →
      liftDroppedIndexBound dropped ((bridgeReads ls).filter fun g => dropped g.2.2) b = some b' →
      ∀ z ∈ b'.slots, NamedIn as z ∨ LinkNamed ls z := by
    intro a ha b b' hbs hl z hz
    obtain ⟨base, off⟩ := b
    cases base with
    | none =>
      simp only [liftDroppedIndexBound, Option.some.injEq] at hl; subst hl
      simp [IndexBound.slots] at hz
    | some t =>
      simp only [liftDroppedIndexBound, Option.map_eq_some_iff] at hl
      obtain ⟨t', ht', rfl⟩ := hl
      exact hdropTerm ha (fun y hy => hbs y (by simpa [IndexBound.slots] using hy)) ht' z
        (by simpa [IndexBound.slots] using hz)
  unfold restateEvery at hb
  dsimp only at hb
  split at hb
  · cases hb
  · obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp hb
    split at hab
    · split at hab
      · rename_i s p start stop body hf
        split at hab
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hab
          obtain ⟨⟨s', p'⟩, hsp, start', hstart, stop', hstop, body', hbody, rfl⟩ := hab
          simp only [Atom.names, IndexFact.slots, Option.toList_none, List.append_nil] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hdropPath ha (by simp [hf, IndexFact.slots]) hsp
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · exact hdropBound ha (fun z hz => by simp [hf, IndexFact.slots, hz]) hstart x hx
            · exact hdropBound ha (fun z hz => by simp [hf, IndexFact.slots, hz]) hstop x hx
          · obtain ⟨B', hB', hBx⟩ := List.mem_flatMap.mp hx
            have hmem : ∀ {xs ys : List BodyClause}, xs.mapM (liftDroppedBodyClause dropped
                ((plainReads ls).filter fun g => dropped g.2.2) ((bridgeReads ls).filter fun g => dropped g.2.2)) = some ys →
                ∀ y ∈ ys, ∃ u ∈ xs, liftDroppedBodyClause dropped
                  ((plainReads ls).filter fun g => dropped g.2.2) ((bridgeReads ls).filter fun g => dropped g.2.2) u = some y := by
              intro xs
              induction xs with
              | nil => intro ys h0 y hy; cases h0; cases hy
              | cons hd tl ih =>
                intro ys h0 y hy
                simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h0
                obtain ⟨hd', hhd, tl', htl, rfl⟩ := h0
                rcases List.mem_cons.mp hy with rfl | hy
                · exact ⟨hd, List.mem_cons_self, hhd⟩
                · obtain ⟨u, hu, huy⟩ := ih htl y hy
                  exact ⟨u, List.mem_cons_of_mem _ hu, huy⟩
            obtain ⟨B, hB, hBB'⟩ := hmem hbody B' hB'
            exact hdropBody ha (fun z hz => by
              simp only [hf, IndexFact.slots]
              exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨B, hB, hz⟩))) hBB' x hBx
        · cases hab
      · cases hab
    · cases hab

/-- **A spine restatement through reads names its input's names or a read's
cell** (`restateSpines`). -/
theorem restateSpines_named {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {b : IndexAtom}
    (hb : b ∈ restateSpines ls dropped as) {x : Nat} (hx : x ∈ (Atom.index b).names) :
    NamedIn as x ∨ LinkNamed ls x := by
  simp only [restateSpines, List.mem_append] at hb
  rcases hb with (hb | hb) | hb
  · split at hb
    · cases hb
    obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp hb
    have lift : ∀ (u w : Nat) (p q : List String) (c : IndexAtom), u ∈ a.fact.slots → w ∈ a.fact.slots →
        (if dropped (u, p).1 || dropped (w, q).1 then do
          let (x, p) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
            ((plainReads ls).filter fun g => dropped g.2.2).length (u, p)
          let (y, q) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
            ((plainReads ls).filter fun g => dropped g.2.2).length (w, q)
          pure { fact := .spineApart x p y q } else none) = some c →
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
      · rename_i u p w q hf
        exact lift u w p q b (by simp [hf, IndexFact.slots]) (by simp [hf, IndexFact.slots]) hab x hx
      · rename_i u p w q hf
        exact lift u w p q b (by simp [hf, IndexFact.slots]) (by simp [hf, IndexFact.slots]) hab x hx
      · cases hab
    · cases hab
  · exact restateAtIndex_named hb hx
  · exact restateEvery_named hb hx

end Verification.TolerantFrames
