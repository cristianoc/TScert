import Verification.Semantics.HeapSeparation
import Verification.Semantics.IndexFacts
import Verification.Programs.BranchRefinement

/-! Primitive heap and immutable-value facts for expression postconditions. Facts
are execution-state assertions, not extra world contracts or source type labels. -/
namespace Verification.HeapKnowledge

variable {ε : EntryState}
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts

/-- An elements atom: every present element of the array the slot `slot`
holds satisfies `pred` (`CallEffects.ElemsAt`), where the slot `cond`, if
stated, holds a truthy value, or a falsy one where `negated`. -/
structure ElemAtom where
  slot : Nat
  pred : CallEffects.ElemPred
  cond : Option Nat := none
  negated : Bool := false
  deriving DecidableEq, Repr, Hashable


/-- An index atom: its fact, where the slot `cond`, if stated, holds a truthy
value, or a falsy one where `negated`, as an elements atom's condition. -/
structure IndexAtom where
  fact : IndexFact
  cond : Option Nat := none
  negated : Bool := false
  deriving DecidableEq, Repr, Hashable

structure Knowledge where
  cells : Facts := []
  values : Facts := []
  links : HeapLinks.Links := []
  /-- Which locations differ (`HeapSeparation`), addressed by level. -/
  separation : HeapSeparation.Separation := {}
  /-- The elements facts (`ElemAtom`). -/
  elems : List ElemAtom := []
  /-- The index facts (`IndexAtom`). -/
  indices : List IndexAtom := []
  deriving DecidableEq, Repr

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, f.contents.mem (ρ f.slot) = true

def ElemsHolds (as : List ElemAtom) (ρ : Env) (h : Heap) : Prop :=
  ∀ a ∈ as, (∀ b, a.cond = some b → tagHolds .truthy (ρ b) = !a.negated) → CallEffects.ElemsAt a.pred (ρ a.slot) h

def IndexHolds (ε : EntryState) (as : List IndexAtom) (ρ : Env) (h : Heap) : Prop :=
  ∀ a ∈ as, (∀ b, a.cond = some b → tagHolds .truthy (ρ b) = !a.negated) → a.fact.HoldsAt ε ρ h

def Holds (k : Knowledge) (ε : EntryState) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ ∧ HeapLinks.Holds k.links ρ h ∧
    HeapSeparation.Holds k.separation ρ ∧ ElemsHolds k.elems ρ h ∧ IndexHolds ε k.indices ρ h

/-- The knowledge read at the entry state itself: each index fact without
entry terms (`IndexFact.toNow`). -/
def Knowledge.toNow (k : Knowledge) : Knowledge :=
  { k with indices := k.indices.map fun a => { a with fact := a.fact.toNow } }

/-- **At the entry state, knowledge holds as its restatement without entry
terms does** (`IndexFact.holdsAt_toNow`). -/
theorem holds_toNow {k : Knowledge} {ρ : Env} {h : Heap} (hρ : ε.env = ρ) (hh : ε.heap = h) :
    Holds k.toNow ε ρ h ↔ Holds k ε ρ h := by
  simp only [Holds, Knowledge.toNow, IndexHolds, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))))
  exact forall_congr' fun a => imp_congr_right fun _ => imp_congr_right fun _ => IndexFact.holdsAt_toNow hρ hh

theorem elemsHolds_nil (ρ h) : ElemsHolds [] ρ h := by simp [ElemsHolds]

theorem indexHolds_nil (ρ h) : IndexHolds ε [] ρ h := by simp [IndexHolds]

theorem indexHolds_extend {as : List IndexAtom} {ρ h} (vs : List Val) (he : IndexHolds ε as ρ h) :
    IndexHolds ε as ρ (h ++ vs) := fun a ha hc => IndexFact.holdsAt_extend vs (he a ha hc)

/-- An atom renamed by a partial map, where it maps every slot the atom names. -/
def mapIndex (f : Nat → Option Nat) (a : IndexAtom) : Option IndexAtom :=
  match a.fact.mapM f, a.cond with
  | some F, none => some { a with fact := F }
  | some F, some c => (f c).map fun c' => { a with fact := F, cond := some c' }
  | none, _ => none

/-- Atoms renamed by a partial map, kept where every slot maps. -/
def mapIndices (f : Nat → Option Nat) (as : List IndexAtom) : List IndexAtom :=
  as.filterMap (mapIndex f)

/-- Renaming keeps the atoms where each renamed slot holds its source slot's value. -/
theorem mapIndices_holds {as : List IndexAtom} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s t, f s = some t → ρ' t = ρ s) (he : IndexHolds ε as ρ h) :
    IndexHolds ε (mapIndices f as) ρ' h := by
  intro a ha hc
  obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
  unfold mapIndex at hab
  split at hab
  · rename_i F hF hcb
    cases hab
    exact (IndexFact.holdsAt_mapM hF (fun s _ t ht => hf s t ht)).mpr (he b hb (by simp [hcb]))
  · rename_i F c hF hcb
    simp only [Option.map_eq_some_iff] at hab
    obtain ⟨t, ht, rfl⟩ := hab
    refine (IndexFact.holdsAt_mapM hF (fun s _ t ht => hf s t ht)).mpr (he b hb ?_)
    intro d hd
    rw [hcb] at hd
    cases hd
    rw [← hf c t ht]
    exact hc t rfl
  · cases hab

theorem empty (ρ h) : Holds {} ε ρ h :=
  ⟨holds_nil ρ h,by simp [ValueHolds],by simp [HeapLinks.Holds],HeapSeparation.empty_holds ρ,elemsHolds_nil ρ h,
    indexHolds_nil ρ h⟩

/-- A heap extension keeps an elements fact: the store and every element
location lie in the old heap. -/
theorem elemsAt_extend {R : CallEffects.ElemPred} {r : Tm} {h : Heap} (vs : List Val)
    (he : CallEffects.ElemsAt R r h) : CallEffects.ElemsAt R r (h ++ vs) := by
  obtain ⟨s, ls, hs, hl, hall⟩ := he
  refine ⟨s, ls, hs, ?_, fun l hm => ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl
  · obtain ⟨v, hv, hr⟩ := hall l hm
    exact ⟨v, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv, hr⟩

theorem elemsHolds_extend {as : List ElemAtom} {ρ h} (vs : List Val) (he : ElemsHolds as ρ h) :
    ElemsHolds as ρ (h ++ vs) := fun a ha hc => elemsAt_extend vs (he a ha hc)

/-- Atoms about slots past the pushed one. -/
def shiftElems (as : List ElemAtom) : List ElemAtom :=
  as.map fun a => { a with slot := a.slot + 1, cond := a.cond.map (· + 1) }

theorem shiftElems_holds {as : List ElemAtom} {ρ h v} (he : ElemsHolds as ρ h) :
    ElemsHolds (shiftElems as) (push v ρ) h := by
  intro a ha hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact he b hb fun c hc' => hc (c + 1) (by simp [hc'])

/-- Atoms about slots below the dropped slot 0, restated one lower. -/
def dropElems (as : List ElemAtom) : List ElemAtom :=
  (as.filter fun a => 0 < a.slot && a.cond.all (0 < ·)).map fun a =>
    { a with slot := a.slot - 1, cond := a.cond.map (· - 1) }

theorem dropElems_holds {as : List ElemAtom} {ρ h v} (he : ElemsHolds as (push v ρ) h) :
    ElemsHolds (dropElems as) ρ h := by
  intro a ha hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hb, hp⟩ := List.mem_filter.mp hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.all_eq_true] at hp
  have hs : push v ρ b.slot = ρ (b.slot - 1) := by
    obtain ⟨i, hi⟩ : ∃ i, b.slot = i + 1 := ⟨b.slot - 1, by omega⟩
    rw [hi]; rfl
  have := he b hb fun c hc' => by
    have hc0 := hp.2 c hc'
    obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
    exact hc i (by simp [hc'])
  simpa [hs] using this

/-- A fresh allocation preserves every assertion about existing cells and aliases. -/
theorem alloc_frame {k ρ h v} (hk : Holds k ε ρ h) : Holds k ε ρ (h ++ [v]) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frame hk.2.2.1, hk.2.2.2.1, elemsHolds_extend [v] hk.2.2.2.2.1,
    indexHolds_extend [v] hk.2.2.2.2.2⟩
  intro f hf
  obtain ⟨flds,c,oid,u,he,hr,hm⟩ := hk.1 f hf
  exact ⟨flds,c,oid,u,he,hr.alloc_frames [v],hm⟩

/-- The same across a whole object's worth of fresh locations. -/
theorem alloc_frames {k ρ h} (vs : List Val) (hk : Holds k ε ρ h) : Holds k ε ρ (h ++ vs) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frames vs hk.2.2.1, hk.2.2.2.1, elemsHolds_extend vs hk.2.2.2.2.1,
    indexHolds_extend vs hk.2.2.2.2.2⟩
  intro f hf
  obtain ⟨flds,c,oid,u,he,hr,hm⟩ := hk.1 f hf
  exact ⟨flds,c,oid,u,he,hr.alloc_frames vs,hm⟩

/-- What every one of several states establishes: a fact about a slot and
field each of them states, holding what any of them says it holds; the first's
links that appear verbatim in all the others; the separation pairs every
state justifies (`HeapSeparation.meet`). Used by the producer at a merge
that is not a cut, where no requirement is stated; every edge is still
checked, and each state's fact covers the union. Each join is widened
(`ValueSet.widen`), so a merge keeps at most 8 clauses per object. -/
def meet : List Knowledge → Knowledge
  | [] => {}
  | k :: ks =>
    let joined := fun (pick : Knowledge → Facts) =>
      (pick k).filterMap fun f =>
        let others := ks.map fun o => (pick o).filter fun g => g.slot == f.slot && g.field == f.field
        if others.all (!·.isEmpty) then
          some { f with contents := others.flatten.foldl (fun V g => if V = g.contents then V else (V.join g.contents).widen) f.contents }
        else none
    ⟨(joined (·.cells)).eraseDups, (joined (·.values)).eraseDups,
     let others := ks.map fun o => (Std.HashSet.ofList o.links : Std.HashSet HeapLinks.Link)
     k.links.filter (fun g => others.all (·.contains g)),
     HeapSeparation.meet (k.separation :: ks.map (·.separation)),
     k.elems.filter fun a => ks.all (·.elems.contains a),
     k.indices.filter fun a => ks.all (·.indices.contains a)⟩

/-- Whether a target atom follows from a source atom on an edge mapping `m`:
the source's slot holds the mapped target slot's value (`M`), its predicate
is within the target's, and its condition is none or the mapped one's. -/
def elemFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (s t : ElemAtom) : Bool :=
  (M (PointClaims.slot m t.slot)).contains s.slot && s.pred.le t.pred &&
    match s.cond, t.cond with
    | none, _ => true
    | some c, some c' => (M (PointClaims.slot m c')).contains c && s.negated == t.negated
    | some _, none => false

def elemsCheckBy (M : Nat → List Nat) (a b : List ElemAtom) (m : PointClaims.Mapping) : Bool :=
  b.all fun t => a.any fun s => elemFollows M m s t

theorem elemsCheckBy_sound {M : Nat → List Nat} {a b : List ElemAtom} {m ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hc : elemsCheckBy M a b m = true) (ha : ElemsHolds a ρ h) :
    ElemsHolds b (PointClaims.mapEnv m ρ) h := by
  intro t ht hcond
  obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc t ht)
  simp only [elemFollows, Bool.and_eq_true, List.contains_iff_mem] at hf
  obtain ⟨⟨hslot, hle⟩, hcd⟩ := hf
  have hsv : ρ s.slot = PointClaims.mapEnv m ρ t.slot := hM _ _ hslot
  have hsc : ∀ c, s.cond = some c → tagHolds .truthy (ρ c) = !s.negated := by
    intro c hc
    rw [hc] at hcd
    cases htc : t.cond with
    | none => rw [htc] at hcd; cases hcd
    | some c' =>
      rw [htc] at hcd
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hcd
      rw [hM _ _ hcd.1, hcd.2]
      exact hcond c' htc
  have := ha s hs hsc
  rw [hsv] at this
  exact this.mono hle

/-- Whether a target term is a source one of the same kind and path, its slot
mapped to a slot whose value the source slot holds (`M`). -/
def termFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (s t : Term) : Bool :=
  s.kind == t.kind && s.path == t.path && s.atEntry == t.atEntry &&
    (if t.atEntry then s.slot == t.slot else (M (PointClaims.slot m t.slot)).contains s.slot)

theorem termFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s t : Term} (hf : termFollows M m s t = true) :
    termValue ε ρ h s = termValue ε (PointClaims.mapEnv m ρ) h t := by
  obtain ⟨k, x, p, a⟩ := s
  obtain ⟨k', y, p', a'⟩ := t
  simp only [termFollows, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hx⟩ := hf
  cases a
  · simp only [Bool.false_eq_true, if_false] at hx
    simp only [termValue, termAt, Bool.false_eq_true, if_false, PointClaims.mapEnv,
      hM _ _ (List.contains_iff_mem.mp hx)]
  · simp only [if_true, beq_iff_eq] at hx
    subst hx
    exact termValue_entry_invariant rfl

/-- Whether a target linear form is a source one, term by term (`termFollows`). -/
def termsFollow (M : Nat → List Nat) (m : PointClaims.Mapping) : Linear.Form Term → Linear.Form Term → Bool
  | [], [] => true
  | (x, c) :: t, (y, c') :: t' => c == c' && termFollows M m x y && termsFollow M m t t'
  | _, _ => false

def formFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : Linear.Fact Term → Linear.Fact Term → Bool
  | .le F d, .le F' d' => d == d' && termsFollow M m F F'
  | .ne F d, .ne F' d' => d == d' && termsFollow M m F F'
  | _, _ => false

theorem termsFollow_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) :
    ∀ {F F' : Linear.Form Term}, termsFollow M m F F' = true →
      Linear.Form.eval (termValuation ε (PointClaims.mapEnv m ρ) h) F' = Linear.Form.eval (termValuation ε ρ h) F ∧
      ∀ y ∈ F'.map (·.1), ∃ x ∈ F.map (·.1), termValue ε ρ h x = termValue ε (PointClaims.mapEnv m ρ) h y := by
  intro F
  induction F with
  | nil => intro F' h; cases F' with
    | nil => exact ⟨rfl, by simp⟩
    | cons _ _ => simp [termsFollow] at h
  | cons p t ih =>
    intro F' hf
    obtain ⟨x, c⟩ := p
    cases F' with
    | nil => simp [termsFollow] at hf
    | cons q t' =>
      obtain ⟨y, c'⟩ := q
      simp only [termsFollow, Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨⟨rfl, hx⟩, ht⟩ := hf
      obtain ⟨he, hv⟩ := ih ht
      have hxy := termFollows_sound (ε := ε) (h := h) hM hx
      refine ⟨?_, ?_⟩
      · simp only [Linear.Form.eval, he, termValuation, ← hxy]
      · intro z hz
        simp only [List.map_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨x, by simp, hxy⟩
        · obtain ⟨w, hw, hwz⟩ := hv z hz
          exact ⟨w, by simp [hw], hwz⟩

theorem formFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    {F F' : Linear.Fact Term} (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hf : formFollows M m F F' = true) :
    (F'.Holds (termValuation ε (PointClaims.mapEnv m ρ) h) ↔ F.Holds (termValuation ε ρ h)) ∧
      ∀ y ∈ F'.vars, ∃ x ∈ F.vars, termValue ε ρ h x = termValue ε (PointClaims.mapEnv m ρ) h y := by
  cases F <;> cases F' <;> simp only [formFollows, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hf
  all_goals
    obtain ⟨rfl, ht⟩ := hf
    obtain ⟨he, hv⟩ := termsFollow_sound (h := h) hM ht
    exact ⟨by simp only [Linear.Fact.Holds, he], hv⟩

/-- Whether a target body variable is a source one: the index, the element,
or a term `termFollows` relates. -/
def boundFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : Bound → Bound → Bool
  | .index, .index => true
  | .elem, .elem => true
  | .offset d, .offset d' => d == d'
  | .project k p, .project k' p' => k == k' && p == p'
  | .free t, .free t' => termFollows M m t t'
  | _, _ => false

theorem boundFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {ls : List (Option Nat)} {i : Nat} {x y : Bound}
    (hf : boundFollows M m x y = true) : boundValue ε ρ h ls i x = boundValue ε (PointClaims.mapEnv m ρ) h ls i y := by
  cases x <;> cases y <;> simp only [boundFollows, Bool.false_eq_true] at hf
  · rfl
  · rfl
  · simp only [beq_iff_eq] at hf; subst hf; rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rfl
  · exact termFollows_sound (ε := ε) hM hf

theorem lookup_mem' {α β : Type} [BEq α] [LawfulBEq α] : ∀ {l : List (α × β)} {a : α} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (a', b') :: t, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      have := LawfulBEq.eq_of_beq he
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem' h)

/-- Whether a target body fact is a source one: its variables, renamed to
the source's in order, give the source fact, each pair related by
`boundFollows`. -/
def bodyFactFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (F F' : LinearClause Bound) : Bool :=
  let ps := F'.vars.zip F.vars
  ps.all (fun (y, x) => boundFollows M m x y) && F'.mapVars (fun y => ps.lookup y) == some F

/-- Whether a target fact follows from a source fact on an edge mapping `m`:
each slot of the source's holds the value of the mapped target slot (`M`). -/
def factFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : IndexFact → IndexFact → Bool
  | .index k, .index k' => (M (PointClaims.slot m k')).contains k
  | .length x n, .length x' n' =>
    (M (PointClaims.slot m x')).contains x && (M (PointClaims.slot m n')).contains n
  | .bound x k st, .bound x' k' st' =>
    (M (PointClaims.slot m x')).contains x && (M (PointClaims.slot m k')).contains k && (st || !st')
  | .int k, .int k' => (M (PointClaims.slot m k')).contains k
  | .pastSafe k, .pastSafe k' => (M (PointClaims.slot m k')).contains k
  | .linear F, .linear F' => formFollows M m F F'
  | .element v x k, .element v' x' k' =>
    (M (PointClaims.slot m v')).contains v && (M (PointClaims.slot m x')).contains x &&
      (M (PointClaims.slot m k')).contains k
  | .every s p st b, .every s' p' st' b' =>
    (M (PointClaims.slot m s')).contains s && p == p' && termFollows M m st st' &&
      b'.all fun F' => b.any fun F => bodyFactFollows M m F F'
  | .apart a b, .apart a' b' =>
    (M (PointClaims.slot m a')).contains a && (M (PointClaims.slot m b')).contains b ||
      (M (PointClaims.slot m a')).contains b && (M (PointClaims.slot m b')).contains a
  | .storeApart a p b q, .storeApart a' p' b' q' =>
    (M (PointClaims.slot m a')).contains a && p == p' && (M (PointClaims.slot m b')).contains b && q == q' ||
      (M (PointClaims.slot m a')).contains b && p' == q && (M (PointClaims.slot m b')).contains a && q' == p
  | .guarded s p g B, .guarded s' p' g' B' =>
    (M (PointClaims.slot m s')).contains s && p == p' && g == g' && factFollows M m B B'
  | _, _ => false

/-- A quantified fact holds at an edge's target where the source's holds:
its array, its bound and its body's terms, renamed by the edge, denote the
same (`factFollows`). -/
theorem every_follows {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s s' : Nat} {p : List String} {st st' : Term}
    {b b' : List (LinearClause Bound)} (hs : (M (PointClaims.slot m s')).contains s = true)
    (hst : termFollows M m st st' = true) (hb : b'.all (fun F' => b.any fun F => bodyFactFollows M m F F') = true)
    (hF : (IndexFact.every s p st b).HoldsAt ε ρ h) :
    (IndexFact.every s' p st' b').HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
  have hs' : PointClaims.mapEnv m ρ s' = ρ s := (hM _ _ (List.contains_iff_mem.mp hs)).symm
  refine ⟨w, sto, ls, n, by rw [hs']; exact hw, hsto, hls, by rw [← termFollows_sound hM hst]; exact hn,
    fun i hi F' hF' => ?_⟩
  obtain ⟨F, hF, hm⟩ := List.any_eq_true.mp (List.all_eq_true.mp hb F' hF')
  simp only [bodyFactFollows, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hm
  obtain ⟨hps, hmap⟩ := hm
  refine (LinearClause.holdsAt_mapVars hmap fun y _ x hx => ?_).mp (hall i hi F hF)
  exact boundFollows_sound hM (hps _ (lookup_mem' hx))

theorem factFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {s t : IndexFact} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hf : factFollows M m s t = true) (hs : s.HoldsAt ε ρ h) :
    t.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  induction s generalizing t with
  | guarded s0 p0 g0 B ih =>
    cases t <;> simp only [factFollows, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, reduceCtorEq] at hf
    rename_i s1 p1 g1 B'
    obtain ⟨⟨⟨hm, rfl⟩, rfl⟩, hB⟩ := hf
    obtain ⟨v, hv, hor⟩ := hs
    refine ⟨v, by simpa only [PointClaims.mapEnv, hM _ _ hm] using hv, ?_⟩
    exact hor.imp id (ih hB)
  | _ => ?_
  all_goals cases t <;> simp only [factFollows, Bool.and_eq_true, List.contains_iff_mem, reduceCtorEq] at hf
  · rename_i k k'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf] using hs
  · rename_i x n x' n'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf.1, hM _ _ hf.2] using hs
  · rename_i x k st x' k' st'
    obtain ⟨⟨hx, hk⟩, hst⟩ := hf
    obtain ⟨s, ls, b, i, hs', hl, hb, hi, hle⟩ := hs
    refine ⟨s, ls, b, i, by simpa only [PointClaims.mapEnv, hM _ _ hx] using hs', hl,
      by simpa only [PointClaims.mapEnv, hM _ _ hk] using hb, hi, ?_⟩
    cases st <;> cases st' <;> simp_all <;> omega
  · rename_i k k'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf] using hs
  · rename_i k k'
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hf] using hs
  · rename_i F F'
    obtain ⟨hh, hv⟩ := formFollows_sound (h := h) hM hf
    refine ⟨fun y hy => ?_, hh.mpr hs.2⟩
    obtain ⟨x, hx, hxy⟩ := hv y hy
    have := hs.1 x hx
    rw [hxy] at this
    exact this
  · rename_i v x k v' x' k'
    obtain ⟨⟨hv, hx⟩, hk⟩ := hf
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hv, hM _ _ hx, hM _ _ hk] using hs
  · rename_i s0 p0 st b s1 p1 st' b'
    obtain ⟨⟨⟨hs0, hp⟩, hst⟩, hb⟩ := hf
    simp only [beq_iff_eq] at hp
    subst hp
    exact every_follows hM (List.contains_iff_mem.mpr hs0) hst hb hs
  · rename_i a b a' b'
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hf
    rcases hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ ha, hM _ _ hb] using hs
    · simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ ha, hM _ _ hb] using
        regionsApart_symm hs
  · rename_i a p b q a' p' b' q'
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hf
    rcases hf with ⟨⟨⟨ha, rfl⟩, hb⟩, rfl⟩ | ⟨⟨⟨ha, rfl⟩, hb⟩, rfl⟩
    · simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ ha, hM _ _ hb] using hs
    · simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ ha, hM _ _ hb] using
        PathStoresApart.symm hs

/-- Whether a source atom's condition holds wherever a target's does: the
source is unconditional, or conditional on a slot of the class of the
target's condition slot (`M`), at the same answer. -/
def condFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (s t : IndexAtom) : Bool :=
  match s.cond, t.cond with
  | none, _ => true
  | some c, some c' => (M (PointClaims.slot m c')).contains c && s.negated == t.negated
  | some _, none => false

/-- A source atom whose condition `condFollows` the target's holds wherever
the target's condition does. -/
theorem condFollows_cond {M : Nat → List Nat} {m : PointClaims.Mapping} {s t : IndexAtom} {ρ : Env}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hcd : condFollows M m s t = true)
    (hcond : ∀ c, t.cond = some c → tagHolds .truthy (PointClaims.mapEnv m ρ c) = !t.negated) :
    ∀ c, s.cond = some c → tagHolds .truthy (ρ c) = !s.negated := by
  intro c hc
  unfold condFollows at hcd
  rw [hc] at hcd
  cases htc : t.cond with
  | none => rw [htc] at hcd; cases hcd
  | some c' =>
    rw [htc] at hcd
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hcd
    rw [hM _ _ hcd.1, hcd.2]
    exact hcond c' htc

/-- Whether a target atom follows from a source atom: its fact follows, and its
condition is none or the mapped one's, at the same answer. -/
def indexFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (s t : IndexAtom) : Bool :=
  factFollows M m s.fact t.fact && condFollows M m s t

/-- A store's length lies between `0` and `maxArrayLength`. -/
def lengthRange (t : Term) : List (Linear.Fact Term) :=
  [.le [(t, -1)] 0, .le [(t, 1)] (maxArrayLength : Int)]

/-- A typed array's length, and a string's, lies between `0` and
`2^53 - 1`, a safe integer. -/
def viewRange (t : Term) : List (Linear.Fact Term) :=
  [.le [(t, -1)] 0, .le [(t, 1)] (2 ^ 53 - 1)]

/-- A safe integer lies between `-(2^53 - 1)` and `2^53 - 1`. -/
def valueRange (t : Term) : List (Linear.Fact Term) :=
  [.le [(t, -1)] (2 ^ 53 - 1), .le [(t, 1)] (2 ^ 53 - 1)]

/-- The range a term's kind gives it: a length's, a typed-array length's or a
string's length's, none of a value, whose range the entailment reads apart
(`valueRanges`). -/
def termRange (t : Term) : List (Linear.Fact Term) :=
  match t.kind with
  | .length => lengthRange t
  | .view | .strLength => viewRange t
  | .value => []

/-- The linear facts a fact states: a linear fact itself, with the range of
each length and typed-array length it names; a length atom `length(x, n)` as the
equality of `n`'s value with `x`'s length, with its range. -/
def factLinear : IndexFact → List (Linear.Fact Term)
  | .linear F => F :: F.vars.flatMap termRange
  | .length x n => .le [(.value n, 1), (.length x, -1)] 0 :: .le [(.value n, -1), (.length x, 1)] 0 :: lengthRange (.length x)
  | _ => []

/-- The linear facts the unconditional atoms state. -/
def linearRaw (as : List IndexAtom) : List (Linear.Fact Term) :=
  as.flatMap fun a => if a.cond.isNone then factLinear a.fact else []

/-- The linear facts the unconditional atoms state, each once. -/
def linearFacts (as : List IndexAtom) : List (Linear.Fact Term) :=
  (linearRaw as).eraseDups

/-- `linearFacts` deduplicated by hashing (`Linear.dedupHash_eq`). -/
def linearFactsHash (as : List IndexAtom) : List (Linear.Fact Term) :=
  Linear.dedupHash (linearRaw as)

@[csimp] theorem linearFacts_eq_hash : @linearFacts = @linearFactsHash := by
  funext as; simp only [linearFacts, linearFactsHash, Linear.dedupHash_eq]

/-- Whether an unconditional atom states that the slot `s` holds a safe integer. -/
def intSlot (as : List IndexAtom) (s : Nat) : Bool :=
  as.any fun a => a.cond.isNone && match a.fact with
    | .int k => k == s
    | .length _ n => n == s
    | .linear F => F.vars.contains (.value s)
    | _ => false

/-- Whether an unconditional atom states that a term denotes an integer: a
linear fact names it; a slot's value, where an atom states the slot a safe
integer (`intSlot`); a slot's length, where a length atom names it. -/
def termDefined (as : List IndexAtom) (t : Term) : Bool :=
  (!t.atEntry && t.path.isEmpty && match t.kind with
    | .value => intSlot as t.slot
    | .length => as.any fun a => a.cond.isNone && match a.fact with
      | .length y _ => y == t.slot
      | _ => false
    | .view | .strLength => false) ||
  as.any fun a => a.cond.isNone && match a.fact with
    | .linear F => F.vars.contains t
    | _ => false

theorem intValue_length {ls : List (Option Nat)} (hm : ls.length ≤ maxArrayLength) :
    intValue (.num (bitsOfNat ls.length)) = some (ls.length : Int) :=
  intValue_num ⟨by simp [maxArrayLength] at hm ⊢; omega, .inl ⟨by omega, by simp⟩⟩

theorem lengthRange_holds {ρ h} {t : Term} (hk : t.kind = .length) (hx : (termValue ε ρ h t).isSome) :
    ∀ F ∈ lengthRange t, F.Holds (termValuation ε ρ h) := by
  obtain ⟨H, v, n, hkv, hn⟩ := termValue_kind hx
  rw [hk] at hkv
  obtain ⟨s, ls, -, -, rfl, hm⟩ := lengthOf_store (h := H) (v := v) hkv
  have hv : termValuation ε ρ h t = ls.length := by simp [termValuation, hn]
  have hm' : (ls.length : Int) ≤ (maxArrayLength : Int) := by exact_mod_cast hm
  intro F hF
  simp only [lengthRange, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> simp only [Linear.Fact.Holds, Linear.Form.eval, hv] <;> omega

theorem viewRange_holds {ρ h} {t : Term} (hk : t.kind = .view) (hx : (termValue ε ρ h t).isSome) :
    ∀ F ∈ viewRange t, F.Holds (termValuation ε ρ h) := by
  obtain ⟨H, v, n, hkv, hn⟩ := termValue_kind hx
  rw [hk] at hkv
  obtain ⟨h0, h1⟩ := viewLengthOf_range (h := H) (v := v) hkv
  have hv : termValuation ε ρ h t = n := by simp [termValuation, hn]
  intro F hF
  simp only [viewRange, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> simp only [Linear.Fact.Holds, Linear.Form.eval, hv] <;> omega

theorem strRange_holds {ρ h} {t : Term} (hk : t.kind = .strLength) (hx : (termValue ε ρ h t).isSome) :
    ∀ F ∈ viewRange t, F.Holds (termValuation ε ρ h) := by
  obtain ⟨H, v, n, hkv, hn⟩ := termValue_kind hx
  rw [hk] at hkv
  obtain ⟨h0, h1⟩ := strLengthOf_range (v := v) hkv
  have hv : termValuation ε ρ h t = n := by simp [termValuation, hn]
  intro F hF
  simp only [viewRange, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> simp only [Linear.Fact.Holds, Linear.Form.eval, hv] <;> omega

theorem valueRange_holds {ρ h} {t : Term} (hk : t.kind = .value) (hx : (termValue ε ρ h t).isSome) :
    ∀ F ∈ valueRange t, F.Holds (termValuation ε ρ h) := by
  obtain ⟨H, v, n, hkv, hn⟩ := termValue_kind hx
  rw [hk] at hkv
  obtain ⟨b, -, hs, -⟩ := intValue_safe hkv
  have hv : termValuation ε ρ h t = n := by simp [termValuation, hn]
  intro F hF
  simp only [valueRange, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> simp only [Linear.Fact.Holds, Linear.Form.eval, hv] <;> omega

theorem termRange_holds {ρ h} {t : Term} (hx : (termValue ε ρ h t).isSome) :
    ∀ F ∈ termRange t, F.Holds (termValuation ε ρ h) := by
  unfold termRange
  split
  · exact lengthRange_holds (by assumption) hx
  · exact viewRange_holds (by assumption) hx
  · exact strRange_holds (by assumption) hx
  · simp

theorem factLinear_holds {f : IndexFact} {ρ h} (hf : f.HoldsAt ε ρ h) :
    ∀ F ∈ factLinear f, F.Holds (termValuation ε ρ h) := by
  intro F hF
  cases f with
  | linear G =>
    simp only [factLinear, List.mem_cons, List.mem_flatMap] at hF
    rcases hF with rfl | ⟨t, ht, hF⟩
    · exact hf.2
    · exact termRange_holds (hf.1 _ ht) F hF
  | length x n =>
    obtain ⟨s, ls, hs, hl, hnv, hm⟩ := hf
    have hlen : termValue ε ρ h (.length x) = some (ls.length : Int) := lengthOf_of_store hs hl hm
    have hval : termValue ε ρ h (.value n) = some (ls.length : Int) := by
      simp only [termValue_value, hnv, intValue_length hm]
    have v1 : termValuation ε ρ h (.length x) = ls.length := by simp [termValuation, hlen]
    have v2 : termValuation ε ρ h (.value n) = ls.length := by simp [termValuation, hval]
    simp only [factLinear, List.mem_cons] at hF
    rcases hF with rfl | rfl | hF
    · simp only [Linear.Fact.Holds, Linear.Form.eval, v1, v2]; omega
    · simp only [Linear.Fact.Holds, Linear.Form.eval, v1, v2]; omega
    · exact lengthRange_holds rfl (by rw [hlen]; rfl) F hF
  | index _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => simp [factLinear] at hF

theorem linearFacts_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    ∀ F ∈ linearFacts as, F.Holds (termValuation ε ρ h) := by
  intro F hF
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hF)
  split at hm
  · rename_i hn
    exact factLinear_holds (he a ha fun b hb => by rw [Option.isNone_iff_eq_none.mp hn] at hb; cases hb) F hm
  · cases hm

theorem linearRaw_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    ∀ F ∈ linearRaw as, F.Holds (termValuation ε ρ h) :=
  fun F hF => linearFacts_holds he F (List.mem_eraseDups.mpr hF)

theorem intSlot_sound {as : List IndexAtom} {ρ h s} (he : IndexHolds ε as ρ h) (hs : intSlot as s = true) :
    (intValue (ρ s)).isSome := by
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp hs
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hn, hf⟩ := hm
  have hat := he a ha fun b hb => by rw [hn] at hb; cases hb
  cases hfa : a.fact with
  | int k => rw [hfa] at hf hat; simp only [beq_iff_eq] at hf; subst hf; exact hat
  | length x n =>
    rw [hfa] at hf hat; simp only [beq_iff_eq] at hf; subst hf
    obtain ⟨_, ls, -, -, hnv, hm⟩ := hat
    rw [hnv, intValue_length hm]; rfl
  | linear G => rw [hfa] at hf hat; exact hat.1 (.value s) (List.contains_iff_mem.mp hf)
  | index _ | bound _ _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => rw [hfa] at hf; cases hf

theorem termDefined_sound {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) {t : Term}
    (ht : termDefined as t = true) : (termValue ε ρ h t).isSome := by
  unfold termDefined at ht
  rcases Bool.or_eq_true_iff.mp ht with ht | ht
  · obtain ⟨k, s, p, a⟩ := t
    simp only at ht
    cases a
    case true => simp at ht
    simp only [Bool.not_false, Bool.true_and] at ht
    cases p with
    | cons _ _ => simp at ht
    | nil =>
    simp only [List.isEmpty_nil, Bool.true_and] at ht
    cases k with
    | value => exact intSlot_sound he ht
    | length =>
      obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp ht
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
      obtain ⟨hn, hf⟩ := hm
      have hat := he a ha fun b hb => by rw [hn] at hb; cases hb
      cases hfa : a.fact with
      | length y n =>
        rw [hfa] at hf hat; simp only [beq_iff_eq] at hf; subst hf
        obtain ⟨s, ls, hs, hl, -, hm⟩ := hat
        simp only [termValue_nil, kindValue, lengthOf_of_store hs hl hm, Option.isSome_some]
      | linear _ | index _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => rw [hfa] at hf; cases hf
    | view | strLength => cases ht
  · obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp ht
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
    obtain ⟨hn, hf⟩ := hm
    have hat := he a ha fun b hb => by rw [hn] at hb; cases hb
    cases hfa : a.fact with
    | linear G => rw [hfa] at hf hat; exact hat.1 t (List.contains_iff_mem.mp hf)
    | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => rw [hfa] at hf; cases hf

/-- The terms the unconditional atoms state defined: each term of a linear
fact, a safe integer's slot's value, a length atom's length and value. -/
def definedTerms (as : List IndexAtom) : List Term :=
  as.flatMap fun a => if a.cond.isNone then match a.fact with
    | .linear F => F.vars
    | .int k => [.value k]
    | .length x n => [.length x, .value n]
    | _ => [] else []

theorem definedTerms_sound {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) {t : Term}
    (ht : t ∈ definedTerms as) : (termValue ε ρ h t).isSome := by
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp ht
  split at hm
  · rename_i hn
    have hat := he a ha fun b hb => by rw [Option.isNone_iff_eq_none.mp hn] at hb; cases hb
    cases hfa : a.fact with
    | linear G => rw [hfa] at hm hat; exact hat.1 t hm
    | int k => rw [hfa] at hm hat; simp only [List.mem_singleton] at hm; subst hm; exact hat
    | length x n =>
      rw [hfa] at hm hat
      obtain ⟨s, ls, hs, hl, hnv, hmx⟩ := hat
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · simp only [termValue_length, lengthOf_of_store hs hl hmx, Option.isSome_some]
      · simp only [termValue_value, hnv, intValue_length hmx, Option.isSome_some]
    | index _ | bound _ _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => rw [hfa] at hm; cases hm
  · cases hm

/-- The safe-integer range of each value term the unconditional atoms state
defined (`definedTerms`): the facts an entailment reads where the linear facts
alone entail no goal (`entailsKnown`). -/
def valueRanges (as : List IndexAtom) : List (Linear.Fact Term) :=
  ((definedTerms as).filter (·.kind == .value)).eraseDups.flatMap valueRange

/-- `valueRanges` deduplicated by hashing (`Linear.dedupHash_eq`). -/
def valueRangesHash (as : List IndexAtom) : List (Linear.Fact Term) :=
  (Linear.dedupHash ((definedTerms as).filter (·.kind == .value))).flatMap valueRange

@[csimp] theorem valueRanges_eq_hash : @valueRanges = @valueRangesHash := by
  funext as; simp only [valueRanges, valueRangesHash, Linear.dedupHash_eq]

/-- `valueRanges` with the terms not made unique: the same facts, each as often
as its term is stated defined. -/
def rangesRaw (as : List IndexAtom) : List (Linear.Fact Term) :=
  ((definedTerms as).filter (·.kind == .value)).flatMap valueRange

theorem valueRanges_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    ∀ F ∈ valueRanges as, F.Holds (termValuation ε ρ h) := by
  intro F hF
  obtain ⟨t, ht, hF⟩ := List.mem_flatMap.mp hF
  obtain ⟨ht, hk⟩ := List.mem_filter.mp (List.mem_eraseDups.mp ht)
  exact valueRange_holds (by simpa using hk) (definedTerms_sound he ht) F hF

theorem rangesRaw_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    ∀ F ∈ rangesRaw as, F.Holds (termValuation ε ρ h) := by
  intro F hF
  obtain ⟨t, ht, hF⟩ := List.mem_flatMap.mp hF
  exact valueRanges_holds he F (List.mem_flatMap.mpr ⟨t, List.mem_eraseDups.mpr ht, hF⟩)

/-- The atoms' linear facts, then the range of each safe integer they name,
prepared once for every query against them (`Linear.Known`). -/
def knownOf (as : List IndexAtom) : Linear.Known Term :=
  Linear.Known.build (linearRaw as) (rangesRaw as)

theorem knownOf_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    (knownOf as).Holds (termValuation ε ρ h) :=
  Linear.Known.build_holds (linearRaw_holds he) (rangesRaw_holds he)

/-- Whether the atoms' linear facts entail a goal, alone or with the range of
each safe integer they name. -/
@[inline] def entailsKnown (as : List IndexAtom) (goal : Linear.Fact Term) : Bool :=
  (knownOf as).entails goal

theorem entailsKnown_sound {as : List IndexAtom} {ρ h} {goal : Linear.Fact Term} (he : IndexHolds ε as ρ h)
    (hg : entailsKnown as goal = true) : goal.Holds (termValuation ε ρ h) :=
  Linear.Known.entails_sound (knownOf_holds he) hg

/-- The first slot of `M z` meeting `p`, or `z`. -/
def pick (M : Nat → List Nat) (p : Nat → Bool) (z : Nat) : Nat := ((M z).find? p).getD z

theorem pick_eq {M : Nat → List Nat} {p : Nat → Bool} {ρ : Env} (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (z : Nat) :
    ρ (pick M p z) = ρ z := by
  unfold pick
  cases hf : (M z).find? p with
  | none => rfl
  | some x => exact hM _ _ (List.mem_of_find?_eq_some hf)

/-- The source slot standing for target slot `y`: one of its class the
source states a safe integer, where there is one. -/
def pickSlot (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom) (y : Nat) : Nat :=
  pick M (intSlot a) (PointClaims.slot m y)

theorem pickSlot_eq {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom} {ρ : Env}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (y : Nat) : ρ (pickSlot M m a y) = PointClaims.mapEnv m ρ y :=
  pick_eq hM _

/-- The source term standing for a target term: of the same kind and path, at
a slot of the class of the mapped slot whose term the source states defined,
where there is one. -/
def pickTerm (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom) (t : Term) : Term :=
  t.mapM' fun s => pick M (fun x => termDefined a (.now t.kind x t.path)) (PointClaims.slot m s)

theorem pickTerm_eq {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (t : Term) :
    termValue ε ρ h (pickTerm M m a t) = termValue ε (PointClaims.mapEnv m ρ) h t := by
  exact termValue_mapM' fun _ => by rw [pick_eq hM]; rfl

/-- Whether the source's facts `K` (`knownOf a`) bound slot `k` by the length
of the store of `x`'s class (`M`): `k` stated a safe integer, the facts
entailing `0 ≤ k` and `k ≤ maxArrayLength - 1`, and, for a slot of the class
whose length is defined, `k ≤ length` (`k < length` where `strict`). -/
def lengthBoundIn (K : Linear.Known Term) (M : List Nat) (a : List IndexAtom) (k : Nat) (strict : Bool) : Bool :=
  intSlot a k && K.entails (.le [(.value k, -1)] 0) &&
    K.entails (.le [(.value k, 1)] ((maxArrayLength : Int) - 1)) &&
    M.any fun y => termDefined a (.length y) &&
      K.entails (.le [(.value k, 1), (.length y, -1)] (if strict then -1 else 0))

/-- `lengthBoundIn` over the source's own facts. -/
@[inline] def lengthBound (M : List Nat) (a : List IndexAtom) (k : Nat) (strict : Bool) : Bool :=
  lengthBoundIn (knownOf a) M a k strict

theorem indexOfBits_safe {b : UInt64} {j : Int} (hb : SafeIntegers.SafeInt b j) (h0 : 0 ≤ j)
    (h1 : j < maxArrayLength) : indexOfBits b = some j.toNat := by
  rcases hb.2 with ⟨-, he⟩ | ⟨hle, he⟩
  · have : b = bitsOfNat j.natAbs := UInt64.toNat_inj.mp he
    have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
    have h1' : j < 4294967295 := by omega
    rw [this, IndexNumbers.indexOfBits_bitsOfNat (by omega)]
    congr 1; omega
  · have hj : j = 0 := by omega
    subst hj
    have : b = 0x8000000000000000 := UInt64.toNat_inj.mp (by rw [he]; simp [SafeIntegers.bitsOfNat_zero])
    subst this; rfl

theorem lengthBoundIn_sound {K : Linear.Known Term} {M : List Nat} {a : List IndexAtom} {k : Nat} {strict : Bool}
    {ρ h} {v : Val} (hK : K.Holds (termValuation ε ρ h))
    (hM : ∀ y ∈ M, ρ y = v) (hc : lengthBoundIn K M a k strict = true) (ha : IndexHolds ε a ρ h) :
    ∃ s ls b idx, Footprints.storeOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length := by
  simp only [lengthBoundIn, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hi, e1⟩, e3⟩, hany⟩ := hc
  obtain ⟨y, hy, hm⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true] at hm
  obtain ⟨hd, e2⟩ := hm
  have f1 := Linear.Known.entails_sound hK e1
  have f2 := Linear.Known.entails_sound hK e2
  have f3 := Linear.Known.entails_sound hK e3
  simp only [Linear.Fact.Holds, Linear.Form.eval] at f1 f2 f3
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (termDefined_sound ha hd)
  obtain ⟨s, ls, hs, hl, rfl, -⟩ := lengthOf_store hn
  have hvn : termValuation ε ρ h (.length y) = ls.length := by simp [termValuation, hn]
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (intSlot_sound ha hi)
  obtain ⟨b, hb, hsafe⟩ := intValue_safe hj
  have hvi : termValuation ε ρ h (.value k) = j := by simp [termValuation, termValue_value, hj]
  rw [hvi, hvn] at f2; rw [hvi] at f1 f3
  have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
  refine ⟨s, ls, b, j.toNat, by rw [← hM y hy]; exact hs, hl, hb,
    indexOfBits_safe hsafe (by omega) (by omega), by cases strict <;> simp at f2 ⊢ <;> omega⟩

theorem lengthBound_sound {M : List Nat} {a : List IndexAtom} {k : Nat} {strict : Bool} {ρ h} {v : Val}
    (hM : ∀ y ∈ M, ρ y = v) (hc : lengthBound M a k strict = true) (ha : IndexHolds ε a ρ h) :
    ∃ s ls b idx, Footprints.storeOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length :=
  lengthBoundIn_sound (knownOf_holds ha) hM hc ha

/-- The linear facts of the atoms conditional on slot `c` at the answer `neg`. -/
def condFacts (as : List IndexAtom) (c : Nat) (neg : Bool) : List (Linear.Fact Term) :=
  as.filterMap fun a => if a.cond == some c && a.negated == neg then match a.fact with
    | .linear F => some F
    | _ => none else none

theorem condFacts_holds {as : List IndexAtom} {c : Nat} {neg : Bool} {ρ h} (he : IndexHolds ε as ρ h)
    (hc : tagHolds .truthy (ρ c) = !neg) : ∀ F ∈ condFacts as c neg, F.Holds (termValuation ε ρ h) := by
  intro F hF
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hF
  split at hm
  · rename_i hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    have hat := he a ha fun c' hc' => by rw [hk.1] at hc'; cases hc'; rw [hk.2]; exact hc
    cases hfa : a.fact with
    | linear G => rw [hfa] at hm hat; cases hm; exact hat.2
    | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => rw [hfa] at hm; cases hm
  · cases hm

/-! ## Read bridges

A read link states that a slot holds what reading a field from another
slot's object gave in the current heap (`HeapLinks.Holds`). A term rooted at
the read value is then the term rooted at the object, the field put before
its path: both denote the same integer, or neither denotes one. A check
restates terms by these links so that a fact over a path is entailed by
facts over the slots holding its reads, and conversely (ARITHMETIC.md,
"Linear facts"). -/

/-- **The read bridge.** Where a current read link (not an alias) gives `v`
as the read of the string-keyed field `f` from `c`'s object, the term of any
kind and path `p` rooted at `v` denotes what the term rooted at `c` with path
`f :: p` denotes. A read through an optional key that found none gave
`undefined`, of which no term denotes an integer, as none does of the path
through the absent key. -/
theorem readBridge {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {g : HeapLinks.Link} (hg : g ∈ ls) (ha : g.alias = false) {f : String}
    (hf : g.field = .str f) (k : Term.Kind) (p : List String) :
    termValue ε ρ h (HeapKnowledge.Term.now k g.cell (f :: p)) = termValue ε ρ h (HeapKnowledge.Term.now k g.value p) := by
  have := hl g hg
  simp only [ha, Bool.false_eq_true, ite_false] at this
  cases ho : g.optional
  · simp only [ho, Bool.false_eq_true, ite_false] at this
    obtain ⟨flds, c, oid, l, he, hlk, hv⟩ := this
    rw [hf] at hlk
    simp only [termValue, termAt, Bool.false_eq_true, if_false, he, readPath_cons hlk hv]
  · simp only [ho, ite_true] at this
    obtain ⟨flds, c, oid, he, hr⟩ := this
    rw [hf] at hr
    unfold HeapFacts.ReadGave at hr
    cases hlk : flds.lookup (.str f) with
    | some l =>
      rw [hlk] at hr
      simp only [termValue, termAt, Bool.false_eq_true, if_false, he, readPath_cons hlk hr]
    | none =>
      rw [hlk] at hr
      have hnone : readPath h (ρ g.cell) (f :: p) = none := by simp [he, readPath, hlk]
      simp only [termValue, termAt, Bool.false_eq_true, if_false, hnone, Option.bind_none, hr.2]
      cases p with
      | nil => cases k <;> simp [readPath, kindValue, intValue, lengthOf, viewLengthOf, strLengthOf,
          Footprints.storeOf, Footprints.fieldsOf]
      | cons q p => simp [readPath]

/-- The read links a bridge follows, as `(cell, field, value)`: the reads of
string-keyed fields that are no aliases. -/
def bridgeReads (ls : HeapLinks.Links) : List (Nat × String × Nat) :=
  ls.filterMap fun g => if g.alias then none else match g.field with
    | .str f => some (g.cell, f, g.value)
    | .sym _ => none

theorem bridgeReads_term {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {c v : Nat} {f : String} (hm : (c, f, v) ∈ bridgeReads ls) (k : Term.Kind) (p : List String) :
    termValue ε ρ h (HeapKnowledge.Term.now k c (f :: p)) = termValue ε ρ h (HeapKnowledge.Term.now k v p) := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hm
  split at hgm
  · cases hgm
  · rename_i ha
    split at hgm
    · rename_i f' hf'
      simp only [Option.some.injEq, Prod.mk.injEq] at hgm
      obtain ⟨rfl, rfl, rfl⟩ := hgm
      exact readBridge hl hg (by simpa using ha) hf' k p
    · cases hgm

/-- A path through a read link's field reads what the rest of the path reads
from the linked value. -/
theorem bridgeReads_path {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {c v : Nat} {f : String} (hm : (c, f, v) ∈ bridgeReads ls) {p : List String} {w : Val}
    (hw : readPath h (ρ c) (f :: p) = some w) : readPath h (ρ v) p = some w := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hm
  split at hgm
  · cases hgm
  · rename_i ha
    split at hgm
    · rename_i f' hf'
      simp only [Option.some.injEq, Prod.mk.injEq] at hgm
      obtain ⟨rfl, rfl, rfl⟩ := hgm
      have := hl g hg
      simp only [ha, Bool.false_eq_true, ite_false] at this
      cases ho : g.optional
      · simp only [ho, Bool.false_eq_true, ite_false] at this
        obtain ⟨flds, cd, oid, l, he, hlk, hv⟩ := this
        rw [hf'] at hlk
        rw [he, readPath_cons hlk hv] at hw
        exact hw
      · simp only [ho, ite_true] at this
        obtain ⟨flds, cd, oid, he, hr⟩ := this
        rw [hf'] at hr
        unfold HeapFacts.ReadGave at hr
        cases hlk : flds.lookup (.str f') with
        | some l =>
          rw [hlk] at hr
          rw [he, readPath_cons hlk hr] at hw
          exact hw
        | none => rw [he] at hw; simp only [readPath, hlk] at hw; cases hw
    · cases hgm

/-- A term restated by read links toward its root: its slot taken to a slot
of its class (`r`); where a read gives the slot's value as field `f` read from
slot `c`, the term rooted at `c` with `f` before its path, at most `n`
times. -/
def liftTerm (r : Nat → Nat) (reads : List (Nat × String × Nat)) : Nat → Term → Term
  | 0, t => t.mapM' r
  | n + 1, t => if t.atEntry then t else match reads.find? (fun g => r g.2.2 == r t.slot) with
    | some (c, f, _) => liftTerm r reads n (HeapKnowledge.Term.now t.kind c (f :: t.path))
    | none => t.mapM' r

theorem liftTerm_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {r : Nat → Nat} (hr : ∀ x, ρ (r x) = ρ x) :
    ∀ n t, termValue ε ρ h (liftTerm r (bridgeReads ls) n t) = termValue ε ρ h t := by
  intro n
  induction n with
  | zero =>
    intro t; simp only [liftTerm]
    exact termValue_mapM' fun _ => hr _
  | succ n ih =>
    intro t
    simp only [liftTerm]
    split
    · rfl
    rename_i he
    split
    · rename_i c f v hfind
      have hm := List.mem_of_find?_eq_some hfind
      have hrv : r v = r t.slot := by simpa using List.find?_some hfind
      rw [ih, bridgeReads_term hl hm]
      exact termValue_now_slot (by rw [← hr v, hrv, hr]) (by simpa using he)
    · exact termValue_mapM' fun _ => hr _

/-- A term restated through a read of slot `0` (`reads`): rooted at the
read's value where it is rooted at the read object with the read field first. -/
def lowerTerm (reads : List (Nat × String × Nat)) (t : Term) : Term :=
  if t.atEntry then t else match t.path with
  | f :: p => match reads.find? (fun g => g.1 == t.slot && g.2.1 == f) with
    | some g => (HeapKnowledge.Term.now t.kind g.2.2 p)
    | none => t
  | [] => t

theorem lowerTerm_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) (t : Term) :
    termValue ε ρ h (lowerTerm reads t) = termValue ε ρ h t := by
  obtain ⟨k, s, p, a⟩ := t
  cases a
  case true => rfl
  cases p with
  | nil => rfl
  | cons f p =>
    simp only [lowerTerm, Bool.false_eq_true, if_false]
    split
    · rename_i g hg
      have hm := hr _ (List.mem_of_find?_eq_some hg)
      have hgf := List.find?_some hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hgf
      obtain ⟨c, f', v⟩ := g
      simp only at hgf ⊢
      obtain ⟨rfl, rfl⟩ := hgf
      exact (bridgeReads_term hl hm k p).symm
    · rfl

/-- An array's root restated alike: the read's value and the path's rest. -/
def lowerRoot (reads : List (Nat × String × Nat)) (s : Nat) (p : List String) : Nat × List String :=
  match p with
  | f :: q => match reads.find? (fun g => g.1 == s && g.2.1 == f) with
    | some g => (g.2.2, q)
    | none => (s, p)
  | [] => (s, p)

theorem lowerRoot_path {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) {s : Nat} {p : List String}
    {w : Val} (hw : readPath h (ρ s) p = some w) :
    readPath h (ρ (lowerRoot reads s p).1) (lowerRoot reads s p).2 = some w := by
  cases p with
  | nil => exact hw
  | cons f q =>
    simp only [lowerRoot]
    split
    · rename_i g hg
      have hm := hr _ (List.mem_of_find?_eq_some hg)
      have hgf := List.find?_some hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hgf
      obtain ⟨c, f', v⟩ := g
      simp only at hgf ⊢
      obtain ⟨rfl, rfl⟩ := hgf
      exact bridgeReads_path hl hm hw
    · exact hw

/-- A body variable restated alike. -/
def lowerBound (reads : List (Nat × String × Nat)) : Bound → Bound
  | .free t => .free (lowerTerm reads t)
  | b => b

/-- A fact with each variable renamed by a total map. -/
def renameFact {V W : Type} (g : V → W) : Linear.Fact V → Linear.Fact W
  | .le F d => .le (F.map fun (x, c) => (g x, c)) d
  | .ne F d => .ne (F.map fun (x, c) => (g x, c)) d

theorem form_mapVars_total {V W : Type} (g : V → W) :
    ∀ F : Linear.Form V, Linear.Form.mapVars (some ∘ g) F = some (F.map fun (x, c) => (g x, c))
  | [] => rfl
  | (x, c) :: t => by simp [Linear.Form.mapVars, form_mapVars_total g t]

theorem renameFact_mapVars {V W : Type} (g : V → W) (F : Linear.Fact V) :
    F.mapVars (some ∘ g) = some (renameFact g F) := by
  cases F <;> simp [Linear.Fact.mapVars, renameFact, form_mapVars_total]

def renameClause {V W : Type} (g : V → W) : LinearClause V → LinearClause W
  | .atom F => .atom (renameFact g F)
  | .either A B => .either (renameClause g A) (renameClause g B)

theorem renameClause_mapVars {V W : Type} (g : V → W) (F : LinearClause V) :
    F.mapVars (some ∘ g) = some (renameClause g F) := by
  induction F with
  | atom F => simp [LinearClause.mapVars, renameClause, renameFact_mapVars]
  | either A B ihA ihB => simp [LinearClause.mapVars, renameClause, ihA, ihB]

/-- A quantified fact restated through a read of slot `0`, where the read
restates its array, its bound or a body term. -/
def readEvery (reads : List (Nat × String × Nat)) (a : IndexAtom) : Option IndexAtom :=
  match a.fact with
  | .every s p st body =>
    if lowerRoot reads s p != (s, p) || lowerTerm reads st != st ||
        body.map (renameClause (lowerBound reads)) != body then
      some { a with fact := (.every (lowerRoot reads s p).1 (lowerRoot reads s p).2 (lowerTerm reads st)
        (body.map (renameClause (lowerBound reads))) : IndexFact) }
    else none
  | _ => none

theorem readEvery_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) {a b : IndexAtom}
    (hab : readEvery reads a = some b) (ha : a.fact.HoldsAt ε ρ h) : b.fact.HoldsAt ε ρ h := by
  unfold readEvery at hab
  split at hab
  · rename_i s p st body hfa
    split at hab
    · simp only [Option.some.injEq] at hab
      subst hab
      rw [hfa] at ha
      obtain ⟨w, sto, ls', n, hw, hsto, hls, hn, hall⟩ := ha
      refine ⟨w, sto, ls', n, lowerRoot_path hl hr hw, hsto, hls, by rw [lowerTerm_eq hl hr]; exact hn,
        fun i hi F' hF' => ?_⟩
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hF'
      refine (LinearClause.holdsAt_mapVars (renameClause_mapVars (lowerBound reads) F) fun x _ y hy => ?_).mpr (hall i hi F hF)
      simp only [Function.comp_apply, Option.some.injEq] at hy
      subst hy
      cases x with
      | index => rfl
      | elem => rfl
      | offset _ => rfl
      | project _ _ => rfl
      | free t => exact lowerTerm_eq (ε := ε) hl hr t
    · cases hab
  · cases hab

/-- **The read rule's bridge.** Where a read link gives slot `0` as the field
`f` read from slot `c`, each linear atom naming a term rooted at `c` whose path
starts with `f` is restated with that term rooted at slot `0`, its path the
rest (`readBridge`): what the knowledge states of the path, it states of the
read's value; a quantified fact's array, bound and body terms alike
(`readEvery`). -/
def readAtoms (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  let reads := (bridgeReads ls).filter (·.2.2 == 0)
  if reads.isEmpty then [] else
  as.filterMap fun a => match a.fact with
    | .linear F => if F.vars.any (fun t => lowerTerm reads t != t) then
        (F.mapVars (some ∘ lowerTerm reads)).map fun F' => { a with fact := .linear F' } else none
    | .every .. => readEvery reads a
    | _ => none

theorem readAtoms_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) : IndexHolds ε (readAtoms ls as) ρ h := by
  have hr : ∀ g ∈ (bridgeReads ls).filter (·.2.2 == 0), g ∈ bridgeReads ls := fun g hg => (List.mem_filter.mp hg).1
  simp only [readAtoms]
  split
  · intro a ha; cases ha
  · intro a ha hc
    obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
    split at hab
    · rename_i F hF
      split at hab
      · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
        have hbF := he b hb hc
        rw [hF] at hbF
        exact (IndexFact.holdsAt_linear_mapVars hF' fun x _ y hy => by
          cases hy; exact lowerTerm_eq hl hr x).mpr hbF
      · cases hab
    · have hc' : ∀ c, b.cond = some c → tagHolds .truthy (ρ c) = !b.negated := by
        unfold readEvery at hab
        split at hab
        · split at hab
          · simp only [Option.some.injEq] at hab; subst hab; exact hc
          · cases hab
        · cases hab
      exact readEvery_holds hl hr hab (he b hb hc')
    · cases hab

def liftReadTerm (ls : HeapLinks.Links) (t : Term) : Term :=
  if t.path.isEmpty && t.kind == .value then liftTerm id (bridgeReads ls) 1 t else t

theorem liftReadTerm_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) (t : Term) :
    termValue ε ρ h (liftReadTerm ls t) = termValue ε ρ h t := by
  unfold liftReadTerm; split
  · exact liftTerm_eq (r := id) hl (fun _ => rfl) 1 t
  · rfl

/-- Restate linear value terms and a prefix bound through one known field
read, including the link established by a field write. Existing paths stay
as they are. -/
def liftEvery (ls : HeapLinks.Links) (a : IndexAtom) : IndexAtom :=
  match a.fact with
  | .every s p stop body => { a with fact := .every s p (liftReadTerm ls stop) body }
  | .linear F => { a with fact := .linear (renameFact (liftReadTerm ls) F) }
  | _ => a

@[simp] theorem liftEvery_cond (ls : HeapLinks.Links) (a : IndexAtom) : (liftEvery ls a).cond = a.cond := by
  unfold liftEvery; split <;> rfl

@[simp] theorem liftEvery_negated (ls : HeapLinks.Links) (a : IndexAtom) : (liftEvery ls a).negated = a.negated := by
  unfold liftEvery; split <;> rfl

theorem liftEvery_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} {a : IndexAtom}
    (hl : HeapLinks.Holds ls ρ h) (ha : a.fact.HoldsAt ε ρ h) : (liftEvery ls a).fact.HoldsAt ε ρ h := by
  unfold liftEvery
  split
  · rename_i s p st body hfact
    rw [hfact] at ha
    obtain ⟨w, sto, elems, n, hw, hs, he, hn, hall⟩ := ha
    exact ⟨w, sto, elems, n, hw, hs, he, (liftReadTerm_eq hl st).trans hn, hall⟩
  · rename_i F hfact
    rw [hfact] at ha
    exact (IndexFact.holdsAt_linear_mapVars (renameFact_mapVars (liftReadTerm ls) F)
      (fun x _ y hy => by cases hy; exact liftReadTerm_eq hl x)).mpr ha
  · exact ha

def liftedEvery (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  (as.filter fun a => match a.fact with | .every .. | .linear .. => liftEvery ls a != a | _ => false).map (liftEvery ls)

theorem liftedEvery_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (ha : IndexHolds ε as ρ h) : IndexHolds ε (liftedEvery ls as) ρ h := by
  intro a hm hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
  exact liftEvery_holds hl (ha b (List.mem_filter.mp hb).1 (by simpa only [liftEvery_cond, liftEvery_negated] using hc))

/-- A knowledge with its read atoms (`readAtoms`) added. -/
def withReadAtoms (k : Knowledge) : Knowledge := { k with indices := k.indices ++ readAtoms k.links k.indices ++ liftedEvery k.links k.indices }

theorem withReadAtoms_holds {k : Knowledge} {ρ h} (hk : Holds k ε ρ h) : Holds (withReadAtoms k) ε ρ h :=
  ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha =>
    (List.mem_append.mp ha).elim
      (fun ha => (List.mem_append.mp ha).elim (hk.2.2.2.2.2 a) (readAtoms_holds hk.2.2.1 hk.2.2.2.2.2 a))
      (liftedEvery_holds hk.2.2.1 hk.2.2.2.2.2 a)⟩

/-- Whether a linear atom names a term with a nonempty path. -/
def namesPath (a : IndexAtom) : Bool :=
  match a.fact with
  | .linear F => F.vars.any fun t => !t.path.isEmpty
  | _ => false

/-- The restatement a check of target atoms `bs` against source atoms `as`
uses: by the source's read links (`liftTerm`), each slot first taken to its
alias class's representative, where some atom names a path and some read
link is followed; none otherwise. -/
def bridgeOf (ls : HeapLinks.Links) (as bs : List IndexAtom) : Option (Term → Term) :=
  let reads := bridgeReads ls
  if !reads.isEmpty && (as.any namesPath || bs.any namesPath) then
    some (liftTerm (HeapLinks.rep (HeapLinks.classes ls)) reads reads.length)
  else none

theorem bridgeOf_eq {ls : HeapLinks.Links} {as bs : List IndexAtom} {c : Term → Term} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (hc : bridgeOf ls as bs = some c) (t : Term) :
    termValue ε ρ h (c t) = termValue ε ρ h t := by
  simp only [bridgeOf] at hc
  split at hc
  · cases hc
    exact liftTerm_eq hl (HeapLinks.rep_eq (HeapLinks.classes_one hl)) _ t
  · cases hc

/-- The known facts restated by a bridge. -/
def bridgeFacts (c : Term → Term) (known : List (Linear.Fact Term)) : List (Linear.Fact Term) :=
  known.filterMap (·.mapVars (some ∘ c))

theorem bridgeFacts_holds {c : Term → Term} {known : List (Linear.Fact Term)} {ρ : Env} {h : Heap}
    (hc : ∀ t, termValue ε ρ h (c t) = termValue ε ρ h t) (hk : ∀ G ∈ known, G.Holds (termValuation ε ρ h)) :
    ∀ G ∈ bridgeFacts c known, G.Holds (termValuation ε ρ h) := by
  intro G hG
  obtain ⟨G₀, hG₀, hm⟩ := List.mem_filterMap.mp hG
  refine (Linear.Fact.holds_mapVars hm fun x _ y hy => ?_).mpr (hk G₀ hG₀)
  cases hy
  simp only [termValuation, hc]

/-- Whether the source states a term defined, itself or a term the bridge
restates to it. -/
def bridgedDefined (c : Term → Term) (a : List IndexAtom) (t : Term) : Bool :=
  termDefined a t || ((definedTerms a).map c).contains t

theorem bridgedDefined_sound {c : Term → Term} {a : List IndexAtom} {t : Term} {ρ : Env} {h : Heap}
    (hc : ∀ t, termValue ε ρ h (c t) = termValue ε ρ h t) (ha : IndexHolds ε a ρ h) (hd : bridgedDefined c a t = true) :
    (termValue ε ρ h t).isSome := by
  rcases Bool.or_eq_true_iff.mp hd with hd | hd
  · exact termDefined_sound ha hd
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hd)
    rw [hc]
    exact definedTerms_sound ha hu

/-- `lengthBound` with each term restated by a bridge: the restated index
and length defined, the restated facts entailing the same bounds. -/
def lengthBoundVia (c : Term → Term) (M : List Nat) (a : List IndexAtom) (k : Nat) (strict : Bool) : Bool :=
  let K := Linear.Known.build (bridgeFacts c (linearRaw a)) (bridgeFacts c (rangesRaw a))
  let i := c (.value k)
  bridgedDefined c a i && K.entails (.le [(i, -1)] 0) && K.entails (.le [(i, 1)] ((maxArrayLength : Int) - 1)) &&
    M.any fun y =>
      let n := c (.length y)
      bridgedDefined c a n && K.entails (.le [(i, 1), (n, -1)] (if strict then -1 else 0))

theorem lengthBoundVia_sound {c : Term → Term} {M : List Nat} {a : List IndexAtom} {k : Nat} {strict : Bool}
    {ρ h} {v : Val} (hc : ∀ t, termValue ε ρ h (c t) = termValue ε ρ h t)
    (hM : ∀ y ∈ M, ρ y = v) (hb : lengthBoundVia c M a k strict = true) (ha : IndexHolds ε a ρ h) :
    ∃ s ls b idx, Footprints.storeOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
      indexOfBits b = some idx ∧ idx + (if strict then 1 else 0) ≤ ls.length := by
  simp only [lengthBoundVia, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hi, e1⟩, e3⟩, hany⟩ := hb
  obtain ⟨y, hy, hm⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true] at hm
  obtain ⟨hd, e2⟩ := hm
  have hK := Linear.Known.build_holds (bridgeFacts_holds hc (linearRaw_holds ha))
    (bridgeFacts_holds hc (rangesRaw_holds ha))
  have f1 := Linear.Known.entails_sound hK e1
  have f2 := Linear.Known.entails_sound hK e2
  have f3 := Linear.Known.entails_sound hK e3
  simp only [Linear.Fact.Holds, Linear.Form.eval] at f1 f2 f3
  have hdn := bridgedDefined_sound hc ha hd
  rw [hc] at hdn
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hdn
  simp only [termValue_length] at hn
  obtain ⟨s, ls, hs, hl, rfl, -⟩ := lengthOf_store hn
  have hvn : termValuation ε ρ h (c (.length y)) = ls.length := by simp [termValuation, hc, hn]
  have hdi := bridgedDefined_sound hc ha hi
  rw [hc] at hdi
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hdi
  simp only [termValue_value] at hj
  obtain ⟨b, hb, hsafe⟩ := intValue_safe hj
  have hvi : termValuation ε ρ h (c (.value k)) = j := by simp [termValuation, hc, termValue_value, hj]
  rw [hvi, hvn] at f2; rw [hvi] at f1 f3
  have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
  refine ⟨s, ls, b, j.toNat, by rw [← hM y hy]; exact hs, hl, hb,
    indexOfBits_safe hsafe (by omega) (by omega), by cases strict <;> simp at f2 ⊢ <;> omega⟩

/-- Whether the facts `known`, prepared as `K` with the ranges of `a`'s safe
integers, entail a target linear fact, each target term renamed to a source
term the source states defined (`pickTerm`); with a bridge, each term of the
target and of `known` restated by it, a restated target term defined where
the source states one restated to it defined. -/
def linearEntailed (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom)
    (B : Option (Term → Term)) (K : Linear.Known Term) (known : List (Linear.Fact Term)) (F : Linear.Fact Term) : Bool :=
  match B with
  | none => match F.mapVars (fun t => some (pickTerm M m a t)) with
    | some F' => F'.vars.all (termDefined a) && K.entails F'
    | none => false
  | some c => match F.mapVars (fun t => some (c (pickTerm M m a t))) with
    | some F' => F'.vars.all (bridgedDefined c a) &&
        Linear.entailsWith (bridgeFacts c known) (bridgeFacts c (rangesRaw a)) F'
    | none => false

/-- A quantified atom witnesses its array's element store, independently of
its bound and body. -/
def elementsKnown (M : Nat → List Nat) (m : PointClaims.Mapping) (as : List IndexAtom)
    (s : Nat) (p : List String) : Bool :=
  as.any fun a => a.cond.isNone && match a.fact with
    | .every x q _ _ => (M (PointClaims.slot m s)).contains x && q == p
    | _ => false

theorem elementsKnown_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {as : List IndexAtom}
    {s : Nat} {p : List String} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (ha : IndexHolds ε as ρ h)
    (hk : elementsKnown M m as s p = true) :
    ∃ w sto ls, readPath h (PointClaims.mapEnv m ρ s) p = some w ∧
      elementsOf w = some sto ∧ h[sto]? = some (.arr ls) := by
  obtain ⟨a, hm, ha0⟩ := List.any_eq_true.mp hk
  simp only [Bool.and_eq_true] at ha0
  obtain ⟨hc, hf⟩ := ha0
  have hF := ha a hm (fun c hc' => by
    rw [Option.isNone_iff_eq_none.mp hc] at hc'; cases hc')
  split at hf
  · rename_i x q st body hfact
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hf
    obtain ⟨hx, rfl⟩ := hf
    rw [hfact] at hF
    obtain ⟨w, sto, ls, _, hp, hs, hl, _⟩ := hF
    exact ⟨w, sto, ls, by simpa [PointClaims.mapEnv, hM _ _ hx] using hp, hs, hl⟩
  · cases hf

/-- Whether a target atom follows from the source's linear facts, prepared as
`K` (`knownOf a`): an unconditional `int` or `bound` atom they give; a linear
atom they entail, unconditional from the unconditional facts, conditional on
a slot from those with the facts conditional on a source slot of its class
at the same answer. -/
def linearFollowsIn (K : Linear.Known Term) (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom)
    (B : Option (Term → Term)) (t : IndexAtom) : Bool :=
  match t.fact with
  | .linear F => match t.cond with
    | none => linearEntailed M m a B K (linearRaw a) F
    | some c' => (M (PointClaims.slot m c')).any fun c =>
        let known := linearRaw a ++ condFacts a c t.negated
        linearEntailed M m a B (Linear.Known.build known (rangesRaw a)) known F
  | .every s p stop _ =>
      (stop == (HeapKnowledge.Term.now .length s p) &&
        linearEntailed M m a B K (linearRaw a) (.le [((HeapKnowledge.Term.now .length s p), 1)] 0)) ||
      (elementsKnown M m a s p && linearEntailed M m a B K (linearRaw a) (.le [(stop, 1)] 0))
  | .bound x k st =>
      t.cond.isNone && (lengthBoundIn K (M (PointClaims.slot m x)) a (pickSlot M m a k) st ||
        match B with
        | some c => lengthBoundVia c (M (PointClaims.slot m x)) a (pickSlot M m a k) st
        | none => false)
  | .int k => t.cond.isNone && (intSlot a (pickSlot M m a k) ||
      match B with
      | some c => bridgedDefined c a (c (.value (pickSlot M m a k)))
      | none => false)
  | _ => false

/-- `linearFollowsIn` over the source's own facts. -/
def linearFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom)
    (B : Option (Term → Term)) (t : IndexAtom) : Bool :=
  linearFollowsIn (knownOf a) M m a B t

theorem linearEntailed_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom}
    {B : Option (Term → Term)} {known : List (Linear.Fact Term)} {F : Linear.Fact Term} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hB : ∀ c, B = some c → ∀ t, termValue ε ρ h (c t) = termValue ε ρ h t)
    {K : Linear.Known Term} (hf : linearEntailed M m a B K known F = true) (ha : IndexHolds ε a ρ h)
    (hK : K.Holds (termValuation ε ρ h)) (hk : ∀ G ∈ known, G.Holds (termValuation ε ρ h)) :
    (IndexFact.linear F).HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  unfold linearEntailed at hf
  split at hf
  · split at hf
    · rename_i F' hF'
      simp only [Bool.and_eq_true, List.all_eq_true] at hf
      obtain ⟨hv, he⟩ := hf
      have hv' : ∀ x ∈ F.vars, ∀ y, (fun t => some (pickTerm M m a t)) x = some y →
          termValuation ε ρ h y = termValuation ε (PointClaims.mapEnv m ρ) h x := by
        intro x _ y hy; cases hy; simp only [termValuation, pickTerm_eq hM]
      refine ⟨fun x hx => ?_, (Linear.Fact.holds_mapVars hF' hv').mp
        (Linear.Known.entails_sound hK he)⟩
      obtain ⟨y, hy, hxy⟩ := Linear.Fact.mapVars_vars_fwd hF' x hx
      cases hxy
      have := termDefined_sound ha (hv _ hy)
      rw [pickTerm_eq hM] at this
      exact this
    · cases hf
  · rename_i c
    have hc := hB c rfl
    split at hf
    · rename_i F' hF'
      simp only [Bool.and_eq_true, List.all_eq_true] at hf
      obtain ⟨hv, he⟩ := hf
      have hv' : ∀ x ∈ F.vars, ∀ y, (fun t => some (c (pickTerm M m a t))) x = some y →
          termValuation ε ρ h y = termValuation ε (PointClaims.mapEnv m ρ) h x := by
        intro x _ y hy; cases hy; simp only [termValuation, hc, pickTerm_eq hM]
      refine ⟨fun x hx => ?_, (Linear.Fact.holds_mapVars hF' hv').mp
        (Linear.entailsWith_sound he (bridgeFacts_holds hc hk) (bridgeFacts_holds hc (rangesRaw_holds ha)))⟩
      obtain ⟨y, hy, hxy⟩ := Linear.Fact.mapVars_vars_fwd hF' x hx
      cases hxy
      have hd := bridgedDefined_sound hc ha (hv _ hy)
      rw [hc, pickTerm_eq hM] at hd
      exact hd
    · cases hf

theorem linearFollowsIn_sound {K : Linear.Known Term} {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom}
    {B : Option (Term → Term)} {t : IndexAtom} {ρ h} (hK : K.Holds (termValuation ε ρ h))
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hB : ∀ c, B = some c → ∀ t, termValue ε ρ h (c t) = termValue ε ρ h t)
    (hf : linearFollowsIn K M m a B t = true) (ha : IndexHolds ε a ρ h)
    (hcond : ∀ c, t.cond = some c → tagHolds .truthy (PointClaims.mapEnv m ρ c) = !t.negated) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  unfold linearFollowsIn at hf
  cases ht : t.fact with
  | int k =>
    rw [ht] at hf
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hf
    rcases hf.2 with hi | hi
    · have := intSlot_sound ha hi
      rw [pickSlot_eq hM] at this
      exact this
    · cases hBv : B with
      | none => rw [hBv] at hi; cases hi
      | some c =>
        rw [hBv] at hi
        have hc := hB c hBv
        have := bridgedDefined_sound hc ha hi
        rw [hc, termValue_value, pickSlot_eq hM] at this
        exact this
  | linear F =>
    rw [ht] at hf
    simp only at hf
    split at hf
    · exact linearEntailed_sound hM hB hf ha hK (linearRaw_holds ha)
    · rename_i c' hc'
      obtain ⟨c, hc, hf⟩ := List.any_eq_true.mp hf
      have hcv : tagHolds .truthy (ρ c) = !t.negated := by
        rw [hM _ _ hc]; exact hcond c' hc'
      have hkn : ∀ G ∈ linearRaw a ++ condFacts a c t.negated, G.Holds (termValuation ε ρ h) := by
        intro G hG
        rcases List.mem_append.mp hG with hG | hG
        · exact linearRaw_holds ha G hG
        · exact condFacts_holds ha hcv G hG
      exact linearEntailed_sound hM hB hf ha (Linear.Known.build_holds hkn (rangesRaw_holds ha)) hkn
  | bound x k st =>
    rw [ht] at hf
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hf
    obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ : ∃ s ls b idx, Footprints.storeOf (PointClaims.mapEnv m ρ x) = some s ∧
        h[s]? = some (.arr ls) ∧ ρ (pickSlot M m a k) = .num b ∧ indexOfBits b = some idx ∧
        idx + (if st then 1 else 0) ≤ ls.length := by
      rcases hf.2 with hb | hb
      · exact lengthBoundIn_sound hK (v := PointClaims.mapEnv m ρ x) (fun y hy => hM _ y hy) hb ha
      · cases hBv : B with
        | none => rw [hBv] at hb; cases hb
        | some c =>
          rw [hBv] at hb
          exact lengthBoundVia_sound (hB c hBv) (v := PointClaims.mapEnv m ρ x) (fun y hy => hM _ y hy) hb ha
    rw [pickSlot_eq hM] at hb
    exact ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩
  | every s p stop body =>
    rw [ht] at hf
    simp only [Bool.or_eq_true] at hf
    rcases hf with hf | hf
    · simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨rfl, hf⟩ := hf
      have hlin := linearEntailed_sound hM hB hf ha hK (linearRaw_holds ha)
      have hd := hlin.1 (HeapKnowledge.Term.now .length s p) (by simp [Linear.Fact.vars])
      obtain ⟨w, n, hw, hn, hterm⟩ := termValue_isSome hd rfl
      obtain ⟨sto, ls, hsto, hls, rfl, -⟩ := lengthOf_store hn
      have hle := hlin.2
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hterm, Option.getD_some, Int.one_mul, Int.add_zero] at hle
      refine ⟨w, sto, ls, ls.length, hw, elementsOf_store hsto, hls, hterm, ?_⟩
      intro i hi
      omega
    · simp only [Bool.and_eq_true] at hf
      obtain ⟨he, hz⟩ := hf
      obtain ⟨w, sto, ls, hp, hs, hl⟩ := elementsKnown_sound hM ha he
      have hlin := linearEntailed_sound hM hB hz ha hK (linearRaw_holds ha)
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hlin.1 stop (by simp [Linear.Fact.vars]))
      have hle := hlin.2
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hn, Option.getD_some] at hle
      exact ⟨w, sto, ls, n, hp, hs, hl, hn, fun i hi => by omega⟩
  | index _ | length _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | apart _ _ | storeApart _ _ _ _ => rw [ht] at hf; cases hf

theorem linearFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom}
    {B : Option (Term → Term)} {t : IndexAtom} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hB : ∀ c, B = some c → ∀ t, termValue ε ρ h (c t) = termValue ε ρ h t)
    (hf : linearFollows M m a B t = true) (ha : IndexHolds ε a ρ h)
    (hcond : ∀ c, t.cond = some c → tagHolds .truthy (PointClaims.mapEnv m ρ c) = !t.negated) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h :=
  linearFollowsIn_sound (knownOf_holds ha) hM hB hf ha hcond

/-! ## Guarded facts (ARITHMETIC.md, "Guarded clauses")

A guarded fact holds where its guard's path reads its tag's value or its
body holds. A read link restates a guard's path toward its root, as the read
bridge restates a term: a path read from a link's value is the path read
from its cell with the link's field before it, the link optional or not
(`ReadGave` reads an absent key as `undefined`). -/

/-- The read links a guard's path follows, as `(cell, field, value)`: the
reads of string-keyed fields, optional ones included. -/
def guardReads (ls : HeapLinks.Links) : List (Nat × String × Nat) :=
  ls.filterMap fun g => if g.alias then none else match g.field with
    | .str f => some (g.cell, f, g.value)
    | .sym _ => none

theorem guardReads_read {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {c v : Nat} {f : String} (hm : (c, f, v) ∈ guardReads ls) (p : List String) :
    readGuard h (ρ c) (f :: p) = readGuard h (ρ v) p := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hm
  split at hgm
  · cases hgm
  · rename_i ha
    split at hgm
    · rename_i f' hf'
      simp only [Option.some.injEq, Prod.mk.injEq] at hgm
      obtain ⟨rfl, rfl, rfl⟩ := hgm
      have hlg := hl g hg
      have ha' : g.alias = false := by simpa using ha
      simp only [ha', Bool.false_eq_true, ite_false] at hlg
      cases ho : g.optional
      · simp only [ho, Bool.false_eq_true, ite_false] at hlg
        obtain ⟨flds, cd, oid, l, he, hlk, hv⟩ := hlg
        rw [hf'] at hlk
        rw [he]
        simp only [readGuard, hlk, hv]
      · simp only [ho, ite_true] at hlg
        obtain ⟨flds, cd, oid, he, hr⟩ := hlg
        rw [he]
        unfold HeapFacts.ReadGave at hr
        rw [hf'] at hr
        cases hlk : flds.lookup (.str f') with
        | some l => rw [hlk] at hr; simp only [readGuard, hlk, hr]
        | none => rw [hlk] at hr; simp only [readGuard, hlk, hr.1, hr.2, ite_true]
    · cases hgm

/-- A guard's path restated by read links toward its root (`liftTerm`): its
slot taken to a slot of its class (`r`); where a read gives the slot's value
as field `f` read from slot `c`, the path from `c` with `f` before it, at
most `n` times. -/
def liftGuard (r : Nat → Nat) (reads : List (Nat × String × Nat)) : Nat → Nat → List String → Nat × List String
  | 0, s, p => (r s, p)
  | n + 1, s, p => match reads.find? (fun g => r g.2.2 == r s) with
    | some (c, f, _) => liftGuard r reads n c (f :: p)
    | none => (r s, p)

theorem liftGuard_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {r : Nat → Nat} (hr : ∀ x, ρ (r x) = ρ x) :
    ∀ n s p, readGuard h (ρ (liftGuard r (guardReads ls) n s p).1) (liftGuard r (guardReads ls) n s p).2 =
      readGuard h (ρ s) p := by
  intro n
  induction n with
  | zero => intro s p; simp only [liftGuard, hr]
  | succ n ih =>
    intro s p
    simp only [liftGuard]
    split
    · rename_i c f v hfind
      have hm := List.mem_of_find?_eq_some hfind
      have hrv : r v = r s := by simpa using List.find?_some hfind
      rw [ih, guardReads_read hl hm]
      rw [← hr v, hrv, hr]
    · simp only [hr]

/-- A guard's path restated by read links toward its end: where a read link
of a slot of `s`'s class (`cls`) gives the field `f` its path starts with as
slot `v`, the path's rest from `v`, at most `n` times. -/
def lowerGuard (reads : List (Nat × String × Nat)) (cls : Nat → List Nat) : Nat → Nat → List String → Nat × List String
  | 0, s, p => (s, p)
  | _ + 1, s, [] => (s, [])
  | n + 1, s, f :: q => match reads.find? (fun g => (cls s).contains g.1 && g.2.1 == f) with
    | some (_, _, v) => lowerGuard reads cls n v q
    | none => (s, f :: q)

theorem lowerGuard_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) :
    ∀ n s p, readGuard h (ρ (lowerGuard (guardReads ls) (HeapLinks.aliases ls) n s p).1)
      (lowerGuard (guardReads ls) (HeapLinks.aliases ls) n s p).2 = readGuard h (ρ s) p := by
  intro n
  induction n with
  | zero => intro s p; rfl
  | succ n ih =>
    intro s p
    cases p with
    | nil => rfl
    | cons f q =>
      simp only [lowerGuard]
      split
      · rename_i c f' v hfind
        have hm := List.mem_of_find?_eq_some hfind
        have hc := List.find?_some hfind
        simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
        obtain ⟨hcs, rfl⟩ := hc
        rw [ih, ← guardReads_read hl hm q, HeapLinks.aliases_eq hl hcs]
      · rfl

/-- The left sides of the sum rule's disjunctions on slot `k`: where `k`
holds no double `2^53`, each holds. -/
def pastLefts (as : List IndexAtom) (k : Nat) : List IndexAtom :=
  as.filterMap fun a => match a.cond, a.fact with
    | none, .either A (.pastSafe k') => if k' == k then some { fact := A } else none
    | _, _ => none

theorem pastLefts_holds {as : List IndexAtom} {ρ h k} (he : IndexHolds ε as ρ h)
    (hk : ¬ (IndexFact.pastSafe k).HoldsAt ε ρ h) : IndexHolds ε (pastLefts as k) ρ h := by
  intro b hb _
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hb
  split at hm
  · rename_i A k' hcn hf
    split at hm
    · rename_i hkk
      cases hm
      have hat := he a ha (fun c hc => by rw [hcn] at hc; cases hc)
      rw [hf] at hat
      simp only [beq_iff_eq] at hkk
      subst hkk
      exact hat.resolve_right hk
    · cases hm
  · cases hm

/-- The left sides of the sum rule's disjunctions (`IndexFact.pastSafe` on
the right) whose slot the atoms state a safe integer: the right side, the
double `2^53`, is no safe integer (`pastClash`). -/
def releasePast (as : List IndexAtom) : List IndexAtom :=
  as.filterMap fun a => match a.cond, a.fact with
    | none, .either A (.pastSafe k) => if intSlot as k then some { fact := A } else none
    | _, _ => none

theorem releasePast_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    IndexHolds ε (releasePast as) ρ h := by
  intro b hb _
  obtain ⟨a, ha, hm⟩ := List.mem_filterMap.mp hb
  split at hm
  · rename_i A k hcn hf
    split at hm
    · rename_i hk
      cases hm
      have hat := he a ha (fun c hc => by rw [hcn] at hc; cases hc)
      rw [hf] at hat
      rcases hat with hA | hB
      · exact hA
      · have hi := intSlot_sound he hk
        simp only [IndexFact.HoldsAt] at hB
        rw [hB] at hi
        simp [intValue, SafeIntegers.safeIntOfBits_pastSafe] at hi
    · cases hm
  · cases hm

/-- Whether atoms `as` entail a fact, its terms and guard paths restated by
`lt` and `lg`: a linear fact as `linearEntailed` reads one; a guarded fact
where an unconditional atom states a guard of the same tag at a path
restated alike, and the body follows from the atoms and that atom's body; or
where its guard's path, restated toward its end by `ld`, reads a slot alone,
and its body follows; or where `tags` states the guard's path, or its
restatement, reads the tag's value. -/
def guardEntails (lt : Term → Term) (lg ld : Nat → List String → Nat × List String)
    (tags : Nat → List String → GuardTag → Bool) : List IndexAtom → IndexFact → Bool
  | as, .either A B => guardEntails lt lg ld tags as A || guardEntails lt lg ld tags as B ||
      match B with
      | .pastSafe k => guardEntails lt lg ld tags (as ++ pastLefts as k) A && pastLefts as k != []
      | _ => false
  | as, .linear F => match F.mapVars (some ∘ lt) with
    | some F' => F'.vars.all (bridgedDefined lt as) &&
        Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) F'
    | none => false
  | as, .guarded s p t B =>
    tags s p t || tags (ld s p).1 (ld s p).2 t ||
    (as.any fun a => a.cond.isNone && match a.fact with
      | .guarded s' p' t' B' => t' == t && lg s' p' == lg s p && guardEntails lt lg ld tags (as ++ [{ fact := B' }]) B
      | _ => false) ||
    ((ld s p).2.isEmpty && guardEntails lt lg ld tags as B)
  | as, .int k => intSlot as k
  | as, .pastSafe k => as.any fun a => a.cond.isNone && a.fact == .pastSafe k
  | _, _ => false

theorem guardEntails_sound {lt : Term → Term} {lg ld : Nat → List String → Nat × List String}
    {tags : Nat → List String → GuardTag → Bool} {ρ : Env} {h : Heap}
    (hlt : ∀ t, termValue ε ρ h (lt t) = termValue ε ρ h t)
    (hlg : ∀ s p, readGuard h (ρ (lg s p).1) (lg s p).2 = readGuard h (ρ s) p)
    (hld : ∀ s p, readGuard h (ρ (ld s p).1) (ld s p).2 = readGuard h (ρ s) p)
    (htags : ∀ s p t, tags s p t = true → readGuard h (ρ s) p = some t.val) :
    ∀ (F : IndexFact) (as : List IndexAtom), guardEntails lt lg ld tags as F = true → IndexHolds ε as ρ h →
      F.HoldsAt ε ρ h := by
  intro F
  induction F with
  | either A B ihA ihB =>
    intro as hf ha
    simp only [guardEntails] at hf
    rcases Bool.or_eq_true_iff.mp hf with hf | hP
    · rcases Bool.or_eq_true_iff.mp hf with hA | hB
      · exact .inl (ihA as hA ha)
      · exact .inr (ihB as hB ha)
    · split at hP
      · rename_i k
        obtain ⟨hA, -⟩ := Bool.and_eq_true_iff.mp hP
        by_cases hk : (IndexFact.pastSafe k).HoldsAt ε ρ h
        · exact .inr hk
        · refine .inl (ihA _ hA fun b hb hc => ?_)
          rcases List.mem_append.mp hb with hb | hb
          · exact ha b hb hc
          · exact pastLefts_holds ha hk b hb hc
      · cases hP
  | linear F =>
    intro as hf ha
    simp only [guardEntails] at hf
    split at hf
    · rename_i F' hF'
      simp only [Bool.and_eq_true, List.all_eq_true] at hf
      obtain ⟨hv, he⟩ := hf
      have hv' : ∀ x ∈ F.vars, ∀ y, (some ∘ lt) x = some y → termValuation ε ρ h y = termValuation ε ρ h x := by
        intro x _ y hy; cases hy; simp only [termValuation, hlt]
      refine ⟨fun x hx => ?_, (Linear.Fact.holds_mapVars hF' hv').mp
        (Linear.entailsWith_sound he (bridgeFacts_holds hlt (linearRaw_holds ha))
          (bridgeFacts_holds hlt (rangesRaw_holds ha)))⟩
      obtain ⟨y, hy, hxy⟩ := Linear.Fact.mapVars_vars_fwd hF' x hx
      cases hxy
      have hd := bridgedDefined_sound hlt ha (hv _ hy)
      rw [hlt] at hd
      exact hd
    · cases hf
  | guarded s p t B ih =>
    intro as hf ha
    simp only [guardEntails, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hf
    rcases hf with ((ht | htl) | hpool) | ⟨hp, hB⟩
    · exact ⟨t.val, htags s p t ht, .inl rfl⟩
    · exact ⟨t.val, by rw [← hld s p]; exact htags _ _ t htl, .inl rfl⟩
    · obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hpool
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
      obtain ⟨hcond, hm⟩ := hm
      split at hm
      · rename_i s' p' t' B' hfa
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨⟨rfl, hpath⟩, hB⟩ := hm
        have hat := ha a haa fun b hb => by rw [hcond] at hb; cases hb
        rw [hfa] at hat
        obtain ⟨v, hv, hor⟩ := hat
        have hread : readGuard h (ρ s) p = some v := by rw [← hlg s p, ← hpath, hlg]; exact hv
        refine ⟨v, hread, hor.imp id fun hB' => ih (as ++ [{ fact := B' }]) hB fun b hb hc => ?_⟩
        rcases List.mem_append.mp hb with hb | hb
        · exact ha b hb hc
        · simp only [List.mem_singleton] at hb; subst hb; exact hB'
      · cases hm
    · refine ⟨ρ (ld s p).1, ?_, .inr (ih as hB ha)⟩
      rw [← hld s p, hp]; rfl
  | int k =>
    intro as hf ha
    exact intSlot_sound ha hf
  | pastSafe k =>
    intro as hf ha
    obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hm
    have hat := ha a haa fun b hb => by rw [hm.1] at hb; cases hb
    rw [hm.2] at hat
    exact hat
  | index _ | length _ _ | bound _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ =>
    intro as hf; simp [guardEntails] at hf

/-- Whether an unconditional atom states that a slot holds the double `2^53`
while the atoms state it a safe integer: no heap meets them both. -/
def pastClash (as : List IndexAtom) : Bool :=
  as.any fun a => a.cond.isNone && match a.fact with
    | .pastSafe k => intSlot as k
    | _ => false

theorem pastClash_sound {as : List IndexAtom} {ρ h} (hc : pastClash as = true) (ha : IndexHolds ε as ρ h) : False := by
  obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hn, hm⟩ := hm
  have hat := ha a haa fun b hb => by rw [hn] at hb; cases hb
  split at hm
  · rename_i k hfa
    rw [hfa] at hat
    have hi := intSlot_sound ha hm
    simp only [IndexFact.HoldsAt] at hat
    rw [hat] at hi
    simp [intValue, SafeIntegers.safeIntOfBits_pastSafe] at hi
  · cases hm

/-- Entailment by finite case splitting. Both arms of an unconditional
 disjunction must entail the target. Exhausting the fuel refuses the split. -/
def caseEntails (check : List IndexAtom → IndexFact → Bool) : Nat → List IndexAtom → IndexFact → Bool
  | 0, as, F => check as F || check as (.linear (.le [] (-1))) || pastClash as
  | n + 1, as, F => caseEntails check 0 as F || as.any fun a => a.cond.isNone && match a.fact with
    | .either _ (.pastSafe _) => false
    | .either A B =>
      caseEntails check n (as.erase a ++ [{ fact := A }]) F &&
      caseEntails check n (as.erase a ++ [{ fact := B }]) F
    | _ => false

theorem caseEntails_sound {check : List IndexAtom → IndexFact → Bool} {ρ : Env} {h : Heap}
    (hcheck : ∀ as F, check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h) :
    ∀ n as F, caseEntails check n as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h := by
  intro n
  induction n with
  | zero =>
    intro as F hf ha
    simp only [caseEntails] at hf
    rcases Bool.or_eq_true_iff.mp hf with hf | hf
    · rcases Bool.or_eq_true_iff.mp hf with hf | hf
      · exact hcheck as F hf ha
      · have bad := (hcheck as (.linear (.le [] (-1))) hf ha).2
        simp [Linear.Fact.Holds, Linear.Form.eval] at bad
    · exact (pastClash_sound hf ha).elim
  | succ n ih =>
    intro as F hf ha
    simp only [caseEntails] at hf
    rcases Bool.or_eq_true_iff.mp hf with hf | hf
    · rcases Bool.or_eq_true_iff.mp hf with hf | hf
      · rcases Bool.or_eq_true_iff.mp hf with hf | hf
        · exact hcheck as F hf ha
        · have bad := (hcheck as (.linear (.le [] (-1))) hf ha).2
          simp [Linear.Fact.Holds, Linear.Form.eval] at bad
      · exact (pastClash_sound hf ha).elim
    · obtain ⟨a, haa, ht⟩ := List.any_eq_true.mp hf
      obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp ht
      have hc : a.cond = none := Option.isNone_iff_eq_none.mp hc
      split at ht
      · cases ht
      · rename_i A B _ he
        obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp ht
        have hab := ha a haa (fun b hb => by rw [hc] at hb; cases hb)
        rw [he] at hab
        have extend : ∀ C : IndexFact, C.HoldsAt ε ρ h → IndexHolds ε (as.erase a ++ [{ fact := C }]) ρ h := by
          intro C hC b hb hbcond
          rcases List.mem_append.mp hb with hb | hb
          · exact ha b (List.mem_of_mem_erase hb) hbcond
          · simp only [List.mem_singleton] at hb; subst hb; exact hC
        rcases hab with hA' | hB'
        · exact ih _ F hA (extend A hA')
        · exact ih _ F hB (extend B hB')
      · cases ht

/-- Whether a guarded target atom, unconditional, follows: its fact renamed
into the source's slots (`pickSlot`), entailed by the source's atoms with its
terms and guard paths restated by the source's read links (`liftTerm`,
`liftGuard`). -/
def guardFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (ls : HeapLinks.Links)
    (tags : Nat → List String → GuardTag → Bool) (a : List IndexAtom) (t : IndexAtom) : Bool :=
  t.cond.isNone && match t.fact with
  | .guarded .. | .either .. | .linear .. => match t.fact.mapM (fun y => some (pickSlot M m a y)) with
    | some F =>
      let r := HeapLinks.rep (HeapLinks.classes ls)
      let reads := bridgeReads ls
      let greads := guardReads ls
      caseEntails (guardEntails (liftTerm r reads reads.length) (liftGuard r greads greads.length)
        (lowerGuard greads (HeapLinks.aliases ls) greads.length) tags) 8 (a ++ releasePast a) F
    | none => false
  | _ => false

theorem guardFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ls : HeapLinks.Links}
    {tags : Nat → List String → GuardTag → Bool} {a : List IndexAtom} {t : IndexAtom} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (htags : ∀ s p t, tags s p t = true → readGuard h (ρ s) p = some t.val)
    (hf : guardFollows M m ls tags a t = true) (ha : IndexHolds ε a ρ h) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  simp only [guardFollows, Bool.and_eq_true] at hf
  obtain ⟨-, hf⟩ := hf
  split at hf <;> try { cases hf }
  all_goals
    split at hf
    · rename_i F hF
      have hr := HeapLinks.rep_eq (HeapLinks.classes_one hl)
      have hF' := caseEntails_sound
        (fun as F => guardEntails_sound (liftTerm_eq hl hr _) (liftGuard_eq hl hr _)
          (lowerGuard_eq hl _) htags F as) 8 (a ++ releasePast a) F hf
          fun b hb hc => (List.mem_append.mp hb).elim (fun hb => ha b hb hc) (fun hb => releasePast_holds ha b hb hc)
      exact (IndexFact.holdsAt_mapM hF fun s _ y hy => by cases hy; exact pickSlot_eq hM s).mp hF'
    · cases hf

/-- Whether the source's read links lead from slot `x` through the path `p`
to a slot of `u`'s class. -/
def pathReaches (M : Nat → List Nat) (ls : HeapLinks.Links) (x : Nat) : List String → Nat → Bool
  | [], u => (M x).contains u
  | f :: p, u => ls.any fun g => !g.alias && !g.optional && (M x).contains g.cell && g.field == .str f &&
      pathReaches M ls g.value p u

theorem pathReaches_sound {M : Nat → List Nat} {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h) :
    ∀ (p : List String) (x u : Nat), pathReaches M ls x p u = true → readPath h (ρ x) p = some (ρ u) := by
  intro p
  induction p with
  | nil =>
    intro x u hr
    simp only [pathReaches, List.contains_iff_mem] at hr
    simp [readPath, hM _ _ hr]
  | cons f p ih =>
    intro x u hr
    simp only [pathReaches, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      List.contains_iff_mem] at hr
    obtain ⟨g, hg, ⟨⟨⟨⟨hal, hop⟩, hcell⟩, hfield⟩, hrest⟩⟩ := hr
    have hh := hl g hg
    simp only [hal, hop, Bool.false_eq_true, if_false] at hh
    obtain ⟨flds, c, oid, l, hobj, hlook, hv⟩ := hh
    rw [← hM _ _ hcell, hobj, readPath_cons (by rw [← hfield]; exact hlook) hv]
    exact ih g.value u hrest

/-- Two regions apart hold different stores. -/
theorem regionsApart_stores {h : Heap} {u w : Val} (ha : RegionsApart h u w) :
    ∀ s t, Footprints.storeOf u = some s → Footprints.storeOf w = some t → s ≠ t := by
  intro s t hs ht
  obtain ⟨sa, xs, sb, ys, hu, hw, hne⟩ := ha
  have hsa : sa = some s := by
    rcases hu with ⟨-, rfl⟩ | ⟨st, hst, hst', -⟩
    · simp [Footprints.storeOf, Footprints.fieldsOf] at hs
    · rw [hs] at hst'; cases hst'; exact hst
  have hsb : sb = some t := by
    rcases hw with ⟨-, rfl⟩ | ⟨st, hst, hst', -⟩
    · simp [Footprints.storeOf, Footprints.fieldsOf] at ht
    · rw [ht] at hst'; cases hst'; exact hst
  exact hne s (.inl hsa) t (.inl hsb)

/-- Whether an unconditional store separation, a target atom, follows from an
unconditional source atom separating the slots its paths reach through the
source's read links (`store-apart-links`): a region fact (`apart`), or a
store separation of the slots themselves. -/
def storeFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (ls : HeapLinks.Links)
    (a : List IndexAtom) (t : IndexAtom) : Bool :=
  t.cond.isNone && match t.fact with
  | .storeApart x p y q =>
    let reach (u w : Nat) := pathReaches M ls (PointClaims.slot m x) p u && pathReaches M ls (PointClaims.slot m y) q w ||
      pathReaches M ls (PointClaims.slot m x) p w && pathReaches M ls (PointClaims.slot m y) q u
    a.any fun s => s.cond.isNone && match s.fact with
      | .apart u w => reach u w
      | .storeApart u [] w [] => reach u w
      | _ => false
  | _ => false

theorem storeFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ls : HeapLinks.Links}
    {a : List IndexAtom} {t : IndexAtom} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (hf : storeFollows M m ls a t = true) (ha : IndexHolds ε a ρ h) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  simp only [storeFollows, Bool.and_eq_true] at hf
  obtain ⟨-, hf⟩ := hf
  split at hf
  case h_2 => cases hf
  rename_i x p y q hfact
  rw [hfact]
  obtain ⟨s, hs, hm⟩ := List.any_eq_true.mp hf
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hn, hm⟩ := hm
  have hat := ha s hs fun b hb => by rw [hn] at hb; cases hb
  -- the separated slots' stores differ, and the target's paths reach them
  have reach : ∀ u w, (∀ s t, Footprints.storeOf (ρ u) = some s → Footprints.storeOf (ρ w) = some t → s ≠ t) →
      (pathReaches M ls (PointClaims.slot m x) p u && pathReaches M ls (PointClaims.slot m y) q w ||
        pathReaches M ls (PointClaims.slot m x) p w && pathReaches M ls (PointClaims.slot m y) q u) = true →
      (IndexFact.storeApart x p y q).HoldsAt ε (PointClaims.mapEnv m ρ) h := by
    intro u w hne hr
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hr
    rcases hr with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨ρ u, ρ w, pathReaches_sound hM hl p _ u hx, pathReaches_sound hM hl q _ w hy, hne⟩
    · exact ⟨ρ w, ρ u, pathReaches_sound hM hl p _ w hx, pathReaches_sound hM hl q _ u hy,
        fun s t hs ht he => hne t s ht hs he.symm⟩
  split at hm
  · rename_i u w hsf
    rw [hsf] at hat
    exact reach u w (regionsApart_stores hat) hm
  · rename_i u w hsf
    rw [hsf] at hat
    obtain ⟨u', w', hu, hw, hne⟩ := hat
    simp only [readPath, Option.some.injEq] at hu hw
    subst hu; subst hw
    exact reach u w hne hm
  · cases hm

/-- A guarded target whose guard reads its slot's own value (path `[]`, a
read that always gives the value) follows from an unconditional source atom
its body follows from (`factFollows`). -/
def guardBodyFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom) (t : IndexAtom) : Bool :=
  t.cond.isNone && match t.fact with
  | .guarded _ [] _ B => a.any fun s => s.cond.isNone && factFollows M m s.fact B
  | _ => false

theorem guardBodyFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {a : List IndexAtom}
    {t : IndexAtom} {ρ h} (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x)
    (hf : guardBodyFollows M m a t = true) (ha : IndexHolds ε a ρ h) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  simp only [guardBodyFollows, Bool.and_eq_true] at hf
  obtain ⟨-, hf⟩ := hf
  split at hf
  · rename_i g tag B hfa
    rw [hfa]
    obtain ⟨s, hs, hm⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
    obtain ⟨hn, hm⟩ := hm
    exact ⟨_, rfl, Or.inr (factFollows_sound hM hm (ha s hs fun c hc => by rw [hn] at hc; cases hc))⟩
  · cases hf

/-- The linear facts known where a target atom's condition holds: the
source's facts `K` for an unconditional target; for one conditional on slot
`c'`, the source's unconditional linear facts with those conditional on a
slot `c` of `c'`'s class at the same answer (`condFacts`), as
`linearFollowsIn` reads them. Whether those of some such `c` entail `goal`. -/
def entailsUnder (K : Linear.Known Term) (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom)
    (t : IndexAtom) (goal : Linear.Fact Term) : Bool :=
  match t.cond with
  | none => K.entails goal
  | some c' => (M (PointClaims.slot m c')).any fun c =>
      (Linear.Known.build (linearRaw a ++ condFacts a c t.negated) (rangesRaw a)).entails goal

theorem entailsUnder_sound {K : Linear.Known Term} {M : Nat → List Nat} {m : PointClaims.Mapping}
    {a : List IndexAtom} {t : IndexAtom} {goal : Linear.Fact Term} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hK : K.Holds (termValuation ε ρ h)) (ha : IndexHolds ε a ρ h)
    (hcond : ∀ c, t.cond = some c → tagHolds .truthy (PointClaims.mapEnv m ρ c) = !t.negated)
    (he : entailsUnder K M m a t goal = true) : goal.Holds (termValuation ε ρ h) := by
  unfold entailsUnder at he
  split at he
  · exact Linear.Known.entails_sound hK he
  · rename_i c' hc'
    obtain ⟨c, hc, he⟩ := List.any_eq_true.mp he
    have hcv : tagHolds .truthy (ρ c) = !t.negated := by
      rw [hM _ _ hc]; exact hcond c' hc'
    have hkn : ∀ G ∈ linearRaw a ++ condFacts a c t.negated, G.Holds (termValuation ε ρ h) := by
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · exact linearRaw_holds ha G hG
      · exact condFacts_holds ha hcv G hG
    exact Linear.Known.entails_sound (Linear.Known.build_holds hkn (rangesRaw_holds ha)) he

/-- **Prefix weakening** of a quantified fact: a target `every(s', p, t, φ)`
follows from a source `every(x, p, u, φ')` over the array of `s'`'s class
(`M`), whose condition holds wherever the target's does (`condFollows`) and
whose body gives each of the target's (`bodyFactFollows`), where the
source's facts state `t` defined and, where the target's condition holds,
entail `t ≤ u` (`entailsUnder`): every index below `t` is below `u`. A bound
equal to the source's is its instance. -/
def everyPrefix (K : Linear.Known Term) (M : Nat → List Nat) (m : PointClaims.Mapping) (a : List IndexAtom)
    (t : IndexAtom) : Bool :=
  match t.fact with
  | .every s' p stop' body' =>
    let u := pickTerm M m a stop'
    termDefined a u && a.any fun src => condFollows M m src t && match src.fact with
      | .every x q st b => (M (PointClaims.slot m s')).contains x && q == p &&
          body'.all (fun F' => b.any fun F => bodyFactFollows M m F F') &&
          entailsUnder K M m a t (.le [(u, 1), (st, -1)] 0)
      | _ => false
  | _ => false

/-- **Prefix weakening is sound** (proved): where the target's condition
holds, from `every(x, p, u, φ')`, `t` defined and `t ≤ u`, the target
`every(s', p, t, φ)` holds. -/
theorem everyPrefix_sound {K : Linear.Known Term} {M : Nat → List Nat} {m : PointClaims.Mapping}
    {a : List IndexAtom} {t : IndexAtom} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hK : K.Holds (termValuation ε ρ h)) (ha : IndexHolds ε a ρ h)
    (hcond : ∀ c, t.cond = some c → tagHolds .truthy (PointClaims.mapEnv m ρ c) = !t.negated)
    (hf : everyPrefix K M m a t = true) : t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  unfold everyPrefix at hf
  split at hf
  · rename_i s' p stop' body' hfact
    rw [hfact]
    simp only [Bool.and_eq_true] at hf
    obtain ⟨hdef, hany⟩ := hf
    obtain ⟨src, hsrc, hm⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true] at hm
    obtain ⟨hcd, hm⟩ := hm
    have hS := ha src hsrc (condFollows_cond hM hcd hcond)
    split at hm
    · rename_i x q st b hsf
      rw [hsf] at hS
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨⟨hx, rfl⟩, hb⟩, hent⟩ := hm
      obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hS
      obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp (termDefined_sound ha hdef)
      have hle := entailsUnder_sound hM hK ha hcond hent
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hn', hn, Option.getD_some] at hle
      have hs' : PointClaims.mapEnv m ρ s' = ρ x := (hM _ _ (List.contains_iff_mem.mp hx)).symm
      refine ⟨w, sto, ls, n', by rw [hs']; exact hw, hsto, hls, by rw [← pickTerm_eq hM]; exact hn',
        fun i hi F' hF' => ?_⟩
      obtain ⟨F, hF, hbf⟩ := List.any_eq_true.mp (hb F' hF')
      simp only [bodyFactFollows, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hbf
      obtain ⟨hps, hmap⟩ := hbf
      refine (LinearClause.holdsAt_mapVars hmap fun y _ z hz => ?_).mp (hall i (by omega) F hF)
      exact boundFollows_sound hM (hps _ (lookup_mem' hz))
    · cases hm
  · cases hf

/-- Whether each target atom follows from a source atom or from the source's
linear facts, with the source's read links `ls` as the bridge (`bridgeOf`),
or, guarded, from the source's guarded atoms (`guardFollows`), `tags` stating
which guard paths read a tag's value, or from an atom its body follows from
(`guardBodyFollows`), or, a quantified fact, from one over a longer prefix
(`everyPrefix`). -/
def indicesCheckWith (tags : Nat → List String → GuardTag → Bool) (M : Nat → List Nat) (ls : HeapLinks.Links)
    (a b : List IndexAtom) (m : PointClaims.Mapping) : Bool :=
  let B := bridgeOf ls a b
  let K := Thunk.mk fun _ => knownOf a
  b.all fun t => a.any (fun s => indexFollows M m s t) || linearFollowsIn K.get M m a B t || guardFollows M m ls tags a t ||
    storeFollows M m ls a t || guardBodyFollows M m a t || everyPrefix K.get M m a t

/-- Whether a value set holds the value a guard's tag names alone. -/
def onlyTag (V : ValueSets.ValueSet) : GuardTag → Bool
  | .null => V == { nul := true }
  | .undef => V == { undef := true }
  | .tru => V == { tru := true }
  | .fls => V == { fls := true }

theorem onlyTag_mem {V : ValueSets.ValueSet} {t : GuardTag} {v : Val} (ho : onlyTag V t = true)
    (hv : V.mem v = true) : v = t.val := by
  cases t <;> simp only [onlyTag, beq_iff_eq] at ho <;> subst ho <;>
    cases v <;> simp_all [ValueSets.ValueSet.mem, ValueSets.Obj.mem, ValueSets.Lit.mem, ValueSets.Lit.none, GuardTag.val]

/-- A guard read of one field through a read the object gave (`ReadGave`). -/
theorem readGuard_readGave {fs : List (PropKey × Nat)} {cd : CallCode} {o : Nat} {f : String} {h : Heap} {v : Val}
    (hr : HeapFacts.ReadGave fs (.str f) h v) (p : List String) :
    readGuard h (.objAt fs cd o) (f :: p) = readGuard h v p := by
  unfold HeapFacts.ReadGave at hr
  cases hlk : fs.lookup (.str f) with
  | some l => rw [hlk] at hr; simp only [readGuard, hlk, hr]
  | none => rw [hlk] at hr; simp only [readGuard, hlk, hr.1, hr.2, ite_true]

/-- Which guard paths a knowledge states read a tag's value: a slot of the
class of a slot whose value fact holds the tag's value alone; one field of a
slot of that class whose cell fact does (`guard-tag`). -/
def guardTags (k : Knowledge) (s : Nat) : List String → GuardTag → Bool
  | [], t => k.values.any fun f => (HeapLinks.aliases k.links s).contains f.slot && onlyTag f.contents t
  | [g], t => k.cells.any fun f => (HeapLinks.aliases k.links s).contains f.slot && f.field == .str g &&
      onlyTag f.contents t
  | _, _ => false

theorem guardTags_sound {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    ∀ s p t, guardTags k s p t = true → readGuard h (ρ s) p = some t.val := by
  intro s p t ht
  match p, ht with
  | [], ht =>
    simp only [guardTags, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at ht
    obtain ⟨f, hf, hs, ho⟩ := ht
    have hv := hk.2.1 f hf
    rw [HeapLinks.aliases_eq hk.2.2.1 hs] at hv
    simp only [readGuard, onlyTag_mem ho hv]
  | [g], ht =>
    simp only [guardTags, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at ht
    obtain ⟨f, hf, ⟨hs, hg⟩, ho⟩ := ht
    obtain ⟨flds, cd, oid, v, he, hr, hv⟩ := hk.1 f hf
    rw [HeapLinks.aliases_eq hk.2.2.1 hs] at he
    rw [hg] at hr
    rw [he, readGuard_readGave hr [], onlyTag_mem ho hv]
    rfl

/-- A fact restated through a read of field `f` of slot `c` into slot `v`:
each guard's path and each term rooted at `c` starting with `f`, rooted at
`v` with the rest. A candidate a check decides (`guardedMeet`). -/
def IndexFact.lowerRead (c : Nat) (f : String) (v : Nat) : IndexFact → IndexFact
  | .linear F => .linear ((F.mapVars fun t => some (match t.path with
      | g :: q => if t.slot == c && g == f && !t.atEntry then (HeapKnowledge.Term.now t.kind v q) else t
      | [] => t)).getD F)
  | .guarded s p t B => match p with
    | g :: q => if s == c && g == f then .guarded v q t (B.lowerRead c f v) else .guarded s p t (B.lowerRead c f v)
    | [] => .guarded s p t (B.lowerRead c f v)
  | F => F

/-- The guarded atoms, each also restated through each read link of its
guard's first field (`IndexFact.lowerRead`). -/
def lowerGuards (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  as.flatMap fun a => match a.fact with
    | .guarded s (f :: _) _ _ => a :: (guardReads ls).filterMap fun (c, g, v) =>
        if c == s && g == f then some { a with fact := a.fact.lowerRead c f v } else none
    | .guarded .. => [a]
    | _ => []

/-- `indicesCheckWith` with no guard path known to read a tag. -/
def indicesCheckBy (M : Nat → List Nat) (ls : HeapLinks.Links) (a b : List IndexAtom) (m : PointClaims.Mapping) : Bool :=
  indicesCheckWith (fun _ _ _ => false) M ls a b m

theorem indicesCheckWith_sound {tags : Nat → List String → GuardTag → Bool} {M : Nat → List Nat}
    {ls : HeapLinks.Links} {a b : List IndexAtom} {m ρ h}
    (htags : ∀ s p t, tags s p t = true → readGuard h (ρ s) p = some t.val)
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h) (hc : indicesCheckWith tags M ls a b m = true)
    (ha : IndexHolds ε a ρ h) :
    IndexHolds ε b (PointClaims.mapEnv m ρ) h := by
  intro t ht hcond
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hc t ht) with hc' | hev
  case inr => exact everyPrefix_sound hM (knownOf_holds ha) ha hcond hev
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hgb
  case inr => exact guardBodyFollows_sound hM hgb ha
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hst
  case inr => exact storeFollows_sound hM hl hst ha
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hg
  case inr => exact guardFollows_sound hM hl htags hg ha
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hlin
  case inr => exact linearFollowsIn_sound (knownOf_holds ha) hM (fun c hc => bridgeOf_eq hl hc) hlin ha hcond
  obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp hc'
  simp only [indexFollows, Bool.and_eq_true] at hf
  obtain ⟨hfact, hcd⟩ := hf
  exact factFollows_sound hM hfact (ha s hs (condFollows_cond hM hcd hcond))

theorem indicesCheckBy_sound {M : Nat → List Nat} {ls : HeapLinks.Links} {a b : List IndexAtom} {m ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h) (hc : indicesCheckBy M ls a b m = true)
    (ha : IndexHolds ε a ρ h) :
    IndexHolds ε b (PointClaims.mapEnv m ρ) h :=
  indicesCheckWith_sound (fun _ _ _ hf => by cases hf) hM hl hc ha

/-- Atoms about slots past the pushed one. -/
def shiftIndices (as : List IndexAtom) : List IndexAtom := mapIndices (fun i => some (i + 1)) as

theorem shiftIndices_holds {as : List IndexAtom} {ρ h v} (he : IndexHolds ε as ρ h) :
    IndexHolds ε (shiftIndices as) (push v ρ) h :=
  mapIndices_holds (fun s t hst => by cases hst; rfl) he

/-- Whether a fact reads the environment alone: `index`, `int`, and a linear
fact of values. -/
def IndexFact.envOnly : IndexFact → Bool
  | .index _ | .int _ | .pastSafe _ => true
  | .linear F => F.vars.all Term.envOnly
  | .length _ _ | .bound _ _ _ | .element _ _ _ | .every _ _ _ _ | .apart _ _ => false
  | .either A B => A.envOnly && B.envOnly
  | .guarded _ p _ B => p.isEmpty && B.envOnly
  | .storeApart _ p _ q => p.isEmpty && q.isEmpty

/-- A fact reading the environment alone holds in every heap. -/
theorem IndexFact.holdsAt_envOnly {F : IndexFact} {ρ : Env} {h : Heap} (henv : F.envOnly = true)
    (hF : F.HoldsAt ε ρ h) (h' : Heap) : F.HoldsAt ε ρ h' := by
  induction F with
  | either A B ihA ihB =>
    simp only [IndexFact.envOnly, Bool.and_eq_true] at henv
    exact hF.imp (ihA henv.1) (ihB henv.2)
  | linear F => exact IndexFact.holdsAt_linear_heap henv hF
  | index _ | int _ | pastSafe _ => exact hF
  | length _ _ | bound _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ => simp [IndexFact.envOnly] at henv
  | storeApart a p b q =>
    simp only [IndexFact.envOnly, Bool.and_eq_true, List.isEmpty_iff] at henv
    obtain ⟨rfl, rfl⟩ := henv
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    exact ⟨u, w, by simpa [readPath] using hu, by simpa [readPath] using hw, hne⟩
  | guarded s p t B ih =>
    simp only [IndexFact.envOnly, Bool.and_eq_true, List.isEmpty_iff] at henv
    obtain ⟨rfl, hB⟩ := henv
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, by simpa [readGuard] using hv, hor.imp id (ih hB)⟩

/-- The atoms whose facts read the environment alone, kept by any heap change. -/
def envIndices (as : List IndexAtom) : List IndexAtom := as.filter (·.fact.envOnly)

theorem envIndices_holds {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) (h' : Heap) :
    IndexHolds ε (envIndices as) ρ h' := by
  intro a ha hc
  obtain ⟨ha, henv⟩ := List.mem_filter.mp ha
  exact IndexFact.holdsAt_envOnly henv (he a ha hc) h'

/-- The atoms a change keeps (`IndexFact.keptBy`), the facts reading no heap
among them. -/
def keptIndices (c : Changes) (first : Nat → String → Bool) (as : List IndexAtom) : List IndexAtom :=
  as.filter (fun a => a.fact.keptBy c first || a.fact.everyKept c first)

theorem keptIndices_holds {c : Changes} {first : Nat → String → Bool} {as : List IndexAtom} {ρ h h'}
    (he : IndexHolds ε as ρ h) (hc : c.Holds h h') (hf : FirstKept first ρ h h') :
    IndexHolds ε (keptIndices c first as) ρ h' := by
  intro a ha hcd
  obtain ⟨ha, hk⟩ := List.mem_filter.mp ha
  exact (Bool.or_eq_true_iff.mp hk).elim
    (fun hk => IndexFact.holdsAt_kept hc hf hk (he a ha hcd))
    (fun hk => IndexFact.everyKept_sound hc hf hk (he a ha hcd))

/-- The atoms a change keeps, a view's count read through a field among them
where `views` frames it (`IndexFact.keptWith`). -/
def keptIndicesWith (c : Changes) (first views : Nat → String → Bool) (as : List IndexAtom) : List IndexAtom :=
  as.filter (fun a => a.fact.keptWith c first views || a.fact.everyKept c first)

theorem keptIndicesWith_holds {c : Changes} {first views : Nat → String → Bool} {as : List IndexAtom} {ρ h h'}
    (he : IndexHolds ε as ρ h) (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h') :
    IndexHolds ε (keptIndicesWith c first views as) ρ h' := by
  intro a ha hcd
  obtain ⟨ha, hk⟩ := List.mem_filter.mp ha
  exact (Bool.or_eq_true_iff.mp hk).elim
    (fun hk => IndexFact.holdsAt_keptWith hc hf hv hk (he a ha hcd))
    (fun hk => IndexFact.everyKept_sound hc hf hk (he a ha hcd))

/-- The atoms a change keeps that also grows the stores `grown` names
(`IndexFact.grownWith`). -/
def keptIndicesGrown (c : Changes) (first views : Nat → String → Bool) (grown : Nat → Bool)
    (as : List IndexAtom) : List IndexAtom :=
  as.filter (fun a => a.fact.grownWith c first views grown || a.fact.everyKept c first)

theorem keptIndicesGrown_holds {c : Changes} {first views : Nat → String → Bool} {grown : Nat → Bool}
    {as : List IndexAtom} {ρ h h'}
    (he : IndexHolds ε as ρ h) (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h')
    (hg : StoresGrown grown ρ h h') :
    IndexHolds ε (keptIndicesGrown c first views grown as) ρ h' := by
  intro a ha hcd
  obtain ⟨ha, hk⟩ := List.mem_filter.mp ha
  exact (Bool.or_eq_true_iff.mp hk).elim
    (fun hk => IndexFact.holdsAt_grownWith hc hf hv hg hk (he a ha hcd))
    (fun hk => IndexFact.everyKept_sound hc hf hk (he a ha hcd))

/-- Nothing is kept by `first` where it names no location. -/
theorem firstKept_none {ρ : Env} {h h' : Heap} : FirstKept (fun _ _ => false) ρ h h' := by
  intro _ _ _ _ _ _ _ hf; cases hf

/-- Two kept-location predicates keep their union. -/
theorem firstKept_or {a b : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    (ha : FirstKept a ρ h h') (hb : FirstKept b ρ h h') :
    FirstKept (fun s g => a s g || b s g) ρ h h' := by
  intro s g fs cd o l v hf
  rcases Bool.or_eq_true_iff.mp hf with hf | hf
  · exact ha s g fs cd o l v hf
  · exact hb s g fs cd o l v hf

/-- The terms the linear facts of the atoms name, conditional ones included. -/
def linearTerms (as : List IndexAtom) : List Term :=
  ((linearFacts as).flatMap (·.vars) ++ as.flatMap fun a => match a.fact with
    | .linear F => F.vars
    | _ => []).eraseDups

/-- `linearTerms` deduplicated by hashing (`Linear.dedupHash_eq`). -/
def linearTermsHash (as : List IndexAtom) : List Term :=
  Linear.dedupHash ((linearFacts as).flatMap (·.vars) ++ as.flatMap fun a => match a.fact with
    | .linear F => F.vars
    | _ => [])

@[csimp] theorem linearTerms_eq_hash : @linearTerms = @linearTermsHash := by
  funext as; simp only [linearTerms, linearTermsHash, Linear.dedupHash_eq]

/-- The atoms with the terms of the slots of `drop` eliminated from the
linear facts with the strict bounds their inequalities give
(`Linear.strengthen`, `Linear.eliminateAll`): from the unconditional ones, and from
those with each condition's atoms, the derived facts naming none of them,
each of whose terms an atom states defined, appended under the condition
they were derived under. -/
def eliminateLinear (drop : List Nat) (as : List IndexAtom) : List IndexAtom :=
  -- No linear or length atom names a slot of `drop`: no term of `linearTerms` does.
  if !as.any (fun a => match a.fact with
    | .linear F => F.vars.any fun t => t.slots.any drop.contains
    | .length x n => drop.contains x || drop.contains n
    | _ => false) then as else
  let used := (linearTerms as).filter fun t => t.slots.any drop.contains
  if used.isEmpty then as else
  let keep := fun (known : List (Linear.Fact Term)) (F : Linear.Fact Term) =>
    !known.contains F && F.vars.all (fun t => !t.slots.any drop.contains && termDefined as t)
  let groups := (as.filterMap fun a => match a.cond, a.fact with
    | some c, .linear _ => if drop.contains c then none else some (c, a.negated)
    | _, _ => none).eraseDups
  as ++ ((Linear.eliminateAll (Linear.strengthen (linearFacts as)) used).filter (keep (linearFacts as))).map
    (fun F => ⟨.linear F, none, false⟩) ++
    groups.flatMap fun (c, neg) =>
      let known := linearFacts as ++ condFacts as c neg
      ((Linear.eliminateAll (Linear.strengthen known) used).filter (keep known)).map fun F => ⟨.linear F, some c, neg⟩

theorem eliminateLinear_holds {drop : List Nat} {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    IndexHolds ε (eliminateLinear drop as) ρ h := by
  simp only [eliminateLinear]
  split
  · exact he
  split
  · exact he
  · intro a ha hc
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact he a ha hc
      · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
        exact ⟨fun x hx => termDefined_sound he (hk.2 x hx).2,
          Linear.eliminateAll_sound (Linear.strengthen_holds (linearFacts_holds he)) F hF⟩
    · obtain ⟨⟨c, neg⟩, -, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
      have hcv := hc c rfl
      refine ⟨fun x hx => termDefined_sound he (hk.2 x hx).2, ?_⟩
      refine Linear.eliminateAll_sound (Linear.strengthen_holds (fun G hG => ?_)) F hF
      rcases List.mem_append.mp hG with hG | hG
      · exact linearFacts_holds he G hG
      · exact condFacts_holds he hcv G hG

/-- The atoms with the terms of the slots of `drop` eliminated
(`eliminateLinear`), after the sum rule's disjunctions it decides are released
(`releasePast`). -/
def eliminateIndices (drop : List Nat) (as : List IndexAtom) : List IndexAtom :=
  eliminateLinear drop (as ++ if drop.any (fun d => as.any fun a => a.fact == .pastSafe d ||
    match a.fact with | .either _ (.pastSafe k) => k == d | _ => false) then releasePast as else [])

theorem eliminateIndices_holds {drop : List Nat} {as : List IndexAtom} {ρ h} (he : IndexHolds ε as ρ h) :
    IndexHolds ε (eliminateIndices drop as) ρ h :=
  eliminateLinear_holds fun a ha hc => by
    rcases List.mem_append.mp ha with ha | ha
    · exact he a ha hc
    · split at ha
      · exact releasePast_holds he a ha hc
      · cases ha

/-- The linear facts, each with its terms defined, an atom's fact states: a
linear fact itself, and a length atom `length(x, n)` as the equality of `n`'s
value with `x`'s length. -/
def atomLinear : IndexFact → List (Linear.Fact Term)
  | .linear F => [F]
  | .length x n => [.le [(.value n, 1), (.length x, -1)] 0, .le [(.value n, -1), (.length x, 1)] 0]
  | _ => []

theorem atomLinear_holds {f : IndexFact} {ρ h} (hf : f.HoldsAt ε ρ h) :
    ∀ F ∈ atomLinear f, (IndexFact.linear F).HoldsAt ε ρ h := by
  intro F hF
  cases f with
  | linear G => simp only [atomLinear, List.mem_singleton] at hF; subst hF; exact hf
  | length x n =>
    obtain ⟨s, ls, hs, hl, hnv, hm⟩ := hf
    have hlen : termValue ε ρ h (.length x) = some (ls.length : Int) := lengthOf_of_store hs hl hm
    have hval : termValue ε ρ h (.value n) = some (ls.length : Int) := by
      simp only [termValue_value, hnv, intValue_length hm]
    have v1 : termValuation ε ρ h (.length x) = ls.length := by simp [termValuation, hlen]
    have v2 : termValuation ε ρ h (.value n) = ls.length := by simp [termValuation, hval]
    have hdef : ∀ t ∈ [Term.value n, Term.length x], (termValue ε ρ h t).isSome := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · rw [hval]; rfl
      · rw [hlen]; rfl
    simp only [atomLinear, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl
    · exact ⟨fun t ht => hdef t (by simpa [Linear.Fact.vars] using ht),
        by simp only [Linear.Fact.Holds, Linear.Form.eval, v1, v2]; omega⟩
    · exact ⟨fun t ht => hdef t (by simpa [Linear.Fact.vars, or_comm] using ht),
        by simp only [Linear.Fact.Holds, Linear.Form.eval, v1, v2]; omega⟩
  | index _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | every _ _ _ _ | apart _ _ | storeApart _ _ _ _ => simp [atomLinear] at hF

/-- A term rooted at a dropped slot restated by reads toward a kept root:
while its root is dropped, where a read gives the root's value as field `f`
read from slot `c`, the term rooted at `c` with `f` before its path; none
where no read reaches a kept root within `n` steps. -/
def liftDropped (dropped : Nat → Bool) (reads : List (Nat × String × Nat)) : Nat → Term → Option Term
  | 0, t => if dropped t.slot && !t.atEntry then none else some t
  | n + 1, t => if dropped t.slot && !t.atEntry then match reads.find? (·.2.2 == t.slot) with
      | some (c, f, _) => liftDropped dropped reads n (HeapKnowledge.Term.now t.kind c (f :: t.path))
      | none => none
    else some t

theorem liftDropped_eq {ls : HeapLinks.Links} {dropped : Nat → Bool} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) :
    ∀ n t t', liftDropped dropped reads n t = some t' → termValue ε ρ h t' = termValue ε ρ h t := by
  intro n
  induction n with
  | zero => intro t t' ht; simp only [liftDropped] at ht; split at ht <;> simp_all
  | succ n ih =>
    intro t t' ht
    simp only [liftDropped] at ht
    split at ht
    · rename_i hcond
      have hne : t.atEntry = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond; exact hcond.2
      split at ht
      · rename_i c f v hfind
        have hm := hr _ (List.mem_of_find?_eq_some hfind)
        have hv : v = t.slot := by simpa using List.find?_some hfind
        rw [ih _ _ ht, bridgeReads_term hl hm, hv]
        obtain ⟨k0, s0, p0, a0⟩ := t
        simp only at hne; subst hne; rfl
      · cases ht
    · cases ht; rfl

/-- The linear facts of atoms naming a term rooted at a dropped slot,
restated where reads give that slot's value as fields read in turn from a
kept slot (`liftDropped`, `readBridge`); each under its atom's condition. -/
def restateReads (ls : HeapLinks.Links) (dropped : Nat → Bool) (as : List IndexAtom) : List IndexAtom :=
  let reads := (bridgeReads ls).filter fun g => dropped g.2.2
  if reads.isEmpty then [] else
  as.flatMap fun a => (atomLinear a.fact).filterMap fun F =>
    if F.vars.any (dropped ·.slot) then
      (F.mapVars (liftDropped dropped reads reads.length)).map fun F' => { a with fact := .linear F' }
    else none

theorem restateReads_holds {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) : IndexHolds ε (restateReads ls dropped as) ρ h := by
  simp only [restateReads]
  split
  · intro a ha; cases ha
  · intro a ha hc
    obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨F, hF, hab⟩ := List.mem_filterMap.mp ha
    split at hab
    · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
      have hbF := atomLinear_holds (he b hb hc) F hF
      exact (IndexFact.holdsAt_linear_mapVars hF' fun x _ y hy =>
        liftDropped_eq hl (fun g hg => (List.mem_filter.mp hg).1) _ x y hy).mpr hbF
    · cases hab

/-- The plain read links: a slot's value read as field `f` of slot `c`. -/
def plainReads (ls : HeapLinks.Links) : List (Nat × String × Nat) :=
  ls.filterMap fun g => if g.alias || g.optional then none else match g.field with
    | .str f => some (g.cell, f, g.value)
    | .sym _ => none

/-- A path rooted at a dropped slot restated by plain reads toward a kept
root: while its root is dropped, where a read gives the root's value as
field `f` of slot `c`, the path rooted at `c` with `f` before it. -/
def liftPath (dropped : Nat → Bool) (reads : List (Nat × String × Nat)) : Nat → Nat × List String →
    Option (Nat × List String)
  | 0, (s, p) => if dropped s then none else some (s, p)
  | n + 1, (s, p) => if dropped s then match reads.find? (·.2.2 == s) with
      | some (c, f, _) => liftPath dropped reads n (c, f :: p)
      | none => none
    else some (s, p)

theorem liftPath_eq {ls : HeapLinks.Links} {dropped : Nat → Bool} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ plainReads ls) :
    ∀ n s p s' p', liftPath dropped reads n (s, p) = some (s', p') → readPath h (ρ s') p' = readPath h (ρ s) p := by
  intro n
  induction n with
  | zero => intro s p s' p' ht; simp only [liftPath] at ht; split at ht <;> simp_all
  | succ n ih =>
    intro s p s' p' ht
    simp only [liftPath] at ht
    split at ht
    · split at ht
      · rename_i c f v hfind
        have hm := hr _ (List.mem_of_find?_eq_some hfind)
        have hv : v = s := by simpa using List.find?_some hfind
        subst hv
        rw [ih _ _ _ _ ht]
        obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hm
        split at hgm
        · cases hgm
        · rename_i hao
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hao
          split at hgm
          · rename_i f' hf'
            simp only [Option.some.injEq, Prod.mk.injEq] at hgm
            obtain ⟨rfl, rfl, rfl⟩ := hgm
            have := hl g hg
            simp only [hao.1, hao.2, Bool.false_eq_true, ite_false] at this
            obtain ⟨flds, cd, oid, l, he, hlk, hval⟩ := this
            rw [hf'] at hlk
            rw [he, readPath_cons hlk hval]
          · cases hgm
      · cases ht
    · cases ht; rfl

/-- The store separations of unconditional atoms naming a dropped slot,
restated where plain reads give the slot's value as fields read in turn from
a kept slot (`liftPath`): a region fact's slots hold different stores
(`regionsApart_stores`). -/
def restateStores (ls : HeapLinks.Links) (dropped : Nat → Bool) (as : List IndexAtom) : List IndexAtom :=
  let reads := (plainReads ls).filter fun g => dropped g.2.2
  if reads.isEmpty then [] else
  let lift (a b : Nat × List String) : Option IndexAtom :=
    if dropped a.1 || dropped b.1 then do
      let (x, p) ← liftPath dropped reads reads.length a
      let (y, q) ← liftPath dropped reads reads.length b
      pure { fact := .storeApart x p y q }
    else none
  as.filterMap fun a => if a.cond.isNone then match a.fact with
    | .apart u w => lift (u, []) (w, [])
    | .storeApart u p w q => lift (u, p) (w, q)
    | _ => none
    else none

theorem restateStores_holds {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) : IndexHolds ε (restateStores ls dropped as) ρ h := by
  simp only [restateStores]
  split
  · intro a ha; cases ha
  · intro a ha _
    obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
    have hreads : ∀ g ∈ (plainReads ls).filter (fun g => dropped g.2.2), g ∈ plainReads ls :=
      fun g hg => (List.mem_filter.mp hg).1
    have lift : ∀ (u w : Nat) (p q : List String), PathStoresApart h (ρ u) p (ρ w) q →
        ∀ c, (if dropped (u, p).1 || dropped (w, q).1 then do
          let (x, p) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
            ((plainReads ls).filter fun g => dropped g.2.2).length (u, p)
          let (y, q) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
            ((plainReads ls).filter fun g => dropped g.2.2).length (w, q)
          pure ({ fact := .storeApart x p y q } : IndexAtom)
          else none) = some c → c.fact.HoldsAt ε ρ h := by
      intro u w p q hap c hc
      split at hc
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hc
        obtain ⟨⟨x, p'⟩, hx, ⟨y, q'⟩, hy, rfl⟩ := hc
        obtain ⟨u', w', hu, hw, hne⟩ := hap
        refine ⟨u', w', ?_, ?_, hne⟩
        · rw [liftPath_eq hl hreads _ _ _ _ _ hx]; exact hu
        · rw [liftPath_eq hl hreads _ _ _ _ _ hy]; exact hw
      · cases hc
    split at hab
    · rename_i hn
      have hbh := he b hb fun c hc => by rw [Option.isNone_iff_eq_none.mp hn] at hc; cases hc
      split at hab
      · rename_i u w hf
        rw [hf] at hbh
        exact lift u w [] [] ⟨ρ u, ρ w, rfl, rfl, regionsApart_stores hbh⟩ a hab
      · rename_i u p w q hf
        rw [hf] at hbh
        exact lift u w p q hbh a hab
      · cases hab
    · cases hab

/-- Atoms about slots below the dropped slot 0, restated one lower; an atom
naming slot 0 is first restated on a slot the links relate to it. -/
def dropIndices (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  let as := eliminateIndices [0] (as ++ restateReads ls (· == 0) as ++ restateStores ls (· == 0) as)
  let restated := match HeapLinks.neighbors ls 0 with
    | y :: _ => as ++ mapIndices (fun i => some (if i = 0 then y else i)) as
    | [] => as
  mapIndices (fun i => if i = 0 then none else some (i - 1)) restated

theorem dropIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ h v}
    (hl : HeapLinks.Holds ls (push v ρ) h) (he : IndexHolds ε as (push v ρ) h) :
    IndexHolds ε (dropIndices ls as) ρ h := by
  have he := eliminateIndices_holds (drop := [0]) (as := as ++ restateReads ls (· == 0) as ++ restateStores ls (· == 0) as)
    fun a ha => (List.mem_append.mp ha).elim
      (fun ha => (List.mem_append.mp ha).elim (he a) (restateReads_holds hl he a)) (restateStores_holds hl he a)
  unfold dropIndices
  generalize eliminateIndices [0] (as ++ restateReads ls (· == 0) as ++ restateStores ls (· == 0) as) = as at he ⊢
  have hr : IndexHolds ε (match HeapLinks.neighbors ls 0 with
      | y :: _ => as ++ mapIndices (fun i => some (if i = 0 then y else i)) as
      | [] => as) (push v ρ) h := by
    split
    · rename_i y _ hn
      have hy : push v ρ y = push v ρ 0 := HeapLinks.neighbors_eq hl (by rw [hn]; simp)
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact he a ha
      · exact mapIndices_holds (fun s t hst => by
          cases hst; split
          · rename_i hs; rw [hs]; exact hy
          · rfl) he a ha
    · exact he
  refine mapIndices_holds (fun s t hst => ?_) hr
  split at hst
  · cases hst
  · cases hst
    obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
    rfl

/-- The atoms conditional on the observed slot's class, at the observed answer,
made unconditional. -/
def promoteIndices (ls : HeapLinks.Links) (as : List IndexAtom) (slot : Nat) (q : Bool) : List IndexAtom :=
  as ++ (as.filter fun a => a.negated == !q &&
    a.cond.any fun c => (HeapLinks.aliases ls slot).contains c).map ({ · with cond := none })

theorem promoteIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {slot : Nat} {q : Bool} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) (ht : tagHolds .truthy (ρ slot) = q) :
    IndexHolds ε (promoteIndices ls as slot q) ρ h := by
  intro a ha hc
  rcases List.mem_append.mp ha with ha | ha
  · exact he a ha hc
  · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨b, ⟨hb, hneg, hcb⟩, rfl⟩ := ha
    refine he b hb fun c hc' => ?_
    rw [hc'] at hcb
    simp only [Option.any_some, List.contains_iff_mem] at hcb
    rw [HeapLinks.aliases_eq hl hcb, ht, hneg]
    cases q <;> rfl

def check (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  HeapFacts.check a.cells b.cells m && (HeapFacts.check a.values b.values m &&
    (HeapLinks.check a.links b.links m && (HeapSeparation.check a.separation b.separation m &&
      (elemsCheckBy (fun x => [x]) a.elems b.elems m && indicesCheckBy (fun x => [x]) a.links a.indices b.indices m))))

theorem check_sound {a b m ρ h} (hc : check a b m = true) (ha : Holds a ε ρ h) :
    Holds b ε (PointClaims.mapEnv m ρ) h := by
  simp only [check,Bool.and_eq_true] at hc
  refine ⟨HeapFacts.check_sound hc.1 ha.1,?_,HeapLinks.check_sound hc.2.2.1 ha.2.2.1,
    HeapSeparation.check_sound hc.2.2.2.1 ha.2.2.2.1,
    elemsCheckBy_sound (fun x y hy => by rw [List.mem_singleton.mp hy]) hc.2.2.2.2.1 ha.2.2.2.2.1,
    indicesCheckBy_sound (fun x y hy => by rw [List.mem_singleton.mp hy]) ha.2.2.1 hc.2.2.2.2.2 ha.2.2.2.2.2⟩
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc.2.1 f hf)
  simp only [Bool.and_eq_true,beq_iff_eq] at hc
  simpa [PointClaims.mapEnv,hc.1] using ValueSets.ValueSet.le_sound hc.2 (ha.2.1 g hg)

def shift (k : Knowledge) : Knowledge :=
  ⟨HeapFacts.shift k.cells,HeapFacts.shift k.values,HeapLinks.pull k.links (fun i => [i+1]),
    HeapSeparation.shift k.separation, shiftElems k.elems, shiftIndices k.indices⟩

theorem shift_holds {k ρ h v} (hk : Holds k ε ρ h) : Holds (shift k) ε (push v ρ) h := by
  refine ⟨HeapFacts.shift_holds hk.1,?_,?_,HeapSeparation.shift_holds hk.2.2.2.1,shiftElems_holds hk.2.2.2.2.1,
    shiftIndices_holds hk.2.2.2.2.2⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hk.2.1 g hg
  · apply HeapLinks.pull_holds (pre := fun i => [i+1]) hk.2.2.1
    intro i j hj
    have hj := List.mem_singleton.mp hj
    subst j
    rfl
/-- Effect-only continuations discard the result slot. Facts about it cannot
be transferred into the old environment. -/
def dropFacts (fs : Facts) : Facts :=
  (fs.filter fun f => 0 < f.slot).map fun f => {f with slot := f.slot - 1}

/-- The facts on slot 0 restated on each of its aliases: what the facts of
its class keep when the slot is dropped. -/
def aliasZero (ls : HeapLinks.Links) (fs : Facts) : Facts :=
  fs ++ (fs.filter (·.slot == 0)).flatMap fun f => (HeapLinks.aliases ls 0).map fun y => { f with slot := y }

def dropResult (k : Knowledge) : Knowledge :=
  ⟨dropFacts (aliasZero k.links k.cells),dropFacts (aliasZero k.links k.values),
    HeapLinks.pull (HeapLinks.bridge k.links (· == 0)) (fun i => if i = 0 then [] else [i-1]),
    HeapSeparation.drop (match HeapLinks.neighbors k.links 0 with
      | y :: _ => HeapSeparation.restate k.separation 0 y
      | [] => k.separation), dropElems k.elems, dropIndices k.links k.indices⟩

theorem aliasZero_mem {ls : HeapLinks.Links} {fs : Facts} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {g : Fact} (hg : g ∈ aliasZero ls fs) : ∃ f ∈ fs, ρ g.slot = ρ f.slot ∧ g.contents = f.contents ∧ g.field = f.field := by
  rcases List.mem_append.mp hg with hg | hg
  · exact ⟨g, hg, rfl, rfl, rfl⟩
  · obtain ⟨f, hf, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hg
    have h0 : f.slot = 0 := by simpa using (List.mem_filter.mp hf).2
    exact ⟨f, (List.mem_filter.mp hf).1, by rw [h0]; exact HeapLinks.aliases_eq hl hy, rfl, rfl⟩

theorem dropResult_holds {k ρ h v} (hk : Holds k ε (push v ρ) h) :
    Holds (dropResult k) ε ρ h := by
  constructor
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    have hp : 0 < g.slot := of_decide_eq_true hg.2
    have he : push v ρ g.slot = ρ (g.slot - 1) := by
      cases hs : g.slot with
      | zero => omega
      | succ i => rfl
    obtain ⟨f, hf, hs, hc, hfl⟩ := aliasZero_mem hk.2.2.1 hg.1
    obtain ⟨flds, c, oid, u, hl, hr, hm⟩ := hk.1 f hf
    exact ⟨flds, c, oid, u, by rw [← he, hs]; exact hl, by rw [hfl]; exact hr, by rw [hc]; exact hm⟩
  · constructor
    · intro f hf
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      have hp : 0 < g.slot := of_decide_eq_true hg.2
      have he : push v ρ g.slot = ρ (g.slot - 1) := by
        cases hs : g.slot with
        | zero => omega
        | succ i => rfl
      obtain ⟨f, hf, hs, hc, -⟩ := aliasZero_mem hk.2.2.1 hg.1
      have := hk.2.1 f hf
      rw [← hs, ← hc, he] at this
      exact this
    have hs : HeapSeparation.Holds (match HeapLinks.neighbors k.links 0 with
        | y :: _ => HeapSeparation.restate k.separation 0 y
        | [] => k.separation) (push v ρ) := by
      split
      · rename_i y _ hn
        exact HeapSeparation.restate_holds (HeapLinks.neighbors_eq hk.2.2.1 (by rw [hn]; simp)) hk.2.2.2.1
      · exact hk.2.2.2.1
    refine ⟨?_, HeapSeparation.drop_holds hs, dropElems_holds hk.2.2.2.2.1,
      dropIndices_holds hk.2.2.1 hk.2.2.2.2.2⟩
    · apply HeapLinks.pull_holds (pre := fun i => if i = 0 then [] else [i-1]) (HeapLinks.bridge_holds hk.2.2.1)
      intro i j hj
      split at hj
      · simp at hj
      · have hj := List.mem_singleton.mp hj
        subst j
        cases i with
        | zero => contradiction
        | succ i => rfl

/-- Project facts along an executable slot map. All runtime aliases selected by
that map are retained, and target slots the map takes from one source slot
are related by alias links (`mapped-alias`); a target slot takes the facts
of every alias of its source slot, so a class keeps its facts when the slot
holding them is not selected. -/
def projectFacts (ls : HeapLinks.Links) (facts : Facts) (m : PointClaims.Mapping) (count : Nat) : Facts :=
  (List.range count).flatMap fun i =>
    let ms := HeapLinks.aliases ls (PointClaims.slot m i)
    (facts.filter fun f => ms.contains f.slot).map fun f => { f with slot := i }

def project (k : Knowledge) (m : PointClaims.Mapping) (count : Nat) : Knowledge :=
  -- The target slots each source slot is mapped to, in increasing order.
  let preimages : Std.HashMap Nat (List Nat) := (List.range count).foldr
    (fun j acc => acc.alter (PointClaims.slot m j) fun js => some (j :: js.getD [])) ∅
  -- Every pair of a group, since `HeapLinks.aliases` reads direct links.
  let pairs : List Nat → HeapLinks.Links := fun js =>
    js.zipIdx.flatMap fun (j, n) => (js.drop (n+1)).map fun r => { cell := j, value := r, alias := true }
  let shared : HeapLinks.Links := preimages.fold (fun acc _ js => match js with
    | _ :: _ :: _ => pairs js ++ acc
    | _ => acc) []
  -- The target slots whose source slots lie in one alias class, each linked
  -- to the first of them: the class keeps its equalities where a chain of
  -- dropped slots joined them, which `bridge`, one dropped slot at a time,
  -- does not span.
  let classLinks : HeapLinks.Links := (HeapLinks.classes k.links).flatMap fun c =>
    match (List.range count).filter fun j => c.contains (PointClaims.slot m j) with
    | first :: rest => rest.map fun r => { cell := first, value := r, alias := true }
    | [] => []
  ⟨projectFacts k.links k.cells m count,projectFacts k.links k.values m count,
    HeapLinks.pull (HeapLinks.bridge (HeapLinks.aliasReads k.links) fun i => (preimages.getD i []).isEmpty)
      (fun i => preimages.getD i []) ++ shared ++ classLinks,
    HeapSeparation.project (HeapLinks.aliases k.links) k.separation m count,
    -- Each target slot takes the atoms of every alias of its source slot,
    -- a condition restated at the first target slot holding it.
    (List.range count).flatMap fun i =>
      let ms := HeapLinks.aliases k.links (PointClaims.slot m i)
      (k.elems.filter fun a => ms.contains a.slot).filterMap fun a => match a.cond with
        | none => some { a with slot := i }
        | some c => ((List.range count).find? fun j =>
            (HeapLinks.aliases k.links (PointClaims.slot m j)).contains c).map fun j =>
              { a with slot := i, cond := some j },
    -- Each slot an index atom names, its condition's included, restated at the
    -- first target slot holding its value.
    -- A slot no target slot holds is first eliminated from the linear facts.
    -- By source slot, the first target slot whose source's aliases hold it.
    let first : Std.HashMap Nat Nat := (List.range count).foldl (fun acc j =>
      (HeapLinks.aliases k.links (PointClaims.slot m j)).foldl (fun acc a =>
        if acc.contains a then acc else acc.insert a j) acc) ∅
    let target := fun s => first.get? s
    let dropped := (linearTerms k.indices).map Term.slot |>.eraseDups.filter fun s => (target s).isNone
    -- A term rooted at a dropped slot is first restated through a read from a
    -- kept slot, where a read link gives one (`restateReads`).
    let indices := k.indices ++ restateReads k.links (fun s => (target s).isNone) k.indices ++
      restateStores k.links (fun s => (target s).isNone) k.indices
    mapIndices target (eliminateIndices dropped indices)⟩

/-! ## Queries by class

What a knowledge states of a slot's value, or of the read of a field from
it, gathered from every slot `M` gives as holding the slot's value: the
classes of a closure, or a slot's aliases in links that state every pair of
a class. -/

theorem any_some {α : Type} {o : Option α} {p : α → Bool} (h : o.any p = true) :
    ∃ x, o = some x ∧ p x = true := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

/-- The meet of a nonempty list of value sets. -/
def meetSome : List ValueSets.ValueSet → Option ValueSets.ValueSet
  | [] => none
  | V :: Vs => some (Vs.foldl (fun V W => if V = W then V else V.meet W) V)

theorem meetSome_mem {l : List ValueSets.ValueSet} {V : ValueSets.ValueSet} {v : Tm}
    (h : meetSome l = some V) (hl : ∀ x ∈ l, x.mem v = true) : V.mem v = true := by
  cases l with
  | nil => cases h
  | cons W Ws =>
    cases h
    have hw := hl W (List.mem_cons_self ..)
    have hws : ∀ x ∈ Ws, x.mem v = true := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    clear hl
    induction Ws generalizing W with
    | nil => exact hw
    | cons a Ws ih =>
      simp only [List.foldl_cons]
      refine ih _ ?_ fun x hx => hws x (List.mem_cons_of_mem _ hx)
      split
      · exact hw
      · rw [ValueSets.ValueSet.mem_meet, hw, hws a (List.mem_cons_self ..)]; rfl

/-- The parts of a meet each about the one read from one object: the meet
holds of that read's value. -/
theorem meetSome_read {l : List ValueSets.ValueSet} {V : ValueSets.ValueSet} {o : Tm} {f : PropKey} {h : Heap}
    (hV : meetSome l = some V)
    (hl : ∀ x ∈ l, ∃ flds c oid u, o = .objAt flds c oid ∧ ReadGave flds f h u ∧ x.mem u = true) :
    ∃ flds c oid u, o = .objAt flds c oid ∧ ReadGave flds f h u ∧ V.mem u = true := by
  cases l with
  | nil => cases hV
  | cons W Ws =>
    obtain ⟨flds, c, oid, u, he, hr, -⟩ := hl W (List.mem_cons_self ..)
    refine ⟨flds, c, oid, u, he, hr, meetSome_mem hV fun x hx => ?_⟩
    obtain ⟨flds', c', oid', u', he', hr', hm'⟩ := hl x hx
    rw [he] at he'
    cases he'
    rw [ReadGave.unique hr hr']
    exact hm'

/-- What a knowledge states of the value of slot `s`: the value facts on
the slots `M s`, and the cell facts of each read into them from the slots
of its receiver. -/
def valueBy (a : Knowledge) (M : Nat → List Nat) (s : Nat) : Option ValueSets.ValueSet :=
  let ms := M s
  -- Each receiver and field once: reads restated on every pair of slots of
  -- two classes give one cell.
  let reads := ((a.links.filter fun g => !g.alias && ms.contains g.value).map fun g =>
    ((M g.cell).foldl min g.cell, g.field)).eraseDups
  meetSome ((a.values.filter fun F => ms.contains F.slot).map (·.contents) ++
    reads.flatMap fun (c, f) =>
      let rs := M c
      (a.cells.filter fun F => rs.contains F.slot && F.field == f).map (·.contents))

/-- What a knowledge states of the read of field `f` from slot `s`'s object:
the cell facts on the slots `M s`, and the value facts of each read of `f`
from them. -/
def cellBy (a : Knowledge) (M : Nat → List Nat) (s : Nat) (f : PropKey) : Option ValueSets.ValueSet :=
  let ms := M s
  -- Each read value's class once, by its least slot.
  let dests := ((a.links.filter fun g => !g.alias && g.field == f && ms.contains g.cell).map fun g =>
    (M g.value).foldl min g.value).eraseDups
  meetSome ((a.cells.filter fun F => ms.contains F.slot && F.field == f).map (·.contents) ++
    dests.flatMap fun d =>
      let ds := M d
      (a.values.filter fun F => ds.contains F.slot).map (·.contents))

/-- The value a link reads, as a `ReadGave`. -/
theorem link_readGave {g : HeapLinks.Link} {ρ : Env} {h : Heap} (ha : g.alias = false)
    (hh : HeapLinks.Holds [g] ρ h) :
    ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value) := by
  have := hh g (List.mem_singleton_self g)
  simp only [ha, Bool.false_eq_true, ite_false] at this
  cases ho : g.optional
  · simp only [ho, Bool.false_eq_true, ite_false] at this
    obtain ⟨flds, c, oid, l, he, hl, hv⟩ := this
    exact ⟨flds, c, oid, he, ReadGave.present hl hv⟩
  · simpa [ho] using this

section queries
variable {a : Knowledge} {M : Nat → List Nat} {ρ : Env} {h : Heap}

/-- The least of a slot and slots holding its value holds its value. -/
theorem foldl_min_eq (x : Nat) : ∀ (l : List Nat) (d : Nat), ρ d = ρ x → (∀ y ∈ l, ρ y = ρ x) →
    ρ (l.foldl min d) = ρ x := by
  intro l
  induction l with
  | nil => intro d hd _; exact hd
  | cons y l ih =>
    intro d hd hl
    simp only [List.foldl_cons]
    refine ih _ ?_ fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rcases Nat.le_total d y with hdy | hyd
    · rw [Nat.min_eq_left hdy]; exact hd
    · rw [Nat.min_eq_right hyd]; exact hl y (List.mem_cons_self ..)

theorem valueBy_mem (ha : Holds a ε ρ h) (hs : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s : Nat} {V : ValueSets.ValueSet}
    (hV : valueBy a M s = some V) : V.mem (ρ s) = true := by
  refine meetSome_mem hV fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hm⟩ := List.mem_filter.mp hF
    rw [← hs s F.slot (List.contains_iff_mem.mp hm)]
    exact ha.2.1 F hF
  · obtain ⟨cf, hcf, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨g, hg, hcf⟩ := List.mem_map.mp (List.mem_eraseDups.mp hcf)
    subst hcf
    obtain ⟨hg, hgs⟩ := List.mem_filter.mp hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hgs
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hk
    obtain ⟨flds, c, oid, u, he, hr, hm⟩ := ha.1 F hF
    obtain ⟨flds', c', oid', he', hr'⟩ := link_readGave hgs.1 fun x hx => by
      rw [List.mem_singleton.mp hx]; exact ha.2.2.1 g hg
    -- The least slot of the receiver's class holds the receiver's value.
    have hmin : ρ ((M g.cell).foldl min g.cell) = ρ g.cell :=
      foldl_min_eq g.cell _ _ rfl fun y hy => hs g.cell y hy
    rw [hs _ F.slot hk.1, hmin, he'] at he
    cases he
    rw [hk.2] at hr
    rw [← hs s g.value hgs.2, ← ReadGave.unique hr hr']
    exact hm

theorem cellBy_holds (ha : Holds a ε ρ h) (hs : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s : Nat} {f : PropKey}
    {V : ValueSets.ValueSet} (hV : cellBy a M s f = some V) :
    ∃ flds c oid u, ρ s = .objAt flds c oid ∧ ReadGave flds f h u ∧ V.mem u = true := by
  refine meetSome_read hV fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hk
    obtain ⟨flds, c, oid, u, he, hr, hm⟩ := ha.1 F hF
    rw [hs s F.slot hk.1] at he
    rw [hk.2] at hr
    exact ⟨flds, c, oid, u, he, hr, hm⟩
  · obtain ⟨d, hd, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hd)
    obtain ⟨hg, hgs⟩ := List.mem_filter.mp hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hgs
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hF, hk⟩ := List.mem_filter.mp hF
    simp only [List.contains_iff_mem] at hk
    obtain ⟨flds, c, oid, he, hr⟩ := link_readGave hgs.1.1 fun x hx => by
      rw [List.mem_singleton.mp hx]; exact ha.2.2.1 g hg
    rw [hs s g.cell hgs.2] at he
    rw [hgs.1.2] at hr
    refine ⟨flds, c, oid, ρ g.value, he, hr, ?_⟩
    have hmin : ρ ((M g.value).foldl min g.value) = ρ g.value :=
      foldl_min_eq g.value _ _ rfl fun y hy => hs g.value y hy
    rw [← hmin, ← hs _ F.slot hk]
    exact ha.2.1 F hF

/-- A slot's aliases hold its value. -/
theorem aliases_class (hl : HeapLinks.Holds a.links ρ h) :
    ∀ x, ∀ y ∈ HeapLinks.aliases a.links x, ρ y = ρ x :=
  fun _ _ hy => HeapLinks.aliases_eq hl hy

end queries

/-- Each cell fact on every alias of its slot: the cells a reader of cells by
slot needs where facts are stored once per class. -/
def aliasCells (k : Knowledge) : Facts :=
  k.cells.flatMap fun F => (HeapLinks.aliases k.links F.slot).map fun y => { F with slot := y }

theorem aliasCells_holds {k : Knowledge} {ρ h} (hk : Holds k ε ρ h) : HeapFacts.Holds (aliasCells k) ρ h := by
  intro F hF
  obtain ⟨G, hG, hF⟩ := List.mem_flatMap.mp hF
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hF
  obtain ⟨flds, c, oid, u, he, hr, hm⟩ := hk.1 G hG
  exact ⟨flds, c, oid, u, by rw [HeapLinks.aliases_eq hk.2.2.1 hy]; exact he, hr, hm⟩

/-- Every live property-read link transfers the observed result predicate,
including observations admitting undefined. -/
def linkFacts (k : Knowledge) (slot : Nat) (R : ValueSets.ValueSet) : Facts :=
  (k.links.filter (fun g => !g.alias && g.value == slot)).map
    (fun g => ⟨g.cell,R,g.field⟩)

theorem linkFacts_holds {k slot R ρ h} (hk : Holds k ε ρ h) (hv : R.mem (ρ slot) = true) :
    HeapFacts.Holds (linkFacts k slot R) ρ h := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have hg := List.mem_filter.mp hg
  have hg2 := hg.2
  simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at hg2
  have hl := hk.2.2.1 g hg.1
  simp only [hg2.1,Bool.false_eq_true,ite_false] at hl
  cases ho : g.optional
  · simp only [ho,Bool.false_eq_true,ite_false] at hl
    obtain ⟨flds,c,oid,l,hl,hfd,hh⟩ := hl
    exact ⟨flds,c,oid,ρ g.value,hl,ReadGave.present hfd hh,by simpa [hg2.2] using hv⟩
  · simp only [ho,ite_true] at hl
    obtain ⟨flds,c,oid,hl,hr⟩ := hl
    exact ⟨flds,c,oid,ρ g.value,hl,hr,by simpa [hg2.2] using hv⟩

/-- An observed Boolean outcome refines cells only through current read links.
The ordinary value fact is useful even when no cell link exists. -/
def observeBoolean (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  let R : ValueSets.ValueSet := if q then { tru := true } else { fls := true }
  ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links,k.separation,
    k.elems ++ (k.elems.filter fun a => a.negated == !q &&
      a.cond.any fun c => (HeapLinks.aliases k.links slot).contains c).map ({ · with cond := none }),
    promoteIndices k.links k.indices slot q⟩

theorem observeBoolean_holds {k slot q ρ h} (hk : Holds k ε ρ h)
    (hq : ρ slot = if q then .tru else .fls) : Holds (observeBoolean k slot q) ε ρ h := by
  have hv : (if q then ({ tru := true } : ValueSets.ValueSet) else { fls := true }).mem (ρ slot) = true := by
    cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hq ⊢ <;> rw [hq] <;> rfl
  have ht : tagHolds .truthy (ρ slot) = q := by cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hq <;> rw [hq] <;> rfl
  refine ⟨?_,?_,hk.2.2.1,hk.2.2.2.1,?_,promoteIndices_holds hk.2.2.1 hk.2.2.2.2.2 ht⟩
  rotate_left 2
  · intro a ha hc
    rcases List.mem_append.mp ha with ha | ha
    · exact hk.2.2.2.2.1 a ha hc
    · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨b, ⟨hb, hneg, hcb⟩, rfl⟩ := ha
      refine hk.2.2.2.2.1 b hb fun c hc' => ?_
      rw [hc'] at hcb
      simp only [Option.any_some, List.contains_iff_mem] at hcb
      rw [HeapLinks.aliases_eq hk.2.2.1 hcb, hneg, hq]
      cases q <;> rfl
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact linkFacts_holds hk hv f hf
    · exact hk.1 f hf
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hv
    · exact hk.2.1 f hf

/-- A tag narrows a saved primitive predicate, and its still-live read links transfer
that observation to the heap. No link means no assertion about a mutable cell. -/
def observeTag (k : Knowledge) (slot : Nat) (tag : Tag) (q : Bool) : Knowledge :=
  match valueBy k (HeapLinks.aliases k.links) slot with
  | none => k
  | some V =>
    let R := V.meet (ValueSets.ofTag tag q)
    ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links,k.separation,k.elems,k.indices⟩

theorem observeTag_holds {k slot tag q ρ h} (hk : Holds k ε ρ h)
    (hq' : tagHolds tag (ρ slot) = q ∨ protoFree tag (ρ slot) = false) :
    Holds (observeTag k slot tag q) ε ρ h := by
  unfold observeTag
  split
  · exact hk
  · rename_i V hV
    have hv : V.mem (ρ slot) = true := valueBy_mem hk (aliases_class hk.2.2.1) hV
    have hR : (V.meet (ValueSets.ofTag tag q)).mem (ρ slot) = true := by
      rw [ValueSets.ValueSet.mem_meet, hv, ValueSets.ofTag_holds (ValueSets.ValueSet.mem_isVal hv) hq']; rfl
    refine ⟨?_,?_,hk.2.2⟩
    · intro f' hf'
      rcases List.mem_append.mp hf' with hf' | hf'
      · exact linkFacts_holds hk hR f' hf'
      · exact hk.1 f' hf'
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hR
      · exact hk.2.1 f' hf'

/-- A truthy answer of the slot `slot` makes the atoms conditional on it
unconditional. -/
def promoteTruthy (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  { k with
    elems := (k.elems ++ (k.elems.filter fun a => a.negated == !q &&
      a.cond.any fun c => (HeapLinks.aliases k.links slot).contains c).map ({ · with cond := none }))
    indices := promoteIndices k.links k.indices slot q }

theorem promoteTruthy_holds {k slot q ρ h} (hk : Holds k ε ρ h) (ht : tagHolds .truthy (ρ slot) = q) :
    Holds (promoteTruthy k slot q) ε ρ h := by
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, ?_, promoteIndices_holds hk.2.2.1 hk.2.2.2.2.2 ht⟩
  intro a ha hc
  rcases List.mem_append.mp ha with ha | ha
  · exact hk.2.2.2.2.1 a ha hc
  · simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨b, ⟨hb, hneg, hcb⟩, rfl⟩ := ha
    refine hk.2.2.2.2.1 b hb fun c hc' => ?_
    rw [hc'] at hcb
    simp only [Option.any_some, List.contains_iff_mem] at hcb
    rw [HeapLinks.aliases_eq hk.2.2.1 hcb, ht, hneg]
    cases q <;> rfl

/-- Whether an observation excludes a guard's tag of the observed value: a
failed `null`, `undefined` or nullish test, or a truthy answer. -/
def excludesTag : BranchRefinement.Observation → GuardTag → Bool
  | .boolean true, .fls | .boolean false, .tru => true
  | .tag .isNul false, .null => true
  | .tag .isUndef false, .undef => true
  | .tag .isNullish false, .null | .tag .isNullish false, .undef => true
  | .tag .truthy true, .null | .tag .truthy true, .undef | .tag .truthy true, .fls => true
  | .tag .truthy false, .tru => true
  | .tag (.boolEq true) false, .tru | .tag (.boolEq false) false, .fls => true
  | .tag (.boolEq true) true, .fls | .tag (.boolEq false) true, .tru => true
  | _, _ => false

theorem excludesTag_ne {o : BranchRefinement.Observation} {v : Val} {t : GuardTag}
    (he : excludesTag o t = true) (ho : o.holds v) : v ≠ t.val := by
  intro hv
  subst hv
  rcases o with q | ⟨tag, q⟩
  · cases q <;> cases t <;> simp_all [excludesTag, BranchRefinement.Observation.holds, GuardTag.val]
  · cases tag <;> cases q <;> cases t <;>
      simp_all [excludesTag, BranchRefinement.Observation.holds, tagHolds, protoFree, GuardTag.val]

/-- Whether a guard's path from `s` reads a value of `slot`'s class: `s` is
of the class, or the path is one field a read link gives as a slot of it. -/
def readsClass (ls : HeapLinks.Links) (slot s : Nat) : List String → Bool
  | [] => (HeapLinks.aliases ls slot).contains s
  | [f] => (guardReads ls).any fun g => g.1 == s && g.2.1 == f && (HeapLinks.aliases ls slot).contains g.2.2
  | _ => false

theorem readsClass_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {slot s : Nat} {p : List String} {v : Val} (hr : readsClass ls slot s p = true)
    (hv : readGuard h (ρ s) p = some v) : v = ρ slot := by
  match p, hr with
  | [], hr =>
    simp only [readsClass, List.contains_iff_mem] at hr
    simp only [readGuard, Option.some.injEq] at hv
    rw [← hv]
    exact HeapLinks.aliases_eq hl hr
  | [f], hr =>
    simp only [readsClass] at hr
    obtain ⟨⟨c, f', w⟩, hg, hm⟩ := List.any_eq_true.mp hr
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hm
    obtain ⟨⟨rfl, rfl⟩, hw⟩ := hm
    rw [guardReads_read hl hg []] at hv
    simp only [readGuard, Option.some.injEq] at hv
    rw [← hv]
    exact HeapLinks.aliases_eq hl hw

/-- **Guard elimination** (`guard-eliminate`): the bodies of the guarded
atoms whose guard reads the observed slot's value, where the observation
excludes the guard's tag: a guard of a slot of the observed slot's class, or
of one field a read link gives as a slot of that class. -/
def unguardIndices (ls : HeapLinks.Links) (as : List IndexAtom) (slot : Nat) (o : BranchRefinement.Observation) :
    List IndexAtom :=
  as.filterMap fun a => match a.fact with
    | .guarded s p t B =>
      if excludesTag o t && readsClass ls slot s p then some { a with fact := B } else none
    | _ => none

theorem unguardIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {slot : Nat}
    {o : BranchRefinement.Observation} {ρ h} (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h)
    (ho : o.holds (ρ slot)) : IndexHolds ε (unguardIndices ls as slot o) ρ h := by
  intro a ha hc
  obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
  split at hab
  · rename_i s p t B hfb
    split at hab
    · rename_i hcond
      cases hab
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨hex, hpath⟩ := hcond
      have hbt := he b hb hc
      rw [hfb] at hbt
      obtain ⟨v, hv, hor⟩ := hbt
      have hvs : v = ρ slot := readsClass_eq hl hpath hv
      rcases hor with heq | hB
      · exact absurd (hvs ▸ heq) (excludesTag_ne hex ho)
      · exact hB
    · cases hab
  · cases hab

/-- **A literal equality's facts** (`num-equal`): a tag test of a value
against a number that is the safe integer `i` states, of each slot of the
tested slot's class known to hold a safe integer, `x = i` on its passing
answer and `x ≠ i` on its failing one. -/
def numEqIndices (ls : HeapLinks.Links) (as : List IndexAtom) (slot : Nat) :
    BranchRefinement.Observation → List IndexAtom
  | .tag (.numEq b) q =>
    match SafeIntegers.safeIntOfBits b with
    | some i =>
      ((HeapLinks.aliases ls slot).filter (intSlot as)).flatMap fun x =>
        if q then [⟨.linear (valueFact (.le [(x, 1)] i)), none, false⟩,
            ⟨.linear (valueFact (.le [(x, -1)] (-i))), none, false⟩]
        else [⟨.linear (valueFact (.ne [(x, 1)] i)), none, false⟩]
    | none => []
  | _ => []

theorem numEqIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {slot : Nat}
    {o : BranchRefinement.Observation} {ρ h} (hl : HeapLinks.Holds ls ρ h)
    (he : IndexHolds ε as ρ h) (ho : o.holds (ρ slot)) : IndexHolds ε (numEqIndices ls as slot o) ρ h := by
  intro a ha _
  unfold numEqIndices at ha
  split at ha
  · rename_i b q
    split at ha
    · rename_i i hi
      obtain ⟨x, hxm, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨hxa, hs⟩ := List.mem_filter.mp hxm
      have hρ : ρ x = ρ slot := HeapLinks.aliases_eq hl hxa
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (intSlot_sound he hs)
      obtain ⟨y, hy, hsafe⟩ := intValue_safe hj
      have hb := SafeIntegers.safeIntOfBits_sound hi
      have htag : numberEqual y b = q := by
        rw [← hρ, hy] at ho
        rcases ho with ho | ho
        · simpa [tagHolds] using ho
        · simp [protoFree] at ho
      have hv : valuation ρ x = j := by simp [valuation, hj]
      have hvars : ∀ (c : Int) (d : Int) (ne : Bool), ∀ z ∈ (if ne then Linear.Fact.ne [(x, c)] d
          else Linear.Fact.le [(x, c)] d).vars, (intValue (ρ z)).isSome := by
        intro c d ne z hz
        cases ne <;> simp [Linear.Fact.vars] at hz <;> subst hz <;> simp [hj]
      cases q with
      | true =>
        have hij := SafeIntegers.numberEqual_safe hsafe hb htag
        simp only [if_true, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact IndexFact.holdsAt_valueFact.mpr ⟨hvars 1 i false, by
            show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv]; omega⟩
        · exact IndexFact.holdsAt_valueFact.mpr ⟨hvars (-1) (-i) false, by
            show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv]; omega⟩
      | false =>
        simp only [Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        have hne : j ≠ i := fun he' => by
          subst he'
          rw [SafeIntegers.numberEqual_of_safe hsafe hb] at htag
          cases htag
        exact IndexFact.holdsAt_valueFact.mpr ⟨hvars 1 i true, by
          show Linear.Form.eval _ _ ≠ _; simp [Linear.Form.eval, hv]; omega⟩
    · cases ha
  · cases ha

def observeCore (k : Knowledge) (slot : Nat) : BranchRefinement.Observation → Knowledge
  | .boolean q => observeBoolean k slot q
  | .tag t q => if t == .truthy then promoteTruthy (observeTag k slot t q) slot q else observeTag k slot t q

/-- An observation's knowledge, with the bodies of the guards it eliminates
(`unguardIndices`). -/
def observe (k : Knowledge) (slot : Nat) (o : BranchRefinement.Observation) : Knowledge :=
  let k' := observeCore k slot o
  { k' with indices := k'.indices ++ unguardIndices k'.links k'.indices slot o ++ numEqIndices k'.links k'.indices slot o }

theorem observeCore_holds {k slot o ρ h} (hk : Holds k ε ρ h)
    (ho : o.holds (ρ slot)) : Holds (observeCore k slot o) ε ρ h := by
  cases o with
  | boolean q => exact observeBoolean_holds hk ho
  | tag t q =>
    simp only [observeCore]
    split
    · rename_i htq
      simp only [beq_iff_eq] at htq
      subst htq
      have ht : tagHolds .truthy (ρ slot) = q := by
        rcases ho with ho | ho
        · exact ho
        · simp [protoFree] at ho
      exact promoteTruthy_holds (observeTag_holds hk ho) ht
    · exact observeTag_holds hk ho

theorem observe_holds {k slot o ρ h} (hk : Holds k ε ρ h)
    (ho : o.holds (ρ slot)) : Holds (observe k slot o) ε ρ h := by
  have hk' := observeCore_holds hk ho
  refine ⟨hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2.1, fun a ha => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact hk'.2.2.2.2.2 a ha
    · exact unguardIndices_holds hk'.2.2.1 hk'.2.2.2.2.2 ho a ha
  · exact numEqIndices_holds hk'.2.2.1 hk'.2.2.2.2.2 ho a ha

/-- A finite predicate vocabulary exactly interprets supported primitive clauses. -/
def primitive : List (Clause (Ty ι)) → Option (List Atom)
  | [] => some []
  | .nul :: cs => (primitive cs).map ([.nul] ++ ·)
  | .undef :: cs => (primitive cs).map ([.undef] ++ ·)
  | .bool :: cs => (primitive cs).map ([.tru,.fls] ++ ·)
  | .boolLit b :: cs => (primitive cs).map ([if b then .tru else .fls] ++ ·)
  | .num :: cs => (primitive cs).map ([.num] ++ ·)
  | .numLit b :: cs => (primitive cs).map ([.numLit b] ++ ·)
  | .str :: cs => (primitive cs).map ([.str] ++ ·)
  | .strLit s :: cs => (primitive cs).map ([.strLit s] ++ ·)
  | .numIn bs :: cs => (primitive cs).map (bs.map .numLit ++ ·)
  | .strIn ss :: cs => (primitive cs).map (ss.map .strLit ++ ·)
  | _ => none

/-- A type's members as atoms, when it is of clause rows. -/
def atoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then primitive (expand G A) else none

/-- `atoms`, deciding once that the type is of clause rows: `expand` would
decide it again. The compiler runs it in place of `atoms` (`atoms_eq_once`). -/
def atomsOnce (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then primitive (clausesOf G A) else none

@[csimp] theorem atoms_eq_once : @atoms = @atomsOnce := by
  funext ι G A
  unfold atoms atomsOnce
  split
  · next h => rw [expand_of_plain h]
  · rfl

theorem primitive_sem {G : NormalGraph ι} {cs R} (hc : primitive cs = some R) (n W v) :
    semList (excOf G) (meaning G) (argMeaning G) cs n W v ↔ ∃ a ∈ R, a.holds v := by
  induction cs generalizing R with
  | nil => simp [primitive] at hc; subst R; simp [semList,setSem]
  | cons c cs ih =>
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        simp only [hr,Option.map_some,Option.some.injEq] at hc
        subst R
        have hi := ih hr
        simp only [semList,setSem,List.mem_cons,exists_eq_or_imp] at hi ⊢
        rw [hi]
        simp [semWithArgs,nulT,undefT,boolT,numT,strT,Atom.holds,apply_ite,or_assoc]
        all_goals try (split <;> simp_all [Atom.holds])
        all_goals try (
          constructor
          · rintro (⟨b, hb, rfl⟩ | ⟨a, ha, hh⟩)
            · exact ⟨_, .inl ⟨b, hb, rfl⟩, rfl⟩
            · exact ⟨a, .inr ha, hh⟩
          · rintro ⟨a, (⟨b, hb, rfl⟩ | ha), hh⟩
            · exact .inl ⟨b, hb, hh⟩
            · exact .inr ⟨a, ha, hh⟩)

/-- The built-ins asks nothing of primitive clauses. -/
theorem primitive_plain : ∀ {cs : List (Clause (Ty ι))} {R}, primitive cs = some R →
    ∀ c ∈ cs, c.carriesInvariant = false
  | [], _, _ => by simp
  | c :: cs, R, hc => by
    intro d hd
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        rcases List.mem_cons.mp hd with rfl | hd
        · rfl
        · exact primitive_plain hr d hd

theorem atoms_sem {G : NormalGraph ι} {A R} (h : atoms G A = some R) (n W v) :
    meaning G A n W v ↔ ∃ a ∈ R, a.holds v := by
  unfold atoms at h
  split at h
  · rw [expand_sem G A (by assumption), setSem_row_plain (primitive_plain h)]
    exact primitive_sem h n W v
  · cases h

/-- The atoms a tag's answer leaves a value of `A` among: a string
equality's `true`, the one string; else, where a primitive predicate states
it, the answer's slice of `A`. -/
def observedAtoms (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Option (List Atom) :=
  match tag, q with
  | .strEq s, true => some [.strLit s]
  | _, _ => atoms G (BranchRefinement.tagSlice G A tag q)

theorem observedAtoms_sound {G : NormalGraph ι} {A : Ty ι} {tag q R n W v}
    (h : observedAtoms G A tag q = some R) (hm : meaning G A n W v)
    (ho : (BranchRefinement.Observation.tag tag q).holds v) : ∃ a ∈ R, a.holds v := by
  unfold observedAtoms at h
  split at h
  · rename_i s
    cases h
    have hv := (meaning_value hm).1
    simp only [BranchRefinement.Observation.holds, protoFree, Bool.true_eq_false, or_false] at ho
    cases v <;> simp [tagHolds] at ho
    subst ho
    exact ⟨.strLit _, by simp, rfl⟩
  · exact (atoms_sem h n W v).mp (BranchRefinement.tagSlice_sound hm ho)

/-- Each slot's type as the value set its predicates admit, where it is of
finitely many primitive predicates: each computed when first read, once. -/
def typeSets (G : NormalGraph ι) (Γ : List (Ty ι)) : Array (Thunk (Option ValueSets.ValueSet)) :=
  Γ.toArray.map fun A => Thunk.mk fun _ => (atoms G A).map ValueSets.ofAtoms

/-- The contexts read from computed type sets, slot `i` at index `i - shift`
(below `shift`, none). Kept out of line, so the sets are computed once by
the caller and only read here. -/
@[noinline] def setsCtx (ts : Array (Thunk (Option ValueSets.ValueSet))) (shift : Nat) :
    Nat → Option ValueSets.ValueSet :=
  fun i => if i < shift then none else (ts[i - shift]?).bind (·.get)

theorem typeSets_get (G : NormalGraph ι) (Γ : List (Ty ι)) (i : Nat) :
    ((typeSets G Γ)[i]?).bind (·.get) = (Γ[i]?).bind fun A => (atoms G A).map ValueSets.ofAtoms := by
  simp only [typeSets, Array.getElem?_map, List.getElem?_toArray]
  cases Γ[i]? <;> rfl

theorem typeSets_mem {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W} (he : EnvOk G Γ ρ n W) {i : Nat}
    {C : ValueSets.ValueSet} (h : ((typeSets G Γ)[i]?).bind (·.get) = some C) : C.mem (ρ i) = true := by
  rw [typeSets_get] at h
  cases hA : Γ[i]? with
  | none => rw [hA] at h; cases h
  | some A =>
    rw [hA] at h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ValueSets.ofAtoms_holds ((atoms_sem hR n W (ρ i)).mp (he.2 i A hA))

/-- What every live read link states of its cell where its value's slot has
a type denoting finitely many primitive predicates (`link-fact`,
PROGRAM-TYPING.md, "A call that keeps the heap"): reading the field gives that
value, so it meets one of them. -/
def typedLinkFacts (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Facts :=
  let sets := typeSets G Γ
  linkFactsBy (setsCtx sets 0) k
where
  /-- With each slot's type set read through `t`, each computed once. -/
  linkFactsBy (t : Nat → Option ValueSets.ValueSet) (k : Knowledge) : Facts :=
    k.links.filterMap fun g => if g.alias then none else (t g.value).map fun R => ⟨g.cell, R, g.field⟩

/-- The knowledge with its read links' typed facts (`typedLinkFacts`). -/
def withTypedLinks (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Knowledge :=
  { k with cells := typedLinkFacts G Γ k ++ k.cells }

theorem withTypedLinks_holds {G : NormalGraph ι} {Γ k ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) : Holds (withTypedLinks G Γ k) ε ρ h := by
  refine ⟨fun f hf => ?_, hk.2.1, hk.2.2⟩
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨g, hg, hf⟩ := List.mem_filterMap.mp hf
    split at hf
    · cases hf
    · rename_i ha
      obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp hf
      have hv := typeSets_mem he (by simpa [setsCtx] using hR)
      exact linkFacts_holds hk hv _ (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, by simp [ha]⟩, rfl⟩)
  · exact hk.1 f hf

/-- A tag observation combines the saved predicate with the tested value's
ordinary type. This retains facts such as a falsy object-or-undefined being
undefined, whose broad saved nullish predicate alone is insufficient. -/
@[nospecialize] def observeTyped (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (slot : Nat) (o : BranchRefinement.Observation) : Knowledge :=
  let out := observe (withTypedLinks G Γ k) slot o
  match o, Γ[slot]? with
  | .tag tag q, some A =>
    match observedAtoms G A tag q with
    | some R => ⟨linkFacts k slot (ValueSets.ofAtoms R) ++ out.cells, ⟨slot,ValueSets.ofAtoms R,valueField⟩ :: out.values,
        out.links, out.separation, out.elems, out.indices⟩
    -- Otherwise the answer itself is a fact of every cell the value was
    -- read from (a separate fact: all of a cell's facts hold). A slice of
    -- objects a test leaves, `x` truthy where `x` is an object or undefined,
    -- also has values neither null nor undefined.
    | none =>
      let out : Knowledge := ⟨linkFacts k slot (ValueSets.ofTag tag q) ++ out.cells, out.values, out.links,
        out.separation, out.elems, out.indices⟩
      if G.plainTy (BranchRefinement.tagSlice G A tag q) && (expand G (BranchRefinement.tagSlice G A tag q)).all
          (fun c => tagClause .isNullish c == some false) then
        ⟨linkFacts k slot (ValueSets.ofAtom .nonNullish) ++ out.cells,
          ⟨slot,ValueSets.ofAtom .nonNullish,valueField⟩ :: out.values, out.links, out.separation, out.elems, out.indices⟩
      else out
  | _, _ => out

theorem observeTyped_holds {G : NormalGraph ι} {Γ k slot o ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) (ho : o.holds (ρ slot)) :
    Holds (observeTyped G Γ k slot o) ε ρ h := by
  have hout := observe_holds (withTypedLinks_holds he hk) ho
  unfold observeTyped
  split
  · rename_i tag q A hi
    split
    · rename_i R hr
      have hv := ValueSets.ofAtoms_holds (observedAtoms_sound hr (he.2 slot A hi) ho)
      refine ⟨?_, ?_, hout.2.2⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact linkFacts_holds hk hv f hf
        · exact hout.1 f hf
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hv
        · exact hout.2.1 f hf
    · have htag : (ValueSets.ofTag tag q).mem (ρ slot) = true :=
        ValueSets.ofTag_holds (meaning_value (he.2 slot A hi)).1 ho
      have hout : Holds ⟨linkFacts k slot (ValueSets.ofTag tag q) ++ (observe (withTypedLinks G Γ k) slot (.tag tag q)).cells,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).values, (observe (withTypedLinks G Γ k) slot (.tag tag q)).links,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).separation,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).elems,
          (observe (withTypedLinks G Γ k) slot (.tag tag q)).indices⟩ ε ρ h := by
        refine ⟨?_, hout.2.1, hout.2.2⟩
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact linkFacts_holds hk htag f hf
        · exact hout.1 f hf
      dsimp only
      by_cases hn : (G.plainTy (BranchRefinement.tagSlice G A tag q) && (expand G (BranchRefinement.tagSlice G A tag q)).all
          (fun c => tagClause .isNullish c == some false)) = true
      · rw [if_pos hn]
        have hm := BranchRefinement.tagSlice_sound (he.2 slot A hi) ho
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hn
        have hq := answers_sound (show Answers G _ .isNullish false from ⟨hn.1, hn.2⟩) hm
        have hval := (meaning_value hm).1
        have hv : (ValueSets.ofAtom .nonNullish).mem (ρ slot) = true := by
          refine ValueSets.ofAtom_holds ⟨hval, ?_, ?_⟩
          · intro h; rw [h] at hq; simp [tagHolds] at hq
          · intro h; rw [h] at hq; simp [tagHolds] at hq
        refine ⟨?_, ?_, hout.2.2⟩
        · intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact linkFacts_holds hk hv f hf
          · exact hout.1 f hf
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hv
          · exact hout.2.1 f hf
      · rw [if_neg hn]; exact hout
  · exact hout

/-- A type's atoms answer no tag: they are primitive predicates. -/
theorem primitive_noTag : ∀ {cs : List (Clause (Ty ι))} {R}, primitive cs = some R → R.all (!·.isTag) = true
  | [], _, h => by simp [primitive] at h; subst h; rfl
  | c :: cs, R, h => by
    cases c <;> simp only [primitive] at h
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at h
      | some rs =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        have := primitive_noTag hr
        simp only [List.all_append, this, Bool.and_true]
        try (rename_i b; cases b)
        all_goals simp [Atom.isTag]

theorem atoms_noTag {G : NormalGraph ι} {A R} (h : atoms G A = some R) : R.all (!·.isTag) = true := by
  unfold atoms at h
  split at h
  · exact primitive_noTag h
  · cases h


/-! ## Reading a quantified fact at an element (ARITHMETIC.md, "Quantified clauses") -/

/-- A checked read of the same array at an index a fixed offset away. -/
def offsetSlot (as : List IndexAtom) (cls : List Nat) (k d : Nat) : Option Nat := do
  let a ← as.find? fun a => a.cond.isNone && match a.fact with
    | .element _ x j => cls.contains x &&
      entailsKnown as (.le [(.value j, 1), (.value k, -1)] d) &&
      entailsKnown as (.le [(.value k, 1), (.value j, -1)] (-(d : Int)))
    | _ => false
  match a.fact with
  | .element r _ _ => some r
  | _ => none

theorem offsetSlot_value {as : List IndexAtom} {cls : List Nat} {k d r x sto i : Nat}
    {ls : List (Option Nat)} {ρ : Env} {h : Heap}
    (ha : IndexHolds ε as ρ h) (hcls : ∀ y ∈ cls, ρ y = ρ x)
    (hsto : elementsOf (ρ x) = some sto) (hls : h[sto]? = some (.arr ls))
    (hki : intValue (ρ k) = some (i : Int)) (hm : offsetSlot as cls k d = some r) :
    termValue ε ρ h (.value r) = elementInt h ls (i + d) := by
  simp only [offsetSlot, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
  obtain ⟨a, hfind, hm⟩ := hm
  have hc := List.find?_some hfind
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
  obtain ⟨hcond, hc⟩ := hc
  have he := ha a (List.mem_of_find?_eq_some hfind) (fun b hb => by rw [hcond] at hb; cases hb)
  cases hf : a.fact <;> simp only [hf] at hm hc he <;> try { cases hm }
  rename_i r' x' j
  simp only [Option.some.injEq] at hm
  subst hm
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
  obtain ⟨⟨hs, hlo⟩, hhi⟩ := hc
  obtain ⟨sto', ls', b, j0, hs', hl', hj, hji, hlt, hpres, hhole⟩ := he
  rw [hcls x' hs, hsto] at hs'
  cases hs'
  rw [hls] at hl'
  cases hl'
  have hji' : intValue (ρ j) = some (j0 : Int) := by rw [hj]; exact intValue_num hji
  have lo := entailsKnown_sound ha hlo
  have hi := entailsKnown_sound ha hhi
  simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hki, hji', Option.getD_some] at lo hi
  have heq : j0 = i + d := by omega
  subst heq
  simp only [termValue_value, elementInt]
  cases hli : ls[i + d]? with
  | none => simp at hli; omega
  | some o =>
    cases o with
    | none => rw [hhole hli]; rfl
    | some l => simp only [hpres l hli, Option.bind_some]

def boundInstance (as : List IndexAtom) (cls : List Nat) (k r : Nat) : Bound → Option Term
  | .offset d => (offsetSlot as cls k d).map Term.value
  | b => some (b.inst k r)

/-- The facts a read of the element at the index the slot `k` holds, its
value in the slot `r`, states of a quantified fact over an array of the read
array's class `cls`: each body fact with the index read as `k` and the element
as `r`, where `0 ≤ k < stop` (`every-read`). -/
def instantiateEvery (as : List IndexAtom) (cls : List Nat) (r k : Nat) : IndexAtom → List IndexAtom
  | ⟨.every s [] st body, none, _⟩ =>
    if cls.contains s && intSlot as k && termDefined as st &&
        entailsKnown as (.le [(.value k, -1)] 0) && entailsKnown as (.le [(.value k, 1), (st, -1)] (-1)) then
      body.filterMap fun F => (F.mapVars (boundInstance as cls k r)).map fun G => { fact := G.toIndexFact }
    else []
  | _ => []

/-- The facts each element read the atoms state instantiates (`instantiateEvery`). -/
def elementFacts (k : Knowledge) : List IndexAtom :=
  k.indices.flatMap fun a => match a with
    | ⟨.element r x i, none, _⟩ => k.indices.flatMap (instantiateEvery k.indices (HeapLinks.aliases k.links x) r i)
    | _ => []

/-- Knowledge with its element reads' instances added. -/
def elementInstances (k : Knowledge) : Knowledge := { k with indices := k.indices ++ elementFacts k }

theorem instantiateEvery_holds {as : List IndexAtom} {cls : List Nat} {r x k : Nat} {ρ : Env} {h : Heap}
    (ha : IndexHolds ε as ρ h) (hcls : ∀ y ∈ cls, ρ y = ρ x) (he : (IndexFact.element r x k).HoldsAt ε ρ h)
    {a : IndexAtom} (hm : a ∈ as) : IndexHolds ε (instantiateEvery as cls r k a) ρ h := by
  obtain ⟨sto, ls, b, i, hsto, hls, hk, hbi, hlt, hpres, hhole⟩ := he
  intro c hc _
  match a, hm, hc with
  | ⟨.every s [] st body, none, ng⟩, hm, hc =>
    simp only [instantiateEvery] at hc
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨⟨hs, -⟩, hd⟩, e0⟩, e1⟩ := hcond
      obtain ⟨F, hF, hG⟩ := List.mem_filterMap.mp hc
      obtain ⟨G, hmG, rfl⟩ := Option.map_eq_some_iff.mp hG
      have hat := ha _ hm (fun b hb => by cases hb)
      obtain ⟨w, sto', ls', n, hw, hsto', hls', hn, hall⟩ := hat
      have hρs : ρ s = ρ x := hcls s hs
      simp only [readPath, Option.some.injEq] at hw
      subst hw
      rw [hρs, hsto] at hsto'
      cases hsto'
      rw [hls] at hls'
      cases hls'
      have hki : intValue (ρ k) = some (i : Int) := by rw [hk]; exact intValue_num hbi
      have f0 := entailsKnown_sound ha e0
      have f1 := entailsKnown_sound ha e1
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hki, hn,
        Option.getD_some] at f1
      refine LinearClause.toIndexFact_holds.mpr ((LinearClause.holdsAt_mapVars hmG fun y _ t ht => ?_).mpr (hall i (by omega) F hF))
      cases y with
      | offset d =>
        obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp ht
        exact offsetSlot_value ha hcls hsto hls hki hr
      | index =>
        simp only [boundInstance, Option.some.injEq] at ht
        subst ht
        simp only [Bound.inst, termValue_value, hki, boundValue]
      | elem =>
        simp only [boundInstance, Option.some.injEq] at ht
        subst ht
        simp only [Bound.inst, termValue_value, boundValue, elementInt]
        have hlt' : i < ls.length := hlt
        cases hli : ls[i]? with
        | none => simp at hli; omega
        | some o =>
          cases o with
          | none => rw [hhole hli]; rfl
          | some l => simp only [hpres l hli, Option.bind_some]
      | project kind path =>
        simp only [boundInstance, Option.some.injEq] at ht
        subst ht
        simp only [Bound.inst, boundValue]
        cases hli : ls[i]? with
        | none => simp at hli; omega
        | some o =>
          cases o with
          | none =>
            simp only [termValue, termAt, Bool.false_eq_true, if_false, hhole hli]
            cases kind <;> cases path <;> rfl
          | some l => simp only [hpres l hli, Option.bind_some, termValue, termAt, Bool.false_eq_true, if_false]
      | free t => cases ht; rfl
    · cases hc
  | ⟨.every _ [] _ _, some _, _⟩, _, hc => simp [instantiateEvery] at hc
  | ⟨.every _ (_ :: _) _ _, _, _⟩, _, hc => simp [instantiateEvery] at hc
  | ⟨.index _, _, _⟩, _, hc | ⟨.length _ _, _, _⟩, _, hc | ⟨.bound _ _ _, _, _⟩, _, hc
  | ⟨.int _, _, _⟩, _, hc | ⟨.linear _, _, _⟩, _, hc | ⟨.guarded _ _ _ _, _, _⟩, _, hc
  | ⟨.either _ _, _, _⟩, _, hc
  | ⟨.element _ _ _, _, _⟩, _, hc => simp [instantiateEvery] at hc

theorem elementInstances_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (elementInstances k) ε ρ h := by
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact hk.2.2.2.2.2 a ha hc
  · obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp ha
    match e, he, hm with
    | ⟨.element r x i, none, ng⟩, he, hm =>
      have hel := hk.2.2.2.2.2 _ he (fun b hb => by cases hb)
      obtain ⟨c, hcm, hm⟩ := List.mem_flatMap.mp hm
      exact instantiateEvery_holds hk.2.2.2.2.2 (fun y hy => HeapLinks.aliases_eq hk.2.2.1 hy) hel hcm a hm hc
    | ⟨.element _ _ _, some _, _⟩, _, hm => simp at hm
    | ⟨.index _, _, _⟩, _, hm | ⟨.length _ _, _, _⟩, _, hm | ⟨.bound _ _ _, _, _⟩, _, hm
    | ⟨.int _, _, _⟩, _, hm | ⟨.linear _, _, _⟩, _, hm | ⟨.guarded _ _ _ _, _, _⟩, _, hm
    | ⟨.either _ _, _, _⟩, _, hm
    | ⟨.every _ _ _ _, _, _⟩, _, hm => simp at hm


/-- An alternative whose other arm contradicts the known linear facts. -/
def releaseEither (as : List IndexAtom) (a : IndexAtom) : List IndexAtom :=
  match a with
  | ⟨.either A B, none, _⟩ =>
    (if entailsKnown (as ++ [{ fact := B }]) (.le [] (-1)) then [{ fact := A }] else []) ++
    (if entailsKnown (as ++ [{ fact := A }]) (.le [] (-1)) then [{ fact := B }] else [])
  | _ => []

theorem releaseEither_holds {as : List IndexAtom} {a : IndexAtom} {ρ : Env} {h : Heap}
    (ha : IndexHolds ε as ρ h) (hm : a ∈ as) : IndexHolds ε (releaseEither as a) ρ h := by
  have bad (F : IndexFact) (hF : F.HoldsAt ε ρ h)
      (hc : entailsKnown (as ++ [{ fact := F }]) (.le [] (-1)) = true) : False := by
    have he : IndexHolds ε (as ++ [{ fact := F }]) ρ h := by
      intro b hb hbcond
      rcases List.mem_append.mp hb with hb | hb
      · exact ha b hb hbcond
      · simp only [List.mem_singleton] at hb; subst hb; exact hF
    have contra := entailsKnown_sound he hc
    simp [Linear.Fact.Holds, Linear.Form.eval] at contra
  match a with
  | ⟨.either A B, none, ng⟩ =>
    have hor := ha _ hm (fun b hb => by cases hb)
    intro b hb _
    simp only [releaseEither, List.mem_append] at hb
    rcases hb with hb | hb
    · split at hb
      · rename_i hc
        simp only [List.mem_singleton] at hb; subst hb
        exact hor.resolve_right (fun hB => bad B hB hc)
      · cases hb
    · split at hb
      · rename_i hc
        simp only [List.mem_singleton] at hb; subst hb
        exact hor.resolve_left (fun hA => bad A hA hc)
      · cases hb
  | ⟨.either _ _, some _, _⟩ => simp [releaseEither, IndexHolds]
  | ⟨.index _, _, _⟩ | ⟨.length _ _, _, _⟩ | ⟨.bound _ _ _, _, _⟩
  | ⟨.int _, _, _⟩ | ⟨.pastSafe _, _, _⟩ | ⟨.linear _, _, _⟩ | ⟨.guarded _ _ _ _, _, _⟩
  | ⟨.element _ _ _, _, _⟩ | ⟨.every _ _ _ _, _, _⟩ | ⟨.apart _ _, _, _⟩
  | ⟨.storeApart _ _ _ _, _, _⟩ => simp [releaseEither, IndexHolds]

def withElements (k : Knowledge) : Knowledge :=
  let k := elementInstances k
  { k with indices := k.indices ++ k.indices.flatMap (releaseEither k.indices) }

theorem withElements_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (withElements k) ε ρ h := by
  have hk := elementInstances_holds hk
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact hk.2.2.2.2.2 a ha hc
  · obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp ha
    exact releaseEither_holds hk.2.2.2.2.2 hb a hm hc

end Verification.HeapKnowledge
