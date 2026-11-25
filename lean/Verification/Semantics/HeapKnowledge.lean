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

/-- A candidate fact at a statement entry: an index atom or a read link.
Kept where every incoming edge establishes it, left out otherwise; acceptance
does not require it. -/
inductive Candidate where
  | index (a : IndexAtom)
  | link (g : HeapLinks.Link)
  deriving DecidableEq, Repr, Hashable

/-- The index atoms among candidates. -/
def Candidate.indices (cs : List Candidate) : List IndexAtom :=
  cs.filterMap fun | .index a => some a | .link _ => none

/-- The links among candidates. -/
def Candidate.links (cs : List Candidate) : HeapLinks.Links :=
  cs.filterMap fun | .link g => some g | .index _ => none

/-- A candidate renamed by a partial map, where it maps every slot the candidate names. -/
def Candidate.mapM (f : Nat → Option Nat) : Candidate → Option Candidate
  | .index a => do pure (.index { a with fact := ← a.fact.mapM f, cond := ← a.cond.mapM f })
  | .link g => do pure (.link { g with cell := ← f g.cell, value := ← f g.value })

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

/-- A knowledge with candidates added: their index atoms and their links. -/
def withCandidates (k : Knowledge) (cs : List Candidate) : Knowledge :=
  { k with indices := k.indices ++ Candidate.indices cs, links := k.links ++ Candidate.links cs }

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, f.contents.mem (ρ f.slot) = true

def ElemsHolds (as : List ElemAtom) (ρ : Env) (h : Heap) : Prop :=
  ∀ a ∈ as, (∀ b, a.cond = some b → tagHolds .truthy (ρ b) = !a.negated) → CallEffects.ElemsAt a.pred (ρ a.slot) h

def IndexHolds (ε : EntryState) (as : List IndexAtom) (ρ : Env) (h : Heap) : Prop :=
  ∀ a ∈ as, (∀ b, a.cond = some b → tagHolds .truthy (ρ b) = !a.negated) → a.fact.HoldsAt ε ρ h

def Holds (k : Knowledge) (ε : EntryState) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ ∧ HeapLinks.Holds k.links ρ h ∧
    HeapSeparation.Holds k.separation ρ ∧ ElemsHolds k.elems ρ h ∧ IndexHolds ε k.indices ρ h

/-- A knowledge's facts hold where those of the knowledge with candidates added hold. -/
theorem holds_of_withCandidates {k : Knowledge} {cs : List Candidate} {ρ : Env} {h : Heap}
    (hk : Holds (withCandidates k cs) ε ρ h) : Holds k ε ρ h :=
  ⟨hk.1, hk.2.1, fun g hg => hk.2.2.1 g (List.mem_append_left _ hg),
   hk.2.2.2.1, hk.2.2.2.2.1, fun a ha => hk.2.2.2.2.2 a (List.mem_append_left _ ha)⟩

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

/-- A heap extension keeps an elements fact: the spine and every element
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

/-- A fresh allocation of several locations preserves every assertion about
existing cells and aliases. -/
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
  · simp only [Bool.false_eq_true, ite_false] at hx
    simp only [termValue, termAt, Bool.false_eq_true, ite_false, PointClaims.mapEnv,
      hM _ _ (List.contains_iff_mem.mp hx)]
  · simp only [ite_true, beq_iff_eq] at hx
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
an offset, a projection, a parallel-array projection, or a term `termFollows` relates. -/
def boundFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : Bound → Bound → Bool
  | .index, .index => true
  | .elem, .elem => true
  | .offset d, .offset d' => d == d'
  | .project k p, .project k' p' => k == k' && p == p'
  | .parallel s p k ep, .parallel s' p' k' ep' =>
    (M (PointClaims.slot m s')).contains s && p == p' && k == k' && ep == ep'
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
  · simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hf
    obtain ⟨⟨⟨hs, rfl⟩, rfl⟩, rfl⟩ := hf
    simp only [boundValue, PointClaims.mapEnv, hM _ _ hs]
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

/-- Whether a target element guard target follows from a source one. -/
def elemTargetFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : ElemTarget → ElemTarget → Bool
  | .self ep, .self ep' => ep == ep'
  | .parallel s p ep, .parallel s' p' ep' =>
    (M (PointClaims.slot m s')).contains s && p == p' && ep == ep'
  | _, _ => false

theorem elemTargetFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {ls : List (Option Nat)} {i : Nat} {t t' : ElemTarget}
    (hf : elemTargetFollows M m t t' = true) :
    t.read ρ h ls i = t'.read (PointClaims.mapEnv m ρ) h ls i := by
  cases t <;> cases t' <;> simp only [elemTargetFollows, Bool.false_eq_true] at hf
  · simp only [beq_iff_eq] at hf; subst hf; rfl
  · simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hf
    obtain ⟨⟨hs, rfl⟩, rfl⟩ := hf
    simp only [ElemTarget.read, PointClaims.mapEnv, hM _ _ hs]

/-- Whether a target body clause follows from a source body clause. -/
def bodyClauseFollows (M : Nat → List Nat) (m : PointClaims.Mapping) : BodyClause → BodyClause → Bool
  | .clause F, .clause F' => bodyFactFollows M m F F'
  | .guarded t g B, .guarded t' g' B' =>
    elemTargetFollows M m t t' && g == g' && bodyClauseFollows M m B B'
  | _, _ => false

theorem bodyClauseFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {ls : List (Option Nat)} {i : Nat} :
    ∀ {B B' : BodyClause}, bodyClauseFollows M m B B' = true →
      B.HoldsAt ε ρ h ls i → B'.HoldsAt ε (PointClaims.mapEnv m ρ) h ls i
  | .clause F, .clause F', hm, hF => by
    simp only [bodyClauseFollows, bodyFactFollows, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hm
    obtain ⟨hps, hmap⟩ := hm
    refine (LinearClause.holdsAt_mapVars hmap fun y _ x hx => ?_).mp hF
    exact boundFollows_sound hM (hps _ (lookup_mem' hx))
  | .guarded t g B, .guarded t' g' B', hm, ⟨w, hw, hor⟩ => by
    simp only [bodyClauseFollows, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨ht, rfl⟩, hB⟩ := hm
    exact ⟨w, (elemTargetFollows_sound hM ht).symm.trans hw,
      hor.imp id (bodyClauseFollows_sound hM hB)⟩
  | .clause _, .guarded _ _ _, hm, _ | .guarded _ _ _, .clause _, hm, _ => by
    simp [bodyClauseFollows] at hm

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
  | .fieldRead v o fld, .fieldRead v' o' fld' =>
    fld == fld' && (M (PointClaims.slot m v')).contains v && (M (PointClaims.slot m o')).contains o
  | .every s p st b, .every s' p' st' b' =>
    (M (PointClaims.slot m s')).contains s && p == p' && termFollows M m st st' &&
      b'.all fun F' => b.any fun F => bodyClauseFollows M m F F'
  | .atIndex s p idx g b, .atIndex s' p' idx' g' b' =>
    (M (PointClaims.slot m s')).contains s && p == p' && termFollows M m idx idx' &&
      (g == g' || g.isNone) && bodyFactFollows M m b b'
  | .apart a b, .apart a' b' =>
    (M (PointClaims.slot m a')).contains a && (M (PointClaims.slot m b')).contains b ||
      (M (PointClaims.slot m a')).contains b && (M (PointClaims.slot m b')).contains a
  | .spineApart a p b q, .spineApart a' p' b' q' =>
    (M (PointClaims.slot m a')).contains a && p == p' && (M (PointClaims.slot m b')).contains b && q == q' ||
      (M (PointClaims.slot m a')).contains b && p' == q && (M (PointClaims.slot m b')).contains a && q' == p
  | .same a b, .same a' b' =>
    (M (PointClaims.slot m a')).contains a && (M (PointClaims.slot m b')).contains b ||
      (M (PointClaims.slot m a')).contains b && (M (PointClaims.slot m b')).contains a
  | .guarded s p g B, .guarded s' p' g' B' =>
    (M (PointClaims.slot m s')).contains s && p == p' && g == g' && factFollows M m B B'
  | .either A B, .either A' B' =>
    (factFollows M m A A' && factFollows M m B B') ||
      (factFollows M m A B' && factFollows M m B A')
  | _, _ => false

/-- A quantified fact holds at an edge's target where the source's holds:
its array, its bound and its body's terms, renamed by the edge, denote the
same (`factFollows`). -/
theorem every_follows {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s s' : Nat} {p : List String} {st st' : Term}
    {b b' : List BodyClause} (hs : (M (PointClaims.slot m s')).contains s = true)
    (hst : termFollows M m st st' = true) (hb : b'.all (fun F' => b.any fun F => bodyClauseFollows M m F F') = true)
    (hF : (IndexFact.every s p st b).HoldsAt ε ρ h) :
    (IndexFact.every s' p st' b').HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
  have hs' : PointClaims.mapEnv m ρ s' = ρ s := (hM _ _ (List.contains_iff_mem.mp hs)).symm
  refine ⟨w, sto, ls, n, by rw [hs']; exact hw, hsto, hls, by rw [← termFollows_sound hM hst]; exact hn,
    fun i hi F' hF' => ?_⟩
  obtain ⟨F, hF, hm⟩ := List.any_eq_true.mp (List.all_eq_true.mp hb F' hF')
  exact bodyClauseFollows_sound hM hm (hall i hi F hF)

theorem atIndex_follows {M : Nat → List Nat} {m : PointClaims.Mapping} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) {s s' : Nat} {p : List String} {idx idx' : Term}
    {g g' : Option GuardTag} {b b' : LinearClause Bound}
    (hs : (M (PointClaims.slot m s')).contains s = true) (hidx : termFollows M m idx idx' = true)
    (hg : (g == g' || g.isNone) = true) (hb : bodyFactFollows M m b b' = true)
    (hF : (IndexFact.atIndex s p idx g b).HoldsAt ε ρ h) :
    (IndexFact.atIndex s' p idx' g' b').HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  obtain ⟨w, sto, ls, i, hw, hsto, hls, hi, hlt, hrest⟩ := hF
  have hs' : PointClaims.mapEnv m ρ s' = ρ s := (hM _ _ (List.contains_iff_mem.mp hs)).symm
  simp only [bodyFactFollows, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hb
  obtain ⟨hps, hmap⟩ := hb
  have hbody : b.HoldsAt (boundValue ε ρ h ls i) → b'.HoldsAt (boundValue ε (PointClaims.mapEnv m ρ) h ls i) := fun hB => by
    refine (LinearClause.holdsAt_mapVars hmap fun y _ x hx => ?_).mp hB
    exact boundFollows_sound hM (hps _ (lookup_mem' hx))
  refine ⟨w, sto, ls, i, by rw [hs']; exact hw, hsto, hls, by rw [← termFollows_sound hM hidx]; exact hi, hlt, ?_⟩
  cases g with
  | none =>
    cases g' with
    | none => exact hbody hrest
    | some _ => exact .inr (.inr (hbody hrest))
  | some tg =>
    simp only [Bool.or_eq_true, beq_iff_eq, Option.isNone_some, Bool.false_eq_true, or_false] at hg
    subst hg
    exact hrest.imp id (Or.imp id hbody)

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
  | either A B ihA ihB =>
    cases t <;> simp only [factFollows, Bool.or_eq_true, Bool.and_eq_true, reduceCtorEq] at hf
    rcases hf with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact hs.imp (ihA hA) (ihB hB)
    · exact hs.elim (fun h => .inr (ihA hA h)) (fun h => .inl (ihB hB h))
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
  · rename_i v o fld v' o' fld'
    simp only [beq_iff_eq] at hf
    obtain ⟨⟨rfl, hv⟩, ho⟩ := hf
    simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ hv, hM _ _ ho] using hs
  · rename_i s0 p0 st b s1 p1 st' b'
    obtain ⟨⟨⟨hs0, hp⟩, hst⟩, hb⟩ := hf
    simp only [beq_iff_eq] at hp
    subst hp
    exact every_follows hM (List.contains_iff_mem.mpr hs0) hst hb hs
  · rename_i s0 p0 idx g b s1 p1 idx' g' b'
    obtain ⟨⟨⟨⟨hs0, hp⟩, hidx⟩, hg⟩, hb⟩ := hf
    simp only [beq_iff_eq] at hp
    subst hp
    exact atIndex_follows hM (List.contains_iff_mem.mpr hs0) hidx hg hb hs
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
        PathSpinesApart.symm hs
  · rename_i a b a' b'
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hf
    rcases hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ ha, hM _ _ hb] using hs
    · simpa only [IndexFact.HoldsAt, PointClaims.mapEnv, hM _ _ ha, hM _ _ hb] using hs.symm

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

/-- A spine's length lies between `0` and `maxArrayLength`. -/
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
  obtain ⟨s, ls, -, -, rfl, hm⟩ := lengthOf_spine (h := H) (v := v) hkv
  have hv : termValuation ε ρ h t = ls.length := by simp [termValuation, hn]
  have hm' : (ls.length : Int) ≤ (maxArrayLength : Int) := by exact_mod_cast hm
  intro F hF
  simp only [lengthRange, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> simp only [Linear.Fact.Holds, Linear.Form.eval, hv] <;> omega

theorem viewRange_holds {ρ h} {t : Term} (hk : t.kind = .view) (hx : (termValue ε ρ h t).isSome) :
    ∀ F ∈ viewRange t, F.Holds (termValuation ε ρ h) := by
  obtain ⟨H, v, n, hkv, hn⟩ := termValue_kind hx
  rw [hk] at hkv
  obtain ⟨h0, h1⟩ := viewLengthOf_range (v := v) hkv
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
    have hlen : termValue ε ρ h (.length x) = some (ls.length : Int) := lengthOf_of_spine hs hl hm
    have hval : termValue ε ρ h (.value n) = some (ls.length : Int) := by
      simp only [termValue_value, hnv, intValue_length hm]
    have v1 : termValuation ε ρ h (.length x) = ls.length := by simp [termValuation, hlen]
    have v2 : termValuation ε ρ h (.value n) = ls.length := by simp [termValuation, hval]
    simp only [factLinear, List.mem_cons] at hF
    rcases hF with rfl | rfl | hF
    · simp only [Linear.Fact.Holds, Linear.Form.eval, v1, v2]; omega
    · simp only [Linear.Fact.Holds, Linear.Form.eval, v1, v2]; omega
    · exact lengthRange_holds rfl (by rw [hlen]; rfl) F hF
  | index _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => simp [factLinear] at hF

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
  | index _ | bound _ _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfa] at hf; cases hf

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
        simp only [termValue_nil, kindValue, lengthOf_of_spine hs hl hm, Option.isSome_some]
      | linear _ | index _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfa] at hf; cases hf
    | view | strLength => cases ht
  · obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp ht
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
    obtain ⟨hn, hf⟩ := hm
    have hat := he a ha fun b hb => by rw [hn] at hb; cases hb
    cases hfa : a.fact with
    | linear G => rw [hfa] at hf hat; exact hat.1 t (List.contains_iff_mem.mp hf)
    | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfa] at hf; cases hf

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
      · simp only [termValue_length, lengthOf_of_spine hs hl hmx, Option.isSome_some]
      · simp only [termValue_value, hnv, intValue_length hmx, Option.isSome_some]
    | index _ | bound _ _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfa] at hm; cases hm
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
of the spine of `x`'s class (`M`): `k` stated a safe integer, the facts
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

theorem lengthBoundIn_sound {K : Linear.Known Term} {M : List Nat} {a : List IndexAtom} {k : Nat} {strict : Bool}
    {ρ h} {v : Val} (hK : K.Holds (termValuation ε ρ h))
    (hM : ∀ y ∈ M, ρ y = v) (hc : lengthBoundIn K M a k strict = true) (ha : IndexHolds ε a ρ h) :
    ∃ s ls b idx, Footprints.spineOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
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
  obtain ⟨s, ls, hs, hl, rfl, -⟩ := lengthOf_spine hn
  have hvn : termValuation ε ρ h (.length y) = ls.length := by simp [termValuation, hn]
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (intSlot_sound ha hi)
  obtain ⟨b, hb, hsafe⟩ := intValue_safe hj
  have hvi : termValuation ε ρ h (.value k) = j := by simp [termValuation, termValue_value, hj]
  rw [hvi, hvn] at f2; rw [hvi] at f1 f3
  have hm : ((maxArrayLength : Nat) : Int) = 4294967295 := rfl
  refine ⟨s, ls, b, j.toNat, by rw [← hM y hy]; exact hs, hl, hb,
    SafeIntegers.indexOfBits_safe hsafe (by omega) (by omega), by cases strict <;> simp at f2 ⊢ <;> omega⟩

theorem lengthBound_sound {M : List Nat} {a : List IndexAtom} {k : Nat} {strict : Bool} {ρ h} {v : Val}
    (hM : ∀ y ∈ M, ρ y = v) (hc : lengthBound M a k strict = true) (ha : IndexHolds ε a ρ h) :
    ∃ s ls b idx, Footprints.spineOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
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
    | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [hfa] at hm; cases hm
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
    simp only [termValue, termAt, Bool.false_eq_true, ite_false, he, readPath_cons hlk hv]
  · simp only [ho, ite_true] at this
    obtain ⟨flds, c, oid, he, hr⟩ := this
    rw [hf] at hr
    unfold HeapFacts.ReadGave at hr
    cases hlk : flds.lookup (.str f) with
    | some l =>
      rw [hlk] at hr
      simp only [termValue, termAt, Bool.false_eq_true, ite_false, he, readPath_cons hlk hr]
    | none =>
      rw [hlk] at hr
      have hnone : readPath h (ρ g.cell) (f :: p) = none := by simp [he, readPath, hlk]
      simp only [termValue, termAt, Bool.false_eq_true, ite_false, hnone, Option.bind_none, hr.2]
      cases p with
      | nil => cases k <;> simp [readPath, kindValue, intValue, lengthOf, viewLengthOf, strLengthOf,
          Footprints.spineOf, Footprints.fieldsOf]
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

/-- A term lowered along read links `(c, f, v)` as far as they go,
normalizing through alias representatives `r`. When two objects share a
read value (`a.f = v` and `b.g = v`), lowering maps both `a.f` and `b.g`
to `r v` before `liftTerm` lifts `r v` to one canonical path. -/
def lowerTermAll (r : Nat → Nat) (reads : List (Nat × String × Nat)) : Nat → Term → Term
  | 0, t => t.mapM' r
  | n + 1, t => if t.atEntry then t else match t.path with
    | f :: p =>
      let rs := r t.slot
      match reads.find? (fun g => g.2.1 == f && r g.1 == rs) with
      | some (_, _, v) => lowerTermAll r reads n (HeapKnowledge.Term.now t.kind v p)
      | none => t.mapM' r
    | [] => t.mapM' r

theorem lowerTermAll_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {r : Nat → Nat} (hr : ∀ x, ρ (r x) = ρ x) :
    ∀ n t, termValue ε ρ h (lowerTermAll r (bridgeReads ls) n t) = termValue ε ρ h t := by
  intro n
  induction n with
  | zero =>
    intro t; simp only [lowerTermAll]
    exact termValue_mapM' fun _ => hr _
  | succ n ih =>
    intro t
    simp only [lowerTermAll]
    split
    · rfl
    · rename_i he
      cases hp : t.path with
      | nil => simp only; exact termValue_mapM' fun _ => hr _
      | cons f p =>
        simp only
        split
        · rename_i c f' v hfind
          have hm := List.mem_of_find?_eq_some hfind
          have hgf := List.find?_some hfind
          simp only [Bool.and_eq_true, beq_iff_eq] at hgf
          obtain ⟨rfl, hrc⟩ := hgf
          rw [ih, ← bridgeReads_term hl hm, ← hp]
          exact termValue_now_slot (by rw [← hr c, hrc, hr]) (by simpa using he)
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
    simp only [lowerTerm, Bool.false_eq_true, ite_false]
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

theorem bridgeReads_readGuard {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {c v : Nat} {f : String} (hm : (c, f, v) ∈ bridgeReads ls) {p : List String} {w : Val}
    (hw : readGuard h (ρ c) (f :: p) = some w) : readGuard h (ρ v) p = some w := by
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
        rw [he] at hw
        simpa [readGuard, hlk, hv] using hw
      · simp only [ho, ite_true] at this
        obtain ⟨flds, cd, oid, he, hr⟩ := this
        rw [hf'] at hr
        unfold HeapFacts.ReadGave at hr
        cases hlk : flds.lookup (.str f') with
        | some l =>
          rw [hlk] at hr
          rw [he] at hw
          simpa [readGuard, hlk, hr] using hw
        | none =>
          rw [hlk] at hr
          rw [he] at hw
          simpa [readGuard, hlk, hr.1, hr.2] using hw
    · cases hgm

theorem lowerRoot_readGuard {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) {s : Nat} {p : List String}
    {w : Val} (hw : readGuard h (ρ s) p = some w) :
    readGuard h (ρ (lowerRoot reads s p).1) (lowerRoot reads s p).2 = some w := by
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
      exact bridgeReads_readGuard hl hm hw
    · exact hw

/-- A body variable restated alike. -/
def lowerBound (reads : List (Nat × String × Nat)) : Bound → Bound
  | .parallel s p k ep => let (s', p') := lowerRoot reads s p; .parallel s' p' k ep
  | .free t => .free (lowerTerm reads t)
  | b => b

/-- An element guard target restated alike. -/
def lowerTarget (reads : List (Nat × String × Nat)) : ElemTarget → ElemTarget
  | .self ep => .self ep
  | .parallel s p ep => let (s', p') := lowerRoot reads s p; .parallel s' p' ep

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

/-- A body clause restated through `reads`. -/
def lowerBodyClause (reads : List (Nat × String × Nat)) : BodyClause → BodyClause
  | .clause F => .clause (renameClause (lowerBound reads) F)
  | .guarded t g b => .guarded (lowerTarget reads t) g (lowerBodyClause reads b)

theorem lowerBodyClause_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) {ls' : List (Option Nat)} {i : Nat} :
    ∀ {B : BodyClause}, B.HoldsAt ε ρ h ls' i → (lowerBodyClause reads B).HoldsAt ε ρ h ls' i
  | .clause F, hF => by
    have hF' : F.HoldsAt (fun x => boundValue ε ρ h ls' i (lowerBound reads x)) := by
      refine LinearClause.holdsAt_extend (fun x _ m hm => ?_) hF
      cases x with
      | index | elem | offset _ | project _ _ => exact hm
      | parallel s p k ep =>
        simp only [lowerBound, boundValue] at hm ⊢
        cases hp : readPath h (ρ s) p with
        | none => simp [hp] at hm
        | some a =>
          simp only [hp] at hm
          rw [lowerRoot_path hl hr hp]; exact hm
      | free t =>
        simp only [lowerBound, boundValue] at hm ⊢
        rw [lowerTerm_eq (ε := ε) hl hr t]; exact hm
    exact (LinearClause.holdsAt_mapVars (renameClause_mapVars (lowerBound reads) F) fun x _ y hy => by
      simp only [Function.comp_apply, Option.some.injEq] at hy; subst hy; rfl).mpr hF'
  | .guarded t g b, ⟨w, hw, hor⟩ => by
    refine ⟨w, ?_, hor.imp id (lowerBodyClause_holds hl hr)⟩
    cases t with
    | self ep => exact hw
    | parallel s p ep =>
      simp only [lowerTarget, ElemTarget.read] at hw ⊢
      cases hp : readPath h (ρ s) p with
      | none => simp [hp] at hw
      | some a =>
        simp only [hp] at hw
        rw [lowerRoot_path hl hr hp]; exact hw

/-- The plain read links: a slot's value read as field `f` of slot `c`. -/
def plainReads (ls : HeapLinks.Links) : List (Nat × String × Nat) :=
  ls.filterMap fun g => if g.alias || g.optional then none else match g.field with
    | .str f => some (g.cell, f, g.value)
    | .sym _ => none

theorem plainReads_bridge {ls : HeapLinks.Links} {g : Nat × String × Nat}
    (hg : g ∈ plainReads ls) : g ∈ bridgeReads ls := by
  obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hg
  refine List.mem_filterMap.mpr ⟨r, hr, ?_⟩
  split at he
  · cases he
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    simpa only [h.1, Bool.false_eq_true, ite_false] using he

/-- A plain link witnesses a field location in both directions. -/
theorem plainReads_path {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) {c v : Nat} {f : String}
    (hm : (c, f, v) ∈ plainReads ls) (p : List String) :
    readPath h (ρ c) (f :: p) = readPath h (ρ v) p := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hm
  split at hgm
  · cases hgm
  · rename_i hao
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hao
    split at hgm
    · rename_i f' hf'
      simp only [Option.some.injEq, Prod.mk.injEq] at hgm
      obtain ⟨rfl, rfl, rfl⟩ := hgm
      have hlink := hl g hg
      simp only [hao.1, hao.2, Bool.false_eq_true, ite_false] at hlink
      obtain ⟨flds, cd, oid, l, he, hloc, hv⟩ := hlink
      rw [hf'] at hloc
      rw [he, readPath_cons hloc hv]
    · cases hgm

theorem lowerRequiredRoot_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (s : Nat) (p : List String) :
    readPath h (ρ (lowerRoot (plainReads ls) s p).1) (lowerRoot (plainReads ls) s p).2 =
      readPath h (ρ s) p := by
  cases p with
  | nil => rfl
  | cons f p =>
    simp only [lowerRoot]
    split
    · rename_i g hg
      have hmem := List.mem_of_find?_eq_some hg
      have hmatch := List.find?_some hg
      obtain ⟨c, f', v⟩ := g
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨rfl, rfl⟩ := hmatch
      exact (plainReads_path hl hmem p).symm
    · rfl

theorem lowerRequiredBody_iff {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) {entries : List (Option Nat)} {i : Nat} :
    ∀ B : BodyClause, (lowerBodyClause (plainReads ls) B).HoldsAt ε ρ h entries i ↔
      B.HoldsAt ε ρ h entries i
  | .clause F => by
    refine LinearClause.holdsAt_mapVars (renameClause_mapVars (lowerBound (plainReads ls)) F)
      (fun x _ y hy => ?_)
    simp only [Function.comp_apply, Option.some.injEq] at hy
    subst y
    cases x with
    | free t => exact lowerTerm_eq hl (fun _ hg => plainReads_bridge hg) t
    | parallel s p k ep =>
      simp only [lowerBound, boundValue, lowerRequiredRoot_eq hl]
    | _ => rfl
  | .guarded t g b => by
    have heq : (lowerTarget (plainReads ls) t).read ρ h entries i = t.read ρ h entries i := by
      cases t with
      | self _ => rfl
      | parallel s p ep => simp only [lowerTarget, ElemTarget.read, lowerRequiredRoot_eq hl]
    simp only [lowerBodyClause, BodyClause.HoldsAt, heq, lowerRequiredBody_iff hl b]

/-- Lower the array, bound, and body of a quantified fact through the same read links. -/
def lowerEveryAt (reads : List (Nat × String × Nat)) (s : Nat) (p : List String)
    (stop : Term) (body : List BodyClause) : IndexFact :=
  let root := lowerRoot reads s p
  .every root.1 root.2 (lowerTerm reads stop) (body.map (lowerBodyClause reads))

/-- Restate a quantified fact through required field reads. All accesses in the
body use the same read links as the array and bound. -/
def lowerRequiredEvery (ls : HeapLinks.Links) : IndexFact → IndexFact
  | .every s p st body => lowerEveryAt (plainReads ls) s p st body
  | .guarded s p g B => .guarded s p g (lowerRequiredEvery ls B)
  | .either A B => .either (lowerRequiredEvery ls A) (lowerRequiredEvery ls B)
  | F => F

/-- Whether a fact contains a quantified body, including below a guard. -/
def IndexFact.hasEvery : IndexFact → Bool
  | .every .. => true
  | .guarded _ _ _ B => B.hasEvery
  | .either A B => A.hasEvery || B.hasEvery
  | _ => false

theorem lowerRequiredEvery_iff {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (F : IndexFact) :
    (lowerRequiredEvery ls F).HoldsAt ε ρ h ↔ F.HoldsAt ε ρ h := by
  induction F with
  | every s p st body =>
    simp only [lowerRequiredEvery, lowerEveryAt, IndexFact.HoldsAt, lowerRequiredRoot_eq hl,
      lowerTerm_eq hl (fun _ hg => plainReads_bridge hg)]
    constructor
    · rintro ⟨w, sp, entries, n, hw, hs, he, hn, hb⟩
      exact ⟨w, sp, entries, n, hw, hs, he, hn, fun i hi B hB =>
        (lowerRequiredBody_iff hl B).mp (hb i hi _ (List.mem_map_of_mem hB))⟩
    · rintro ⟨w, sp, entries, n, hw, hs, he, hn, hb⟩
      refine ⟨w, sp, entries, n, hw, hs, he, hn, fun i hi B hB => ?_⟩
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
      exact (lowerRequiredBody_iff hl A).mpr (hb i hi A hA)
  | guarded s p t B ih => simp only [lowerRequiredEvery, IndexFact.HoldsAt, ih]
  | either A B ha hb => simp only [lowerRequiredEvery, IndexFact.HoldsAt, ha, hb]
  | _ => rfl

/-- A quantified fact restated through a read of slot `0`, where the read
restates its array, its bound or a body term. -/
def readEvery (reads : List (Nat × String × Nat)) (a : IndexAtom) : Option IndexAtom :=
  match a.fact with
  | .every s p st body =>
    if lowerRoot reads s p != (s, p) || lowerTerm reads st != st ||
        body.map (lowerBodyClause reads) != body then
      some { a with fact := lowerEveryAt reads s p st body }
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
      exact lowerBodyClause_holds hl hr (hall i hi F hF)
    · cases hab
  · cases hab

/-- Whether an index fact is or contains an `atIndex` fact. -/
def IndexFact.hasAtIndex : IndexFact → Bool
  | .atIndex .. => true
  | .either A B => A.hasAtIndex || B.hasAtIndex
  | _ => false

/-- Lower an indexed-element fact (or a disjunction containing one) through read
links: its array path, index term and free body terms lowered toward the ends
of their paths. -/
def lowerAtIndexFact (reads : List (Nat × String × Nat)) : IndexFact → Option IndexFact
  | .atIndex s p idx g body =>
    let root := lowerRoot reads s p
    let idx' := lowerTerm reads idx
    let body' := renameClause (lowerBound reads) body
    if root != (s, p) || idx' != idx || body' != body then
      some (.atIndex root.1 root.2 idx' g body')
    else none
  | .linear F =>
    if F.vars.any (fun t => lowerTerm reads t != t) then
      some (.linear (renameFact (lowerTerm reads) F))
    else none
  | .either A B =>
    if !(A.hasAtIndex || B.hasAtIndex) then none else
    match lowerAtIndexFact reads A, lowerAtIndexFact reads B with
    | some A', some B' => some (.either A' B')
    | some A', none => some (.either A' B)
    | none, some B' => some (.either A B')
    | none, none => none
  | _ => none

theorem lowerAtIndexFact_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) :
    ∀ {F F' : IndexFact}, lowerAtIndexFact reads F = some F' → F.HoldsAt ε ρ h → F'.HoldsAt ε ρ h := by
  intro F
  induction F with
  | atIndex s p idx g body =>
    intro F' hab ha
    simp only [lowerAtIndexFact] at hab
    split at hab
    · simp only [Option.some.injEq] at hab; subst hab
      obtain ⟨w, sto, ls', i, hw, hsto, hls, hi, hlt, hrest⟩ := ha
      have hbody : body.HoldsAt (boundValue ε ρ h ls' i) →
          (renameClause (lowerBound reads) body).HoldsAt (boundValue ε ρ h ls' i) :=
        lowerBodyClause_holds (B := .clause body) hl hr
      refine ⟨w, sto, ls', i, lowerRoot_path hl hr hw, hsto, hls, by rw [lowerTerm_eq hl hr]; exact hi, hlt, ?_⟩
      cases g with
      | none => exact hbody hrest
      | some _ => exact hrest.imp id (Or.imp id hbody)
    · cases hab
  | linear F =>
    intro F' hab ha
    simp only [lowerAtIndexFact] at hab
    split at hab
    · simp only [Option.some.injEq] at hab; subst hab
      exact (IndexFact.holdsAt_linear_mapVars (renameFact_mapVars (lowerTerm reads) F) fun x _ y hy => by
        cases hy; exact lowerTerm_eq hl hr x).mpr ha
    · cases hab
  | either A B ihA ihB =>
    intro F' hab ha
    simp only [lowerAtIndexFact] at hab
    split at hab
    · cases hab
    · cases hA : lowerAtIndexFact reads A <;> cases hB : lowerAtIndexFact reads B <;>
        simp only [hA, hB, Option.some.injEq] at hab
      · cases hab
      · subst hab; exact ha.imp id (ihB hB)
      · subst hab; exact ha.imp (ihA hA) id
      · subst hab; exact ha.imp (ihA hA) (ihB hB)
  | _ => intro F' hab; simp [lowerAtIndexFact] at hab

/-- An indexed-element fact (or a disjunction containing one) restated through
read links (`lowerAtIndexFact`). -/
def readAtIndex (reads : List (Nat × String × Nat)) (a : IndexAtom) : Option IndexAtom :=
  (lowerAtIndexFact reads a.fact).map fun f => { a with fact := f }

theorem readAtIndex_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) {a b : IndexAtom}
    (hab : readAtIndex reads a = some b) (ha : a.fact.HoldsAt ε ρ h) : b.fact.HoldsAt ε ρ h := by
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
  exact lowerAtIndexFact_holds hl hr hf ha

/-- A guarded fact restated through read links: its guard path and inner body
(nested guards, linear facts, and quantified facts) lowered toward the ends of
their paths. -/
def lowerGuardedFact (reads : List (Nat × String × Nat)) : IndexFact → Option IndexFact
  | .guarded s p t B =>
    let root := lowerRoot reads s p
    let B' := lowerGuardedFact reads B
    if root != (s, p) || B'.isSome then some (.guarded root.1 root.2 t (B'.getD B)) else none
  | .linear F =>
    if F.vars.any (fun t => lowerTerm reads t != t) then
      some (.linear (renameFact (lowerTerm reads) F))
    else none
  | .every s p st body =>
    let root := lowerRoot reads s p
    let st' := lowerTerm reads st
    let body' := body.map (lowerBodyClause reads)
    if root != (s, p) || st' != st || body' != body then
      some (.every root.1 root.2 st' body')
    else none
  | _ => none

theorem lowerGuardedFact_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) :
    ∀ {F F' : IndexFact}, lowerGuardedFact reads F = some F' → F.HoldsAt ε ρ h → F'.HoldsAt ε ρ h := by
  intro F
  induction F with
  | guarded s p t B ih =>
    intro F' hab ha
    simp only [lowerGuardedFact] at hab
    split at hab
    · simp only [Option.some.injEq] at hab; subst hab
      obtain ⟨w, hw, hor⟩ := ha
      refine ⟨w, lowerRoot_readGuard hl hr hw, ?_⟩
      cases hB : lowerGuardedFact reads B with
      | none => exact hor
      | some B' => exact hor.imp id (ih hB)
    · cases hab
  | linear F =>
    intro F' hab ha
    simp only [lowerGuardedFact] at hab
    split at hab
    · simp only [Option.some.injEq] at hab; subst hab
      exact (IndexFact.holdsAt_linear_mapVars (renameFact_mapVars (lowerTerm reads) F) fun x _ y hy => by
        cases hy; exact lowerTerm_eq hl hr x).mpr ha
    · cases hab
  | every s p st body =>
    intro F' hab ha
    simp only [lowerGuardedFact] at hab
    split at hab
    · simp only [Option.some.injEq] at hab; subst hab
      obtain ⟨w, sto, ls', n, hw, hsto, hls, hn, hall⟩ := ha
      refine ⟨w, sto, ls', n, lowerRoot_path hl hr hw, hsto, hls, by rw [lowerTerm_eq hl hr]; exact hn,
        fun i hi C' hC' => ?_⟩
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
      exact lowerBodyClause_holds hl hr (hall i hi C hC)
    · cases hab
  | _ => intro F' hab; simp [lowerGuardedFact] at hab

/-- A guarded atom restated through read links (`lowerGuardedFact`). -/
def readGuarded (reads : List (Nat × String × Nat)) (a : IndexAtom) : Option IndexAtom :=
  (lowerGuardedFact reads a.fact).map fun f => { a with fact := f }

/-- **The read rule's bridge.** Where a read link gives slot `0` as the field
`f` read from slot `c`, each linear atom naming a term rooted at `c` whose path
starts with `f` is restated with that term rooted at slot `0`, its path the
rest (`readBridge`): what the knowledge states of the path, it states of the
read's value; a quantified fact's array, bound and body terms alike
(`readEvery`), a guarded fact's guard path and body alike (`readGuarded`), and
an indexed-element fact's alike (`readAtIndex`). -/
def readAtoms (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  let reads := (bridgeReads ls).filter (·.2.2 == 0)
  if reads.isEmpty then [] else
  as.filterMap fun a => match a.fact with
    | .linear F => if F.vars.any (fun t => lowerTerm reads t != t) then
        (F.mapVars (some ∘ lowerTerm reads)).map fun F' => { a with fact := .linear F' } else none
    | .every .. => readEvery reads a
    | .guarded .. => readGuarded reads a
    | .atIndex .. | .either .. => readAtIndex reads a
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
    · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
      exact lowerGuardedFact_holds hl hr hf (he b hb hc)
    · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
      exact lowerAtIndexFact_holds hl hr hf (he b hb hc)
    · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
      exact lowerAtIndexFact_holds hl hr hf (he b hb hc)
    · cases hab

def liftReadTerm (ls : HeapLinks.Links) (t : Term) : Term :=
  if t.path.isEmpty && t.kind == .value then liftTerm id (bridgeReads ls) 1 t else t

theorem liftReadTerm_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) (t : Term) :
    termValue ε ρ h (liftReadTerm ls t) = termValue ε ρ h t := by
  unfold liftReadTerm; split
  · exact liftTerm_eq (r := id) hl (fun _ => rfl) 1 t
  · rfl

/-- A body variable with its free term lifted through one known field read. -/
def liftReadBound (ls : HeapLinks.Links) : Bound → Bound
  | .free t => .free (liftReadTerm ls t)
  | b => b

/-- Restate linear value terms, indexed-element facts, disjunctions and prefix
bounds through one known field read, including the link established by a field
write. Existing paths stay as they are. -/
def liftEveryFact (ls : HeapLinks.Links) : IndexFact → IndexFact
  | .every s p stop body => .every s p (liftReadTerm ls stop) body
  | .atIndex s p idx g body =>
    .atIndex s p (liftReadTerm ls idx) g (renameClause (liftReadBound ls) body)
  | .linear F => .linear (renameFact (liftReadTerm ls) F)
  | .either A B => .either (liftEveryFact ls A) (liftEveryFact ls B)
  | F => F

theorem liftEveryFact_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) : ∀ {F : IndexFact}, F.HoldsAt ε ρ h → (liftEveryFact ls F).HoldsAt ε ρ h := by
  intro F
  induction F with
  | every s p st body =>
    intro ⟨w, sto, elems, n, hw, hs, he, hn, hall⟩
    exact ⟨w, sto, elems, n, hw, hs, he, (liftReadTerm_eq hl st).trans hn, hall⟩
  | atIndex s p idx g body =>
    intro ⟨w, sto, elems, i, hw, hs, he, hi, hlt, hrest⟩
    have hbody : body.HoldsAt (boundValue ε ρ h elems i) →
        (renameClause (liftReadBound ls) body).HoldsAt (boundValue ε ρ h elems i) := fun hB => by
      refine (LinearClause.holdsAt_mapVars (renameClause_mapVars (liftReadBound ls) body) fun x _ y hy => ?_).mpr hB
      simp only [Function.comp_apply, Option.some.injEq] at hy
      subst hy
      cases x with
      | free t => exact liftReadTerm_eq (ε := ε) hl t
      | _ => rfl
    refine ⟨w, sto, elems, i, hw, hs, he, (liftReadTerm_eq hl idx).trans hi, hlt, ?_⟩
    cases g with
    | none => exact hbody hrest
    | some _ => exact hrest.imp id (Or.imp id hbody)
  | linear F =>
    intro ha
    exact (IndexFact.holdsAt_linear_mapVars (renameFact_mapVars (liftReadTerm ls) F)
      (fun x _ y hy => by cases hy; exact liftReadTerm_eq hl x)).mpr ha
  | either A B ihA ihB =>
    intro ha
    exact ha.imp ihA ihB
  | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ =>
    exact id

def liftEvery (ls : HeapLinks.Links) (a : IndexAtom) : IndexAtom :=
  { a with fact := liftEveryFact ls a.fact }

@[simp] theorem liftEvery_cond (ls : HeapLinks.Links) (a : IndexAtom) : (liftEvery ls a).cond = a.cond := rfl

@[simp] theorem liftEvery_negated (ls : HeapLinks.Links) (a : IndexAtom) : (liftEvery ls a).negated = a.negated := rfl

theorem liftEvery_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} {a : IndexAtom}
    (hl : HeapLinks.Holds ls ρ h) (ha : a.fact.HoldsAt ε ρ h) : (liftEvery ls a).fact.HoldsAt ε ρ h :=
  liftEveryFact_holds hl ha

def liftedEvery (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  (as.filter fun a => match a.fact with
    | .every .. | .atIndex .. | .linear .. => liftEvery ls a != a
    | .either .. => a.fact.hasAtIndex && liftEvery ls a != a
    | _ => false).map (liftEvery ls)

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

/-- A term restated by read links toward the end of its path, field by
field (`lowerTerm`), at most `n` times: where a read link gives slot `v` as
field `f` read from slot `c`, the term rooted at `c` with path `f :: p` is
the term rooted at `v` with path `p`. Each restatement shortens the path, so
`n` the path's length restates it as far as the links reach. -/
def lowerStar (reads : List (Nat × String × Nat)) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => let t' := lowerTerm reads t; if t' == t then t else lowerStar reads n t'

theorem lowerStar_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) :
    ∀ n t, termValue ε ρ h (lowerStar reads n t) = termValue ε ρ h t := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    simp only [lowerStar]
    split
    · rfl
    · rw [ih]; exact lowerTerm_eq hl hr t

/-- A term restated by every read link toward the end of its path
(`lowerStar`, as far as the links reach). -/
def lowerByLinks (reads : List (Nat × String × Nat)) (t : Term) : Term := lowerStar reads t.path.length t

/-- Lower a spine separation (or a guarded spine separation) through read links:
each array path lowered toward its end (`lowerRoot`). -/
def lowerSpineApartFact (reads : List (Nat × String × Nat)) : IndexFact → Option IndexFact
  | .spineApart a p b q =>
    let ra := lowerRoot reads a p
    let rb := lowerRoot reads b q
    if ra != (a, p) || rb != (b, q) then
      some (.spineApart ra.1 ra.2 rb.1 rb.2)
    else none
  | .guarded s p t B =>
    (lowerSpineApartFact reads B).map (.guarded s p t)
  | _ => none

theorem lowerSpineApartFact_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {reads : List (Nat × String × Nat)} (hr : ∀ g ∈ reads, g ∈ bridgeReads ls) :
    ∀ {F G : IndexFact}, lowerSpineApartFact reads F = some G → F.HoldsAt ε ρ h → G.HoldsAt ε ρ h
  | .spineApart a p b q, G, hfg, hF => by
    simp only [lowerSpineApartFact] at hfg
    split at hfg
    · cases hfg
      obtain ⟨va, vb, hva, hvb, hne⟩ := hF
      exact ⟨va, vb, lowerRoot_path hl hr hva, lowerRoot_path hl hr hvb, hne⟩
    · cases hfg
  | .guarded s p t B, G, hfg, hF => by
    simp only [lowerSpineApartFact] at hfg
    obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.mp hfg
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, hv, hor.imp id (lowerSpineApartFact_holds hl hr hB')⟩
  | .index _, _, hfg, _ | .length _ _, _, hfg, _ | .bound _ _ _, _, hfg, _
  | .int _, _, hfg, _ | .pastSafe _, _, hfg, _ | .linear _, _, hfg, _
  | .either _ _, _, hfg, _ | .element _ _ _, _, hfg, _ | .every _ _ _ _, _, hfg, _
  | .atIndex _ _ _ _ _, _, hfg, _ | .apart _ _, _, hfg, _ | .same _ _, _, hfg, _ => by
    simp [lowerSpineApartFact] at hfg

/-- **Facts read modulo the read links.** Each linear atom naming a term
some read link restates (`lowerByLinks`) is restated with every term so
restated; a quantified atom's array, bound and body through one read
(`readEvery`); a spine separation or guarded spine separation through one
read (`lowerSpineApartFact`): what the knowledge states of a path it states of
the value a link holds for it, whenever the fact entered the knowledge. -/
def lowerAtoms (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  let reads := bridgeReads ls
  if reads.isEmpty then [] else
  as.filterMap fun a => match a.fact with
    | .linear F => if F.vars.any (fun t => lowerByLinks reads t != t) then
        some { a with fact := .linear (renameFact (lowerByLinks reads) F) } else none
    | .every .. => readEvery reads a
    | .guarded .. => (readGuarded reads a).orElse fun _ =>
        (lowerSpineApartFact reads a.fact).map fun f => { a with fact := f }
    | .atIndex .. | .either .. => readAtIndex reads a
    | .spineApart .. => (lowerSpineApartFact reads a.fact).map fun f => { a with fact := f }
    | _ => none

theorem lowerAtoms_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) : IndexHolds ε (lowerAtoms ls as) ρ h := by
  have hr : ∀ g ∈ bridgeReads ls, g ∈ bridgeReads ls := fun _ hg => hg
  simp only [lowerAtoms]
  split
  · intro a ha; cases ha
  · intro a ha hc
    obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
    split at hab
    · rename_i F hF
      split at hab
      · cases hab
        have hbF := he b hb hc
        rw [hF] at hbF
        exact (IndexFact.holdsAt_linear_mapVars (renameFact_mapVars (lowerByLinks (bridgeReads ls)) F)
          fun x _ y hy => by cases hy; exact lowerStar_eq hl hr _ x).mpr hbF
      · cases hab
    · have hc' : ∀ c, b.cond = some c → tagHolds .truthy (ρ c) = !b.negated := by
        unfold readEvery at hab
        split at hab
        · split at hab
          · simp only [Option.some.injEq] at hab; subst hab; exact hc
          · cases hab
        · cases hab
      exact readEvery_holds hl hr hab (he b hb hc')
    · cases hrg : readGuarded (bridgeReads ls) b with
      | some a' =>
        simp only [hrg, Option.orElse_some, Option.some.injEq] at hab
        subst hab
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hrg
        exact lowerGuardedFact_holds hl hr hf (he b hb hc)
      | none =>
        simp only [hrg, Option.orElse_none] at hab
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
        exact lowerSpineApartFact_holds hl hr hf (he b hb hc)
    · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
      exact lowerAtIndexFact_holds hl hr hf (he b hb hc)
    · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
      exact lowerAtIndexFact_holds hl hr hf (he b hb hc)
    · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hab
      exact lowerSpineApartFact_holds hl hr hf (he b hb hc)
    · cases hab

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
    let r := HeapLinks.rep (HeapLinks.classes ls)
    some fun t => liftTerm r reads reads.length (lowerTermAll r reads reads.length t)
  else none

theorem bridgeOf_eq {ls : HeapLinks.Links} {as bs : List IndexAtom} {c : Term → Term} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (hc : bridgeOf ls as bs = some c) (t : Term) :
    termValue ε ρ h (c t) = termValue ε ρ h t := by
  simp only [bridgeOf] at hc
  split at hc
  · cases hc
    have hr := HeapLinks.rep_eq (HeapLinks.classes_one hl)
    exact (liftTerm_eq hl hr _ _).trans (lowerTermAll_eq hl hr _ _)
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
    ∃ s ls b idx, Footprints.spineOf v = some s ∧ h[s]? = some (.arr ls) ∧ ρ k = .num b ∧
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
  obtain ⟨s, ls, hs, hl, rfl, -⟩ := lengthOf_spine hn
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
    SafeIntegers.indexOfBits_safe hsafe (by omega) (by omega), by cases strict <;> simp at f2 ⊢ <;> omega⟩

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

/-- A quantified atom witnesses its array's element spine, independently of
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
      elementsOf w = some sto ∧ h[sto]?.bind spineEntries = some ls := by
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
    obtain ⟨s, ls, b, idx, hs, hl, hb, hidx, hle⟩ : ∃ s ls b idx, Footprints.spineOf (PointClaims.mapEnv m ρ x) = some s ∧
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
      obtain ⟨sto, ls, hsto, hls, rfl, -⟩ := lengthOf_spine hn
      have hle := hlin.2
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hterm, Option.getD_some, Int.one_mul, Int.add_zero] at hle
      refine ⟨w, sto, ls, ls.length, hw, elementsOf_spine hsto, by rw [hls]; rfl, hterm, ?_⟩
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
  | index _ | length _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => rw [ht] at hf; cases hf

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
of a slot of `s`'s class (`r`) gives the field `f` its path starts with as
slot `v`, the path's rest from `v`, at most `n` times. -/
def lowerGuard (reads : List (Nat × String × Nat)) (r : Nat → Nat) : Nat → Nat → List String → Nat × List String
  | 0, s, p => (s, p)
  | _ + 1, s, [] => (s, [])
  | n + 1, s, f :: q =>
    let rs := r s
    match reads.find? (fun g => g.2.1 == f && r g.1 == rs) with
    | some (_, _, v) => lowerGuard reads r n v q
    | none => (s, f :: q)

theorem lowerGuard_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {r : Nat → Nat} (hr : ∀ x, ρ (r x) = ρ x) :
    ∀ n s p, readGuard h (ρ (lowerGuard (guardReads ls) r n s p).1)
      (lowerGuard (guardReads ls) r n s p).2 = readGuard h (ρ s) p := by
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
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, hrc⟩ := hc
        have heq : ρ c = ρ s := by rw [← hr c, hrc, hr]
        rw [ih, ← guardReads_read hl hm q, heq]
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

/-- The bodies of every unconditional guarded atom in `as` whose guard has tag
`t` at a path `lg` restates to the same target as `(s, p)`. -/
def sameGuardBodies (lg : Nat → List String → Nat × List String) (as : List IndexAtom)
    (s : Nat) (p : List String) (t : GuardTag) : List IndexAtom :=
  let goal := lg s p
  as.filterMap fun a => match a.cond, a.fact with
    | none, .guarded s' p' t' B' => if t' == t && lg s' p' == goal then some { fact := B' } else none
    | _, _ => none

theorem sameGuardBodies_mem {lg : Nat → List String → Nat × List String} {as : List IndexAtom}
    {s : Nat} {p : List String} {t : GuardTag} {ρ h}
    (hlg : ∀ s p, readGuard h (ρ (lg s p).1) (lg s p).2 = readGuard h (ρ s) p)
    (ha : IndexHolds ε as ρ h) {b : IndexAtom} (hb : b ∈ sameGuardBodies lg as s p t) :
    ∃ v, readGuard h (ρ s) p = some v ∧ (t.holds v ∨ b.fact.HoldsAt ε ρ h) := by
  simp only [sameGuardBodies, List.mem_filterMap] at hb
  obtain ⟨a, haa, hm⟩ := hb
  split at hm
  · rename_i s' p' t' B' hcond hfa
    split at hm
    · rename_i hmatch
      cases hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨rfl, hpath⟩ := hmatch
      have hat := ha a haa fun c hc => by rw [hcond] at hc; cases hc
      rw [hfa] at hat
      obtain ⟨v, hv, hor⟩ := hat
      exact ⟨v, by rw [← hlg s p, ← hpath, hlg]; exact hv, hor⟩
    · cases hm
  · cases hm

/-- Whether atoms `as` entail a fact, its terms and guard paths restated by
`lt` and `lg`: a linear fact as `linearEntailed` reads one; a guarded fact
where unconditional atoms state guards of the same tag at paths restated alike,
and the body follows from the atoms together with all those atoms' bodies; or
where its guard's path, restated toward its end by `ld`, reads a slot alone,
and its body follows; or where `tags` states the guard's path, or its
restatement, reads the tag's value. -/
def guardEntailsIn (lt : Term → Term) (lg ld : Nat → List String → Nat × List String)
    (tags : Nat → List String → GuardTag → Bool) (base : List IndexAtom → IndexFact → Bool)
    (K : Option (Thunk (Linear.Known Term))) :
    List IndexAtom → IndexFact → Bool
  | as, .either A B => guardEntailsIn lt lg ld tags base K as A || guardEntailsIn lt lg ld tags base K as B ||
      match B with
      | .pastSafe k => guardEntailsIn lt lg ld tags base none (as ++ pastLefts as k) A && pastLefts as k != []
      | _ => false
  | as, .linear F =>
    match K with
    | some kt => match F.mapVars (some ∘ lt) with
        | some F' => kt.get.entails F' && F'.vars.all (bridgedDefined lt as)
        | none => false
    | none =>
        (as.any fun a => a.cond.isNone && a.fact == .linear F) ||
        match F.mapVars (some ∘ lt) with
        | some F' => F'.vars.all (bridgedDefined lt as) &&
            Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) F'
        | none => false
  | as, .guarded s p t B =>
    tags s p t || tags (ld s p).1 (ld s p).2 t ||
    ((ld s p).2.isEmpty && as.any (fun a => a.cond.isNone && a.fact == B)) ||
    let same := sameGuardBodies lg as s p t
    match same with
    | [] => (ld s p).2.isEmpty && guardEntailsIn lt lg ld tags base K as B
    | _ :: _ =>
      same.any (fun a => a.fact == B) ||
      let K' := K.map fun kt => Thunk.mk fun _ =>
        (same.flatMap fun a => bridgeFacts lt (factLinear a.fact)).foldl Linear.Known.add kt.get
      guardEntailsIn lt lg ld tags base K' (as ++ same) B
  | as, .int k => intSlot as k
  | as, .pastSafe k => as.any fun a => a.cond.isNone && a.fact == .pastSafe k
  | as, F => base as F

def guardEntails (lt : Term → Term) (lg ld : Nat → List String → Nat × List String)
    (tags : Nat → List String → GuardTag → Bool) (base : List IndexAtom → IndexFact → Bool)
    (as : List IndexAtom) (F : IndexFact) : Bool :=
  guardEntailsIn lt lg ld tags base none as F

theorem guardEntailsIn_sound {lt : Term → Term} {lg ld : Nat → List String → Nat × List String}
    {tags : Nat → List String → GuardTag → Bool} {ρ : Env} {h : Heap}
    (hlt : ∀ t, termValue ε ρ h (lt t) = termValue ε ρ h t)
    (hlg : ∀ s p, readGuard h (ρ (lg s p).1) (lg s p).2 = readGuard h (ρ s) p)
    (hld : ∀ s p, readGuard h (ρ (ld s p).1) (ld s p).2 = readGuard h (ρ s) p)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    {base : List IndexAtom → IndexFact → Bool}
    (hbase : ∀ as F, base as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h) :
    ∀ (F : IndexFact) (K : Option (Thunk (Linear.Known Term))) (as : List IndexAtom),
      (∀ kt, K = some kt → kt.get.Holds (termValuation ε ρ h)) →
      guardEntailsIn lt lg ld tags base K as F = true → IndexHolds ε as ρ h →
      F.HoldsAt ε ρ h := by
  intro F
  induction F with
  | either A B ihA ihB =>
    intro K as hK hf ha
    simp only [guardEntailsIn] at hf
    rcases Bool.or_eq_true_iff.mp hf with hf | hP
    · rcases Bool.or_eq_true_iff.mp hf with hA | hB
      · exact .inl (ihA K as hK hA ha)
      · exact .inr (ihB K as hK hB ha)
    · split at hP
      · rename_i k
        obtain ⟨hA, -⟩ := Bool.and_eq_true_iff.mp hP
        by_cases hk : (IndexFact.pastSafe k).HoldsAt ε ρ h
        · exact .inr hk
        · refine .inl (ihA none _ (fun _ h => by cases h) hA fun b hb hc => ?_)
          rcases List.mem_append.mp hb with hb | hb
          · exact ha b hb hc
          · exact pastLefts_holds ha hk b hb hc
      · cases hP
  | linear F =>
    intro K as hK hf ha
    simp only [guardEntailsIn] at hf
    have hv' : ∀ x ∈ F.vars, ∀ y, (some ∘ lt) x = some y → termValuation ε ρ h y = termValuation ε ρ h x := by
      intro x _ y hy; cases hy; simp only [termValuation, hlt]
    cases hKe : K with
    | some kt =>
      rw [hKe] at hf
      dsimp only at hf
      split at hf
      · rename_i F' hF'
        simp only [Bool.and_eq_true, List.all_eq_true] at hf
        refine ⟨fun x hx => ?_, (Linear.Fact.holds_mapVars hF' hv').mp (Linear.Known.entails_sound (hK kt hKe) hf.1)⟩
        obtain ⟨y, hy, hxy⟩ := Linear.Fact.mapVars_vars_fwd hF' x hx
        cases hxy
        have hd := bridgedDefined_sound hlt ha (hf.2 _ hy)
        rw [hlt] at hd
        exact hd
      · cases hf
    | none =>
      rw [hKe] at hf
      dsimp only at hf
      rcases Bool.or_eq_true_iff.mp hf with hmem | hf
      · obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hmem
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hm
        have hat := ha a haa fun b hb => by rw [hm.1] at hb; cases hb
        rw [hm.2] at hat
        exact hat
      · split at hf
        · rename_i F' hF'
          simp only [Bool.and_eq_true, List.all_eq_true] at hf
          have hF'Holds := Linear.entailsWith_sound hf.2 (bridgeFacts_holds hlt (linearRaw_holds ha))
            (bridgeFacts_holds hlt (rangesRaw_holds ha))
          refine ⟨fun x hx => ?_, (Linear.Fact.holds_mapVars hF' hv').mp hF'Holds⟩
          obtain ⟨y, hy, hxy⟩ := Linear.Fact.mapVars_vars_fwd hF' x hx
          cases hxy
          have hd := bridgedDefined_sound hlt ha (hf.1 _ hy)
          rw [hlt] at hd
          exact hd
        · cases hf
  | guarded s p t B ih =>
    intro K as hK hf ha
    simp only [guardEntailsIn, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hf
    rcases hf with ((ht | htl) | ⟨hp, hmem⟩) | hrel
    · obtain ⟨v, hv, htv⟩ := htags s p t ht
      exact ⟨v, hv, .inl htv⟩
    · obtain ⟨v, hv, htv⟩ := htags _ _ t htl
      exact ⟨v, by rw [← hld s p]; exact hv, .inl htv⟩
    · obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hmem
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hm
      have hat := ha a haa fun b hb => by rw [hm.1] at hb; cases hb
      rw [hm.2] at hat
      exact ⟨ρ (ld s p).1, by rw [← hld s p, hp]; rfl, .inr hat⟩
    · generalize hsm : sameGuardBodies lg as s p t = same at hrel
      cases same with
      | nil =>
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hrel
        exact ⟨ρ (ld s p).1, by rw [← hld s p, hrel.1]; rfl, .inr (ih K as hK hrel.2 ha)⟩
      | cons a0 as0 =>
        have hmem0 : a0 ∈ sameGuardBodies lg as s p t := by rw [hsm]; exact List.mem_cons_self
        obtain ⟨v, hv, _⟩ := sameGuardBodies_mem hlg ha hmem0
        by_cases htv : t.holds v
        · exact ⟨v, hv, .inl htv⟩
        · have hall : ∀ a ∈ a0 :: as0, a.fact.HoldsAt ε ρ h := fun a ha' => by
            have hma : a ∈ sameGuardBodies lg as s p t := by rw [hsm]; exact ha'
            obtain ⟨v', hv', hor'⟩ := sameGuardBodies_mem hlg ha hma
            rw [hv] at hv'; cases hv'
            exact hor'.resolve_left htv
          simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hrel
          rcases hrel with ⟨a, ham, rfl⟩ | hrec
          · exact ⟨v, hv, .inr (hall a ham)⟩
          · refine ⟨v, hv, .inr (ih _ (as ++ a0 :: as0) ?_ hrec fun b hb hc => ?_)⟩
            · intro kt' hkt'
              obtain ⟨kt, rfl, hmk⟩ := Option.map_eq_some_iff.mp hkt'
              rw [← hmk]
              intro G hG
              rcases Linear.Known.mem_foldl_add hG with hG | hG
              · exact hK kt rfl G hG
              · obtain ⟨a, ham, hG'⟩ := List.mem_flatMap.mp hG
                exact bridgeFacts_holds hlt (factLinear_holds (hall a ham)) G hG'
            · rcases List.mem_append.mp hb with hb | hb
              · exact ha b hb hc
              · exact hall b hb
  | int k =>
    intro _ as _ hf ha
    exact intSlot_sound ha hf
  | pastSafe k =>
    intro _ as _ hf ha
    obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hm
    have hat := ha a haa fun b hb => by rw [hm.1] at hb; cases hb
    rw [hm.2] at hat
    exact hat
  | index _ | length _ _ | bound _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ =>
    intro _ as _ hf; exact hbase as _ (by simpa [guardEntailsIn] using hf)

theorem guardEntails_sound {lt : Term → Term} {lg ld : Nat → List String → Nat × List String}
    {tags : Nat → List String → GuardTag → Bool} {ρ : Env} {h : Heap}
    (hlt : ∀ t, termValue ε ρ h (lt t) = termValue ε ρ h t)
    (hlg : ∀ s p, readGuard h (ρ (lg s p).1) (lg s p).2 = readGuard h (ρ s) p)
    (hld : ∀ s p, readGuard h (ρ (ld s p).1) (ld s p).2 = readGuard h (ρ s) p)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    {base : List IndexAtom → IndexFact → Bool}
    (hbase : ∀ as F, base as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h) :
    ∀ (F : IndexFact) (as : List IndexAtom), guardEntails lt lg ld tags base as F = true → IndexHolds ε as ρ h →
      F.HoldsAt ε ρ h :=
  fun F as hf ha => guardEntailsIn_sound hlt hlg hld htags hbase F none as (fun _ h => by cases h) hf ha

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

/-- The unconditional disjunctions in `as` (excluding `pastSafe` alternatives)
sharing a slot with `F` (all of them where `F` names no slot). -/
def eithersOf (as : List IndexAtom) (F : IndexFact) : List IndexAtom :=
  let all := as.filter fun a => a.cond.isNone && match a.fact with
    | .either _ (.pastSafe _) => false
    | .either _ _ => true
    | _ => false
  if all.isEmpty then [] else
  let fs := F.slots
  if fs.isEmpty then all else
  all.filter fun a => a.fact.slots.any fs.contains

theorem eithersOf_sub {as : List IndexAtom} {F : IndexFact} {a : IndexAtom} (h : a ∈ eithersOf as F) : a ∈ as := by
  unfold eithersOf at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · exact (List.mem_filter.mp h).1
    · exact (List.mem_filter.mp (List.mem_filter.mp h).1).1

private theorem eval_negForm {v : Term → Int} :
    ∀ (form : Linear.Form Term), Linear.Form.eval v (form.map fun (t, c) => (t, -c)) = -Linear.Form.eval v form
  | [] => by simp [Linear.Form.eval]
  | (t, c) :: rest => by
    simp only [List.map_cons, Linear.Form.eval, eval_negForm rest]
    have hmul : (-c) * v t = -(c * v t) := Int.neg_mul c (v t)
    omega

/-- Whether an arm `C` of a disjunction contradicts `as`: for a linear
inequality or disequality, by checking its targeted negation over `as`
(avoiding a whole-store contradiction search); otherwise by checking
contradiction or `pastClash` over `as ++ [C]`. -/
def armContradicts (check : List IndexAtom → IndexFact → Bool) (as : List IndexAtom) : IndexFact → Bool
  | .linear (.le form d) => check as (.linear (.le (form.map fun (t, c) => (t, -c)) (-d - 1)))
  | .linear (.ne form d) =>
    check as (.linear (.le form d)) && check as (.linear (.le (form.map fun (t, c) => (t, -c)) (-d)))
  | C => check (as ++ [{ fact := C }]) (.linear (.le [] (-1))) || pastClash (as ++ [{ fact := C }])

theorem armContradicts_sound {check : List IndexAtom → IndexFact → Bool} {ρ : Env} {h : Heap}
    (hcheck : ∀ as F, check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h)
    {as : List IndexAtom} {C : IndexFact} (hc : armContradicts check as C = true)
    (ha : IndexHolds ε as ρ h) (hC : C.HoldsAt ε ρ h) : False := by
  cases C with
  | linear L =>
    cases L with
    | le form d =>
      have hneg := (hcheck as _ hc ha).2
      simp only [Linear.Fact.Holds, eval_negForm] at hneg
      have hpos : Linear.Form.eval (termValuation ε ρ h) form ≤ d := hC.2
      omega
    | ne form d =>
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
      have hle1 : Linear.Form.eval (termValuation ε ρ h) form ≤ d := (hcheck as _ h1 ha).2
      have hle2 := (hcheck as _ h2 ha).2
      simp only [Linear.Fact.Holds, eval_negForm] at hle2
      have hne : Linear.Form.eval (termValuation ε ρ h) form ≠ d := hC.2
      omega
  | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _
  | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ =>
    have hext : IndexHolds ε (as ++ [{ fact := _ }]) ρ h := fun b hb hbcond =>
      (List.mem_append.mp hb).elim (fun hb => ha b hb hbcond)
        (fun hb => by simp only [List.mem_singleton] at hb; subst hb; exact hC)
    rcases Bool.or_eq_true_iff.mp hc with hc | hp
    · have bad := (hcheck _ (.linear (.le [] (-1))) hc hext).2
      simp [Linear.Fact.Holds, Linear.Form.eval] at bad
    · exact pastClash_sound hp hext

/-- Sequential case splitting over a queue `rem` of disjunctions in `as`:
each step splits the head disjunction `a = A ∨ B`, checking each arm by
targeted contradiction (`armContradicts`), direct entailment of `F`, or
further splitting over `rest`. -/
def caseEntailsAux (check : List IndexAtom → IndexFact → Bool) :
    Nat → List IndexAtom → List IndexAtom → IndexFact → Bool
  | 0, _, _, _ => false
  | _, _, [], _ => false
  | n + 1, as, a :: rest, F =>
    match a.cond, a.fact with
    | none, .either A B =>
      let armOk (C : IndexFact) : Bool :=
        armContradicts check as C ||
        let as' := as ++ [{ fact := C }]
        check as' F ||
        let rC := match C with | .either _ _ => ({ fact := C } : IndexAtom) :: rest | _ => rest
        caseEntailsAux check n as' rC F
      armOk A && armOk B
    | _, _ => false

theorem caseEntailsAux_sound {check : List IndexAtom → IndexFact → Bool} {ρ : Env} {h : Heap}
    (hcheck : ∀ as F, check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h) :
    ∀ n as rem F, (∀ a ∈ rem, a ∈ as) → caseEntailsAux check n as rem F = true →
      IndexHolds ε as ρ h → F.HoldsAt ε ρ h := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hf; simp [caseEntailsAux] at hf
  | succ n ih =>
    intro as rem F hsub hf ha
    cases rem with
    | nil => simp [caseEntailsAux] at hf
    | cons a rest =>
      simp only [caseEntailsAux] at hf
      split at hf
      · rename_i A B hc he
        obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hf
        have hab := ha a (hsub a (List.mem_cons_self ..)) (fun b hb => by rw [hc] at hb; cases hb)
        rw [he] at hab
        have solveArm : ∀ C : IndexFact, C.HoldsAt ε ρ h →
            (armContradicts check as C || (check (as ++ [{ fact := C }]) F ||
              caseEntailsAux check n (as ++ [{ fact := C }])
                (match C with | .either _ _ => ({ fact := C } : IndexAtom) :: rest | _ => rest) F)) = true →
            F.HoldsAt ε ρ h := by
          intro C hC hok
          have hext : IndexHolds ε (as ++ [{ fact := C }]) ρ h := fun b hb hbcond =>
            (List.mem_append.mp hb).elim (fun hb => ha b hb hbcond)
              (fun hb => by simp only [List.mem_singleton] at hb; subst hb; exact hC)
          rcases Bool.or_eq_true_iff.mp hok with hcon | h1
          · exact (armContradicts_sound hcheck hcon ha hC).elim
          · rcases Bool.or_eq_true_iff.mp h1 with hdir | hrec
            · exact hcheck _ F hdir hext
            · refine ih _ _ F ?_ hrec hext
              intro b hb
              split at hb
              · rcases List.mem_cons.mp hb with rfl | hb
                · exact List.mem_append_right _ (List.mem_singleton_self _)
                · exact List.mem_append_left _ (hsub b (List.mem_cons_of_mem _ hb))
              · exact List.mem_append_left _ (hsub b (List.mem_cons_of_mem _ hb))
        rcases hab with hA' | hB'
        · exact solveArm A hA' hA
        · exact solveArm B hB' hB
      · cases hf

/-- Disjunction monotonicity (`A' ∨ B' ⊢ A ∨ B` when `A' ⊢ A` and `B' ⊢ B`),
applied once at the top of `caseEntails` so `caseEntailsAux` does not repeat
the scan over `as` at every split branch. -/
def eitherMono (check : List IndexAtom → IndexFact → Bool) (as : List IndexAtom) : IndexFact → Bool
  | .either A B =>
    as.any fun a => a.cond.isNone && match a.fact with
      | .either A' B' =>
        let asA := as ++ [{ fact := A' }]
        let asB := as ++ [{ fact := B' }]
        (check asA A || eitherMono check asA A) &&
        (check asB B || eitherMono check asB B)
      | _ => false
  | _ => false

theorem eitherMono_sound {check : List IndexAtom → IndexFact → Bool} {ρ : Env} {h : Heap}
    (hcheck : ∀ as F, check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h) :
    ∀ F as, eitherMono check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h := by
  intro F
  induction F with
  | either A B ihA ihB =>
    intro as hf ha
    simp only [eitherMono] at hf
    obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
    obtain ⟨hcond, hm⟩ := hm
    split at hm
    · rename_i A' B' hfa
      obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hm
      have hat := ha a haa fun b hb => by rw [hcond] at hb; cases hb
      rw [hfa] at hat
      rcases hat with hA' | hB'
      · have hext : IndexHolds ε (as ++ [{ fact := A' }]) ρ h := fun b hb hc =>
          (List.mem_append.mp hb).elim (fun hb => ha b hb hc)
            (fun hb => by simp only [List.mem_singleton] at hb; subst hb; exact hA')
        exact .inl ((Bool.or_eq_true_iff.mp hA).elim (fun h1 => hcheck _ A h1 hext) (fun h2 => ihA _ h2 hext))
      · have hext : IndexHolds ε (as ++ [{ fact := B' }]) ρ h := fun b hb hc =>
          (List.mem_append.mp hb).elim (fun hb => ha b hb hc)
            (fun hb => by simp only [List.mem_singleton] at hb; subst hb; exact hB')
        exact .inr ((Bool.or_eq_true_iff.mp hB).elim (fun h1 => hcheck _ B h1 hext) (fun h2 => ihB _ h2 hext))
    · cases hm
  | _ => intro _ hf; simp [eitherMono] at hf

/-- Entailment by finite case splitting. Both arms of an unconditional
 disjunction must entail the target. Exhausting the fuel refuses the split. -/
def caseEntails (check : List IndexAtom → IndexFact → Bool) (n : Nat) (as : List IndexAtom) (F : IndexFact) : Bool :=
  check as F || eitherMono check as F || check as (.linear (.le [] (-1))) || pastClash as || caseEntailsAux check n as (eithersOf as F) F

theorem caseEntails_sound {check : List IndexAtom → IndexFact → Bool} {ρ : Env} {h : Heap}
    (hcheck : ∀ as F, check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h) :
    ∀ n as F, caseEntails check n as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h := by
  intro n as F hf ha
  unfold caseEntails at hf
  rcases Bool.or_eq_true_iff.mp hf with h0 | haux
  · rcases Bool.or_eq_true_iff.mp h0 with h1 | hp
    · rcases Bool.or_eq_true_iff.mp h1 with h2 | hcon
      · rcases Bool.or_eq_true_iff.mp h2 with hdir | hmono
        · exact hcheck as F hdir ha
        · exact eitherMono_sound hcheck F as hmono ha
      · have bad := (hcheck as (.linear (.le [] (-1))) hcon ha).2
        simp [Linear.Fact.Holds, Linear.Form.eval] at bad
    · exact (pastClash_sound hp ha).elim
  · exact caseEntailsAux_sound hcheck n as (eithersOf as F) F (fun _ h => eithersOf_sub h) haux ha

/-- Two regions apart hold different spines. -/
theorem regionsApart_spines {h : Heap} {u w : Val} (ha : RegionsApart h u w) :
    ∀ s t, Footprints.spineOf u = some s → Footprints.spineOf w = some t → s ≠ t := by
  intro s t hs ht
  obtain ⟨sa, xs, sb, ys, hu, hw, hne⟩ := ha
  have hsa : sa = some s := by
    rcases hu with ⟨-, rfl⟩ | ⟨st, hst, hst', -⟩
    · simp [Footprints.spineOf, Footprints.fieldsOf] at hs
    · rw [hs] at hst'; cases hst'; exact hst
  have hsb : sb = some t := by
    rcases hw with ⟨-, rfl⟩ | ⟨st, hst, hst', -⟩
    · simp [Footprints.spineOf, Footprints.fieldsOf] at ht
    · rw [ht] at hst'; cases hst'; exact hst
  exact hne s (.inl hsa) t (.inl hsb)

/-- The sites that read what the path `p` from slot `x` reads, through the
source's read links: the path itself, and for a first field `f` that a
non-optional read link from a slot of `x`'s class reads into slot `y`, the
sites of the rest from `y`. -/
def pathSites (M : Nat → List Nat) (ls : HeapLinks.Links) : Nat → List String → List (Nat × List String)
  | x, [] => [(x, [])]
  | x, f :: p => (x, f :: p) :: ls.flatMap fun g =>
      if !g.alias && !g.optional && (M x).contains g.cell && g.field == .str f then pathSites M ls g.value p else []

/-- **Every site of a path reads what the path reads.** -/
theorem pathSites_read {M : Nat → List Nat} {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h) :
    ∀ (p : List String) (x : Nat) {z : Nat} {r : List String}, (z, r) ∈ pathSites M ls x p →
      readPath h (ρ z) r = readPath h (ρ x) p := by
  intro p
  induction p with
  | nil => intro x z r hm; simp only [pathSites, List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm; rfl
  | cons f p ih =>
    intro x z r hm
    simp only [pathSites, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨g, hg, hm⟩
    · rfl
    · split at hm
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hc
        obtain ⟨⟨⟨hal, hop⟩, hcell⟩, hfield⟩ := hc
        rw [ih g.value hm]
        have hh := hl g hg
        simp only [hal, hop, Bool.false_eq_true, ite_false] at hh
        obtain ⟨flds, c, oid, l, hobj, hlook, hv⟩ := hh
        rw [← hM _ _ hcell, hobj, readPath_cons (by rw [← hfield]; exact hlook) hv]
      · cases hm

/-- Two lists of sites share a site: the same path from slots of one class. -/
def sitesMeet (M : Nat → List Nat) (X Y : List (Nat × List String)) : Bool :=
  X.any fun z => Y.any fun w => z.2 == w.2 && (M z.1).contains w.1

theorem sitesMeet_read {M : Nat → List Nat} {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h) {x y : Nat} {p q : List String}
    (hs : sitesMeet M (pathSites M ls x p) (pathSites M ls y q) = true) :
    readPath h (ρ x) p = readPath h (ρ y) q := by
  obtain ⟨⟨z, r⟩, hz, hm⟩ := List.any_eq_true.mp hs
  obtain ⟨⟨w, r'⟩, hw, hm⟩ := List.any_eq_true.mp hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hm
  obtain ⟨rfl, hc⟩ := hm
  rw [← pathSites_read hM hl p x hz, ← pathSites_read hM hl q y hw, hM _ _ hc]

/-- The two sites an unconditional atom states the spines of apart: a region
fact's slots, or a spine separation's paths. -/
def spineSites : IndexFact → Option ((Nat × List String) × (Nat × List String))
  | .apart u w => some ((u, []), (w, []))
  | .spineApart u p w q => some ((u, p), (w, q))
  | _ => none

theorem spineSites_holds {F : IndexFact} {u w : Nat} {p q : List String} {ρ h}
    (hs : spineSites F = some ((u, p), (w, q))) (hF : F.HoldsAt ε ρ h) : PathSpinesApart h (ρ u) p (ρ w) q := by
  cases F <;> simp only [spineSites, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hs
  · obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hs
    exact ⟨_, _, rfl, rfl, regionsApart_spines hF⟩
  · obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hs
    exact hF

/-- Whether an unconditional spine separation, a target atom, follows from an
unconditional source atom stating two spines apart (`spineSites`) whose sites
the target's paths share through the source's read links (`pathSites`,
`store-apart-links`). -/
def spineFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (ls : HeapLinks.Links)
    (a : List IndexAtom) (t : IndexAtom) : Bool :=
  t.cond.isNone && match t.fact with
  | .spineApart x p y q =>
    let X := pathSites M ls (PointClaims.slot m x) p
    let Y := pathSites M ls (PointClaims.slot m y) q
    a.any fun s => s.cond.isNone && match spineSites s.fact with
      | some ((u, p'), (w, q')) =>
        let U := pathSites M ls u p'
        let W := pathSites M ls w q'
        sitesMeet M X U && sitesMeet M Y W || sitesMeet M X W && sitesMeet M Y U
      | none => false
  | _ => false

theorem spineFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ls : HeapLinks.Links}
    {a : List IndexAtom} {t : IndexAtom} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (hf : spineFollows M m ls a t = true) (ha : IndexHolds ε a ρ h) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  simp only [spineFollows, Bool.and_eq_true] at hf
  obtain ⟨-, hf⟩ := hf
  split at hf
  case h_2 => cases hf
  rename_i x p y q hfact
  rw [hfact]
  obtain ⟨s, hs, hm⟩ := List.any_eq_true.mp hf
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hn, hm⟩ := hm
  have hat := ha s hs fun b hb => by rw [hn] at hb; cases hb
  split at hm
  · rename_i u p' w q' hsf
    obtain ⟨u', w', hu, hw, hne⟩ := spineSites_holds hsf hat
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hm
    show PathSpinesApart h (ρ (PointClaims.slot m x)) p (ρ (PointClaims.slot m y)) q
    rcases hm with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨u', w', (sitesMeet_read hM hl hx).trans hu, (sitesMeet_read hM hl hy).trans hw, hne⟩
    · exact ⟨w', u', (sitesMeet_read hM hl hx).trans hw, (sitesMeet_read hM hl hy).trans hu,
        fun s t hs ht he => hne t s ht hs he.symm⟩
  · cases hm

/-- Whether a `fieldRead v o fld` fact holds by a non-optional read link in `ls`. -/
def fieldReadFollows (M : Nat → List Nat) (ls : HeapLinks.Links) : IndexFact → Bool
  | .fieldRead v o fld => ls.any fun g => !g.alias && !g.optional && g.field == .str fld &&
      (M o).contains g.cell && (M v).contains g.value
  | _ => false

theorem fieldReadFollows_sound {M : Nat → List Nat} {ls : HeapLinks.Links} {F : IndexFact} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (hf : fieldReadFollows M ls F = true) : F.HoldsAt ε ρ h := by
  cases F with
  | fieldRead v o fld =>
    obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hm
    obtain ⟨⟨⟨⟨ha, ho⟩, hfld⟩, hcell⟩, hval⟩ := hm
    have hlg := hl g hg
    simp only [ha, ho, Bool.false_eq_true, ite_false] at hlg
    obtain ⟨flds, cd, oid, l, hobj, hlk, hlv⟩ := hlg
    rw [hfld] at hlk
    simp only [IndexFact.HoldsAt]
    rw [← hM o g.cell hcell, ← hM v g.value hval, hobj]
    simp [readPath, hlk, hlv]
  | _ => simp [fieldReadFollows] at hf

/-- A fact follows from the atoms, read at their own slots: an unconditional
atom it follows from (`factFollows`), a spine separation the atoms state
at sites its paths share (`spineFollows`), or a field read a link states
(`fieldReadFollows`). -/
def baseFollows (M : Nat → List Nat) (ls : HeapLinks.Links) (as : List IndexAtom) (F : IndexFact) : Bool :=
  as.any (fun s => s.cond.isNone && factFollows M none s.fact F) || spineFollows M none ls as { fact := F } ||
    fieldReadFollows M ls F

theorem baseFollows_sound {M : Nat → List Nat} {ls : HeapLinks.Links} {as : List IndexAtom} {F : IndexFact} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (hf : baseFollows M ls as F = true) (ha : IndexHolds ε as ρ h) : F.HoldsAt ε ρ h := by
  rcases Bool.or_eq_true_iff.mp hf with hf | hf
  · rcases Bool.or_eq_true_iff.mp hf with hf | hf
    · obtain ⟨s, hs, hm⟩ := List.any_eq_true.mp hf
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
      exact factFollows_sound (m := none) hM hm.2 (ha s hs fun b hb => by rw [hm.1] at hb; cases hb)
    · exact spineFollows_sound (m := none) hM hl hf ha
  · exact fieldReadFollows_sound hM hl hf

/-- Unwraps any leading guards of a fact whose complementary guard holds under
`tags` (directly or lowered through `ld`). -/
def releaseFact (tags : Nat → List String → GuardTag → Bool)
    (ld : Nat → List String → Nat × List String) : IndexFact → Option IndexFact
  | .guarded s p t B =>
    if tags s p t.complement || tags (ld s p).1 (ld s p).2 t.complement then
      some ((releaseFact tags ld B).getD B)
    else none
  | _ => none

theorem releaseFact_holds {tags : Nat → List String → GuardTag → Bool}
    {ld : Nat → List String → Nat × List String} {ρ : Env} {h : Heap}
    (hld : ∀ s p, readGuard h (ρ (ld s p).1) (ld s p).2 = readGuard h (ρ s) p)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v) :
    ∀ {F G : IndexFact}, releaseFact tags ld F = some G → F.HoldsAt ε ρ h → G.HoldsAt ε ρ h := by
  intro F
  induction F with
  | guarded s p t B ih =>
    intro G hG hF
    simp only [releaseFact] at hG
    split at hG
    · rename_i htc
      simp only [Option.some.injEq] at hG
      obtain ⟨v, hv, hor⟩ := hF
      have hcomp : ∃ w, readGuard h (ρ s) p = some w ∧ t.complement.holds w := by
        rcases Bool.or_eq_true_iff.mp htc with ht1 | ht2
        · exact htags s p t.complement ht1
        · obtain ⟨w, hw, htw⟩ := htags _ _ t.complement ht2
          exact ⟨w, by rw [← hld s p]; exact hw, htw⟩
      obtain ⟨w, hw, htw⟩ := hcomp
      rw [hv] at hw; cases hw
      have hB : B.HoldsAt ε ρ h := hor.resolve_left (GuardTag.complement_not_holds htw)
      cases hr : releaseFact tags ld B with
      | none => rw [hr] at hG; subst hG; exact hB
      | some B' => rw [hr] at hG; subst hG; exact ih hr hB
    · cases hG
  | _ => intro G hG; simp [releaseFact] at hG

/-- The bodies of guarded atoms whose guard's complement holds under `tags`. -/
def releaseGuarded (tags : Nat → List String → GuardTag → Bool)
    (ld : Nat → List String → Nat × List String) (as : List IndexAtom) : List IndexAtom :=
  as.filterMap fun a => (releaseFact tags ld a.fact).map fun G => { a with fact := G }

theorem releaseGuarded_holds {tags : Nat → List String → GuardTag → Bool}
    {ld : Nat → List String → Nat × List String} {as : List IndexAtom} {ρ : Env} {h : Heap}
    (hld : ∀ s p, readGuard h (ρ (ld s p).1) (ld s p).2 = readGuard h (ρ s) p)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    (ha : IndexHolds ε as ρ h) : IndexHolds ε (releaseGuarded tags ld as) ρ h := by
  intro b hb hc
  obtain ⟨a, haa, hbm⟩ := List.mem_filterMap.mp hb
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hbm
  exact releaseFact_holds hld htags hG (ha a haa hc)

/-- A body variable with its free term lifted by `lt`. -/
def liftBound (lt : Term → Term) : Bound → Bound
  | .free t => .free (lt t)
  | b => b

/-- Whether two terms are entailed equal under the read bridge `lt`: equal
after lifting, or both defined with both inequalities entailed. -/
def entailsTermEq (lt : Term → Term) (as : List IndexAtom) (a b : Term) : Bool :=
  let la := lt a
  let lb := lt b
  la == lb ||
    (bridgedDefined lt as la && bridgedDefined lt as lb &&
      Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) (.le [(la, 1), (lb, -1)] 0) &&
      Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) (.le [(lb, 1), (la, -1)] 0))

theorem entailsTermEq_sound {lt : Term → Term} {as : List IndexAtom} {a b : Term} {ρ : Env} {h : Heap}
    (hlt : ∀ t, termValue ε ρ h (lt t) = termValue ε ρ h t) (ha : IndexHolds ε as ρ h)
    (heq : entailsTermEq lt as a b = true) : termValue ε ρ h a = termValue ε ρ h b := by
  unfold entailsTermEq at heq
  rcases Bool.or_eq_true_iff.mp heq with hsyn | hlin
  · rw [← hlt a, ← hlt b, beq_iff_eq.mp hsyn]
  · simp only [Bool.and_eq_true] at hlin
    obtain ⟨⟨⟨hda, hdb⟩, h1⟩, h2⟩ := hlin
    obtain ⟨na, hna⟩ := Option.isSome_iff_exists.mp (bridgedDefined_sound hlt ha hda)
    obtain ⟨nb, hnb⟩ := Option.isSome_iff_exists.mp (bridgedDefined_sound hlt ha hdb)
    have f1 := Linear.entailsWith_sound h1 (bridgeFacts_holds hlt (linearRaw_holds ha))
      (bridgeFacts_holds hlt (rangesRaw_holds ha))
    have f2 := Linear.entailsWith_sound h2 (bridgeFacts_holds hlt (linearRaw_holds ha))
      (bridgeFacts_holds hlt (rangesRaw_holds ha))
    simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hna, hnb, Option.getD_some] at f1 f2
    rw [← hlt a, ← hlt b, hna, hnb]; congr; omega

/-- Instantiate a body variable at a read `r = a[j]` of an array element. -/
def instBoundAt (r j : Nat) : Bound → Option Term
  | .index => some (.value j)
  | .elem => some (.value r)
  | .project k q => some (.now k r q)
  | .free t => some t
  | .offset _ | .parallel _ _ _ _ => none

/-- Order on body variables for linear entailment over `Bound`. -/
def boundRank : Bound → Nat
  | .index => 0
  | .elem => 1
  | .offset _ => 2
  | .project _ _ => 3
  | .free _ => 4
  | .parallel _ _ _ _ => 5

def boundBefore (a b : Bound) : Bool :=
  match a, b with
  | .offset d1, .offset d2 => decide (d1 < d2)
  | .project k1 p1, .project k2 p2 => decide (Term.now k1 0 p1 < Term.now k2 0 p2)
  | .free t1, .free t2 => decide (t1 < t2)
  | .parallel s1 p1 k1 ep1, .parallel s2 p2 k2 ep2 =>
      decide ((Term.now .value s1 p1 < Term.now .value s2 p2) ∨
        (Term.now .value s1 p1 = Term.now .value s2 p2 ∧ Term.now k1 0 ep1 < Term.now k2 0 ep2))
  | a, b => decide (boundRank a < boundRank b)

local instance : LT Bound := ⟨fun a b => boundBefore a b = true⟩
local instance : DecidableRel (α := Bound) (· < ·) := fun a b => inferInstanceAs (Decidable (boundBefore a b = true))

/-- Whether a lifted body clause `lbody` follows from a lifted source body
clause `lbody'` and the ambient linear facts of `as` (under `lt`). -/
def bodyClauseEntails (lt : Term → Term) (as : List IndexAtom) (lbody' lbody : LinearClause Bound) : Bool :=
  lbody' == lbody || match lbody', lbody with
  | .atom F', .atom F =>
    F.vars.all (fun v => F'.vars.contains v || match v with
      | .index => true
      | .free t => bridgedDefined lt as t
      | _ => false) &&
    Linear.entailsWith (F' :: (bridgeFacts lt (linearRaw as)).map (renameFact Bound.free))
      ((bridgeFacts lt (rangesRaw as)).map (renameFact Bound.free)) F
  | _, _ => false

theorem bodyClauseEntails_sound {lt : Term → Term} {as : List IndexAtom} {lbody' lbody : LinearClause Bound}
    {elemLs : List (Option Nat)} {i : Nat} {ρ : Env} {h : Heap}
    (hlt : ∀ t, termValue ε ρ h (lt t) = termValue ε ρ h t) (ha : IndexHolds ε as ρ h)
    (he : bodyClauseEntails lt as lbody' lbody = true)
    (h' : lbody'.HoldsAt (boundValue ε ρ h elemLs i)) :
    lbody.HoldsAt (boundValue ε ρ h elemLs i) := by
  unfold bodyClauseEntails at he
  rcases Bool.or_eq_true_iff.mp he with hsyn | hlin
  · exact (beq_iff_eq.mp hsyn) ▸ h'
  · cases lbody' with
    | either _ _ => simp at hlin
    | atom F' =>
      cases lbody with
      | either _ _ => simp at hlin
      | atom F =>
        simp only [Bool.and_eq_true, List.all_eq_true] at hlin
        obtain ⟨hdef, hent⟩ := hlin
        have hbf : ∀ G ∈ (bridgeFacts lt (linearRaw as)).map (renameFact Bound.free),
            G.Holds (fun x => (boundValue ε ρ h elemLs i x).getD 0) := by
          intro G hG
          obtain ⟨G0, hG0, rfl⟩ := List.mem_map.mp hG
          exact (Linear.Fact.holds_mapVars (renameFact_mapVars Bound.free G0) fun x _ y hy => by
            cases hy; rfl).mpr (bridgeFacts_holds hlt (linearRaw_holds ha) G0 hG0)
        have hbr : ∀ G ∈ (bridgeFacts lt (rangesRaw as)).map (renameFact Bound.free),
            G.Holds (fun x => (boundValue ε ρ h elemLs i x).getD 0) := by
          intro G hG
          obtain ⟨G0, hG0, rfl⟩ := List.mem_map.mp hG
          exact (Linear.Fact.holds_mapVars (renameFact_mapVars Bound.free G0) fun x _ y hy => by
            cases hy; rfl).mpr (bridgeFacts_holds hlt (rangesRaw_holds ha) G0 hG0)
        refine ⟨fun v hv => ?_, Linear.entailsWith_sound hent (fun G hG => ?_) hbr⟩
        · rcases Bool.or_eq_true_iff.mp (hdef v hv) with hmem | hkind
          · exact h'.1 v (List.contains_iff_mem.mp hmem)
          · cases v with
            | index => rfl
            | free t => exact bridgedDefined_sound hlt ha hkind
            | elem | offset _ | project _ _ | parallel _ _ _ _ => cases hkind
        · rcases List.mem_cons.mp hG with rfl | hG
          · exact h'.2
          · exact hbf G hG

/-- Whether an indexed-element fact `atIndex s p idx guard body` follows from
the source atoms `as`: by matching an existing `atIndex` (at a shared array
site, equal index, compatible guard and entailed body), by introducing from a
checked element read `element r x j` whose read value satisfies the body (or
its guard), or by specializing a quantified `every` over the same array at a
known in-bounds index. -/
def atIndexFollows (M : Nat → List Nat) (ls : HeapLinks.Links)
    (lt : Term → Term) (lg ld : Nat → List String → Nat × List String)
    (tags : Nat → List String → GuardTag → Bool) (as : List IndexAtom) : IndexFact → Bool
  | .atIndex s p idx guard body =>
    let S := pathSites M ls s p
    let lbody := renameClause (liftBound lt) body
    as.any fun a => a.cond.isNone && match a.fact with
      | .atIndex s' p' idx' guard' body' =>
        sitesMeet M S (pathSites M ls s' p') && (guard' == guard || guard'.isNone) &&
          entailsTermEq lt as idx' idx && bodyClauseEntails lt as (renameClause (liftBound lt) body') lbody
      | .element r x j =>
        sitesMeet M S (pathSites M ls x []) && entailsTermEq lt as (.value j) idx &&
          match body.mapVars (instBoundAt r j) with
          | some inst =>
            guardEntails lt lg ld tags (baseFollows M ls) as
              (match guard with | some g => .guarded r [] g inst.toIndexFact | none => inst.toIndexFact)
          | none => false
      | .every s' p' stop everyBody =>
        let lidx := lt idx
        let lstop := lt stop
        let llen := lt (.now .length s' p')
        sitesMeet M S (pathSites M ls s' p') &&
          bridgedDefined lt as lidx && bridgedDefined lt as llen &&
          Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) (.le [(lidx, -1)] 0) &&
          Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) (.le [(lidx, 1), (lstop, -1)] (-1)) &&
          Linear.entailsWith (bridgeFacts lt (linearRaw as)) (bridgeFacts lt (rangesRaw as)) (.le [(lidx, 1), (llen, -1)] (-1)) &&
          everyBody.any fun
            | .clause F' => bodyClauseEntails lt as (renameClause (liftBound lt) F') lbody
            | .guarded .. => false
      | _ => false
  | _ => false

theorem atIndexFollows_sound {M : Nat → List Nat} {ls : HeapLinks.Links}
    {lt : Term → Term} {lg ld : Nat → List String → Nat × List String}
    {tags : Nat → List String → GuardTag → Bool} {as : List IndexAtom} {F : IndexFact} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (hlt : ∀ t, termValue ε ρ h (lt t) = termValue ε ρ h t)
    (hlg : ∀ s p, readGuard h (ρ (lg s p).1) (lg s p).2 = readGuard h (ρ s) p)
    (hld : ∀ s p, readGuard h (ρ (ld s p).1) (ld s p).2 = readGuard h (ρ s) p)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    (hf : atIndexFollows M ls lt lg ld tags as F = true) (ha : IndexHolds ε as ρ h) :
    F.HoldsAt ε ρ h := by
  cases F with
  | atIndex s p idx guard body =>
    simp only [atIndexFollows] at hf
    obtain ⟨a, haa, hm⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hm
    obtain ⟨hcond, hm⟩ := hm
    have hat := ha a haa fun b hb => by rw [hcond] at hb; cases hb
    have hliftBody : ∀ (elemLs : List (Option Nat)) (i : Nat) (C : LinearClause Bound),
        (renameClause (liftBound lt) C).HoldsAt (boundValue ε ρ h elemLs i) ↔
          C.HoldsAt (boundValue ε ρ h elemLs i) := fun elemLs i C =>
      LinearClause.holdsAt_mapVars (renameClause_mapVars (liftBound lt) C) fun x _ y hy => by
        simp only [Function.comp_apply, Option.some.injEq] at hy; subst hy
        cases x with
        | free t => exact hlt t
        | _ => rfl
    cases hfa : a.fact with
    | atIndex s' p' idx' guard' body' =>
      rw [hfa] at hm hat
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨⟨hsites, hguard⟩, hidxEq⟩, hbodyEq⟩ := hm
      obtain ⟨w, sto, elemLs, i, hw, hsto, hls, hi, hltLen, hrest⟩ := hat
      have hw' : readPath h (ρ s) p = some w := (sitesMeet_read hM hl hsites).trans hw
      have hi' : termValue ε ρ h idx = some (i : Int) := (entailsTermEq_sound hlt ha hidxEq).symm.trans hi
      have hbodyImp : body'.HoldsAt (boundValue ε ρ h elemLs i) → body.HoldsAt (boundValue ε ρ h elemLs i) := fun hB =>
        (hliftBody elemLs i body).mp (bodyClauseEntails_sound hlt ha hbodyEq ((hliftBody elemLs i body').mpr hB))
      refine ⟨w, sto, elemLs, i, hw', hsto, hls, hi', hltLen, ?_⟩
      cases guard' with
      | none =>
        cases guard with
        | none => exact hbodyImp hrest
        | some _ => exact .inr (.inr (hbodyImp hrest))
      | some tg =>
        simp only [Bool.or_eq_true, beq_iff_eq, Option.isNone_some, Bool.false_eq_true, or_false] at hguard
        subst hguard
        exact hrest.imp id (Or.imp id hbodyImp)
    | element r x j =>
      rw [hfa] at hm hat
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨hsites, hidxEq⟩, hinst⟩ := hm
      obtain ⟨sto, elemLs, bj, i, hsto, hls, hj, hbi, hltLen, hpres, hhole⟩ := hat
      have hw' : readPath h (ρ s) p = some (ρ x) := sitesMeet_read hM hl hsites
      have hjv : termValue ε ρ h (.value j) = some (i : Int) := by
        simp only [termValue_value, hj, intValue_num hbi]
      have hi' : termValue ε ρ h idx = some (i : Int) := (entailsTermEq_sound hlt ha hidxEq).symm.trans hjv
      split at hinst
      · rename_i inst hmap
        have hg := guardEntails_sound hlt hlg hld htags (fun as F hb ha => baseFollows_sound hM hl hb ha) _ as hinst ha
        have hval : ∀ C : LinearClause Term, body.mapVars (instBoundAt r j) = some C →
            C.toIndexFact.HoldsAt ε ρ h → body.HoldsAt (boundValue ε ρ h elemLs i) := by
          intro C hC hCh
          refine (LinearClause.holdsAt_mapVars hC fun v _ t ht => ?_).mp (LinearClause.toIndexFact_holds.mp hCh)
          cases v with
          | index => cases ht; exact hjv
          | elem =>
            cases ht; simp only [termValue_value, boundValue, elementInt]
            cases hli : elemLs[i]? with
            | none => simp at hli; omega
            | some o =>
              cases o with
              | none => rw [hhole hli]; rfl
              | some l => simp only [hpres l hli, Option.bind_some]
          | project kind q =>
            cases ht; simp only [boundValue]
            cases hli : elemLs[i]? with
            | none => simp at hli; omega
            | some o =>
              cases o with
              | none =>
                simp only [termValue, termAt, Bool.false_eq_true, ite_false, hhole hli]
                cases kind <;> cases q <;> rfl
              | some l => simp only [hpres l hli, Option.bind_some, termValue, termAt, Bool.false_eq_true, ite_false]
          | free t' => cases ht; rfl
          | offset _ | parallel _ _ _ _ => simp [instBoundAt] at ht
        refine ⟨ρ x, sto, elemLs, i, hw', hsto, hls, hi', hltLen, ?_⟩
        cases guard with
        | none => exact hval inst hmap hg
        | some tg =>
          obtain ⟨v, hv, hor⟩ := hg
          simp only [readGuard, Option.some.injEq] at hv
          subst hv
          rcases hor with htag | hB
          · cases hli : elemLs[i]? with
            | none => simp at hli; omega
            | some o =>
              cases o with
              | none =>
                have hru := hhole hli
                rw [hru] at htag
                exact .inr (.inl ⟨rfl, htag⟩)
              | some l =>
                exact .inl ⟨l, ρ r, rfl, hpres l hli, htag⟩
          · exact .inr (.inr (hval inst hmap hB))
      · cases hinst
    | every s' p' stop everyBody =>
      rw [hfa] at hm hat
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨⟨⟨⟨⟨hsites, hdi⟩, hdl⟩, hge0⟩, hltStop⟩, hltLenF⟩, hmem⟩ := hm
      obtain ⟨w, sto, elemLs, n, hw, hsto, hls, hn, hall⟩ := hat
      have hw' : readPath h (ρ s) p = some w := (sitesMeet_read hM hl hsites).trans hw
      obtain ⟨zi, hzi⟩ := Option.isSome_iff_exists.mp (bridgedDefined_sound hlt ha hdi)
      obtain ⟨zl, hzl⟩ := Option.isSome_iff_exists.mp (bridgedDefined_sound hlt ha hdl)
      have hzi0 : termValue ε ρ h idx = some zi := (hlt idx).symm.trans hzi
      have hzl0 : termValue ε ρ h (.now .length s' p') = some zl := (hlt (.now .length s' p')).symm.trans hzl
      have f0 := Linear.entailsWith_sound hge0 (bridgeFacts_holds hlt (linearRaw_holds ha))
        (bridgeFacts_holds hlt (rangesRaw_holds ha))
      have f1 := Linear.entailsWith_sound hltStop (bridgeFacts_holds hlt (linearRaw_holds ha))
        (bridgeFacts_holds hlt (rangesRaw_holds ha))
      have f2 := Linear.entailsWith_sound hltLenF (bridgeFacts_holds hlt (linearRaw_holds ha))
        (bridgeFacts_holds hlt (rangesRaw_holds ha))
      have hn' : termValue ε ρ h (lt stop) = some n := (hlt stop).trans hn
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, hzi, hn', hzl, Option.getD_some] at f0 f1 f2
      -- Extract `zl = elemLs.length` from `lengthOf h w = some zl`.
      simp only [termValue, termAt, Bool.false_eq_true, ite_false, hw, Option.bind_some, kindValue] at hzl0
      obtain ⟨s0, ls0, hs0, hls0, rfl, -⟩ := lengthOf_spine hzl0
      have hstEq : sto = s0 := Option.some.inj (hsto.symm.trans (elementsOf_spine hs0))
      subst hstEq
      rw [hls0] at hls
      simp only [Option.bind_some, spineEntries, Option.some.injEq] at hls
      subst hls
      obtain ⟨i, rfl⟩ : ∃ i : Nat, zi = (i : Int) := ⟨zi.toNat, by omega⟩
      obtain ⟨B', hB', hFeq⟩ := List.any_eq_true.mp hmem
      cases B' with
      | guarded _ _ _ => simp at hFeq
      | clause F' =>
        have hB : body.HoldsAt (boundValue ε ρ h ls0 i) :=
          (hliftBody ls0 i body).mp (bodyClauseEntails_sound hlt ha hFeq ((hliftBody ls0 i F').mpr (hall i (by omega) (.clause F') hB')))
        refine ⟨w, sto, ls0, i, hw', hsto, by rw [hls0]; rfl, hzi0, by omega, ?_⟩
        cases guard with
        | none => exact hB
        | some _ => exact .inr (.inr hB)
    | _ => rw [hfa] at hm; simp at hm
  | _ => simp [atIndexFollows] at hf

/-- Precomputed complementary guard pairs `(s, p, t, pos, neg)` in `as` where
both `t` (positive) and `t.complement` appear as unconditional guards at the
same `lg`-restated path, deduplicated by `(lg s p, t)`. Empty in one scan when
no negative-tag guard appears in `as`. -/
def compGuardPairs (lg : Nat → List String → Nat × List String) (as : List IndexAtom) :
    List (Nat × List String × GuardTag × List IndexAtom × List IndexAtom) :=
  let negKeys := as.filterMap fun a => match a.cond, a.fact with
    | none, .guarded s p t _ => if !t.isPositive then some (lg s p, t.complement) else none
    | _, _ => none
  if negKeys.isEmpty then [] else
  let rec go (seen : List ((Nat × List String) × GuardTag)) :
      List IndexAtom → List (Nat × List String × GuardTag × List IndexAtom × List IndexAtom)
    | [] => []
    | a :: rest => match a.cond, a.fact with
      | none, .guarded s p t _ =>
        let key := (lg s p, t)
        if t.isPositive && negKeys.contains key && !seen.contains key then
          let pos := sameGuardBodies lg as s p t
          let neg := sameGuardBodies lg as s p t.complement
          if !pos.isEmpty && !neg.isEmpty then
            (s, p, t, pos, neg) :: go (key :: seen) rest
          else go (key :: seen) rest
        else go seen rest
      | _, _ => go seen rest
  go [] as

theorem compGuardPairs_mem {lg : Nat → List String → Nat × List String} {as : List IndexAtom}
    {s : Nat} {p : List String} {t : GuardTag} {pos neg : List IndexAtom}
    (hm : (s, p, t, pos, neg) ∈ compGuardPairs lg as) :
    (∃ a ∈ as, a.cond = none ∧ ∃ B0, a.fact = .guarded s p t B0) ∧
    pos = sameGuardBodies lg as s p t ∧ neg = sameGuardBodies lg as s p t.complement := by
  unfold compGuardPairs at hm
  dsimp only at hm
  split at hm
  · cases hm
  · have hgo : ∀ (negKeys seen : List ((Nat × List String) × GuardTag)) (xs : List IndexAtom),
        (∀ x ∈ xs, x ∈ as) → (s, p, t, pos, neg) ∈ compGuardPairs.go lg as negKeys seen xs →
        (∃ a ∈ as, a.cond = none ∧ ∃ B0, a.fact = .guarded s p t B0) ∧
        pos = sameGuardBodies lg as s p t ∧ neg = sameGuardBodies lg as s p t.complement := by
      intro negKeys seen xs
      induction xs generalizing seen with
      | nil => intro _ h; cases h
      | cons a rest ih =>
        intro hsub h
        simp only [compGuardPairs.go] at h
        split at h
        · rename_i s' p' t' B0 hcond hfa
          split at h
          · split at h
            · rcases List.mem_cons.mp h with heq | hrest
              · simp only [Prod.mk.injEq] at heq
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
                exact ⟨⟨a, hsub a (List.mem_cons_self ..), hcond, B0, hfa⟩, rfl, rfl⟩
              · exact ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hrest
            · exact ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h
          · exact ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h
        · exact ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h
    exact hgo _ [] as (fun _ h => h) hm

/-- Precomputed read/guard bridges, released atoms, and deduplicated
complementary guard pairs shared across target atoms in `indicesCheckWith`. -/
structure GuardPrep where
  lt : Term → Term
  lg : Nat → List String → Nat × List String
  ld : Nat → List String → Nat × List String
  aug : List IndexAtom
  compPairs : Thunk (List (Nat × List String × GuardTag × List IndexAtom × List IndexAtom))
  known : Thunk (Linear.Known Term)
  unsat : Thunk Bool
  eithers : Thunk (List IndexAtom)

def guardPrep (ls : HeapLinks.Links) (tags : Nat → List String → GuardTag → Bool)
    (a : List IndexAtom) : GuardPrep :=
  let r := HeapLinks.rep (HeapLinks.classes ls)
  let reads := bridgeReads ls
  let greads := guardReads ls
  let lt := fun t => liftTerm r reads reads.length (lowerTermAll r reads reads.length t)
  let lg := liftGuard r greads greads.length
  let ld := lowerGuard greads r greads.length
  let past := if a.any (fun x => x.cond.isNone && match x.fact with | .either _ (.pastSafe _) => true | _ => false)
    then releasePast a else []
  let guarded := if a.any (fun x => match x.fact with | .guarded .. => true | _ => false)
    then (releaseGuarded tags ld a).filter (!a.contains ·) else []
  let aug := a ++ past ++ guarded
  let compPairs := Thunk.mk fun _ => compGuardPairs lg aug
  let known := Thunk.mk fun _ => Linear.Known.build (bridgeFacts lt (linearRaw aug)) (bridgeFacts lt (rangesRaw aug))
  let unsat := Thunk.mk fun _ => known.get.entails (.le [] (-1)) || pastClash aug
  let eithers := Thunk.mk fun _ => aug.filter fun x => x.cond.isNone && match x.fact with
    | .either _ (.pastSafe _) => false
    | .either _ _ => true
    | _ => false
  { lt, lg, ld, aug, compPairs, known, unsat, eithers }

/-- Complementary-guard elimination using the precomputed deduplicated pairs
`compGuardPairs lg as`: every value read at the guard's path fails either `t`
or `t.complement`, so if both body sets entail `F`, `F` holds. -/
def complementaryGuardElim
    (pairs : List (Nat × List String × GuardTag × List IndexAtom × List IndexAtom))
    (check : List IndexAtom → IndexFact → Bool) (as : List IndexAtom) (F : IndexFact) : Bool :=
  pairs.any fun (_, _, _, pos, neg) => check (as ++ pos) F && check (as ++ neg) F

theorem complementaryGuardElim_sound {lg : Nat → List String → Nat × List String}
    {check : List IndexAtom → IndexFact → Bool} {ρ : Env} {h : Heap}
    (hlg : ∀ s p, readGuard h (ρ (lg s p).1) (lg s p).2 = readGuard h (ρ s) p)
    (hcheck : ∀ as F, check as F = true → IndexHolds ε as ρ h → F.HoldsAt ε ρ h)
    {as : List IndexAtom} {F : IndexFact}
    (hf : complementaryGuardElim (compGuardPairs lg as) check as F = true) (ha : IndexHolds ε as ρ h) :
    F.HoldsAt ε ρ h := by
  simp only [complementaryGuardElim, List.any_eq_true, Bool.and_eq_true] at hf
  obtain ⟨⟨s, p, t, pos, neg⟩, hmem, hpos, hneg⟩ := hf
  obtain ⟨⟨a, haa, hcond, B0, hfa⟩, rfl, rfl⟩ := compGuardPairs_mem hmem
  have hat := ha a haa fun c hc => by rw [hcond] at hc; cases hc
  rw [hfa] at hat
  obtain ⟨v, hv, -⟩ := hat
  by_cases htv : t.holds v
  · have hnotc : ¬ t.complement.holds v := by
      cases t <;> simp_all [GuardTag.complement, GuardTag.holds]
    have hext : IndexHolds ε (as ++ sameGuardBodies lg as s p t.complement) ρ h := by
      intro b hb hbc
      rcases List.mem_append.mp hb with hb | hb
      · exact ha b hb hbc
      · obtain ⟨v', hv', hor⟩ := sameGuardBodies_mem hlg ha hb
        rw [hv] at hv'; cases hv'
        exact hor.resolve_left hnotc
    exact hcheck _ F hneg hext
  · have hext : IndexHolds ε (as ++ sameGuardBodies lg as s p t) ρ h := by
      intro b hb hbc
      rcases List.mem_append.mp hb with hb | hb
      · exact ha b hb hbc
      · obtain ⟨v', hv', hor⟩ := sameGuardBodies_mem hlg ha hb
        rw [hv] at hv'; cases hv'
        exact hor.resolve_left htv
    exact hcheck _ F hpos hext

def guardFollowsWith (gp : GuardPrep) (M : Nat → List Nat) (m : PointClaims.Mapping) (ls : HeapLinks.Links)
    (tags : Nat → List String → GuardTag → Bool) (a : List IndexAtom) (t : IndexAtom)
    (useExtra : Bool := true) : Bool :=
  t.cond.isNone && match t.fact with
  | .guarded .. | .either .. | .linear .. | .atIndex .. | .spineApart .. =>
    match t.fact.mapM (fun y => some (pickSlot M m a y)) with
    | some F =>
      let base := fun as F => baseFollows M ls as F || atIndexFollows M ls gp.lt gp.lg gp.ld tags as F
      let check := guardEntails gp.lt gp.lg gp.ld tags base
      let eithers :=
        let all := gp.eithers.get
        if all.isEmpty then [] else
        let fs := F.slots
        if fs.isEmpty then all else all.filter fun x => x.fact.slots.any fs.contains
      guardEntailsIn gp.lt gp.lg gp.ld tags base (some gp.known) gp.aug F ||
        (useExtra && eitherMono check gp.aug F) ||
        gp.unsat.get ||
        (!eithers.isEmpty && caseEntailsAux check 8 gp.aug eithers F) ||
        (useExtra && complementaryGuardElim gp.compPairs.get check gp.aug F)
    | none => false
  | _ => false

/-- Whether a guarded target atom, unconditional, follows: its fact renamed
into the source's slots (`pickSlot`), entailed by the source's atoms with its
terms and guard paths restated by the source's read links (`lowerTermAll`,
`liftTerm`, `liftGuard`), a fact of any other kind by the source's atoms
(`baseFollows`, `atIndexFollows`). -/
def guardFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (ls : HeapLinks.Links)
    (tags : Nat → List String → GuardTag → Bool) (a : List IndexAtom) (t : IndexAtom)
    (useExtra : Bool := true) : Bool :=
  guardFollowsWith (guardPrep ls tags a) M m ls tags a t useExtra

theorem guardPrep_aug_holds {ls : HeapLinks.Links} {tags : Nat → List String → GuardTag → Bool}
    {a : List IndexAtom} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    (ha : IndexHolds ε a ρ h) : IndexHolds ε (guardPrep ls tags a).aug ρ h := by
  intro b hb hc
  simp only [guardPrep] at hb
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · exact ha b hb hc
    · split at hb
      · exact releasePast_holds ha b hb hc
      · cases hb
  · split at hb
    · exact releaseGuarded_holds (lowerGuard_eq hl (HeapLinks.rep_eq (HeapLinks.classes_one hl)) _) htags ha b
        (List.mem_filter.mp hb).1 hc
    · cases hb

theorem guardFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {ls : HeapLinks.Links}
    {tags : Nat → List String → GuardTag → Bool} {a : List IndexAtom} {t : IndexAtom} {useExtra : Bool} {ρ h}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h)
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    (hf : guardFollows M m ls tags a t useExtra = true) (ha : IndexHolds ε a ρ h) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  simp only [guardFollows, guardFollowsWith, Bool.and_eq_true] at hf
  obtain ⟨-, hf⟩ := hf
  cases htf : t.fact with
  | guarded _ _ _ _ | either _ _ | linear _ | atIndex _ _ _ _ _ | spineApart _ _ _ _ =>
    rw [htf] at hf
    dsimp only at hf
    split at hf
    · rename_i F hF
      have hr := HeapLinks.rep_eq (HeapLinks.classes_one hl)
      have hlt : ∀ u, termValue ε ρ h ((guardPrep ls tags a).lt u) = termValue ε ρ h u :=
        fun u => (liftTerm_eq hl hr _ _).trans (lowerTermAll_eq hl hr _ _)
      have hlg : ∀ s p, readGuard h (ρ ((guardPrep ls tags a).lg s p).1) ((guardPrep ls tags a).lg s p).2 =
          readGuard h (ρ s) p := liftGuard_eq hl hr _
      have hld : ∀ s p, readGuard h (ρ ((guardPrep ls tags a).ld s p).1) ((guardPrep ls tags a).ld s p).2 =
          readGuard h (ρ s) p := lowerGuard_eq hl hr _
      have haug := guardPrep_aug_holds hl htags ha
      have hbase : ∀ as F, (baseFollows M ls as F || atIndexFollows M ls (guardPrep ls tags a).lt (guardPrep ls tags a).lg (guardPrep ls tags a).ld tags as F) = true →
          IndexHolds ε as ρ h → F.HoldsAt ε ρ h := fun as F hb ha' =>
        (Bool.or_eq_true_iff.mp hb).elim (fun h1 => baseFollows_sound hM hl h1 ha')
          (fun h2 => atIndexFollows_sound hM hl hlt hlg hld htags h2 ha')
      have hKgp : (guardPrep ls tags a).known.get.Holds (termValuation ε ρ h) :=
        Linear.Known.build_holds (bridgeFacts_holds hlt (linearRaw_holds haug)) (bridgeFacts_holds hlt (rangesRaw_holds haug))
      have hcheck := fun as F => guardEntails_sound hlt hlg hld htags hbase F as
      have hF' : F.HoldsAt ε ρ h := by
        rcases Bool.or_eq_true_iff.mp hf with hf | hcomp
        · rcases Bool.or_eq_true_iff.mp hf with hf | hcase
          · rcases Bool.or_eq_true_iff.mp hf with hf | huns
            · rcases Bool.or_eq_true_iff.mp hf with htop | hmono
              · exact guardEntailsIn_sound hlt hlg hld htags hbase F (some (guardPrep ls tags a).known) (guardPrep ls tags a).aug
                  (fun kt hkt => by cases hkt; exact hKgp) htop haug
              · exact eitherMono_sound hcheck F (guardPrep ls tags a).aug (Bool.and_eq_true_iff.mp hmono).2 haug
            · rcases Bool.or_eq_true_iff.mp huns with hle | hpc
              · have bad := Linear.Known.entails_sound hKgp hle
                simp [Linear.Fact.Holds, Linear.Form.eval] at bad
              · exact (pastClash_sound hpc haug).elim
          · exact caseEntailsAux_sound hcheck
              8 (guardPrep ls tags a).aug _ F (fun _ h => by
                split at h
                · cases h
                · split at h
                  · exact (List.mem_filter.mp h).1
                  · exact (List.mem_filter.mp (List.mem_filter.mp h).1).1) (Bool.and_eq_true_iff.mp hcase).2 haug
        · exact complementaryGuardElim_sound hlg hcheck (Bool.and_eq_true_iff.mp hcomp).2 haug
      exact (IndexFact.holdsAt_mapM hF fun s _ y hy => by cases hy; exact pickSlot_eq hM s).mp hF'
    · cases hf
  | _ => rw [htf] at hf; cases hf

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
          body'.all (fun F' => b.any fun F => bodyClauseFollows M m F F') &&
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
      exact bodyClauseFollows_sound hM hbf (hall i (by omega) F hF)
    · cases hm
  · cases hf

/-- Whether a target `same x y` atom follows directly from alias equality (`M`)
between the mapped slots `m x` and `m y`. -/
def sameFollows (M : Nat → List Nat) (m : PointClaims.Mapping) (t : IndexAtom) : Bool :=
  match t.fact, t.cond with
  | .same x y, none =>
    let x' := PointClaims.slot m x
    let y' := PointClaims.slot m y
    x' == y' || (M x').contains y'
  | _, _ => false

theorem sameFollows_sound {M : Nat → List Nat} {m : PointClaims.Mapping} {t : IndexAtom} {ρ : Env} {h : Heap}
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hf : sameFollows M m t = true) :
    t.fact.HoldsAt ε (PointClaims.mapEnv m ρ) h := by
  unfold sameFollows at hf
  split at hf
  · rename_i x y hfact _
    rw [hfact]
    simp only [IndexFact.HoldsAt, PointClaims.mapEnv, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hf ⊢
    rcases hf with h | h
    · rw [h]
    · exact (hM _ _ h).symm
  · cases hf

/-- Whether each target atom follows from a source atom or from the source's
linear facts, with the source's read links `ls` as the bridge (`bridgeOf`),
or, guarded, from the source's guarded atoms (`guardFollows`), `tags` stating
which guard paths read a tag's value, or from an atom its body follows from
(`guardBodyFollows`), or, a quantified fact, from one over a longer prefix
(`everyPrefix`), or a slot-equality fact from alias links (`sameFollows`). -/
def indicesCheckWith (tags : Nat → List String → GuardTag → Bool) (M : Nat → List Nat) (ls : HeapLinks.Links)
    (a b : List IndexAtom) (m : PointClaims.Mapping) : Bool :=
  let B := Thunk.mk fun _ => bridgeOf ls a b
  let K := Thunk.mk fun _ => knownOf a
  let G := Thunk.mk fun _ => guardPrep ls tags a
  b.all fun t => a.any (fun s => indexFollows M m s t) ||
    (match t.fact with | .linear .. | .every .. | .bound .. | .int .. => linearFollowsIn K.get M m a B.get t | _ => false) ||
    (t.cond.isNone && match t.fact with | .guarded .. | .either .. | .linear .. | .atIndex .. | .spineApart .. => guardFollowsWith G.get M m ls tags a t | _ => false) ||
    spineFollows M m ls a t || guardBodyFollows M m a t ||
    (match t.fact with | .every .. => everyPrefix K.get M m a t | _ => false) || sameFollows M m t

/-- Whether every value in a value set satisfies a guard tag (including the empty set). -/
def onlyTag (V : ValueSets.ValueSet) : GuardTag → Bool
  | .null => V == { nul := true } || V == {}
  | .undef => V == { undef := true } || V == {}
  | .tru => V == { tru := true } || V == {}
  | .fls => V == { fls := true } || V == {}
  | .notNull => !V.nul
  | .notUndef => !V.undef
  | .notTru => !V.tru
  | .notFls => !V.fls

theorem onlyTag_mem {V : ValueSets.ValueSet} {t : GuardTag} {v : Val} (ho : onlyTag V t = true)
    (hv : V.mem v = true) : t.holds v := by
  cases t with
  | null | undef | tru | fls =>
    simp only [onlyTag, Bool.or_eq_true, beq_iff_eq] at ho
    rcases ho with rfl | rfl <;>
      cases v <;> simp_all [ValueSets.ValueSet.mem, ValueSets.Obj.mem, ValueSets.Lit.mem, ValueSets.Lit.none, GuardTag.holds]
  | notNull | notUndef | notTru | notFls =>
    simp only [onlyTag, Bool.not_eq_true'] at ho
    cases v <;> simp_all [ValueSets.ValueSet.mem, GuardTag.holds]

/-- A guard read of one field through a read the object gave (`ReadGave`). -/
theorem readGuard_readGave {fs : List (PropKey × Nat)} {cd : CallCode} {o : Nat} {f : String} {h : Heap} {v : Val}
    (hr : HeapFacts.ReadGave fs (.str f) h v) (p : List String) :
    readGuard h (.objAt fs cd o) (f :: p) = readGuard h v p := by
  unfold HeapFacts.ReadGave at hr
  cases hlk : fs.lookup (.str f) with
  | some l => rw [hlk] at hr; simp only [readGuard, hlk, hr]
  | none => rw [hlk] at hr; simp only [readGuard, hlk, hr.1, hr.2, ite_true]

/-- Which guard paths a knowledge states satisfy a guard tag: a slot of the
class of a slot whose value fact satisfies the tag; one field of a slot of
that class whose cell fact does (`guard-tag`). -/
def guardTags (k : Knowledge) : Nat → List String → GuardTag → Bool :=
  let r := HeapLinks.rep (HeapLinks.classes k.links)
  fun s p t => match p with
    | [] =>
      let rs := r s
      k.values.any fun f => onlyTag f.contents t && r f.slot == rs
    | [g] =>
      let rs := r s
      k.cells.any fun f => f.field == .str g && onlyTag f.contents t && r f.slot == rs
    | _ => false

theorem guardTags_sound {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    ∀ s p t, guardTags k s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v := by
  intro s p t ht
  have hr : ∀ x, ρ (HeapLinks.rep (HeapLinks.classes k.links) x) = ρ x :=
    HeapLinks.rep_eq (HeapLinks.classes_one hk.2.2.1)
  match p, ht with
  | [], ht =>
    simp only [guardTags, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨f, hf, ho, heq⟩ := ht
    have hv := hk.2.1 f hf
    have hfs : ρ f.slot = ρ s := by rw [← hr f.slot, heq, hr]
    rw [hfs] at hv
    exact ⟨ρ s, rfl, onlyTag_mem ho hv⟩
  | [g], ht =>
    simp only [guardTags, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨f, hf, ⟨hg, ho⟩, heq⟩ := ht
    obtain ⟨flds, cd, oid, v, he, hrg, hv⟩ := hk.1 f hf
    have hfs : ρ f.slot = ρ s := by rw [← hr f.slot, heq, hr]
    rw [hfs] at he
    rw [hg] at hrg
    exact ⟨v, by rw [he, readGuard_readGave hrg []]; rfl, onlyTag_mem ho hv⟩
  | _ :: _ :: _, ht => simp [guardTags] at ht

/-- Discharges guarded index atoms in `k` whose guard's complement holds under
`guardTags k`. -/
def dischargeGuards (k : Knowledge) : Knowledge :=
  if !k.indices.any (fun a => match a.fact with | .guarded .. => true | _ => false) then k
  else
    let r := HeapLinks.rep (HeapLinks.classes k.links)
    let greads := guardReads k.links
    let ld := lowerGuard greads r greads.length
    let released := releaseGuarded (guardTags k) ld k.indices
    { k with indices := k.indices ++ released.filter (!k.indices.contains ·) }

theorem dischargeGuards_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (dischargeGuards k) ε ρ h := by
  unfold dischargeGuards
  split
  · exact hk
  · refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact hk.2.2.2.2.2 a ha hc
    · exact releaseGuarded_holds (lowerGuard_eq hk.2.2.1 (HeapLinks.rep_eq (HeapLinks.classes_one hk.2.2.1)) _)
        (guardTags_sound hk) hk.2.2.2.2.2 a (List.mem_filter.mp ha).1 hc

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
    (htags : ∀ s p t, tags s p t = true → ∃ v, readGuard h (ρ s) p = some v ∧ t.holds v)
    (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x) (hl : HeapLinks.Holds ls ρ h) (hc : indicesCheckWith tags M ls a b m = true)
    (ha : IndexHolds ε a ρ h) :
    IndexHolds ε b (PointClaims.mapEnv m ρ) h := by
  intro t ht hcond
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hc t ht) with hc' | hsm
  case inr => exact sameFollows_sound hM hsm
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hev
  case inr =>
    cases htf : t.fact <;> rw [htf] at hev <;> simp at hev
    rw [← htf]; exact everyPrefix_sound hM (knownOf_holds ha) ha hcond hev
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hgb
  case inr => exact guardBodyFollows_sound hM hgb ha
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hst
  case inr => exact spineFollows_sound hM hl hst ha
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hg
  case inr =>
    obtain ⟨-, hg⟩ := Bool.and_eq_true_iff.mp hg
    cases htf : t.fact <;> rw [htf] at hg <;> simp at hg
    all_goals rw [← htf]; exact guardFollows_sound hM hl htags hg ha
  rcases Bool.or_eq_true_iff.mp hc' with hc' | hlin
  case inr =>
    cases htf : t.fact <;> rw [htf] at hlin <;> simp at hlin
    all_goals rw [← htf]; exact linearFollowsIn_sound (knownOf_holds ha) hM (fun c hc => bridgeOf_eq hl hc) hlin ha hcond
  obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp hc'
  simp only [indexFollows, Bool.and_eq_true] at hf
  obtain ⟨hfact, hcd⟩ := hf
  exact factFollows_sound hM hfact (ha s hs (condFollows_cond hM hcd hcond))

/-- Filter candidate atoms to those entailed by `k`, hoisting per-knowledge
precomputations (alias classes, read bridges, guarded linear context) across
all candidates. -/
def indicesFilter (k : Knowledge) (cs : List IndexAtom) (useCases : Bool := true) : List IndexAtom :=
  if cs.isEmpty then [] else
  let a := k.indices
  let aSet : Std.HashSet IndexAtom := Std.HashSet.ofList a
  let aGuarded := Thunk.mk fun _ => a.filter fun s => match s.fact with | .guarded .. => true | _ => false
  let aEither := Thunk.mk fun _ => a.filter fun s => match s.fact with | .either .. => true | _ => false
  let ls := k.links
  let M := HeapLinks.aliases ls
  let tags := guardTags k
  let K := Thunk.mk fun _ => knownOf a
  let B := Thunk.mk fun _ => bridgeOf ls a cs
  let r := HeapLinks.rep (HeapLinks.classes ls)
  let reads := bridgeReads ls
  let greads := guardReads ls
  let lt := liftTerm r reads reads.length
  let lg := liftGuard r greads greads.length
  let ld := lowerGuard greads r greads.length
  let a' := a ++ releasePast a
  let K' := Thunk.mk fun _ => Linear.Known.build (bridgeFacts lt (linearRaw a')) (bridgeFacts lt (rangesRaw a'))
  let unsat := Thunk.mk fun _ => K'.get.entails (.le [] (-1)) || pastClash a'
  let eithersAll := Thunk.mk fun _ => a'.filter fun x => x.cond.isNone && match x.fact with
    | .either _ (.pastSafe _) => false
    | .either _ _ => true
    | _ => false
  let check := fun (as : List IndexAtom) (F : IndexFact) =>
    guardEntailsIn lt lg ld tags (baseFollows M ls) none as F
  let checkTop := fun (F : IndexFact) =>
    guardEntailsIn lt lg ld tags (baseFollows M ls) (some K') a' F
  let solveF := fun (F : IndexFact) =>
    checkTop F || unsat.get ||
      (useCases &&
      let all := eithersAll.get
      if all.isEmpty then false else
      let fs := F.slots
      let es := if fs.isEmpty then all else all.filter fun x => x.fact.slots.any fs.contains
      !es.isEmpty && caseEntailsAux check 8 a' es F)
  let directHit := fun (t : IndexAtom) =>
    aSet.contains t ||
    (t.cond.isNone && match t.fact with
     | .guarded s p tag B => tags (pickSlot M none a s) p tag || (p.isEmpty && aSet.contains { fact := B })
     | _ => false)
  let indexHit := fun (t : IndexAtom) =>
    match t.fact with
    | .guarded .. => aGuarded.get.any (fun s => indexFollows M none s t)
    | .either .. => aEither.get.any (fun s => indexFollows M none s t)
    | _ => a.any (fun s => indexFollows M none s t)
  let gFollows := fun (t : IndexAtom) =>
    t.cond.isNone && match t.fact with
    | .guarded .. | .either .. | .linear .. =>
      match t.fact.mapM (fun y => some (pickSlot M none a y)) with
      | some F => solveF F
      | none => false
    | _ => false
  cs.filter fun t => directHit t || indexHit t || guardBodyFollows M none a t ||
    (match t.fact with | .linear .. | .every .. | .bound .. | .int .. => linearFollowsIn K.get M none a B.get t | _ => false) ||
    gFollows t ||
    spineFollows M none ls a t ||
    (match t.fact with | .every .. => everyPrefix K.get M none a t | _ => false)

theorem indicesFilter_sub {k : Knowledge} {cs : List IndexAtom} {useCases : Bool} {t : IndexAtom}
    (ht : t ∈ indicesFilter k cs useCases) : t ∈ cs := by
  unfold indicesFilter at ht
  split at ht
  · cases ht
  · exact (List.mem_filter.mp ht).1

theorem indicesFilter_holds {k : Knowledge} {cs : List IndexAtom} {useCases : Bool} {ρ : Env} {h : Heap}
    (hk : Holds k ε ρ h) : IndexHolds ε (indicesFilter k cs useCases) ρ h := by
  unfold indicesFilter
  split
  · intro _ h; cases h
  · intro t ht hcond
    have hpred := (List.mem_filter.mp ht).2
    have ha := hk.2.2.2.2.2
    have hl := hk.2.2.1
    have hM : ∀ x, ∀ y ∈ HeapLinks.aliases k.links x, ρ y = ρ x := fun _ _ hy => HeapLinks.aliases_eq hl hy
    have htags := guardTags_sound hk
    have hmap : PointClaims.mapEnv none ρ = ρ := rfl
    rcases Bool.or_eq_true_iff.mp hpred with hpred | hev
    case inr =>
      cases htf : t.fact <;> rw [htf] at hev <;> simp at hev
      rw [← htf]; exact hmap ▸ everyPrefix_sound hM (knownOf_holds ha) ha hcond hev
    rcases Bool.or_eq_true_iff.mp hpred with hpred | hst
    case inr => exact hmap ▸ spineFollows_sound hM hl hst ha
    rcases Bool.or_eq_true_iff.mp hpred with hpred | hgf
    case inr =>
      have hr := HeapLinks.rep_eq (HeapLinks.classes_one hl)
      have hlt := liftTerm_eq (ε := ε) hl hr (bridgeReads k.links).length
      have hlg := liftGuard_eq hl hr (guardReads k.links).length
      have hld := lowerGuard_eq hl hr (guardReads k.links).length
      have ha' : IndexHolds ε (k.indices ++ releasePast k.indices) ρ h := fun b hb hc =>
        (List.mem_append.mp hb).elim (fun hb => ha b hb hc) (fun hb => releasePast_holds ha b hb hc)
      have hK' : (Linear.Known.build (bridgeFacts (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length) (linearRaw (k.indices ++ releasePast k.indices)))
          (bridgeFacts (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length) (rangesRaw (k.indices ++ releasePast k.indices)))).Holds (termValuation ε ρ h) :=
        Linear.Known.build_holds (bridgeFacts_holds hlt (linearRaw_holds ha')) (bridgeFacts_holds hlt (rangesRaw_holds ha'))
      have solveF_sound : ∀ (F : IndexFact),
          (guardEntailsIn (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length)
            (liftGuard (HeapLinks.rep (HeapLinks.classes k.links)) (guardReads k.links) (guardReads k.links).length)
            (lowerGuard (guardReads k.links) (HeapLinks.rep (HeapLinks.classes k.links)) (guardReads k.links).length)
            (guardTags k) (baseFollows (HeapLinks.aliases k.links) k.links)
            (some (Thunk.mk fun _ => Linear.Known.build (bridgeFacts (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length) (linearRaw (k.indices ++ releasePast k.indices)))
              (bridgeFacts (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length) (rangesRaw (k.indices ++ releasePast k.indices)))))
            (k.indices ++ releasePast k.indices) F ||
          (Thunk.mk fun _ => (Thunk.mk fun _ => Linear.Known.build (bridgeFacts (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length) (linearRaw (k.indices ++ releasePast k.indices)))
              (bridgeFacts (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length) (rangesRaw (k.indices ++ releasePast k.indices)))).get.entails (.le [] (-1)) || pastClash (k.indices ++ releasePast k.indices)).get ||
          (useCases &&
            let all := (Thunk.mk fun _ => (k.indices ++ releasePast k.indices).filter fun x => x.cond.isNone && match x.fact with
              | .either _ (.pastSafe _) => false
              | .either _ _ => true
              | _ => false).get
            if all.isEmpty then false else
            let fs := F.slots
            let es := if fs.isEmpty then all else all.filter fun x => x.fact.slots.any fs.contains
            !es.isEmpty && caseEntailsAux (fun as G => guardEntailsIn (liftTerm (HeapLinks.rep (HeapLinks.classes k.links)) (bridgeReads k.links) (bridgeReads k.links).length)
              (liftGuard (HeapLinks.rep (HeapLinks.classes k.links)) (guardReads k.links) (guardReads k.links).length)
              (lowerGuard (guardReads k.links) (HeapLinks.rep (HeapLinks.classes k.links)) (guardReads k.links).length)
              (guardTags k) (baseFollows (HeapLinks.aliases k.links) k.links) none as G)
              8 (k.indices ++ releasePast k.indices) es F)) = true →
          F.HoldsAt ε ρ h := by
        intro F hok
        rcases Bool.or_eq_true_iff.mp hok with hok | haux
        · rcases Bool.or_eq_true_iff.mp hok with htop | huns
          · exact guardEntailsIn_sound hlt hlg hld htags (fun _ _ hb ha0 => baseFollows_sound hM hl hb ha0) F _ _
              (fun kt hkt => by cases hkt; exact hK') htop ha'
          · rcases Bool.or_eq_true_iff.mp huns with hle | hpc
            · have bad := Linear.Known.entails_sound hK' hle
              simp [Linear.Fact.Holds, Linear.Form.eval] at bad
            · exact (pastClash_sound hpc ha').elim
        · have haux := (Bool.and_eq_true_iff.mp haux).2
          dsimp only at haux
          split at haux
          · cases haux
          · exact caseEntailsAux_sound
              (fun as G hG ha0 => guardEntailsIn_sound hlt hlg hld htags (fun _ _ hb ha1 => baseFollows_sound hM hl hb ha1) G none as (fun _ h => by cases h) hG ha0)
              8 _ _ F (fun _ h => by
                split at h
                · exact (List.mem_filter.mp h).1
                · exact (List.mem_filter.mp (List.mem_filter.mp h).1).1) (Bool.and_eq_true_iff.mp haux).2 ha'
      simp only [Bool.and_eq_true] at hgf
      obtain ⟨-, hgf⟩ := hgf
      cases htf : t.fact with
      | guarded _ _ _ _ | either _ _ | linear _ =>
        rw [htf] at hgf; dsimp only at hgf
        split at hgf
        · rename_i F hF
          exact (IndexFact.holdsAt_mapM hF fun s _ y hy => by cases hy; exact pickSlot_eq (m := none) hM s).mp (solveF_sound F hgf)
        · cases hgf
      | _ => rw [htf] at hgf; cases hgf
    rcases Bool.or_eq_true_iff.mp hpred with hpred | hlin
    case inr =>
      cases htf : t.fact <;> rw [htf] at hlin <;> simp at hlin
      all_goals rw [← htf]; exact hmap ▸ linearFollowsIn_sound (knownOf_holds ha) hM (fun _ hc => bridgeOf_eq hl hc) hlin ha hcond
    rcases Bool.or_eq_true_iff.mp hpred with hpred | hgb
    case inr => exact hmap ▸ guardBodyFollows_sound hM hgb ha
    rcases Bool.or_eq_true_iff.mp hpred with hdh | hih
    case inl =>
      rcases Bool.or_eq_true_iff.mp hdh with hmem | hth
      · exact ha t (List.contains_iff_mem.mp ((Std.HashSet.mem_ofList).mp (Std.HashSet.contains_iff_mem.mp hmem))) hcond
      · simp only [Bool.and_eq_true] at hth
        obtain ⟨-, hth⟩ := hth
        cases htf : t.fact with
        | guarded s p tag B =>
          rw [htf] at hth; dsimp only at hth
          rcases Bool.or_eq_true_iff.mp hth with htg | hb
          · obtain ⟨v, hrg, htv⟩ := htags _ _ _ htg
            rw [pickSlot_eq (m := none) hM s] at hrg
            exact ⟨v, hrg, Or.inl htv⟩
          · obtain ⟨hp, hb⟩ := Bool.and_eq_true_iff.mp hb
            rw [List.isEmpty_iff.mp hp]
            have hB := ha { fact := B } (List.contains_iff_mem.mp ((Std.HashSet.mem_ofList).mp (Std.HashSet.contains_iff_mem.mp hb))) (fun _ h => by cases h)
            exact ⟨ρ s, rfl, Or.inr hB⟩
        | _ => rw [htf] at hth; cases hth
    have hmemA : ∃ s ∈ k.indices, indexFollows (HeapLinks.aliases k.links) none s t = true := by
      dsimp only at hih
      cases htf : t.fact with
      | guarded _ _ _ _ | either _ _ =>
        rw [htf] at hih; dsimp only at hih
        obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp hih
        exact ⟨s, (List.mem_filter.mp hs).1, hf⟩
      | _ =>
        rw [htf] at hih; dsimp only at hih
        obtain ⟨s, hs, hf⟩ := List.any_eq_true.mp hih
        exact ⟨s, hs, hf⟩
    obtain ⟨s, hs, hf⟩ := hmemA
    simp only [indexFollows, Bool.and_eq_true] at hf
    obtain ⟨hfact, hcd⟩ := hf
    exact hmap ▸ factFollows_sound hM hfact (ha s hs (condFollows_cond hM hcd hcond))

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
  | .index _ | .int _ | .pastSafe _ | .same _ _ => true
  | .linear F => F.vars.all Term.envOnly
  | .length _ _ | .bound _ _ _ | .element _ _ _ | .fieldRead _ _ _ | .every _ _ _ _ | .atIndex _ _ _ _ _ | .apart _ _ => false
  | .either A B => A.envOnly && B.envOnly
  | .guarded _ p _ B => p.isEmpty && B.envOnly
  | .spineApart _ p _ q => p.isEmpty && q.isEmpty

/-- The atoms whose facts read the environment alone, of the empty support
(`Footprints.IndexFact.support?_envOnly`). -/
def envIndices (as : List IndexAtom) : List IndexAtom := as.filter (·.fact.envOnly)

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

/-- The atoms a change keeps, a typed array's length read through a field
among them (`IndexFact.keptWith`). -/
def keptIndicesWith (c : Changes) (first : Nat → String → Bool) (as : List IndexAtom) : List IndexAtom :=
  as.filter (fun a => a.fact.keptWith c first || a.fact.everyKept c first)

theorem keptIndicesWith_holds {c : Changes} {first : Nat → String → Bool} {as : List IndexAtom} {ρ h h'}
    (he : IndexHolds ε as ρ h) (hc : c.Holds h h') (hf : FirstKept first ρ h h') :
    IndexHolds ε (keptIndicesWith c first as) ρ h' := by
  intro a ha hcd
  obtain ⟨ha, hk⟩ := List.mem_filter.mp ha
  exact (Bool.or_eq_true_iff.mp hk).elim
    (fun hk => IndexFact.holdsAt_keptWith hc hf hk (he a ha hcd))
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
  -- Each derived fact is tested against the facts it was derived from
  -- through a hash set of them.
  let keep := fun (known : Std.HashSet (Linear.Fact Term)) (F : Linear.Fact Term) =>
    !known.contains F && F.vars.all (fun t => !t.slots.any drop.contains && termDefined as t)
  let groups := (as.filterMap fun a => match a.cond, a.fact with
    | some c, .linear _ => if drop.contains c then none else some (c, a.negated)
    | _, _ => none).eraseDups
  as ++ ((Linear.eliminateAll (Linear.strengthen (linearFacts as)) used).filter
      (keep (Std.HashSet.ofList (linearFacts as)))).map (fun F => ⟨.linear F, none, false⟩) ++
    groups.flatMap fun (c, neg) =>
      let known := linearFacts as ++ condFacts as c neg
      ((Linear.eliminateAll (Linear.strengthen known) used).filter (keep (Std.HashSet.ofList known))).map
        fun F => ⟨.linear F, some c, neg⟩

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
    have hlen : termValue ε ρ h (.length x) = some (ls.length : Int) := lengthOf_of_spine hs hl hm
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
  | index _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _ | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => simp [atomLinear] at hF

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
        exact plainReads_path hl hm p
      · cases ht
    · cases ht; rfl

/-- Abstract a term relative to an element slot `r` (with its known length
slots `lenSlots`), lifting all other dropped slots through `breads`. -/
def abstractAtElem (r : Nat) (lenSlots : List Nat) (dropped : Nat → Bool)
    (breads : List (Nat × String × Nat)) (t : Term) : Option Bound :=
  if !t.atEntry && t.slot == r then
    match t.kind, t.path with
    | .value, [] => some .elem
    | k, p => some (.project k p)
  else if !t.atEntry && t.kind == .value && t.path.isEmpty && lenSlots.contains t.slot then
    some (.project .length [])
  else
    (liftDropped dropped breads breads.length t).map .free

theorem abstractAtElem_eq {ls : HeapLinks.Links} {dropped : Nat → Bool}
    {breads : List (Nat × String × Nat)} {r : Nat} {lenSlots : List Nat}
    {elemLs : List (Option Nat)} {i : Nat} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (hbr : ∀ g ∈ breads, g ∈ bridgeReads ls)
    (hlt : i < elemLs.length)
    (hpres : ∀ l, elemLs[i]? = some (some l) → h[l]? = some (ρ r))
    (hhole : elemLs[i]? = some none → ρ r = .undef)
    (hlen : ∀ n ∈ lenSlots, termValue ε ρ h (.value n) = termValue ε ρ h (.length r))
    {t : Term} {b : Bound} (hab : abstractAtElem r lenSlots dropped breads t = some b) :
    boundValue ε ρ h elemLs i b = termValue ε ρ h t := by
  have hproj : ∀ k p, boundValue ε ρ h elemLs i (.project k p) = termValue ε ρ h (.now k r p) := by
    intro k p
    simp only [boundValue]
    cases hli : elemLs[i]? with
    | none => simp at hli; omega
    | some o =>
      cases o with
      | none =>
        simp only [termValue, termAt, Bool.false_eq_true, ite_false, hhole hli]
        cases k <;> cases p <;> rfl
      | some l =>
        simp only [hpres l hli, Option.bind_some, termValue, termAt, Bool.false_eq_true, ite_false]
  unfold abstractAtElem at hab
  split at hab
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcond
    obtain ⟨hne, hsr⟩ := hcond
    obtain ⟨k, s, p, ae⟩ := t
    simp only at hne hsr; subst hne; subst hsr
    cases k with
    | value =>
      cases p with
      | nil =>
        simp only [Option.some.injEq] at hab; subst hab
        simp only [boundValue, elementInt, termValue, termAt, Bool.false_eq_true, ite_false, readPath, Option.bind_some,
          kindValue]
        cases hli : elemLs[i]? with
        | none => simp at hli; omega
        | some o =>
          cases o with
          | none => rw [hhole hli]; rfl
          | some l => simp only [hpres l hli, Option.bind_some]
      | cons f q =>
        simp only [Option.some.injEq] at hab; subst hab
        exact hproj .value (f :: q)
    | length | view | strLength =>
      simp only [Option.some.injEq] at hab; subst hab
      exact hproj _ p
  · split at hab
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hne, hk⟩, hp⟩, hmem⟩ := hcond
      cases hab
      obtain ⟨k, s, p, ae⟩ := t
      simp only at hne hk hp hmem; subst hne; subst hk; subst hp
      rw [hproj .length []]
      exact (hlen s hmem).symm
    · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hab
      exact liftDropped_eq hl hbr _ t t' ht'

/-- Indexed-element facts restated across dropped slots: existing `atIndex`
atoms naming a dropped slot lifted through reads, and linear (or singly guarded
linear) atoms mentioning a dropped element slot `r` (`element r x j`) restated
as `atIndex` over `x`'s lifted path and `j`'s lifted index. -/
def restateAtIndex (ls : HeapLinks.Links) (dropped : Nat → Bool) (as : List IndexAtom) : List IndexAtom :=
  let preads := (plainReads ls).filter fun g => dropped g.2.2
  let breads := (bridgeReads ls).filter fun g => dropped g.2.2
  let lifted : List IndexAtom :=
    if preads.isEmpty && breads.isEmpty then [] else
    as.filterMap fun a => if a.cond.isNone then match a.fact with
      | .atIndex s p idx g body =>
        if dropped s || idx.slots.any dropped || body.vars.any (fun b => b.slots.any dropped) then do
          let (s', p') ← liftPath dropped preads preads.length (s, p)
          let idx' ← liftDropped dropped breads breads.length idx
          let body' ← body.mapVars fun
            | .free t => (liftDropped dropped breads breads.length t).map .free
            | b => some b
          pure { fact := .atIndex s' p' idx' g body' }
        else none
      | _ => none
      else none
  let elems := as.filterMap fun a => if a.cond.isNone then match a.fact with
    | .element r x j => if dropped r then some (r, x, j) else none
    | _ => none
    else none
  let introduced : List IndexAtom :=
    if elems.isEmpty then [] else
    elems.flatMap fun (r, x, j) =>
      match liftPath dropped preads preads.length (x, []), liftDropped dropped breads breads.length (.value j) with
      | some (x', p'), some idx' =>
        let lenSlots := as.filterMap fun a => if a.cond.isNone then match a.fact with
          | .length r' n => if r' == r then some n else none
          | _ => none
          else none
        let mentionsR (t : Term) : Bool :=
          (!t.atEntry && t.slot == r) ||
            (!t.atEntry && t.kind == .value && t.path.isEmpty && lenSlots.contains t.slot)
        as.filterMap fun a => if a.cond.isNone then match a.fact with
          | .linear F =>
            if F.vars.any mentionsR then
              (F.mapVars (abstractAtElem r lenSlots dropped breads)).map fun F' =>
                { fact := .atIndex x' p' idx' none (.atom F') }
            else none
          | .guarded s [] g (.linear F) =>
            if s == r && F.vars.any mentionsR then
              (F.mapVars (abstractAtElem r lenSlots dropped breads)).map fun F' =>
                { fact := .atIndex x' p' idx' (some g) (.atom F') }
            else none
          | _ => none
          else none
      | _, _ => []
  lifted ++ introduced

theorem restateAtIndex_holds {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) : IndexHolds ε (restateAtIndex ls dropped as) ρ h := by
  intro a ha _
  simp only [restateAtIndex, List.mem_append] at ha
  have hpr : ∀ g ∈ (plainReads ls).filter (fun g => dropped g.2.2), g ∈ plainReads ls :=
    fun g hg => (List.mem_filter.mp hg).1
  have hbr : ∀ g ∈ (bridgeReads ls).filter (fun g => dropped g.2.2), g ∈ bridgeReads ls :=
    fun g hg => (List.mem_filter.mp hg).1
  rcases ha with ha | ha
  · split at ha
    · cases ha
    · obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
      split at hab
      · rename_i hcn
        have hbh := he b hb fun c hc => by rw [Option.isNone_iff_eq_none.mp hcn] at hc; cases hc
        split at hab
        · rename_i s p idx g body hf
          split at hab
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hab
            obtain ⟨⟨s', p'⟩, hsp, idx', hidx, body', hbody, rfl⟩ := hab
            rw [hf] at hbh
            obtain ⟨w, sto, elemLs, i, hw, hsto, hls, hi, hlt, hrest⟩ := hbh
            have hB : body.HoldsAt (boundValue ε ρ h elemLs i) → body'.HoldsAt (boundValue ε ρ h elemLs i) := fun h0 => by
              refine (LinearClause.holdsAt_mapVars hbody fun x _ y hy => ?_).mpr h0
              cases x with
              | free t =>
                obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hy
                exact liftDropped_eq hl hbr _ t t' ht'
              | index | elem | offset _ | project _ _ | parallel _ _ _ _ => cases hy; rfl
            refine ⟨w, sto, elemLs, i, ?_, hsto, hls, ?_, hlt, ?_⟩
            · rw [liftPath_eq hl hpr _ _ _ _ _ hsp]; exact hw
            · rw [liftDropped_eq hl hbr _ _ _ hidx]; exact hi
            · cases g with
              | none => exact hB hrest
              | some _ => exact hrest.imp id (Or.imp id hB)
          · cases hab
        · cases hab
      · cases hab
  · split at ha
    · cases ha
    · obtain ⟨⟨r0, x0, j0⟩, hmem, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨be, hbe, hbem⟩ := List.mem_filterMap.mp hmem
      split at hbem
      · rename_i hcen
        split at hbem
        · rename_i r x j hfe
          split at hbem
          · simp only [Option.some.injEq, Prod.mk.injEq] at hbem
            obtain ⟨rfl, rfl, rfl⟩ := hbem
            have hel := he be hbe fun c hc => by rw [Option.isNone_iff_eq_none.mp hcen] at hc; cases hc
            rw [hfe] at hel
            obtain ⟨sto, elemLs, bits, i, hsto, hls, hj, hbi, hlt, hpres, hhole⟩ := hel
            have hlen : ∀ n ∈ as.filterMap (fun a => if a.cond.isNone then match a.fact with
                | .length r' n => if r' == r then some n else none
                | _ => none
                else none), termValue ε ρ h (.value n) = termValue ε ρ h (.length r) := by
              intro n hn
              obtain ⟨bl, hbl, hblm⟩ := List.mem_filterMap.mp hn
              split at hblm
              · rename_i hcl
                split at hblm
                · rename_i r' n' hfl
                  split at hblm
                  · rename_i hrr
                    simp only [Option.some.injEq] at hblm; subst hblm
                    rw [beq_iff_eq] at hrr; subst hrr
                    have hll := he bl hbl fun c hc => by rw [Option.isNone_iff_eq_none.mp hcl] at hc; cases hc
                    rw [hfl] at hll
                    obtain ⟨s0, ls0, hs0, hls0, hnv, hm0⟩ := hll
                    have hrl : termValue ε ρ h (.length r') = some (ls0.length : Int) := lengthOf_of_spine hs0 hls0 hm0
                    rw [hrl]
                    simp only [termValue_value, hnv, intValue_length hm0]
                  · cases hblm
                · cases hblm
              · cases hblm
            split at ha
            · rename_i x' p' idx' hxp hidx
              obtain ⟨ba, hba, hab⟩ := List.mem_filterMap.mp ha
              split at hab
              · rename_i hca
                have hbah := he ba hba fun c hc => by rw [Option.isNone_iff_eq_none.mp hca] at hc; cases hc
                have hji : termValue ε ρ h idx' = some (i : Int) := by
                  rw [liftDropped_eq hl hbr _ _ _ hidx, termValue_value, hj]; exact intValue_num hbi
                have hread : readPath h (ρ x') p' = some (ρ x) := by
                  rw [liftPath_eq hl hpr _ _ _ _ _ hxp]; rfl
                split at hab
                · rename_i F hfa
                  split at hab
                  · obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
                    rw [hfa] at hbah
                    refine ⟨ρ x, sto, elemLs, i, hread, hsto, hls, hji, hlt, ?_⟩
                    refine ⟨fun y hy => ?_, (Linear.Fact.holds_mapVars hF' fun t _ b hb => ?_).mpr hbah.2⟩
                    · obtain ⟨t, ht, htb⟩ := Linear.Fact.mapVars_vars hF' y hy
                      rw [abstractAtElem_eq hl hbr hlt hpres hhole hlen htb]
                      exact hbah.1 t ht
                    · simp only [abstractAtElem_eq hl hbr hlt hpres hhole hlen hb, termValuation]
                  · cases hab
                · rename_i s g F hfa
                  split at hab
                  · rename_i hcond
                    obtain ⟨F', hF', rfl⟩ := Option.map_eq_some_iff.mp hab
                    have hsr : s = r := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).1
                    subst hsr
                    rw [hfa] at hbah
                    obtain ⟨v, hv, hor⟩ := hbah
                    simp only [readGuard, Option.some.injEq] at hv; subst hv
                    refine ⟨ρ x, sto, elemLs, i, hread, hsto, hls, hji, hlt, ?_⟩
                    rcases hor with htag | hlin
                    · cases hli : elemLs[i]? with
                      | none => simp at hli; omega
                      | some o =>
                        cases o with
                        | none =>
                          have hru := hhole hli
                          rw [hru] at htag
                          exact .inr (.inl ⟨rfl, htag⟩)
                        | some l =>
                          exact .inl ⟨l, ρ s, rfl, hpres l hli, htag⟩
                    · refine .inr (.inr ⟨fun y hy => ?_, (Linear.Fact.holds_mapVars hF' fun t _ b hb => ?_).mpr hlin.2⟩)
                      · obtain ⟨t, ht, htb⟩ := Linear.Fact.mapVars_vars hF' y hy
                        rw [abstractAtElem_eq hl hbr hlt hpres hhole hlen htb]
                        exact hlin.1 t ht
                      · simp only [abstractAtElem_eq hl hbr hlt hpres hhole hlen hb, termValuation]
                  · cases hab
                · cases hab
              · cases hab
            · cases ha
          · cases hbem
        · cases hbem
      · cases hbem

/-- The spine separations and indexed-element facts of unconditional atoms
naming a dropped slot, restated where plain reads give the slot's value as
fields read in turn from a kept slot (`liftPath`): a region fact's slots hold
different spines (`regionsApart_spines`), and an element read's linear facts
become `atIndex` (`restateAtIndex`). -/
def restateSpines (ls : HeapLinks.Links) (dropped : Nat → Bool) (as : List IndexAtom) : List IndexAtom :=
  let reads := (plainReads ls).filter fun g => dropped g.2.2
  let spines :=
    if reads.isEmpty then [] else
    let lift (a b : Nat × List String) : Option IndexAtom :=
      if dropped a.1 || dropped b.1 then do
        let (x, p) ← liftPath dropped reads reads.length a
        let (y, q) ← liftPath dropped reads reads.length b
        pure { fact := .spineApart x p y q }
      else none
    as.filterMap fun a => if a.cond.isNone then match a.fact with
      | .apart u w => lift (u, []) (w, [])
      | .spineApart u p w q => lift (u, p) (w, q)
      | _ => none
      else none
  spines ++ restateAtIndex ls dropped as

theorem restateSpines_holds {ls : HeapLinks.Links} {dropped : Nat → Bool} {as : List IndexAtom} {ρ h}
    (hl : HeapLinks.Holds ls ρ h) (he : IndexHolds ε as ρ h) : IndexHolds ε (restateSpines ls dropped as) ρ h := by
  intro a ha hc
  simp only [restateSpines, List.mem_append] at ha
  rcases ha with ha | ha
  · split at ha
    · cases ha
    · obtain ⟨b, hb, hab⟩ := List.mem_filterMap.mp ha
      have hreads : ∀ g ∈ (plainReads ls).filter (fun g => dropped g.2.2), g ∈ plainReads ls :=
        fun g hg => (List.mem_filter.mp hg).1
      have lift : ∀ (u w : Nat) (p q : List String), PathSpinesApart h (ρ u) p (ρ w) q →
          ∀ c, (if dropped (u, p).1 || dropped (w, q).1 then do
            let (x, p) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
              ((plainReads ls).filter fun g => dropped g.2.2).length (u, p)
            let (y, q) ← liftPath dropped ((plainReads ls).filter fun g => dropped g.2.2)
              ((plainReads ls).filter fun g => dropped g.2.2).length (w, q)
            pure ({ fact := .spineApart x p y q } : IndexAtom)
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
          exact lift u w [] [] ⟨ρ u, ρ w, rfl, rfl, regionsApart_spines hbh⟩ a hab
        · rename_i u p w q hf
          rw [hf] at hbh
          exact lift u w p q hbh a hab
        · cases hab
      · cases hab
  · exact restateAtIndex_holds hl he a ha hc

/-- Atoms about slots below the dropped slot 0, restated one lower; an atom
naming slot 0 is first restated on a slot the links relate to it. -/
def dropIndices (ls : HeapLinks.Links) (as : List IndexAtom) : List IndexAtom :=
  let as := eliminateIndices [0] (as ++ restateReads ls (· == 0) as ++ restateSpines ls (· == 0) as)
  let restated := match HeapLinks.neighbors ls 0 with
    | y :: _ => as ++ mapIndices (fun i => some (if i = 0 then y else i)) as
    | [] => as
  mapIndices (fun i => if i = 0 then none else some (i - 1)) restated

theorem dropIndices_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ h v}
    (hl : HeapLinks.Holds ls (push v ρ) h) (he : IndexHolds ε as (push v ρ) h) :
    IndexHolds ε (dropIndices ls as) ρ h := by
  have he := eliminateIndices_holds (drop := [0]) (as := as ++ restateReads ls (· == 0) as ++ restateSpines ls (· == 0) as)
    fun a ha => (List.mem_append.mp ha).elim
      (fun ha => (List.mem_append.mp ha).elim (he a) (restateReads_holds hl he a)) (restateSpines_holds hl he a)
  unfold dropIndices
  generalize eliminateIndices [0] (as ++ restateReads ls (· == 0) as ++ restateSpines ls (· == 0) as) = as at he ⊢
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
      restateSpines k.links (fun s => (target s).isNone) k.indices
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
failed `null`, `undefined` or nullish test, a passing test for a negated tag,
or a truthy answer. -/
def excludesTag : BranchRefinement.Observation → GuardTag → Bool
  | .boolean true, .fls | .boolean false, .tru => true
  | .boolean true, .notTru | .boolean false, .notFls => true
  | .tag .isNul false, .null | .tag .isNul true, .notNull => true
  | .tag .isUndef false, .undef | .tag .isUndef true, .notUndef => true
  | .tag .isNullish false, .null | .tag .isNullish false, .undef => true
  | .tag .truthy true, .null | .tag .truthy true, .undef | .tag .truthy true, .fls => true
  | .tag .truthy false, .tru => true
  | .tag (.boolEq true) false, .tru | .tag (.boolEq false) false, .fls => true
  | .tag (.boolEq true) true, .fls | .tag (.boolEq false) true, .tru => true
  | .tag (.boolEq true) true, .notTru | .tag (.boolEq false) true, .notFls => true
  | _, _ => false

theorem excludesTag_ne {o : BranchRefinement.Observation} {v : Val} {t : GuardTag}
    (he : excludesTag o t = true) (ho : o.holds v) : ¬ t.holds v := by
  rcases o with q | ⟨tag, q⟩
  · cases q <;> cases t <;> simp_all [excludesTag, BranchRefinement.Observation.holds, GuardTag.holds]
  · cases tag with
    | boolEq b =>
      cases b <;> cases q <;> cases t <;> simp only [excludesTag, Bool.false_eq_true] at he
      all_goals cases v <;> simp_all [BranchRefinement.Observation.holds, tagHolds, protoFree, GuardTag.holds]
    | _ =>
      cases q <;> cases t <;> simp only [excludesTag, Bool.false_eq_true] at he
      all_goals cases v <;> simp_all [BranchRefinement.Observation.holds, tagHolds, protoFree, GuardTag.holds]

/-- Whether a guard's path from `s` reads a value of `slot`'s class: `s` is
of the class, or the path follows read links to a slot of it. -/
def readsClass (ls : HeapLinks.Links) (slot : Nat) : Nat → List String → Bool
  | s, [] => (HeapLinks.aliases ls slot).contains s
  | s, f :: rest => (guardReads ls).any fun g => g.1 == s && g.2.1 == f && readsClass ls slot g.2.2 rest

theorem readsClass_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {slot : Nat} : ∀ {s : Nat} {p : List String} {v : Val}, readsClass ls slot s p = true →
    readGuard h (ρ s) p = some v → v = ρ slot
  | s, [], v, hr, hv => by
    simp only [readsClass, List.contains_iff_mem] at hr
    simp only [readGuard, Option.some.injEq] at hv
    rw [← hv]
    exact HeapLinks.aliases_eq hl hr
  | s, f :: rest, v, hr, hv => by
    simp only [readsClass] at hr
    obtain ⟨⟨c, f', w⟩, hg, hm⟩ := List.any_eq_true.mp hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨rfl, rfl⟩, hrest⟩ := hm
    rw [guardReads_read hl hg rest] at hv
    exact readsClass_eq hl hrest hv

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
        simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact IndexFact.holdsAt_valueFact.mpr ⟨hvars 1 i false, by
            show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv]; omega⟩
        · exact IndexFact.holdsAt_valueFact.mpr ⟨hvars (-1) (-i) false, by
            show Linear.Form.eval _ _ ≤ _; simp [Linear.Form.eval, hv]; omega⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at ha
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

/-- The strongest supported nullish exclusion implied by a value type. -/
def nullishAtoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then
    let nn := (expand G A).all (fun c => tagClause .isNul c == some false)
    let nu := (expand G A).all (fun c => tagClause .isUndef c == some false)
    if nn && nu then some [.nonNullish]
    else if nu then some [.defined]
    else if nn then some [.nonNull]
    else none
  else none

theorem nullishAtoms_sound {G : NormalGraph ι} {A R n W v}
    (hr : nullishAtoms G A = some R) (hv : meaning G A n W v) :
    ∃ a ∈ R, a.holds v := by
  unfold nullishAtoms at hr
  split at hr
  · rename_i hp
    have hn : (expand G A).all (fun c => tagClause .isNul c == some false) = true → v ≠ .nul := by
      intro h he
      have hq : Answers G A .isNul false := ⟨hp, by simpa only [List.all_eq_true, beq_iff_eq] using h⟩
      have := answers_sound hq hv
      rw [he] at this; simp [tagHolds] at this
    have hu : (expand G A).all (fun c => tagClause .isUndef c == some false) = true → v ≠ .undef := by
      intro h he
      have hq : Answers G A .isUndef false := ⟨hp, by simpa only [List.all_eq_true, beq_iff_eq] using h⟩
      have := answers_sound hq hv
      rw [he] at this; simp [tagHolds] at this
    dsimp only at hr
    split at hr
    · rename_i hb; cases hr
      simp only [Bool.and_eq_true] at hb
      exact ⟨.nonNullish, by simp, (meaning_value hv).1, hn hb.1, hu hb.2⟩
    · split at hr
      · rename_i h; cases hr
        exact ⟨.defined, by simp, (meaning_value hv).1, hu h⟩
      · split at hr
        · rename_i h; cases hr
          exact ⟨.nonNull, by simp, (meaning_value hv).1, hn h⟩
        · cases hr
  · cases hr

/-- **The values a type admits**, as atoms: its finitely many primitive
predicates where it is of them (`atoms`), else the nullish values it
excludes (`nullishAtoms`). -/
def typeAtoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  (atoms G A).orElse fun _ => nullishAtoms G A

theorem typeAtoms_sound {G : NormalGraph ι} {A R n W v} (hr : typeAtoms G A = some R)
    (hv : meaning G A n W v) : ∃ a ∈ R, a.holds v := by
  unfold typeAtoms at hr
  cases ha : atoms G A with
  | some S =>
    rw [ha] at hr; cases hr
    exact (atoms_sem ha n W v).mp hv
  | none =>
    rw [ha] at hr
    exact nullishAtoms_sound hr hv

/-- Each slot's type as the value set it admits (`typeAtoms`): each computed
when first read, once. -/
def typeSets (G : NormalGraph ι) (Γ : List (Ty ι)) : Array (Thunk (Option ValueSets.ValueSet)) :=
  Γ.toArray.map fun A => Thunk.mk fun _ => (typeAtoms G A).map ValueSets.ofAtoms

/-- The contexts read from computed type sets, slot `i` at index `i - shift`
(below `shift`, none). Kept out of line, so the sets are computed once by
the caller and only read here. -/
@[noinline] def setsCtx (ts : Array (Thunk (Option ValueSets.ValueSet))) (shift : Nat) :
    Nat → Option ValueSets.ValueSet :=
  fun i => if i < shift then none else (ts[i - shift]?).bind (·.get)

theorem typeSets_get (G : NormalGraph ι) (Γ : List (Ty ι)) (i : Nat) :
    ((typeSets G Γ)[i]?).bind (·.get) = (Γ[i]?).bind fun A => (typeAtoms G A).map ValueSets.ofAtoms := by
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
    exact ValueSets.ofAtoms_holds (typeAtoms_sound hR (he.2 i A hA))

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
      · rw [ite_eq_left hn]
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
      · rw [ite_eq_right hn]; exact hout
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
    (hsto : elementsOf (ρ x) = some sto) (hls : h[sto]?.bind spineEntries = some ls)
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

/-- Whether the links `ls` read path `p` from slot `s` into slot `x`. -/
def readsPath (ls : HeapLinks.Links) : Nat → List String → Nat → Bool
  | s, [], x => (HeapLinks.aliases ls x).contains s
  | s, f :: p, x => (bridgeReads ls).any fun (c, g, v) =>
      (HeapLinks.aliases ls c).contains s && g == f && readsPath ls v p x

theorem readsPath_eq {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h) :
    ∀ {s x : Nat} {p : List String}, readsPath ls s p x = true →
      ∀ {w : Val}, readPath h (ρ s) p = some w → w = ρ x
  | s, x, [], hr, w, hw => by
    simp only [readsPath, List.contains_iff_mem] at hr
    simp only [readPath, Option.some.injEq] at hw
    rw [← hw]; exact HeapLinks.aliases_eq hl hr
  | s, x, f :: p, hr, w, hw => by
    obtain ⟨⟨c, g, v⟩, hbr, hm⟩ := List.any_eq_true.mp hr
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hm
    obtain ⟨⟨hs, rfl⟩, hrest⟩ := hm
    rw [HeapLinks.aliases_eq hl hs] at hw
    exact readsPath_eq hl hrest (bridgeReads_path hl hbr hw)

/-- A checked read of a parallel array `(s', p')` at an index equal to `k`. -/
def parallelSlot (K : Linear.Known Term) (ls : HeapLinks.Links) (as : List IndexAtom) (s' : Nat) (p' : List String) (k : Nat) : Option Nat := do
  let a ← as.find? fun a => a.cond.isNone && match a.fact with
    | .element _ y j => readsPath ls s' p' y &&
      (j == k || (K.entails (.le [(.value j, 1), (.value k, -1)] 0) &&
        K.entails (.le [(.value k, 1), (.value j, -1)] 0)))
    | _ => false
  match a.fact with
  | .element r' _ _ => some r'
  | _ => none

theorem parallelSlot_read {K : Linear.Known Term} {ls : HeapLinks.Links} {as : List IndexAtom} {s' k r' i : Nat} {p' : List String}
    {ρ : Env} {h : Heap} (hK : K.Holds (termValuation ε ρ h)) (hl : HeapLinks.Holds ls ρ h) (ha : IndexHolds ε as ρ h)
    (hki : intValue (ρ k) = some (i : Int)) (hm : parallelSlot K ls as s' p' k = some r') :
    ∀ {a : Val} {st : Nat} {ls' : List (Option Nat)},
      readPath h (ρ s') p' = some a → elementsOf a = some st → h[st]?.bind spineEntries = some ls' →
      i < ls'.length ∧ (∀ l, ls'[i]? = some (some l) → h[l]? = some (ρ r')) ∧
      (ls'[i]? = some none → ρ r' = .undef) := by
  intro a st ls' hrp hsto hls'
  simp only [parallelSlot, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
  obtain ⟨at_, hfind, hm⟩ := hm
  have hc := List.find?_some hfind
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
  obtain ⟨hcond, hc⟩ := hc
  have he := ha at_ (List.mem_of_find?_eq_some hfind) (fun b hb => by rw [hcond] at hb; cases hb)
  cases hf : at_.fact <;> simp only [hf] at hm hc he <;> try { cases hm }
  rename_i r0 y j
  simp only [Option.some.injEq] at hm; subst hm
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hpath, hjk⟩ := hc
  obtain ⟨sto0, ls0, b, j0, hs0, hl0, hj, hji, hlt, hpres, hhole⟩ := he
  have hya : a = ρ y := readsPath_eq hl hpath hrp
  rw [← hya, hsto] at hs0; cases hs0
  rw [hls'] at hl0; cases hl0
  have hji' : intValue (ρ j) = some (j0 : Int) := by rw [hj]; exact intValue_num hji
  have heq : j0 = i := by
    rcases hjk with rfl | ⟨hlo, hhi⟩
    · rw [hki] at hji'; cases hji'; rfl
    · have lo := Linear.Known.entails_sound hK hlo
      have hi := Linear.Known.entails_sound hK hhi
      simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hki, hji', Option.getD_some] at lo hi
      omega
  subst heq
  exact ⟨hlt, hpres, hhole⟩

def boundInstance (K : Linear.Known Term) (ls : HeapLinks.Links) (as : List IndexAtom) (cls : List Nat) (k r : Nat) : Bound → Option Term
  | .offset d => (offsetSlot as cls k d).map Term.value
  | .parallel s' p' kind ep => (parallelSlot K ls as s' p' k).map fun r' => Term.now kind r' ep
  | b => some (b.inst k r)

/-- Instantiate a body clause at element read `(r, k)`, returning an `IndexFact`
where every parallel array reference resolves to an element read at `k`. -/
def instantiateBodyClause (K : Linear.Known Term) (ls : HeapLinks.Links) (as : List IndexAtom) (cls : List Nat) (r k : Nat) :
    BodyClause → Option IndexFact
  | .clause F => (F.mapVars (boundInstance K ls as cls k r)).map LinearClause.toIndexFact
  | .guarded (.self ep) tag b => (instantiateBodyClause K ls as cls r k b).map (.guarded r ep tag)
  | .guarded (.parallel s' p' ep) tag b => do
      let r' ← parallelSlot K ls as s' p' k
      let b' ← instantiateBodyClause K ls as cls r k b
      pure (.guarded r' ep tag b')

/-- The facts a read of the element at the index the slot `k` holds, its
value in the slot `r`, states of a quantified fact over an array whose path
resolves to the read array `x`: each body clause with the index read as `k`
and the element as `r`, where `0 ≤ k < stop` (`every-read`). -/
def instantiateEvery (K : Thunk (Linear.Known Term)) (ls : HeapLinks.Links) (as : List IndexAtom) (cls : List Nat) (r x k : Nat) :
    IndexAtom → List IndexAtom
  | ⟨.every s p st body, none, _⟩ =>
    if readsPath ls s p x && intSlot as k && termDefined as st then
      if K.get.entails (.le [(.value k, -1)] 0) && K.get.entails (.le [(.value k, 1), (st, -1)] (-1)) then
        body.filterMap fun B => (instantiateBodyClause K.get ls as cls r k B).map fun F => { fact := F }
      else []
    else []
  | _ => []

/-- Whether `k.values` excludes `t` for slot `r` (or one of its aliases). -/
def valExcludesTag (k : Knowledge) (r : Nat) (t : GuardTag) : Bool :=
  let rCls := HeapLinks.aliases k.links r
  k.values.any fun f => rCls.contains f.slot && onlyTag f.contents t.complement

theorem valExcludesTag_ne {k : Knowledge} {r : Nat} {t : GuardTag} {ρ : Env} {h : Heap}
    (hk : Holds k ε ρ h) (he : valExcludesTag k r t = true) : ¬ t.holds (ρ r) := by
  simp only [valExcludesTag, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at he
  obtain ⟨f, hf, hmem, hno⟩ := he
  have hv := hk.2.1 f hf
  rw [HeapLinks.aliases_eq hk.2.2.1 hmem] at hv
  exact GuardTag.complement_not_holds (onlyTag_mem hno hv)

/-- Instantiate an indexed-element fact (or a disjunction containing one) at an
element read `element r x i` when `s ∈ cls` and `idx = i`. -/
def instAtIndexFact (K : Thunk (Linear.Known Term)) (k : Knowledge) (cls kCls : List Nat) (r i : Nat) : IndexFact → Option IndexFact
  | .atIndex s [] idx guard body =>
    if !cls.contains s then none else
    let idxEq :=
      (!idx.atEntry && idx.kind == .value && idx.path.isEmpty && kCls.contains idx.slot) ||
      (termDefined k.indices idx &&
        K.get.entails (.le [(.value i, 1), (idx, -1)] 0) &&
        K.get.entails (.le [(idx, 1), (.value i, -1)] 0))
    if idxEq then
      (body.mapVars (boundInstance K.get k.links k.indices cls i r)).map fun G =>
        match guard with
        | none => G.toIndexFact
        | some g => if valExcludesTag k r g then G.toIndexFact else .guarded r [] g G.toIndexFact
    else none
  | .either A B =>
    match instAtIndexFact K k cls kCls r i A, instAtIndexFact K k cls kCls r i B with
    | some A', some B' => some (.either A' B')
    | some A', none => some (.either A' B)
    | none, some B' => some (.either A B')
    | none, none => none
  | _ => none

/-- The fact a read of the element at index `i`, its value in `r`, states of an
indexed-element fact (or disjunction containing one) over an array of the read
array's class `cls` when `idx` equals `i`. -/
def instantiateAtIndex (K : Thunk (Linear.Known Term)) (k : Knowledge) (cls kCls : List Nat) (r i : Nat) : IndexAtom → List IndexAtom
  | ⟨fact, none, _⟩ => match instAtIndexFact K k cls kCls r i fact with
    | some F' => [{ fact := F' }]
    | none => []
  | _ => []

/-- The facts each element read the atoms state instantiates
(`instantiateEvery`, `instantiateAtIndex`). -/
def elementFacts (k : Knowledge) : List IndexAtom :=
  let everys := k.indices.filter fun a => a.cond.isNone && match a.fact with | .every .. => true | _ => false
  let atIdxs := k.indices.filter fun a => a.cond.isNone && a.fact.hasAtIndex
  if everys.isEmpty && atIdxs.isEmpty then [] else
  let elems := k.indices.filterMap fun a => match a with | ⟨.element r x i, none, _⟩ => some (r, x, i) | _ => none
  if elems.isEmpty then [] else
  let K := Thunk.mk fun _ => Linear.Known.build (linearRaw k.indices) []
  elems.flatMap fun (r, x, i) =>
    let cls := HeapLinks.aliases k.links x
    let kCls := if atIdxs.isEmpty then [] else HeapLinks.aliases k.links i
    everys.flatMap (instantiateEvery K k.links k.indices cls r x i) ++
    atIdxs.flatMap (instantiateAtIndex K k cls kCls r i)

/-- Knowledge with its element reads' instances added. -/
def elementInstances (k : Knowledge) : Knowledge :=
  let ef := (elementFacts k).eraseDups.filter (!k.indices.contains ·)
  if ef.isEmpty then k else { k with indices := k.indices ++ ef }

private theorem linearClause_holdsAt_mapVars_imp {V W : Type} {f : V → Option W}
    {val : V → Option Int} {val' : W → Option Int}
    {F : LinearClause V} {G : LinearClause W} (hm : F.mapVars f = some G)
    (hf : ∀ x ∈ F.vars, ∀ y n, f x = some y → val x = some n → val' y = some n)
    (hF : F.HoldsAt val) : G.HoldsAt val' := by
  induction F generalizing G with
  | atom F =>
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hm
    refine (factAt_mapVars hG (val := val) (val' := val') ?_).mpr hF
    intro x hx y hy
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hF.1 x hx)
    rw [hn]; exact hf x hx y n hy hn
  | either A B ihA ihB =>
    simp only [LinearClause.mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hm
    obtain ⟨A', hA, B', hB, rfl⟩ := hm
    exact hF.imp (ihA hA fun x hx => hf x (List.mem_append_left _ hx))
      (ihB hB fun x hx => hf x (List.mem_append_right _ hx))

theorem instantiateBodyClause_holds {K : Linear.Known Term} {ls_links : HeapLinks.Links} {as : List IndexAtom} {cls : List Nat}
    {r x k sto i : Nat} {ls : List (Option Nat)} {ρ : Env} {h : Heap}
    (hK : K.Holds (termValuation ε ρ h)) (hl : HeapLinks.Holds ls_links ρ h) (ha : IndexHolds ε as ρ h)
    (hcls : ∀ y ∈ cls, ρ y = ρ x) (hsto : elementsOf (ρ x) = some sto)
    (hls : h[sto]?.bind spineEntries = some ls) (hki : intValue (ρ k) = some (i : Int))
    (hlt : i < ls.length) (hpres : ∀ l, ls[i]? = some (some l) → h[l]? = some (ρ r))
    (hhole : ls[i]? = some none → ρ r = .undef) :
    ∀ {B : BodyClause} {G : IndexFact},
      instantiateBodyClause K ls_links as cls r k B = some G →
      B.HoldsAt ε ρ h ls i → G.HoldsAt ε ρ h
  | .clause F, G, hinst, hB => by
    obtain ⟨G', hmG, rfl⟩ := Option.map_eq_some_iff.mp hinst
    refine LinearClause.toIndexFact_holds.mpr (linearClause_holdsAt_mapVars_imp hmG (fun y _ t n ht hn => ?_) hB)
    cases y with
    | offset d =>
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp ht
      rw [offsetSlot_value ha hcls hsto hls hki hr]; exact hn
    | index =>
      simp only [boundInstance, Option.some.injEq] at ht; subst ht
      simp only [Bound.inst, termValue_value, hki]
      simpa [boundValue] using hn
    | elem =>
      simp only [boundInstance, Option.some.injEq] at ht; subst ht
      simp only [Bound.inst, termValue_value]
      simp only [boundValue, elementInt] at hn
      cases hli : ls[i]? with
      | none => simp at hli; omega
      | some o =>
        cases o with
        | none => simp [hli] at hn
        | some l => simp only [hli, hpres l hli, Option.bind_some] at hn; exact hn
    | project kind path =>
      simp only [boundInstance, Option.some.injEq] at ht; subst ht
      simp only [Bound.inst, termValue, termAt, Bool.false_eq_true, ite_false]
      simp only [boundValue] at hn
      cases hli : ls[i]? with
      | none => simp at hli; omega
      | some o =>
        cases o with
        | none => simp [hli] at hn
        | some l =>
          simp only [hli, hpres l hli, Option.bind_some] at hn
          exact hn
    | parallel s' p' kind ep =>
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp ht
      simp only [boundValue] at hn
      cases hrp : readPath h (ρ s') p' with
      | none => simp [hrp] at hn
      | some a =>
        cases hea : elementsOf a with
        | none => simp [hrp, hea] at hn
        | some st' =>
          cases hls' : h[st']?.bind spineEntries with
          | none => simp [hrp, hea, hls'] at hn
          | some ls' =>
            obtain ⟨hlt', hpres', hhole'⟩ := parallelSlot_read hK hl ha hki hr' hrp hea hls'
            simp only [hrp, hea, hls'] at hn
            cases hli : ls'[i]? with
            | none => simp at hli; omega
            | some o =>
              cases o with
              | none => simp [hli] at hn
              | some l =>
                simp only [hli, hpres' l hli, Option.bind_some] at hn
                simpa [termValue, termAt, Bool.false_eq_true, ite_false] using hn
    | free t => cases ht; exact hn
  | .guarded (.self ep) tag b, G, hinst, ⟨w, hw, hor⟩ => by
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hinst
    simp only [ElemTarget.read] at hw
    cases hli : ls[i]? with
    | none => simp [hli] at hw
    | some o =>
      cases o with
      | none => simp [hli] at hw
      | some l =>
        simp only [hli] at hw
        obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
        have hveq : v = ρ r := Option.some.inj (hv.symm.trans (hpres l hli))
        subst hveq
        exact ⟨w, hrg, hor.imp id (instantiateBodyClause_holds hK hl ha hcls hsto hls hki hlt hpres hhole hb')⟩
  | .guarded (.parallel s' p' ep) tag b, G, hinst, ⟨w, hw, hor⟩ => by
    simp only [instantiateBodyClause, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hinst
    obtain ⟨r', hr', b', hb', rfl⟩ := hinst
    simp only [ElemTarget.read] at hw
    cases hrp : readPath h (ρ s') p' with
    | none => simp [hrp] at hw
    | some a =>
      simp only [hrp] at hw
      cases hea : elementsOf a with
      | none => simp [hea] at hw
      | some st' =>
        simp only [hea] at hw
        cases hls' : h[st']?.bind spineEntries with
        | none => simp [hls'] at hw
        | some ls' =>
          simp only [hls'] at hw
          obtain ⟨-, hpres', -⟩ := parallelSlot_read hK hl ha hki hr' hrp hea hls'
          cases hli : ls'[i]? with
          | none => simp [hli] at hw
          | some o =>
            cases o with
            | none => simp [hli] at hw
            | some l =>
              simp only [hli] at hw
              obtain ⟨v, hv, hrg⟩ := Option.bind_eq_some_iff.mp hw
              have hveq : v = ρ r' := Option.some.inj (hv.symm.trans (hpres' l hli))
              subst hveq
              exact ⟨w, hrg, hor.imp id (instantiateBodyClause_holds hK hl ha hcls hsto hls hki hlt hpres hhole hb')⟩

theorem instantiateEvery_holds {K : Thunk (Linear.Known Term)} {ls_links : HeapLinks.Links} {as : List IndexAtom} {cls : List Nat}
    {r x k : Nat} {ρ : Env} {h : Heap}
    (hK : K.get.Holds (termValuation ε ρ h)) (hl : HeapLinks.Holds ls_links ρ h) (ha : IndexHolds ε as ρ h)
    (hcls : ∀ y ∈ cls, ρ y = ρ x) (he : (IndexFact.element r x k).HoldsAt ε ρ h)
    {a : IndexAtom} (hm : a ∈ as) : IndexHolds ε (instantiateEvery K ls_links as cls r x k a) ρ h := by
  obtain ⟨sto, ls, b, i, hsto, hls, hk, hbi, hlt, hpres, hhole⟩ := he
  intro c hc _
  match a, hm, hc with
  | ⟨.every s p st body, none, ng⟩, hm, hc =>
    simp only [instantiateEvery] at hc
    split at hc
    · rename_i hpre
      split at hc
      · rename_i hent
        simp only [Bool.and_eq_true] at hpre hent
        obtain ⟨⟨hpath, -⟩, hd⟩ := hpre
        obtain ⟨e0, e1⟩ := hent
        obtain ⟨B, hB, hG⟩ := List.mem_filterMap.mp hc
        obtain ⟨G, hmG, rfl⟩ := Option.map_eq_some_iff.mp hG
        have hat := ha _ hm (fun b hb => by cases hb)
        obtain ⟨w, sto', ls', n, hw, hsto', hls', hn, hall⟩ := hat
        have hwx : w = ρ x := readsPath_eq hl hpath hw
        subst hwx
        rw [hsto] at hsto'; cases hsto'
        rw [hls] at hls'; cases hls'
        have hki : intValue (ρ k) = some (i : Int) := by rw [hk]; exact intValue_num hbi
        have f1 := Linear.Known.entails_sound hK e1
        simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hki, hn,
          Option.getD_some] at f1
        exact instantiateBodyClause_holds hK hl ha hcls hsto hls hki hlt hpres hhole hmG (hall i (by omega) B hB)
      · cases hc
    · cases hc
  | ⟨.every _ _ _ _, some _, _⟩, _, hc => simp [instantiateEvery] at hc
  | ⟨.index _, _, _⟩, _, hc | ⟨.length _ _, _, _⟩, _, hc | ⟨.bound _ _ _, _, _⟩, _, hc
  | ⟨.int _, _, _⟩, _, hc | ⟨.pastSafe _, _, _⟩, _, hc | ⟨.linear _, _, _⟩, _, hc
  | ⟨.guarded _ _ _ _, _, _⟩, _, hc | ⟨.either _ _, _, _⟩, _, hc
  | ⟨.element _ _ _, _, _⟩, _, hc | ⟨.fieldRead _ _ _, _, _⟩, _, hc | ⟨.atIndex _ _ _ _ _, _, _⟩, _, hc
  | ⟨.apart _ _, _, _⟩, _, hc | ⟨.spineApart _ _ _ _, _, _⟩, _, hc | ⟨.same _ _, _, _⟩, _, hc => simp [instantiateEvery] at hc

theorem instAtIndexFact_holds {K : Thunk (Linear.Known Term)} {k : Knowledge} {cls kCls : List Nat} {r x i : Nat} {ρ : Env} {h : Heap}
    (hK : K.get.Holds (termValuation ε ρ h)) (hk : Holds k ε ρ h) (hcls : ∀ y ∈ cls, ρ y = ρ x) (hkCls : ∀ y ∈ kCls, ρ y = ρ i)
    (he : (IndexFact.element r x i).HoldsAt ε ρ h) :
    ∀ {F F' : IndexFact}, instAtIndexFact K k cls kCls r i F = some F' → F.HoldsAt ε ρ h → F'.HoldsAt ε ρ h := by
  obtain ⟨sto, ls, b, idxNat, hsto, hls, hi, hbi, hlt, hpres, hhole⟩ := he
  have ha := hk.2.2.2.2.2
  have hki : intValue (ρ i) = some (idxNat : Int) := by rw [hi]; exact intValue_num hbi
  intro F
  induction F with
  | atIndex s path idx guard body =>
    intro F' hc hat
    cases path with
    | cons _ _ => simp [instAtIndexFact] at hc
    | nil =>
      simp only [instAtIndexFact] at hc
      split at hc
      · cases hc
      · rename_i hns
        have hs : s ∈ cls := List.contains_iff_mem.mp (by simpa using hns)
        split at hc
        · rename_i hidxEq
          obtain ⟨w, sto', ls', n, hw, hsto', hls', hn, hlt', hrest⟩ := hat
          have hρs : ρ s = ρ x := hcls s hs
          simp only [readPath, Option.some.injEq] at hw
          subst hw
          rw [hρs, hsto] at hsto'
          cases hsto'
          rw [hls] at hls'
          cases hls'
          have hneq : n = idxNat := by
            rcases Bool.or_eq_true_iff.mp hidxEq with hsyn | hlin
            · simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff, List.contains_iff_mem] at hsyn
              obtain ⟨⟨⟨hae, hkd⟩, hpt⟩, hmem⟩ := hsyn
              have hρj : ρ idx.slot = ρ i := hkCls idx.slot hmem
              simp only [termValue, termAt, hae, Bool.false_eq_true, ite_false, hpt, hkd, readPath, Option.bind_some,
                kindValue, hρj, hki, Option.some.injEq] at hn
              omega
            · simp only [Bool.and_eq_true] at hlin
              obtain ⟨⟨hd, hle1⟩, hle2⟩ := hlin
              have f1 := Linear.Known.entails_sound hK hle1
              have f2 := Linear.Known.entails_sound hK hle2
              simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, termValue_value, hki, hn,
                Option.getD_some] at f1 f2
              omega
          subst hneq
          obtain ⟨G, hmG, rfl⟩ := Option.map_eq_some_iff.mp hc
          have hBody : body.HoldsAt (boundValue ε ρ h ls n) → G.toIndexFact.HoldsAt ε ρ h := fun hB =>
            instantiateBodyClause_holds (B := .clause body) hK hk.2.2.1 ha hcls hsto hls hki hlt hpres hhole
              (by simp [instantiateBodyClause, hmG]) hB
          cases guard with
          | none => exact hBody hrest
          | some g =>
            have hguard : g.holds (ρ r) ∨ G.toIndexFact.HoldsAt ε ρ h := by
              rcases hrest with ⟨l, v, hli, hlv, hgv⟩ | ⟨hli, hgu⟩ | hB
              · left; have := hpres l hli; rw [hlv] at this; exact (Option.some.inj this) ▸ hgv
              · left; rw [hhole hli]; exact hgu
              · right; exact hBody hB
            dsimp only
            split
            · rename_i hex
              exact hguard.resolve_left (valExcludesTag_ne hk hex)
            · exact ⟨ρ r, rfl, hguard⟩
        · cases hc
  | either A B ihA ihB =>
    intro F' hc hat
    simp only [instAtIndexFact] at hc
    cases hA : instAtIndexFact K k cls kCls r i A <;> cases hB : instAtIndexFact K k cls kCls r i B <;>
      simp only [hA, hB, Option.some.injEq] at hc
    · cases hc
    · subst hc; exact hat.imp id (ihB hB)
    · subst hc; exact hat.imp (ihA hA) id
    · subst hc; exact hat.imp (ihA hA) (ihB hB)
  | _ => intro F' hc; simp [instAtIndexFact] at hc

theorem instantiateAtIndex_holds {K : Thunk (Linear.Known Term)} {k : Knowledge} {cls kCls : List Nat} {r x i : Nat} {ρ : Env} {h : Heap}
    (hK : K.get.Holds (termValuation ε ρ h)) (hk : Holds k ε ρ h) (hcls : ∀ y ∈ cls, ρ y = ρ x) (hkCls : ∀ y ∈ kCls, ρ y = ρ i)
    (he : (IndexFact.element r x i).HoldsAt ε ρ h)
    {a : IndexAtom} (hm : a ∈ k.indices) : IndexHolds ε (instantiateAtIndex K k cls kCls r i a) ρ h := by
  intro c hc _
  rcases a with ⟨fact, cond, ng⟩
  cases cond with
  | some _ => simp [instantiateAtIndex] at hc
  | none =>
    simp only [instantiateAtIndex] at hc
    cases hinst : instAtIndexFact K k cls kCls r i fact with
    | none => simp [hinst] at hc
    | some F' =>
      simp only [hinst, List.mem_singleton] at hc
      subst hc
      exact instAtIndexFact_holds hK hk hcls hkCls he hinst (hk.2.2.2.2.2 _ hm (fun _ h0 => by cases h0))

theorem elementInstances_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (elementInstances k) ε ρ h := by
  unfold elementInstances
  dsimp only
  split
  · exact hk
  · refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact hk.2.2.2.2.2 a ha hc
    · have ha' := List.mem_eraseDups.mp (List.mem_filter.mp ha).1
      unfold elementFacts at ha'
      dsimp only at ha'
      split at ha'
      · cases ha'
      · split at ha'
        · cases ha'
        · obtain ⟨⟨r, x, i⟩, he, hm⟩ := List.mem_flatMap.mp ha'
          obtain ⟨e, hem, hme⟩ := List.mem_filterMap.mp he
          match e, hem, hme with
          | ⟨.element r' x' i', none, _⟩, hem, hme =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hme
            obtain ⟨rfl, rfl, rfl⟩ := hme
            have hel := hk.2.2.2.2.2 _ hem (fun b hb => by cases hb)
            rcases List.mem_append.mp hm with hm | hm
            · obtain ⟨c, hcm, hm⟩ := List.mem_flatMap.mp hm
              exact instantiateEvery_holds (K := Thunk.mk fun _ => Linear.Known.build (linearRaw k.indices) [])
                (Linear.Known.build_holds (linearRaw_holds hk.2.2.2.2.2) (by simp)) hk.2.2.1 hk.2.2.2.2.2
                (fun y hy => HeapLinks.aliases_eq hk.2.2.1 hy) hel (List.mem_filter.mp hcm).1 a hm hc
            · obtain ⟨c, hcm, hm⟩ := List.mem_flatMap.mp hm
              have hne : (k.indices.filter fun a => a.cond.isNone && a.fact.hasAtIndex).isEmpty = false := by
                cases hne' : (k.indices.filter fun a => a.cond.isNone && a.fact.hasAtIndex).isEmpty
                · rfl
                · rw [List.isEmpty_iff.mp hne'] at hcm; cases hcm
              simp only [hne, Bool.false_eq_true, ite_false] at hm
              exact instantiateAtIndex_holds (K := Thunk.mk fun _ => Linear.Known.build (linearRaw k.indices) [])
                (Linear.Known.build_holds (linearRaw_holds hk.2.2.2.2.2) (by simp)) hk
                (fun y hy => HeapLinks.aliases_eq hk.2.2.1 hy)
                (fun y hy => HeapLinks.aliases_eq hk.2.2.1 hy) hel (List.mem_filter.mp hcm).1 a hm hc
          | ⟨.element _ _ _, some _, _⟩, _, hme => cases hme
          | ⟨.index _, _, _⟩, _, hme | ⟨.length _ _, _, _⟩, _, hme | ⟨.bound _ _ _, _, _⟩, _, hme
          | ⟨.int _, _, _⟩, _, hme | ⟨.pastSafe _, _, _⟩, _, hme | ⟨.linear _, _, _⟩, _, hme
          | ⟨.guarded _ _ _ _, _, _⟩, _, hme | ⟨.either _ _, _, _⟩, _, hme | ⟨.fieldRead _ _ _, _, _⟩, _, hme
          | ⟨.apart _ _, _, _⟩, _, hme | ⟨.spineApart _ _ _ _, _, _⟩, _, hme | ⟨.every _ _ _ _, _, _⟩, _, hme
          | ⟨.atIndex _ _ _ _ _, _, _⟩, _, hme | ⟨.same _ _, _, _⟩, _, hme => cases hme


/-- Whether a linear fact contradicts a prepared linear context `K`, checked
by its targeted negation over `F`'s variables rather than a whole-store
contradiction search. -/
def contradictsIn (K : Linear.Known Term) : IndexFact → Bool
  | .linear (.le form d) => K.entails (.le (form.map fun (t, c) => (t, -c)) (-d - 1))
  | .linear (.ne form d) =>
    K.entails (.le form d) && K.entails (.le (form.map fun (t, c) => (t, -c)) (-d))
  | _ => false

theorem contradictsIn_sound {K : Linear.Known Term} {F : IndexFact} {ρ : Env} {h : Heap}
    (hK : K.Holds (termValuation ε ρ h)) (hc : contradictsIn K F = true) (hF : F.HoldsAt ε ρ h) : False := by
  cases F with
  | linear L =>
    cases L with
    | le form d =>
      have hneg := Linear.Known.entails_sound hK hc
      simp only [Linear.Fact.Holds, eval_negForm] at hneg
      have hpos : Linear.Form.eval (termValuation ε ρ h) form ≤ d := hF.2
      omega
    | ne form d =>
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
      have hle1 : Linear.Form.eval (termValuation ε ρ h) form ≤ d := Linear.Known.entails_sound hK h1
      have hle2 := Linear.Known.entails_sound hK h2
      simp only [Linear.Fact.Holds, eval_negForm] at hle2
      have hne : Linear.Form.eval (termValuation ε ρ h) form ≠ d := hF.2
      omega
  | index _ | length _ _ | bound _ _ _ | int _ | pastSafe _ | either _ _ | guarded _ _ _ _
  | element _ _ _ | fieldRead _ _ _ | every _ _ _ _ | atIndex _ _ _ _ _ | apart _ _ | spineApart _ _ _ _ | same _ _ => simp [contradictsIn] at hc

/-- An alternative whose other arm contradicts the prepared linear facts `K`. -/
def releaseEitherIn (K : Linear.Known Term) (a : IndexAtom) : List IndexAtom :=
  match a with
  | ⟨.either A B, none, _⟩ =>
    (if contradictsIn K B then [{ fact := A }] else []) ++
    (if contradictsIn K A then [{ fact := B }] else [])
  | _ => []

theorem releaseEitherIn_holds {as : List IndexAtom} {K : Linear.Known Term} {a : IndexAtom} {ρ : Env} {h : Heap}
    (hK : K.Holds (termValuation ε ρ h)) (ha : IndexHolds ε as ρ h) (hm : a ∈ as) :
    IndexHolds ε (releaseEitherIn K a) ρ h := by
  match a with
  | ⟨.either A B, none, ng⟩ =>
    have hor := ha _ hm (fun b hb => by cases hb)
    intro b hb _
    simp only [releaseEitherIn, List.mem_append] at hb
    rcases hb with hb | hb
    · split at hb
      · rename_i hc
        simp only [List.mem_singleton] at hb; subst hb
        exact hor.resolve_right (fun hB => contradictsIn_sound hK hc hB)
      · cases hb
    · split at hb
      · rename_i hc
        simp only [List.mem_singleton] at hb; subst hb
        exact hor.resolve_left (fun hA => contradictsIn_sound hK hc hA)
      · cases hb
  | ⟨.either _ _, some _, _⟩ => simp [releaseEitherIn, IndexHolds]
  | ⟨.index _, _, _⟩ | ⟨.length _ _, _, _⟩ | ⟨.bound _ _ _, _, _⟩
  | ⟨.int _, _, _⟩ | ⟨.pastSafe _, _, _⟩ | ⟨.linear _, _, _⟩ | ⟨.guarded _ _ _ _, _, _⟩
  | ⟨.element _ _ _, _, _⟩ | ⟨.fieldRead _ _ _, _, _⟩ | ⟨.every _ _ _ _, _, _⟩ | ⟨.atIndex _ _ _ _ _, _, _⟩ | ⟨.apart _ _, _, _⟩
  | ⟨.spineApart _ _ _ _, _, _⟩ | ⟨.same _ _, _, _⟩ => simp [releaseEitherIn, IndexHolds]

/-- An alternative whose other arm contradicts the known linear facts. -/
def releaseEither (as : List IndexAtom) (a : IndexAtom) : List IndexAtom :=
  releaseEitherIn (Linear.Known.build (linearRaw as) (rangesRaw as)) a

theorem releaseEither_holds {as : List IndexAtom} {a : IndexAtom} {ρ : Env} {h : Heap}
    (ha : IndexHolds ε as ρ h) (hm : a ∈ as) : IndexHolds ε (releaseEither as a) ρ h :=
  releaseEitherIn_holds (Linear.Known.build_holds (linearRaw_holds ha) (rangesRaw_holds ha)) ha hm

/-- Whether a value set excludes values satisfying the guard tag. -/
def noTag (V : ValueSets.ValueSet) (t : GuardTag) : Bool :=
  onlyTag V t.complement

theorem noTag_ne {V : ValueSets.ValueSet} {t : GuardTag} {v : Val}
    (h : noTag V t = true) (hm : V.mem v = true) : ¬ t.holds v :=
  GuardTag.complement_not_holds (onlyTag_mem h hm)

/-- Whether precomputed `gr` and equivalence-class representative `rep` place
`readGuard h (ρ s) p` in a slot whose value fact excludes `t`. -/
def guardExcludedIn (gr : List (Nat × String × Nat)) (rep : Nat → Nat)
    (excl : GuardTag → List Nat) : Nat → List String → GuardTag → Bool
  | s, [], t => (excl t).contains (rep s)
  | s, f :: rest, t => gr.any fun g => g.1 == s && g.2.1 == f && guardExcludedIn gr rep excl g.2.2 rest t

theorem guardExcludedIn_ne {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h)
    {rep : Nat → Nat} (hrep : ∀ s, ρ (rep s) = ρ s)
    {excl : GuardTag → List Nat}
    (hexcl : ∀ t r, r ∈ excl t → ∃ f ∈ k.values, noTag f.contents t = true ∧ rep f.slot = r) :
    ∀ {s : Nat} {p : List String} {t : GuardTag} {v : Val},
      guardExcludedIn (guardReads k.links) rep excl s p t = true →
      readGuard h (ρ s) p = some v → ¬ t.holds v
  | s, [], t, v, he, hv => by
    simp only [guardExcludedIn, List.contains_iff_mem] at he
    obtain ⟨f, hf, hnt, hrf⟩ := hexcl t (rep s) he
    simp only [readGuard, Option.some.injEq] at hv
    have hveq : v = ρ f.slot := by
      rw [← hv, ← hrep s, ← hrf, hrep f.slot]
    rw [hveq]
    exact noTag_ne hnt (hk.2.1 f hf)
  | s, f :: rest, t, v, he, hv => by
    simp only [guardExcludedIn] at he
    obtain ⟨⟨c, f', w⟩, hg, hm⟩ := List.any_eq_true.mp he
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨rfl, rfl⟩, hrest⟩ := hm
    rw [guardReads_read hk.2.2.1 hg rest] at hv
    exact guardExcludedIn_ne hk hrep hexcl hrest hv

/-- Guarded facts whose leading guards are already excluded by `k`'s value facts,
stripped recursively (`guard-eliminate`). -/
def releaseGuardedIn (gr : List (Nat × String × Nat)) (rep : Nat → Nat)
    (excl : GuardTag → List Nat) : IndexAtom → List IndexAtom
  | ⟨.guarded s p t B, none, _⟩ =>
    if guardExcludedIn gr rep excl s p t then
      let b : IndexAtom := { fact := B }
      b :: releaseGuardedIn gr rep excl b
    else []
  | _ => []

theorem releaseGuardedIn_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h)
    {rep : Nat → Nat} (hrep : ∀ s, ρ (rep s) = ρ s)
    {excl : GuardTag → List Nat}
    (hexcl : ∀ t r, r ∈ excl t → ∃ f ∈ k.values, noTag f.contents t = true ∧ rep f.slot = r) :
    ∀ (a : IndexAtom), a.cond = none → a.fact.HoldsAt ε ρ h →
      IndexHolds ε (releaseGuardedIn (guardReads k.links) rep excl a) ρ h
  | ⟨.guarded s p t B, none, _⟩, _, hat => by
    simp only [releaseGuardedIn]
    split
    · rename_i hex
      obtain ⟨v, hv, hor⟩ := hat
      have hB : B.HoldsAt ε ρ h := hor.resolve_left (guardExcludedIn_ne hk hrep hexcl hex hv)
      intro b hb hc
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hB
      · exact releaseGuardedIn_holds hk hrep hexcl { fact := B } rfl hB b hb hc
    · intro b hb; cases hb
  | ⟨.guarded _ _ _ _, some _, _⟩, h, _ => by cases h
  | ⟨.index _, _, _⟩, _, _ | ⟨.length _ _, _, _⟩, _, _ | ⟨.bound _ _ _, _, _⟩, _, _
  | ⟨.int _, _, _⟩, _, _ | ⟨.pastSafe _, _, _⟩, _, _ | ⟨.linear _, _, _⟩, _, _
  | ⟨.either _ _, _, _⟩, _, _ | ⟨.element _ _ _, _, _⟩, _, _ | ⟨.fieldRead _ _ _, _, _⟩, _, _
  | ⟨.every _ _ _ _, _, _⟩, _, _ | ⟨.atIndex _ _ _ _ _, _, _⟩, _, _
  | ⟨.apart _ _, _, _⟩, _, _ | ⟨.spineApart _ _ _ _, _, _⟩, _, _ | ⟨.same _ _, _, _⟩, _, _ =>
    fun b hb _ => by simp [releaseGuardedIn] at hb

def unguardedInstances (k : Knowledge) : Knowledge :=
  if k.values.isEmpty || !k.indices.any (fun a => a.cond.isNone && match a.fact with | .guarded .. => true | _ => false) then k else
  let gr := guardReads k.links
  let rep := HeapLinks.rep (HeapLinks.classes k.links)
  let exclOf := fun (t : GuardTag) =>
    (k.values.filterMap fun f => if noTag f.contents t then some (rep f.slot) else none).eraseDups
  let exNull := exclOf .null
  let exUndef := exclOf .undef
  let exTru := exclOf .tru
  let exFls := exclOf .fls
  let exNotNull := exclOf .notNull
  let exNotUndef := exclOf .notUndef
  let exNotTru := exclOf .notTru
  let exNotFls := exclOf .notFls
  let excl : GuardTag → List Nat := fun
    | .null => exNull
    | .undef => exUndef
    | .tru => exTru
    | .fls => exFls
    | .notNull => exNotNull
    | .notUndef => exNotUndef
    | .notTru => exNotTru
    | .notFls => exNotFls
  let u := (k.indices.flatMap (releaseGuardedIn gr rep excl)).eraseDups.filter (!k.indices.contains ·)
  if u.isEmpty then k else { k with indices := k.indices ++ u }

theorem unguardedInstances_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (unguardedInstances k) ε ρ h := by
  unfold unguardedInstances
  split
  · exact hk
  · dsimp only
    split
    · exact hk
    · refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
      rcases List.mem_append.mp ha with ha | ha
      · exact hk.2.2.2.2.2 a ha hc
      · have ha' := List.mem_eraseDups.mp (List.mem_filter.mp ha).1
        obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp ha'
        have hrep := HeapLinks.rep_eq (HeapLinks.classes_one hk.2.2.1)
        have hexcl : ∀ t r, r ∈ (match t with
            | .null => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .null then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .undef => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .undef then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .tru => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .tru then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .fls => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .fls then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .notNull => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .notNull then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .notUndef => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .notUndef then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .notTru => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .notTru then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups
            | .notFls => (k.values.filterMap fun (f : HeapFacts.Fact) => if noTag f.contents .notFls then some (HeapLinks.rep (HeapLinks.classes k.links) f.slot) else none).eraseDups) →
            ∃ f ∈ k.values, noTag f.contents t = true ∧ HeapLinks.rep (HeapLinks.classes k.links) f.slot = r := by
          intro t r hr
          cases t <;> (
            have hr' := List.mem_eraseDups.mp hr
            obtain ⟨f, hf, hfm⟩ := List.mem_filterMap.mp hr'
            split at hfm
            · rename_i hnt; simp only [Option.some.injEq] at hfm; exact ⟨f, hf, hnt, hfm⟩
            · cases hfm)
        cases hbc : b.cond with
        | none => exact releaseGuardedIn_holds hk hrep hexcl b hbc (hk.2.2.2.2.2 b hb (by rw [hbc]; intro _ hc'; cases hc')) a hm hc
        | some _ => cases b with | mk bf bc bn => simp only at hbc; subst hbc; cases bf <;> simp [releaseGuardedIn] at hm

/-- The runtime tag test and answer that excludes a guard tag: `null` (`isNul = false`),
`undefined` (`isUndef = false`), Boolean (`isBool = false`), or their negations. -/
def tagOfGuard : GuardTag → Option (Tag × Bool)
  | .null => some (.isNul, false)
  | .undef => some (.isUndef, false)
  | .tru => some (.isBool, false)
  | .fls => some (.isBool, false)
  | .notNull => some (.isNul, true)
  | .notUndef => some (.isUndef, true)
  | .notTru | .notFls => none

/-- Whether a plain type excludes values satisfying the guard tag. -/
@[nospecialize] def typeExcludes (G : NormalGraph ι) (A : Ty ι) (t : GuardTag) : Bool :=
  match tagOfGuard t with
  | none => false
  | some (tag, ans) => G.plainTy A && (expand G A).all fun c => tagClause tag c == some ans

theorem typeExcludes_ne {G : NormalGraph ι} {A : Ty ι} {t : GuardTag} {v : Val} {n : Nat} {W : WorldT n}
    (hex : typeExcludes G A t = true) (hv : meaning G A n W v) : ¬ t.holds v := by
  cases t with
  | notTru | notFls => simp [typeExcludes, tagOfGuard] at hex
  | null | undef | tru | fls | notNull | notUndef =>
    simp only [typeExcludes, tagOfGuard, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hex
    have hq := answers_sound (show Answers G A _ _ from ⟨hex.1, hex.2⟩) hv
    cases v <;> simp_all [GuardTag.holds, tagHolds]

/-- Guarded facts on bare slots whose leading guard is excluded by the slot's
type in `Γ`, stripped recursively. -/
@[nospecialize] def releaseTypedGuarded (G : NormalGraph ι) (Γ : List (Ty ι)) : IndexAtom → List IndexAtom
  | ⟨.guarded s [] t B, none, _⟩ =>
    match Γ[s]? with
    | some A =>
      if typeExcludes G A t then
        let b : IndexAtom := { fact := B }
        b :: releaseTypedGuarded G Γ b
      else []
    | none => []
  | _ => []

theorem releaseTypedGuarded_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G Γ ρ n W) :
    ∀ (a : IndexAtom), a.cond = none → a.fact.HoldsAt ε ρ h →
      IndexHolds ε (releaseTypedGuarded G Γ a) ρ h
  | ⟨.guarded s [] t B, none, _⟩, _, hat => by
    simp only [releaseTypedGuarded]
    cases hA : Γ[s]? with
    | none => intro b hb; cases hb
    | some A =>
      simp only
      split
      · rename_i hex
        obtain ⟨v, hv, hor⟩ := hat
        simp only [readGuard, Option.some.injEq] at hv
        have hne : ¬ t.holds v := hv ▸ typeExcludes_ne hex (he.2 s A hA)
        have hB : B.HoldsAt ε ρ h := hor.resolve_left hne
        intro b hb hc
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hB
        · exact releaseTypedGuarded_holds he { fact := B } rfl hB b hb hc
      · intro b hb; cases hb
  | ⟨.guarded _ (_ :: _) _ _, none, _⟩, _, _ => fun b hb _ => by simp [releaseTypedGuarded] at hb
  | ⟨.guarded _ _ _ _, some _, _⟩, h, _ => by cases h
  | ⟨.index _, _, _⟩, _, _ | ⟨.length _ _, _, _⟩, _, _ | ⟨.bound _ _ _, _, _⟩, _, _
  | ⟨.int _, _, _⟩, _, _ | ⟨.pastSafe _, _, _⟩, _, _ | ⟨.linear _, _, _⟩, _, _
  | ⟨.either _ _, _, _⟩, _, _ | ⟨.element _ _ _, _, _⟩, _, _ | ⟨.fieldRead _ _ _, _, _⟩, _, _
  | ⟨.every _ _ _ _, _, _⟩, _, _ | ⟨.atIndex _ _ _ _ _, _, _⟩, _, _
  | ⟨.apart _ _, _, _⟩, _, _ | ⟨.spineApart _ _ _ _, _, _⟩, _, _ | ⟨.same _ _, _, _⟩, _, _ =>
    fun b hb _ => by simp [releaseTypedGuarded] at hb

/-- Knowledge with every unconditional guarded fact whose guard slot's type
in `Γ` excludes the guard tag released. -/
@[nospecialize] def unguardedByTypes (G : NormalGraph ι) (Γ : List (Ty ι)) (k : Knowledge) : Knowledge :=
  if !k.indices.any (fun a => a.cond.isNone && match a.fact with | .guarded _ [] _ _ => true | _ => false) then k else
  let u := (k.indices.flatMap (releaseTypedGuarded G Γ)).eraseDups.filter (!k.indices.contains ·)
  if u.isEmpty then k else { k with indices := k.indices ++ u }

theorem unguardedByTypes_holds {G : NormalGraph ι} {Γ : List (Ty ι)} {k : Knowledge} {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ε ρ h) : Holds (unguardedByTypes G Γ k) ε ρ h := by
  unfold unguardedByTypes
  split
  · exact hk
  · dsimp only
    split
    · exact hk
    · refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => ?_⟩
      rcases List.mem_append.mp ha with ha | ha
      · exact hk.2.2.2.2.2 a ha hc
      · have ha' := List.mem_eraseDups.mp (List.mem_filter.mp ha).1
        obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp ha'
        cases hbc : b.cond with
        | none => exact releaseTypedGuarded_holds he b hbc (hk.2.2.2.2.2 b hb (by rw [hbc]; intro _ hc'; cases hc')) a hm hc
        | some _ => cases b with | mk bf bc bn => simp only at hbc; subst hbc; cases bf <;> simp [releaseTypedGuarded] at hm

/-- Release every unconditional `.either` in `eithers` whose opposite linear arm
is contradicted by `K`, checking each distinct linear arm once. -/
def releaseEithersIn (K : Linear.Known Term) (eithers : List IndexAtom) : List IndexAtom :=
  let linearArms := (eithers.flatMap fun a => match a.fact with
    | .either A B =>
      (match A with | .linear _ => [A] | _ => []) ++
      (match B with | .linear _ => [B] | _ => [])
    | _ => []).eraseDups
  if linearArms.isEmpty then [] else
  let contra := linearArms.filter (contradictsIn K)
  if contra.isEmpty then [] else
  eithers.flatMap fun a => match a with
    | ⟨.either A B, none, _⟩ =>
      (if contra.contains B then [{ fact := A }] else []) ++
      (if contra.contains A then [{ fact := B }] else [])
    | _ => []

theorem releaseEithersIn_holds {K : Linear.Known Term} {as eithers : List IndexAtom} {ρ : Env} {h : Heap}
    (hK : K.Holds (termValuation ε ρ h)) (ha : IndexHolds ε as ρ h) (hsub : ∀ b ∈ eithers, b ∈ as) :
    IndexHolds ε (releaseEithersIn K eithers) ρ h := by
  unfold releaseEithersIn
  dsimp only
  split
  · intro _ hm; cases hm
  · split
    · intro _ hm; cases hm
    · intro a hm _
      obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp hm
      cases b with
      | mk bf bc bn =>
        cases bc with
        | some _ => cases bf <;> simp at hm
        | none =>
          cases bf with
          | either A B =>
            have hor := ha _ (hsub _ hb) (fun _ hc => by cases hc)
            rcases List.mem_append.mp hm with hm | hm
            · split at hm
              · rename_i hc
                simp only [List.mem_singleton] at hm; subst hm
                have hct := (List.mem_filter.mp (List.contains_iff_mem.mp hc)).2
                exact hor.resolve_right (fun hB => contradictsIn_sound hK hct hB)
              · cases hm
            · split at hm
              · rename_i hc
                simp only [List.mem_singleton] at hm; subst hm
                have hct := (List.mem_filter.mp (List.contains_iff_mem.mp hc)).2
                exact hor.resolve_left (fun hA => contradictsIn_sound hK hct hA)
              · cases hm
          | _ => simp at hm

def withElements (k : Knowledge) : Knowledge :=
  let k := unguardedInstances (elementInstances k)
  let eithers := k.indices.filter fun a => a.cond.isNone && match a.fact with
    | .either A B => !k.indices.contains { fact := A } && !k.indices.contains { fact := B }
    | _ => false
  if eithers.isEmpty then k else
  let K := Linear.Known.build (linearRaw k.indices) []
  let released := releaseEithersIn K eithers
  if released.isEmpty then k else
  let lowered := (released ++ lowerAtoms k.links released).eraseDups.filter (!k.indices.contains ·)
  if lowered.isEmpty then k else
  let k1 := { k with indices := k.indices ++ lowered }
  if lowered.any (fun a => a.cond.isNone && match a.fact with | .atIndex .. | .every .. => true | _ => false) then
    elementInstances k1
  else k1

theorem withElements_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (withElements k) ε ρ h := by
  have hk0 := unguardedInstances_holds (elementInstances_holds hk)
  unfold withElements
  generalize unguardedInstances (elementInstances k) = k0 at hk0 ⊢
  dsimp only
  split
  · exact hk0
  · have hrel : IndexHolds ε (releaseEithersIn (Linear.Known.build (linearRaw k0.indices) [])
        (k0.indices.filter fun a => a.cond.isNone && match a.fact with
          | .either A B => !k0.indices.contains { fact := A } && !k0.indices.contains { fact := B }
          | _ => false)) ρ h :=
      releaseEithersIn_holds (Linear.Known.build_holds (linearRaw_holds hk0.2.2.2.2.2) (by simp))
        hk0.2.2.2.2.2 fun _ hb => (List.mem_filter.mp hb).1
    generalize releaseEithersIn (Linear.Known.build (linearRaw k0.indices) [])
        (k0.indices.filter fun a => a.cond.isNone && match a.fact with
          | .either A B => !k0.indices.contains { fact := A } && !k0.indices.contains { fact := B }
          | _ => false) = released at hrel ⊢
    split
    · exact hk0
    · split
      · exact hk0
      · have hk1 : Holds { k0 with indices := k0.indices ++ (released ++ lowerAtoms k0.links released).eraseDups.filter (!k0.indices.contains ·) } ε ρ h := by
          refine ⟨hk0.1, hk0.2.1, hk0.2.2.1, hk0.2.2.2.1, hk0.2.2.2.2.1, fun a ha hc => ?_⟩
          rcases List.mem_append.mp ha with ha | ha
          · exact hk0.2.2.2.2.2 a ha hc
          · have ha' := List.mem_eraseDups.mp (List.mem_filter.mp ha).1
            rcases List.mem_append.mp ha' with ha' | ha'
            · exact hrel a ha' hc
            · exact lowerAtoms_holds hk0.2.2.1 hrel a ha' hc
        split
        · exact elementInstances_holds hk1
        · exact hk1

end Verification.HeapKnowledge
