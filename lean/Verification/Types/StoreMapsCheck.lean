import Verification.Types.StoreMaps
import Std.Data.HashMap

/-! # Store maps: the check

A decidable procedure that finds a store map (`StoreMaps.StoreMap`) between
two graphs from a pair of root types, and its soundness.

`matchStores G H canon fuel I A` runs in two phases:

1. **Proposal** (`propose`, untrusted): a worklist over pairs of labels from
   the roots, structural on `fuel`, builds a label map `φ` as a hash map.
   A pair's rows give the pairs of their operands: clauses are paired by
   their skeleton (`skeleton`: the clause with each operand replaced by its
   size, so constructor, keys, literals, flags and effects included), else
   by their skeleton with the keyed conjunctions in key order (`keyOrder`),
   and a union's members by the shape of their rows to depth two
   (`sameDeepShape`: the row's shape and its operands' members' shapes),
   first unused match first. Nothing about the proposal is relied on.
2. **Check** (`checkMap`, proved): every label of the map's domain has its
   image's kind, a scheme mapped to the image's scheme (unqualified), a meet
   mapped to the image's meet, its further meet parameters renamed as sets,
   and, for a clause row, its clauses and the image's related both ways;
   the domain is closed under reads, meet parts and binders and holds the
   built-ins' types, which are related; the map is injective (an inverse
   map's check); the roots are in the domain, and the image root is a union
   of the same members as the root renamed. A clause and an image clause
   are related (`clauseRelB`) where each operand `S` maps to the image
   clause's first operand of the members of `S.map φ`, else to
   `canon (S.map φ)` (`pairOperand`; `canon` any function keeping members),
   each such image a union of those members, and the mapped clause is the
   image clause up to the order of a record's or a dictionary's
   conjunctions (`reorderedB`, `StoreMaps.Reordered`).

**Soundness** (`matchStores_sound`, proved): an accepted check gives a
`StoreMap G H` whose region holds the root and whose map renames the root
to a union with the image root's members, for graphs whose environments
agree (both empty, as every equation graph's).

**Incompleteness.** The check refuses where the proposal pairs wrongly:
unions with two members of one row shape to depth two, two clauses of one
skeleton in a row, or two conjuncts of one key in a clause, paired in the
other order; a qualified scheme (nonempty resolution, whose domains the
check does not relate); built-ins in one graph only; an image clause
holding two operands of the same members in different orders, and an
operand of a scheme or a meet's parameters not in `canon`'s normal form.

**Cost.** With `R` the reachable rows, `s` their total size and `k` the
largest number of clauses of a row: the proposal is `O(s · k)` hash-map
operations (each clause scans its image row for its skeleton), the check
`O(s · k)` clause comparisons, each quadratic in the clause (an operand's
image found among the image clause's operands, a conjunction among the
image's). -/

namespace Verification.StoreMaps
open PositiveGraphs PositiveNormalization PositiveRules

variable {ι κ : Type} [DecidableEq ι] [Hashable ι] [DecidableEq κ] [Hashable κ]

/-! ## The proposal -/

/-- A clause's skeleton: each operand replaced by its size. -/
@[nospecialize] def skeleton {α : Type} (c : Clause (List α)) : Clause Nat := c.map List.length

/-- A row's shape: its kind, whether it is a scheme or a meet, and its
clauses' skeletons. -/
@[nospecialize] def shapeKey {α : Type} (G : NormalGraph α) (i : α) :
    Option ParameterKind × Bool × Bool × List (Clause Nat) :=
  (G.parameterKinds i, (G.schemes i).isSome, (G.meets i).isSome, (G.rows i).map skeleton)

abbrev Shape := Option ParameterKind × Bool × Bool × List (Clause Nat)

/-- The shapes of the members of a row's operands. -/
@[nospecialize] def memberShapes {α : Type} (G : NormalGraph α) (i : α) : List Shape :=
  (G.rows i).flatMap fun c => c.operands.flatMap (·.map (shapeKey G))

/-- A row's shape to depth two: its shape and its operands' members'
shapes. -/
@[nospecialize] def deepShape {α : Type} (G : NormalGraph α) (i : α) : Shape × List Shape :=
  (shapeKey G i, memberShapes G i)

/-- Two rows of one shape to depth two: the same shape, and their operands'
members of the same shapes as sets (an operand's order is the store's). -/
@[nospecialize] def sameDeepShape (d d' : Shape × List Shape) : Bool :=
  decide (d'.1 = d.1) && d.2.all (fun x => d'.2.contains x) && d'.2.all (fun x => d.2.contains x)

/-- A shape's fingerprint: whether it is a scheme or a meet and its
clauses' operand sizes, equal for equal shapes. -/
@[nospecialize] def shapePrint (d : Shape) : UInt64 :=
  hash (d.2.1, d.2.2.1, d.2.2.2.map (·.operands))

/-- A deep shape's fingerprint: its shape's, and its members' shapes' as a
sorted set, equal for two deep shapes `sameDeepShape` relates. -/
@[nospecialize] def deepFingerprint (d : Shape × List Shape) : UInt64 :=
  hash (shapePrint d.1, ((d.2.map shapePrint).mergeSort (· ≤ ·)).eraseReps)

/-- Pairs of a union's members with an image union's: each member with the
first unused image member of the same row shape to depth two. Each member's
shape is computed once, and the image members are looked up among those of
its fingerprint, in order. -/
@[nospecialize] def pairUnion (G : NormalGraph ι) (H : NormalGraph κ) (S : List ι) (S' : List κ) :
    List (ι × κ) :=
  match S, S' with
  | [j], [j'] => [(j, j')]
  | _, _ =>
    let buckets : Std.HashMap UInt64 (List (κ × (Shape × List Shape))) :=
      S'.reverse.foldl (fun m j' =>
        let d := deepShape H j'
        let k := deepFingerprint d
        m.insert k ((j', d) :: m.getD k [])) {}
    (S.foldl (fun (acc : List (ι × κ) × Std.HashMap UInt64 (List (κ × (Shape × List Shape)))) j =>
      let d := deepShape G j
      let k := deepFingerprint d
      let bucket := acc.2.getD k []
      match bucket.find? (fun (_, d') => sameDeepShape d d') with
      | some (j', _) => ((j, j') :: acc.1, acc.2.insert k (bucket.eraseP (·.1 == j')))
      | none => acc) ([], buckets)).1

/-- Pairs of related operand lists, position by position. -/
@[nospecialize] def pairOps (G : NormalGraph ι) (H : NormalGraph κ) (ops : List (List ι))
    (ops' : List (List κ)) : List (ι × κ) :=
  (ops.zip ops').flatMap fun (S, S') => pairUnion G H S S'

/-- A clause with its keyed conjunctions in key order (its fields, views,
optional fields and methods, a dictionary's index views and cells), so two
clauses alike up to their order (`Reordered`) list them alike, keys
repeated aside. -/
@[nospecialize] def keyOrder {α : Type} : Clause α → Clause α
  | .refs a bs vs os ms ks st => .refs (byKey a) bs (byKey vs) (os.mergeSort fun x y => toString x.key ≤ toString y.key)
      (ms.mergeSort fun x y => toString x.key ≤ toString y.key) ks st
  | .dict a bs vs ds os ms ks cs st => .dict (byKey a) bs (byKey vs) (byIndex ds)
      (os.mergeSort fun x y => toString x.key ≤ toString y.key) (ms.mergeSort fun x y => toString x.key ≤ toString y.key)
      ks (byIndex cs) st
  | c => c
where
  byKey {β : Type} (l : List (PropKey × β)) : List (PropKey × β) := l.mergeSort fun x y => toString x.1 ≤ toString y.1
  byIndex {β : Type} (l : List (IndexKeys × β)) : List (IndexKeys × β) :=
    l.mergeSort fun x y => reprStr x.1 ≤ reprStr y.1

/-- Pairs of two clause lists' operands, each clause with the first image
clause of its skeleton, or else of its skeleton in key order, their
operands then paired in key order. -/
@[nospecialize] def pairClauses (G : NormalGraph ι) (H : NormalGraph κ) (L : List (Clause (List ι)))
    (L' : List (Clause (List κ))) : List (ι × κ) :=
  L.flatMap fun c => match L'.find? (fun c' => decide (skeleton c' = skeleton c)) with
    | some c' => pairOps G H c.operands c'.operands
    | none => match L'.find? (fun c' => decide (skeleton (keyOrder c') = skeleton (keyOrder c))) with
      | some c' => pairOps G H (keyOrder c).operands (keyOrder c').operands
      | none => []

/-- The pairs a label pair's rows give. -/
@[nospecialize] def childPairs (G : NormalGraph ι) (H : NormalGraph κ) (i : ι) (i' : κ) : List (ι × κ) :=
  let rows := pairClauses G H (G.rows i) (H.rows i')
  let meets := match G.meets i, H.meets i' with
    | some (p, cs), some (p', cs') => (p, p') :: pairClauses G H cs cs' ++
        pairUnion G H (G.meetParams i) (H.meetParams i')
    | _, _ => []
  let schemes := match G.schemes i, H.schemes i' with
    | some s, some s' => s.binders.zip s'.binders ++ (s.bounds.zip s'.bounds).map (fun (b, b') => (b.1, b'.1)) ++
        pairOps G H (schemeOps s) (schemeOps s')
    | _, _ => []
  rows ++ meets ++ schemes

/-- The proposal's worklist: each pair whose label is not yet mapped maps it
and adds the pairs its rows give. -/
@[nospecialize] def propose (G : NormalGraph ι) (H : NormalGraph κ) :
    Nat → List (ι × κ) → Std.HashMap ι κ → Std.HashMap ι κ
  | 0, _, mp => mp
  | _ + 1, [], mp => mp
  | fuel + 1, (i, i') :: rest, mp =>
    if mp.contains i then propose G H fuel rest mp
    else propose G H fuel (childPairs G H i i' ++ rest) (mp.insert i i')

/-! ## The check -/

/-- Two lists of the same members. -/
@[nospecialize] def sameB {α : Type} [DecidableEq α] (l l' : List α) : Bool :=
  l.all (fun x => decide (x ∈ l')) && l'.all fun x => decide (x ∈ l)

/-- **Two clauses alike up to the order of their conjunctions**, decided
(`Reordered`). -/
@[nospecialize] def reorderedB {α : Type} [DecidableEq α] : Clause α → Clause α → Bool
  | .refs a bs vs os ms ks st, c' => match c' with
    | .refs a' bs' vs' os' ms' ks' st' => sameB a a' && sameB bs bs' && sameB vs vs' && sameB os os' &&
        sameB ms ms' && sameB ks ks' && sameB st st'
    | _ => false
  | .dict a bs vs ds os ms ks cs st, c' => match c' with
    | .dict a' bs' vs' ds' os' ms' ks' cs' st' => sameB a a' && sameB bs bs' && sameB vs vs' && sameB ds ds' &&
        sameB os os' && sameB ms ms' && sameB ks ks' && sameB cs cs' && sameB st st'
    | _ => false
  | c, c' => decide (c' = c)

theorem sameB_sound {α : Type} [DecidableEq α] {l l' : List α} (h : sameB l l' = true) : SameMembers l l' := by
  simp only [sameB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun x => ⟨h.1 x, h.2 x⟩

/-- The decision is sound (proved). -/
theorem reorderedB_sound {α : Type} [DecidableEq α] {c c' : Clause α} (h : reorderedB c c' = true) :
    Reordered c c' := by
  cases c
  case refs a bs vs os ms ks st =>
    cases c' <;> simp only [reorderedB, Bool.and_eq_true, reduceCtorEq] at h
    case refs a' bs' vs' os' ms' ks' st' =>
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
      exact ⟨a', bs', vs', os', ms', ks', st', rfl, sameB_sound h1, sameB_sound h2, sameB_sound h3,
        sameB_sound h4, sameB_sound h5, sameB_sound h6, sameB_sound h7⟩
  case dict a bs vs ds os ms ks cs st =>
    cases c' <;> simp only [reorderedB, Bool.and_eq_true, reduceCtorEq] at h
    case dict a' bs' vs' ds' os' ms' ks' cs' st' =>
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
      exact ⟨a', bs', vs', ds', os', ms', ks', cs', st', rfl, sameB_sound h1, sameB_sound h2, sameB_sound h3,
        sameB_sound h4, sameB_sound h5, sameB_sound h6, sameB_sound h7, sameB_sound h8, sameB_sound h9⟩
  all_goals (simp only [reorderedB, decide_eq_true_eq] at h; exact h)

section Check
variable (G : NormalGraph ι) (H : NormalGraph κ) (φ : ι → κ) (inD : ι → Bool) (σ : List ι → List κ)

/-- Two label lists of the same members, the first renamed. -/
@[nospecialize] def sameMembersB (S : List ι) (T : List κ) : Bool :=
  T.all (fun x => decide (x ∈ S.map φ)) && (S.map φ).all fun x => decide (x ∈ T)

/-- The operand map a clause pair is checked at: an operand to the image
clause's first operand of its members renamed, else to `σ`'s. -/
@[nospecialize] def pairOperand (c' : Clause (List κ)) (S : List ι) : List κ :=
  (c'.operands.find? fun T => sameMembersB φ S T).getD (σ S)

/-- One clause and an image clause related: each operand, and the empty
one, mapped (`pairOperand`) to a union of its members renamed, and the
mapped clause the image clause up to the order of its conjunctions
(`reorderedB`). -/
@[nospecialize] def clauseRelB (c : Clause (List ι)) (c' : Clause (List κ)) : Bool :=
  ([] :: c.operands).all (fun S => sameMembersB φ S (pairOperand φ σ c' S)) &&
    reorderedB (c.map (pairOperand φ σ c')) c'

/-- Two clause lists related both ways (`clauseRelB`). -/
@[nospecialize] def rowsRelB (L : List (Clause (List ι))) (L' : List (Clause (List κ))) : Bool :=
  L.all (fun c => L'.any fun c' => clauseRelB φ σ c c') &&
    L'.all (fun c' => L.any fun c => clauseRelB φ σ c c')

@[nospecialize] def schemeOkB (i : ι) : Bool :=
  match G.schemes i, H.schemes (φ i) with
  | none, none => true
  | some s, some s' => decide (s.resolution = []) && decide (s' = mapSchemeWith φ σ s) &&
      s.binders.all inD && s.bounds.all (fun b => inD b.1)
  | _, _ => false

@[nospecialize] def meetOkB (i : ι) : Bool :=
  match G.meets i, H.meets (φ i) with
  | none, none => true
  | some (p, cs), some (p', cs') => decide (p' = φ p) && rowsRelB φ σ cs cs'
  | _, _ => false

/-- A label against the inverse map of the labels whose images are their
own (`bind`: parameters and binders): its image's inverse is itself, or it
has none and the label needs none. -/
@[nospecialize] def invOkB (inv : κ → Option ι) (bind : ι → Bool) (i : ι) : Bool :=
  match inv (φ i) with
  | some a => decide (a = i)
  | none => !bind i

/-- One label of the domain against its image. -/
@[nospecialize] def labelOkB (inv : κ → Option ι) (bind : ι → Bool) (i : ι) : Bool :=
  decide (H.parameterKinds (φ i) = G.parameterKinds i) &&
  schemeOkB G H φ inD σ i && meetOkB G H φ σ i &&
  sameMembersB φ (G.meetParams i) (H.meetParams (φ i)) &&
  (!G.plain i || rowsRelB φ σ (G.rows i) (H.rows (φ i))) &&
  (reads G i).all inD && (meetParts G i).all inD &&
  invOkB φ inv bind i

@[nospecialize] def builtinsOkB : Bool :=
  match G.builtins, H.builtins with
  | none, none => true
  | some r, some r' => decide (r'.keys = r.keys) && sameMembersB φ r.proto r'.proto &&
      sameMembersB φ r.unknown r'.unknown && r.proto.all inD && r.unknown.all inD
  | _, _ => false

end Check

/-- The image of a label under a proposed map. -/
@[nospecialize] def mapOf [Inhabited κ] (mp : Std.HashMap ι κ) (i : ι) : κ := mp.getD i default

/-- An operand under a proposed map: its members renamed, in `canon`'s form. -/
@[nospecialize] def opOf [Inhabited κ] (canon : List κ → List κ) (mp : Std.HashMap ι κ) (S : List ι) : List κ :=
  canon (S.map (mapOf mp))

/-- Whether a label of a proposed map's domain is a parameter or a binder of
a scheme of the domain: one whose image no other label may share. -/
@[nospecialize] def bindsOf (G : NormalGraph ι) (keys : List ι) (i : ι) : Bool :=
  G.params i || keys.any fun k => match G.schemes k with
    | some s => s.binders.contains i || s.bounds.any (·.1 == i)
    | none => false

/-- **The check of a proposed map** against the roots `I` and `A`. -/
@[nospecialize] def checkMap [Inhabited κ] (G : NormalGraph ι) (H : NormalGraph κ) (canon : List κ → List κ)
    (mp : Std.HashMap ι κ) (I : List ι) (A : List κ) : Bool :=
  let bind := bindsOf G mp.keys
  let inv : Std.HashMap κ ι := mp.fold (fun acc k v => if bind k then acc.insert v k else acc) {}
  let φ := mapOf mp
  let inD := fun i => mp.contains i
  mp.keys.all (labelOkB G H φ inD (opOf canon mp) (fun k => inv.get? k) bind) &&
    builtinsOkB G H φ inD && I.all inD && sameMembersB φ I A

/-- The proposal's first pairs: the roots', then the built-ins'. -/
@[nospecialize] def startPairs (G : NormalGraph ι) (H : NormalGraph κ) (I : List ι) (A : List κ) : List (ι × κ) :=
  pairUnion G H I A ++ match G.builtins, H.builtins with
    | some r, some r' => pairUnion G H r.proto r'.proto ++ pairUnion G H r.unknown r'.unknown
    | _, _ => []

/-- **The store-map check**: a map proposed from the roots `I` and `A`,
returned where the check accepts it. -/
@[nospecialize] def matchStores [Inhabited κ] (G : NormalGraph ι) (H : NormalGraph κ)
    (canon : List κ → List κ) (fuel : Nat) (I : List ι) (A : List κ) : Option (Std.HashMap ι κ) :=
  let mp := propose G H fuel (startPairs G H I A) {}
  if checkMap G H canon mp I A then some mp else none

/-! ## Soundness -/

section Sound
variable {G : NormalGraph ι} {H : NormalGraph κ} {φ : ι → κ} {inD : ι → Bool} {σ : List ι → List κ}

omit [DecidableEq ι] [Hashable ι] [Hashable κ] in
theorem sameMembersB_sound {S : List ι} {T : List κ} (h : sameMembersB φ S T = true) :
    ∀ x, x ∈ T ↔ x ∈ S.map φ := by
  simp only [sameMembersB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun x => ⟨h.1 x, h.2 x⟩

omit [DecidableEq ι] [Hashable ι] [Hashable κ] in
/-- An accepted clause pair is related (proved): its operand map
(`pairOperand`) agrees with `φ`, checked operand by operand. -/
theorem clauseRelB_sound {c : Clause (List ι)} {c' : Clause (List κ)} (h : clauseRelB φ σ c c' = true) :
    ClauseRel φ c c' := by
  simp only [clauseRelB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨pairOperand φ σ c', fun S hS x => ?_, reorderedB_sound h.2⟩
  have hS' : S ∈ [] :: c.operands := by
    rcases hS with hS | rfl
    · exact List.mem_cons_of_mem _ hS
    · exact List.mem_cons_self
  exact sameMembersB_sound (h.1 S hS') x

omit [DecidableEq ι] [Hashable ι] [Hashable κ] in
theorem rowsRelB_sound {L : List (Clause (List ι))} {L' : List (Clause (List κ))}
    (h : rowsRelB φ σ L L' = true) : RowsRel φ L L' := by
  simp only [rowsRelB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
  · obtain ⟨c', hc', he⟩ := h.1 c hc
    exact ⟨c', hc', clauseRelB_sound he⟩
  · obtain ⟨c, hc, he⟩ := h.2 c' hc'
    exact ⟨c, hc, clauseRelB_sound he⟩

omit [DecidableEq ι] [Hashable ι] [DecidableEq κ] [Hashable κ] in
theorem all_inD {L : List ι} (h : L.all inD = true) : ∀ j ∈ L, inD j = true := by
  simpa only [List.all_eq_true] using h

/-- What one accepted label gives. -/
structure LabelFacts (G : NormalGraph ι) (H : NormalGraph κ) (φ : ι → κ) (inD : ι → Bool)
    (inv : κ → Option ι) (bind : ι → Bool) (i : ι) : Prop where
  kinds : H.parameterKinds (φ i) = G.parameterKinds i
  schemesNone : G.schemes i = none → H.schemes (φ i) = none
  schemes : ∀ s, G.schemes i = some s →
    s.resolution = [] ∧ (∃ σ, Equiv φ σ (schemeOps s) ∧ H.schemes (φ i) = some (mapSchemeWith φ σ s)) ∧
    (∀ b ∈ s.binders, inD b = true) ∧ ∀ b ∈ s.bounds, inD b.1 = true
  meetsNone : G.meets i = none → H.meets (φ i) = none
  meets : ∀ p cs, G.meets i = some (p, cs) → ∃ cs', H.meets (φ i) = some (φ p, cs') ∧ RowsRel φ cs cs'
  meetParams : ∀ x, x ∈ H.meetParams (φ i) ↔ x ∈ (G.meetParams i).map φ
  rows : G.plain i = true → RowsRel φ (G.rows i) (H.rows (φ i))
  reads : ∀ j ∈ PositiveRules.reads G i, inD j = true
  parts : ∀ j ∈ meetParts G i, inD j = true
  invUnique : ∀ a, inv (φ i) = some a → a = i
  invBind : bind i = true → inv (φ i) = some i

omit [Hashable ι] [Hashable κ] in
theorem labelOkB_sound (hσ : ∀ S x, x ∈ σ S ↔ x ∈ S.map φ) {inv : κ → Option ι} {bind : ι → Bool} {i : ι}
    (h : labelOkB G H φ inD σ inv bind i = true) : LabelFacts G H φ inD inv bind i := by
  simp only [labelOkB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk, hs⟩, hm⟩, hmp⟩, hr⟩, hrd⟩, hpt⟩, hinv⟩ := h
  have hE : ∀ ops, Equiv φ σ ops := fun _ S _ x => hσ S x
  have hinv1 : ∀ a, inv (φ i) = some a → a = i := by
    intro a ha
    unfold invOkB at hinv
    rw [ha] at hinv
    simpa using hinv
  have hinv2 : bind i = true → inv (φ i) = some i := by
    intro hb
    unfold invOkB at hinv
    cases hx : inv (φ i) with
    | none => rw [hx] at hinv; simp [hb] at hinv
    | some a => rw [hx] at hinv; simp only [decide_eq_true_eq] at hinv; rw [hinv]
  refine ⟨hk, ?_, ?_, ?_, ?_, sameMembersB_sound hmp, ?_, all_inD hrd, all_inD hpt, hinv1, hinv2⟩
  · intro hn
    unfold schemeOkB at hs
    rw [hn] at hs
    cases h' : H.schemes (φ i) with
    | none => rfl
    | some _ => rw [h'] at hs; exact absurd hs (by simp)
  · intro s hss
    unfold schemeOkB at hs
    rw [hss] at hs
    cases h' : H.schemes (φ i) with
    | none => rw [h'] at hs; exact absurd hs (by simp)
    | some s' =>
      rw [h'] at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨hres, he⟩, hb⟩, hbb⟩ := hs
      exact ⟨hres, ⟨σ, hE _, by rw [he]⟩, all_inD hb, by simpa only [List.all_eq_true] using hbb⟩
  · intro hn
    unfold meetOkB at hm
    rw [hn] at hm
    cases h' : H.meets (φ i) with
    | none => rfl
    | some _ => rw [h'] at hm; exact absurd hm (by simp)
  · intro p cs hpc
    unfold meetOkB at hm
    rw [hpc] at hm
    cases h' : H.meets (φ i) with
    | none => rw [h'] at hm; exact absurd hm (by simp)
    | some pc' =>
      obtain ⟨p', cs'⟩ := pc'
      rw [h'] at hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      exact ⟨cs', by rw [hm.1], rowsRelB_sound hm.2⟩
  · intro hp
    rcases hr with hr | hr
    · rw [hp] at hr; exact absurd hr (by simp)
    · exact rowsRelB_sound hr

end Sound

/-- **The check is sound** (proved): an accepted proposed map is a store map
on the labels it maps, holding the roots, renaming the root `I` to a union
of `A`'s members, where the graphs' environments agree. -/
theorem checkMap_sound [Inhabited κ] {G : NormalGraph ι} {H : NormalGraph κ} {canon : List κ → List κ}
    (hcanon : ∀ S x, x ∈ canon S ↔ x ∈ S) (henv : ∀ p q, H.env.1 q = G.env.1 p)
    {mp : Std.HashMap ι κ} {I : List ι} {A : List κ} (h : checkMap G H canon mp I A = true) :
    ∃ m : StoreMap G H, (∀ j ∈ I, m.D j) ∧ ∀ x, x ∈ A ↔ x ∈ I.map m.φ := by
  simp only [checkMap, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hall, hb⟩, hI⟩, hA⟩ := h
  let bind := bindsOf G mp.keys
  let inv : Std.HashMap κ ι := mp.fold (fun acc k v => if bind k then acc.insert v k else acc) {}
  let φ := mapOf mp
  let inD : ι → Bool := fun i => mp.contains i
  have hσ : ∀ S x, x ∈ opOf canon mp S ↔ x ∈ S.map φ := fun S x => hcanon _ x
  have hfacts : ∀ i, inD i = true → LabelFacts G H φ inD (fun k => inv.get? k) bind i := by
    intro i hi
    have hk : i ∈ mp.keys := Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_contains.mpr hi)
    exact labelOkB_sound hσ ((List.all_eq_true.mp hall) i hk)
  have hE : ∀ ops, Equiv φ (opOf canon mp) ops := fun _ S _ x => hσ S x
  unfold builtinsOkB at hb
  refine ⟨{
    φ := φ
    D := fun i => inD i = true
    inj := fun a b ha hb hbd he => by
      have hba : bind a = true := by
        show (G.params a || mp.keys.any _) = true
        rcases hbd with hp | ⟨k, hk, s, hs, hm⟩
        · simp [hp]
        · refine Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨k, ?_, ?_⟩))
          · exact Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_contains.mpr hk)
          · simp only [hs, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq]
            exact hm
      have h1 := (hfacts a ha).invBind hba
      rw [he] at h1
      exact (hfacts b hb).invUnique a h1
    reads := fun i hi j hj => (hfacts i hi).reads j hj
    parts := fun i hi j hj => (hfacts i hi).parts j hj
    binders := fun i hi s hs => by
      obtain ⟨-, -, h1, h2⟩ := (hfacts i hi).schemes s hs
      exact ⟨h1, h2⟩
    builtins := by
      cases hg : G.builtins with
      | none =>
        rw [hg] at hb
        cases hh : H.builtins with
        | none => trivial
        | some _ => rw [hh] at hb; exact absurd hb (by simp)
      | some r =>
        rw [hg] at hb
        cases hh : H.builtins with
        | none => rw [hh] at hb; exact absurd hb (by simp)
        | some r' =>
          rw [hh] at hb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          exact ⟨hb.1.1.1.1, sameMembersB_sound hb.1.1.1.2, sameMembersB_sound hb.1.1.2⟩
    builtinsIn := fun r hr => by
      rw [hr] at hb
      cases hh : H.builtins with
      | none => rw [hh] at hb; exact absurd hb (by simp)
      | some r' =>
        rw [hh] at hb
        simp only [Bool.and_eq_true] at hb
        exact ⟨all_inD hb.1.2, all_inD hb.2⟩
    kinds := fun i hi => (hfacts i hi).kinds
    schemesNone := fun i hi hs => (hfacts i hi).schemesNone hs
    schemes := fun i hi s hs => ((hfacts i hi).schemes s hs).2.1
    meetsNone := fun i hi hs => (hfacts i hi).meetsNone hs
    meets := fun i hi p cs hpc => (hfacts i hi).meets p cs hpc
    meetParams := fun i hi => (hfacts i hi).meetParams
    rows := fun i hi hp => (hfacts i hi).rows hp
    allowed := fun i hi s hs s' hs' As => by
      obtain ⟨hres, ⟨σ', _, he⟩, -⟩ := (hfacts i hi).schemes s hs
      rw [he] at hs'
      cases hs'
      exact iff_of_true (H.domain.ordinary_allowed _ As hres) (G.domain.ordinary_allowed s As hres)
    env := fun p _ => henv p (φ p) }, all_inD hI, sameMembersB_sound hA⟩

/-- **The store-map check is sound** (proved): where `matchStores` accepts,
there is a store map from `G` to `H` whose region holds the root `I` and
which renames it to a union of the members of `A`. -/
theorem matchStores_sound [Inhabited κ] {G : NormalGraph ι} {H : NormalGraph κ} {canon : List κ → List κ}
    (hcanon : ∀ S x, x ∈ canon S ↔ x ∈ S) (henv : ∀ p q, H.env.1 q = G.env.1 p)
    {fuel : Nat} {I : List ι} {A : List κ} {mp : Std.HashMap ι κ}
    (h : matchStores G H canon fuel I A = some mp) :
    ∃ m : StoreMap G H, (∀ j ∈ I, m.D j) ∧ ∀ x, x ∈ A ↔ x ∈ I.map m.φ := by
  unfold matchStores at h
  by_cases hc : checkMap G H canon (propose G H fuel (startPairs G H I A) {}) I A = true
  · exact checkMap_sound hcanon henv hc
  · simp only [hc] at h
    exact absurd h (by simp)

omit [DecidableEq ι] [Hashable ι] [DecidableEq κ] [Hashable κ] in
/-- Two empty environments agree (proved): the hypothesis of
`matchStores_sound` for graphs that state no environment. -/
theorem env_empty_agree {G : NormalGraph ι} {H : NormalGraph κ}
    (hG : G.env = ParameterAssignment.empty .mixed) (hH : H.env = ParameterAssignment.empty .mixed) :
    ∀ p q, H.env.1 q = G.env.1 p := by
  intro p q
  rw [hG, hH]
  rfl

end Verification.StoreMaps
