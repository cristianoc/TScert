import Verification.Types.StoreMaps
import Std.Data.HashMap
import Std.Data.HashSet.Lemmas

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

/-- A discriminating structural fingerprint of a clause skeleton, equal for
equal clause skeletons and separating distinct literals and field-key sets. -/
def clausePrint : Clause Nat → UInt64
  | .nul => 1
  | .bool => 2
  | .num => 3
  | .undef => 4
  | .top => 5
  | .source => 6
  | .str => 7
  | .bigint => 8
  | .symbol => 9
  | .int => 10
  | .boolLit b => mixHash 11 (hash b)
  | .numLit b => mixHash 12 (hash b)
  | .strLit s => mixHash 13 (hash s)
  | .bigintLit v => mixHash 14 (hash v)
  | .symbolLit id => mixHash 15 (hash id)
  | .numIn bs => mixHash 16 (hash bs)
  | .strIn ss => mixHash 17 (hash ss)
  | c@(.refs a bs vs os _ _ _) =>
    mixHash 18 (hash (a.map (·.1), bs.map (·.map (·.1)), vs.map (·.1), os.map (·.key), c.operands))
  | c@(.dict a bs vs _ os _ _ _ _) =>
    mixHash 19 (hash (a.map (·.1), bs.map (·.map (·.1)), vs.map (·.1), os.map (·.key), c.operands))
  | c => mixHash 20 (hash c.operands)

/-- A shape's fingerprint: equal for equal shapes. -/
@[nospecialize] def shapePrint (d : Shape) : UInt64 :=
  hash (d.2.1, d.2.2.1, d.2.2.2.map clausePrint)

/-- A depth-two signature of a row, for untrusted union pairing:
its fingerprint, its exact shape, and its distinct operand members' exact
shapes bucketed by `shapePrint`. Equivalent to `sameDeepShape` while running
in O(k) per comparison. -/
structure DeepKey where
  fp : UInt64
  shape : Shape
  prints : List UInt64
  members : Std.HashMap UInt64 (List Shape)

/-- Cache of `(shapeKey, shapePrint)` and `DeepKey` per label, threaded across
one graph's proposal worklist so each label's shape, fingerprint and depth-two
signature are computed at most once. Untrusted: only `checkMap` decides
acceptance. -/
structure ShapeCache (α : Type) [BEq α] [Hashable α] where
  shapes : Std.HashMap α (Shape × UInt64) := {}
  deeps : Std.HashMap α DeepKey := {}

@[nospecialize] def getShape {α : Type} [BEq α] [Hashable α] (G : NormalGraph α)
    (c : ShapeCache α) (i : α) : (Shape × UInt64) × ShapeCache α :=
  match c.shapes.get? i with
  | some s => (s, c)
  | none =>
    let s := shapeKey G i
    let sp := (s, shapePrint s)
    (sp, { c with shapes := c.shapes.insert i sp })

@[nospecialize] def getDeep {α : Type} [BEq α] [Hashable α] (G : NormalGraph α)
    (c : ShapeCache α) (i : α) : DeepKey × ShapeCache α :=
  match c.deeps.get? i with
  | some d => (d, c)
  | none =>
    let ((sh, shp), c) := getShape G c i
    let distinct : Std.HashSet α := (G.rows i).foldl (fun acc cl =>
      cl.operands.foldl (fun acc S => S.foldl (fun s l => s.insert l) acc) acc) {}
    let (members, c) := distinct.fold (fun (acc : Std.HashMap UInt64 (List Shape) × ShapeCache α) l =>
      let ((ls, p), c') := getShape G acc.2 l
      let bucket := acc.1.getD p []
      if bucket.contains ls then (acc.1, c')
      else (acc.1.insert p (ls :: bucket), c')) ({}, c)
    let prints := members.keys.mergeSort (· ≤ ·)
    let key : DeepKey := { fp := hash (shp, prints), shape := sh, prints, members }
    (key, { c with deeps := c.deeps.insert i key })

@[nospecialize] def sameDeepKey (d d' : DeepKey) : Bool :=
  d.fp == d'.fp && d.prints == d'.prints && decide (d.shape = d'.shape) &&
    d.prints.all fun p =>
      let b := d.members.getD p []
      let b' := d'.members.getD p []
      b.length == b'.length && b.all (fun s => b'.contains s) && b'.all (fun s => b.contains s)

/-- Pairs of a union's unmapped members with an image union's, using cached
depth-two keys: skips any member already mapped in `mp` so large shared unions
(such as AST node unions) are paired once instead of on every field reference. -/
@[nospecialize] def pairUnionCached (G : NormalGraph ι) (H : NormalGraph κ)
    (mp : Std.HashMap ι κ) (cG : ShapeCache ι) (cH : ShapeCache κ) (S : List ι) (S' : List κ) :
    List (ι × κ) × ShapeCache ι × ShapeCache κ :=
  match S, S' with
  | [j], [j'] => if mp.contains j then ([], cG, cH) else ([(j, j')], cG, cH)
  | _, _ =>
    let unmapped := S.filter fun j => !mp.contains j
    if unmapped.isEmpty then ([], cG, cH)
    else
      let used : Std.HashSet κ := S.foldl (fun acc j =>
        match mp.get? j with | some j' => acc.insert j' | none => acc) {}
      let avail := S'.filter fun j' => !used.contains j'
      let target := if avail.isEmpty then S' else avail
      let (buckets, cH) := target.reverse.foldl (fun (acc : Std.HashMap UInt64 (List (κ × DeepKey)) × ShapeCache κ) j' =>
        let (d, cH') := getDeep H acc.2 j'
        (acc.1.insert d.fp ((j', d) :: acc.1.getD d.fp []), cH')) ({}, cH)
      let (pairs, _, cG) := unmapped.foldl (fun (acc : List (ι × κ) × Std.HashMap UInt64 (List (κ × DeepKey)) × ShapeCache ι) j =>
        let (d, cG') := getDeep G acc.2.2 j
        let bucket := acc.2.1.getD d.fp []
        match bucket.find? (fun (_, d') => sameDeepKey d d') with
        | some (j', _) => ((j, j') :: acc.1, acc.2.1.insert d.fp (bucket.eraseP (·.1 == j')), cG')
        | none => (acc.1, acc.2.1, cG')) ([], buckets, cG)
      (pairs, cG, cH)

/-- Pairs of a union's members with an image union's (stateless entry point). -/
@[nospecialize] def pairUnion (G : NormalGraph ι) (H : NormalGraph κ) (S : List ι) (S' : List κ) :
    List (ι × κ) :=
  (pairUnionCached G H {} {} {} S S').1

/-- Pairs of related operand lists, position by position, threading shape caches. -/
@[nospecialize] def pairOpsCached (G : NormalGraph ι) (H : NormalGraph κ)
    (mp : Std.HashMap ι κ) (cG : ShapeCache ι) (cH : ShapeCache κ) (ops : List (List ι)) (ops' : List (List κ)) :
    List (ι × κ) × ShapeCache ι × ShapeCache κ :=
  (ops.zip ops').foldl (fun (acc : List (ι × κ) × ShapeCache ι × ShapeCache κ) (S, S') =>
    let (ps, cG', cH') := pairUnionCached G H mp acc.2.1 acc.2.2 S S'
    (ps ++ acc.1, cG', cH')) ([], cG, cH)

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
@[nospecialize] def pairClausesCached (G : NormalGraph ι) (H : NormalGraph κ)
    (mp : Std.HashMap ι κ) (cG : ShapeCache ι) (cH : ShapeCache κ) (L : List (Clause (List ι))) (L' : List (Clause (List κ))) :
    List (ι × κ) × ShapeCache ι × ShapeCache κ :=
  L.foldl (fun (acc : List (ι × κ) × ShapeCache ι × ShapeCache κ) c =>
    let sk := skeleton c
    match L'.find? (fun c' => decide (skeleton c' = sk)) with
    | some c' =>
      let (ps, cG', cH') := pairOpsCached G H mp acc.2.1 acc.2.2 c.operands c'.operands
      (ps ++ acc.1, cG', cH')
    | none =>
      let ck := keyOrder c
      let skk := skeleton ck
      match L'.find? (fun c' => decide (skeleton (keyOrder c') = skk)) with
      | some c' =>
        let (ps, cG', cH') := pairOpsCached G H mp acc.2.1 acc.2.2 ck.operands (keyOrder c').operands
        (ps ++ acc.1, cG', cH')
      | none => acc) ([], cG, cH)

/-- The pairs a label pair's rows give, threading shape caches and skipping
already-mapped labels. -/
@[nospecialize] def childPairsCached (G : NormalGraph ι) (H : NormalGraph κ)
    (mp : Std.HashMap ι κ) (cG : ShapeCache ι) (cH : ShapeCache κ) (i : ι) (i' : κ) :
    List (ι × κ) × ShapeCache ι × ShapeCache κ :=
  let (rows, cG, cH) := pairClausesCached G H mp cG cH (G.rows i) (H.rows i')
  let (meets, cG, cH) := match G.meets i, H.meets i' with
    | some (p, cs), some (p', cs') =>
      let (pcs, cG, cH) := pairClausesCached G H mp cG cH cs cs'
      let (pm, cG, cH) := pairUnionCached G H mp cG cH (G.meetParams i) (H.meetParams i')
      let head := if mp.contains p then [] else [(p, p')]
      (head ++ pcs ++ pm, cG, cH)
    | _, _ => ([], cG, cH)
  let (schemes, cG, cH) := match G.schemes i, H.schemes i' with
    | some s, some s' =>
      let (po, cG, cH) := pairOpsCached G H mp cG cH (schemeOps s) (schemeOps s')
      let raw := s.binders.zip s'.binders ++ (s.bounds.zip s'.bounds).map (fun (b, b') => (b.1, b'.1))
      let bs := raw.filter fun p => !mp.contains p.1
      (bs ++ po, cG, cH)
    | _, _ => ([], cG, cH)
  (rows ++ meets ++ schemes, cG, cH)

/-- Commit each unmapped pair in `pairs` into `mp` immediately and return the
newly committed pairs to expand, so shared unions referenced by many rows are
paired once instead of once per reference. -/
@[nospecialize] def enqueuePairs (mp : Std.HashMap ι κ) (pairs : List (ι × κ)) :
    Std.HashMap ι κ × List (ι × κ) :=
  pairs.foldl (fun (acc : Std.HashMap ι κ × List (ι × κ)) p =>
    if acc.1.contains p.1 then acc
    else (acc.1.insert p.1 p.2, p :: acc.2)) (mp, [])

@[nospecialize] def proposeGo (G : NormalGraph ι) (H : NormalGraph κ) :
    Nat → List (ι × κ) → Std.HashMap ι κ → ShapeCache ι → ShapeCache κ → Std.HashMap ι κ
  | _, [], mp, _, _ => mp
  | 0, _, mp, _, _ => mp
  | fuel + 1, (i, i') :: rest, mp, cG, cH =>
    let (kids, cG', cH') := childPairsCached G H mp cG cH i i'
    let (mp', added) := enqueuePairs mp kids
    proposeGo G H fuel (added ++ rest) mp' cG' cH'

/-- The proposal's worklist: commits each unmapped pair into `mp` on enqueue
and expands its rows' pairs, caching row shapes per label. -/
@[nospecialize] def propose (G : NormalGraph ι) (H : NormalGraph κ)
    (fuel : Nat) (pairs : List (ι × κ)) (mp : Std.HashMap ι κ) : Std.HashMap ι κ :=
  let (mp₀, init) := enqueuePairs mp pairs
  proposeGo G H fuel init.reverse mp₀ {} {}

/-! ## The check -/

/-- Two lists of the same members. -/
@[nospecialize] def sameB {α : Type} [DecidableEq α] (l l' : List α) : Bool :=
  l.all (fun x => decide (x ∈ l')) && l'.all fun x => decide (x ∈ l)

@[nospecialize] def sameBFast {α : Type} [DecidableEq α] (l l' : List α) : Bool :=
  if l == l' then true else sameB l l'

@[csimp] theorem sameB_eq_fast : @sameB = @sameBFast := by
  funext α de l l'
  unfold sameBFast
  by_cases h : l = l'
  · subst h
    simp [sameB]
  · simp [beq_iff_eq, h]

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

/-- Two label lists of the same members, the first renamed: O(|S| + |T|) via
hash sets, with fast paths for empty and singleton unions. -/
@[nospecialize] def sameMembersB (S : List ι) (T : List κ) : Bool :=
  match S, T with
  | [], [] => true
  | [a], [b] => φ a == b
  | _, _ =>
    let sMap := S.map φ
    let sSet := Std.HashSet.ofList sMap
    let tSet := Std.HashSet.ofList T
    T.all sSet.contains && sMap.all tSet.contains

/-- Order- and duplicate-invariant hash of a list of labels as a set. -/
@[nospecialize] def setHash (T : List κ) : UInt64 :=
  (Std.HashSet.ofList T).fold (fun acc x => acc ^^^ hash x) 0

/-- Indexed lookup of an operand in `c'.operands` matching `S.map φ`. -/
@[nospecialize] def pairOperandIndexed (buckets : Std.HashMap UInt64 (List (List κ))) (S : List ι) : List κ :=
  let key := (S.foldl (fun (acc : Std.HashSet κ) x => acc.insert (φ x)) {}).fold (fun acc x => acc ^^^ hash x) 0
  ((buckets.getD key []).find? fun T => sameMembersB φ S T).getD (σ S)

/-- One clause and an image clause related: tries direct `c.map σ` (exact or
reordered) first in O(|c|), falling back to hash-bucketed operand matching
only when an image operand's member order differs from `σ`'s. -/
@[nospecialize] def clauseRelB (c : Clause (List ι)) (c' : Clause (List κ)) : Bool :=
  let mapped := c.map σ
  if mapped == c' || reorderedB mapped c' then true
  else
    let buckets : Std.HashMap UInt64 (List (List κ)) :=
      c'.operands.reverse.foldl (fun m T =>
        let k := setHash T
        m.insert k (T :: m.getD k [])) {}
    let pair := pairOperandIndexed φ σ buckets
    ([] :: c.operands).all (fun S => sameMembersB φ S (pair S)) &&
      reorderedB (c.map pair) c'

/-- Two clause lists related both ways (`clauseRelB`): checks aligned clauses
in a single pass first, falling back to pairwise search otherwise. -/
@[nospecialize] def rowsRelB (L : List (Clause (List ι))) (L' : List (Clause (List κ))) : Bool :=
  (L.length == L'.length && (L.zip L').all fun p => clauseRelB φ σ p.1 p.2) ||
  (L.all (fun c => L'.any fun c' => clauseRelB φ σ c c') &&
    L'.all (fun c' => L.any fun c => clauseRelB φ σ c c'))

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

/-- The scheme binders in the domain of a proposed map. Each scheme is
looked up once even when many labels query this set. -/
def schemeBinders (G : NormalGraph ι) (keys : List ι) : Std.HashSet ι :=
  Std.HashSet.ofList (keys.flatMap fun k => match G.schemes k with
    | some s => s.binders ++ s.bounds.map (·.1)
    | none => [])

theorem bindsOf_eq_index (G : NormalGraph ι) (keys : List ι) (i : ι) :
    bindsOf G keys i = (G.params i || (schemeBinders G keys).contains i) := by
  simp only [bindsOf, schemeBinders, Std.HashSet.contains_ofList]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.contains_iff_mem, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, h⟩
    refine ⟨k, hk, ?_⟩
    cases hs : G.schemes k <;> simp_all [List.mem_map, List.any_eq_true, beq_iff_eq]
  · rintro ⟨k, hk, h⟩
    refine ⟨k, hk, ?_⟩
    cases hs : G.schemes k <;> simp_all [List.mem_map, List.any_eq_true, beq_iff_eq]

/-- **The check of a proposed map** against the roots `I` and `A`. -/
@[nospecialize] def checkMap [Inhabited κ] (G : NormalGraph ι) (H : NormalGraph κ) (canon : List κ → List κ)
    (mp : Std.HashMap ι κ) (I : List ι) (A : List κ) : Bool :=
  let bind := bindsOf G mp.keys
  let inv : Std.HashMap κ ι := mp.fold (fun acc k v => if bind k then acc.insert v k else acc) {}
  let φ := mapOf mp
  let inD := fun i => mp.contains i
  mp.keys.all (labelOkB G H φ inD (opOf canon mp) (fun k => inv.get? k) bind) &&
    builtinsOkB G H φ inD && I.all inD && sameMembersB φ I A

/-- The root-independent body of `checkMap`: checks every label of `mp`'s
domain and the built-ins once, reusable across all root pairs `(I, A)`
sharing the same store map `mp`. -/
@[nospecialize] def checkMapBody [Inhabited κ] (G : NormalGraph ι) (H : NormalGraph κ) (canon : List κ → List κ)
    (mp : Std.HashMap ι κ) : Bool :=
  let keys := mp.keys
  let binders := schemeBinders G keys
  let bind := fun i => G.params i || binders.contains i
  let inv : Std.HashMap κ ι := mp.fold (fun acc k v => if bind k then acc.insert v k else acc) {}
  let φ := mapOf mp
  let inD := fun i => mp.contains i
  keys.all (labelOkB G H φ inD (opOf canon mp) (fun k => inv.get? k) bind) &&
    builtinsOkB G H φ inD

/-- The per-root check of `checkMap`: every label of `I` is mapped by `mp`
and `I` renames to `A`'s members. -/
@[nospecialize] def checkMapRoots [Inhabited κ] (mp : Std.HashMap ι κ) (I : List ι) (A : List κ) : Bool :=
  I.all (fun i => mp.contains i) && sameMembersB (mapOf mp) I A

/-- The same map check with a single index of its domain's scheme binders. -/
@[nospecialize] def checkMapIndexed [Inhabited κ] (G : NormalGraph ι) (H : NormalGraph κ) (canon : List κ → List κ)
    (mp : Std.HashMap ι κ) (I : List ι) (A : List κ) : Bool :=
  checkMapBody G H canon mp && checkMapRoots mp I A

@[csimp] theorem checkMap_eq_indexed : @checkMap = @checkMapIndexed := by
  funext ι κ de h de' h' inh G H canon mp I A
  unfold checkMap checkMapIndexed checkMapBody checkMapRoots
  rw [show bindsOf G mp.keys = (fun i => G.params i || (schemeBinders G mp.keys).contains i) from
    funext (bindsOf_eq_index G mp.keys)]
  simp only [Bool.and_assoc]

theorem checkMap_of_body_roots [Inhabited κ] {G : NormalGraph ι} {H : NormalGraph κ} {canon : List κ → List κ}
    {mp : Std.HashMap ι κ} {I : List ι} {A : List κ}
    (hb : checkMapBody G H canon mp = true) (hr : checkMapRoots mp I A = true) :
    checkMap G H canon mp I A = true := by
  rw [checkMap_eq_indexed]
  simp only [checkMapIndexed, hb, hr, Bool.and_true]

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

omit [DecidableEq ι] [Hashable ι] in
theorem sameMembersB_sound {S : List ι} {T : List κ} (h : sameMembersB φ S T = true) :
    ∀ x, x ∈ T ↔ x ∈ S.map φ := by
  unfold sameMembersB at h
  split at h
  · simp
  · simp only [beq_iff_eq] at h; subst h; simp
  · simp only [Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem] at h
    exact fun x => ⟨h.1 x, h.2 x⟩

theorem Reordered.refl {α : Type} (c : Clause α) : Reordered c c := by
  cases c with
  | refs a bs vs os ms ks st =>
    exact ⟨a, bs, vs, os, ms, ks, st, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
      fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | dict a bs vs ds os ms ks cs st =>
    exact ⟨a, bs, vs, ds, os, ms, ks, cs, st, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
      fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | _ => rfl

omit [DecidableEq ι] [Hashable ι] in
/-- An accepted clause pair is related (proved): either `c.map σ` relates
directly (equal or reordered), or the hash-bucketed operand map agrees with
`φ` operand by operand. -/
theorem clauseRelB_sound (hσ : ∀ S x, x ∈ σ S ↔ x ∈ S.map φ) {c : Clause (List ι)} {c' : Clause (List κ)}
    (h : clauseRelB φ σ c c' = true) :
    ClauseRel φ c c' := by
  unfold clauseRelB at h
  dsimp only at h
  split at h
  · rename_i hm
    rcases Bool.or_eq_true_iff.mp hm with heq | hre
    · exact ⟨σ, fun S _ x => hσ S x, beq_iff_eq.mp heq ▸ Reordered.refl c'⟩
    · exact ⟨σ, fun S _ x => hσ S x, reorderedB_sound hre⟩
  · simp only [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨_, fun S hS x => ?_, reorderedB_sound h.2⟩
    have hS' : S ∈ [] :: c.operands := by
      rcases hS with hS | rfl
      · exact List.mem_cons_of_mem _ hS
      · exact List.mem_cons_self
    exact sameMembersB_sound (h.1 S hS') x

omit [DecidableEq ι] [Hashable ι] in
theorem rowsRelB_sound (hσ : ∀ S x, x ∈ σ S ↔ x ∈ S.map φ) {L : List (Clause (List ι))} {L' : List (Clause (List κ))}
    (h : rowsRelB φ σ L L' = true) : RowsRel φ L L' := by
  unfold rowsRelB at h
  rcases Bool.or_eq_true_iff.mp h with hzip | hgen
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hzip
    obtain ⟨hlen, hall⟩ := hzip
    refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      have hi' : i < L'.length := hlen ▸ hi
      have hmem : (L[i], L'[i]) ∈ L.zip L' := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by rw [List.length_zip]; omega, by simp⟩
      exact ⟨L'[i], List.getElem_mem hi', clauseRelB_sound hσ (hall _ hmem)⟩
    · obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hc'
      have hi : i < L.length := hlen.symm ▸ hi'
      have hmem : (L[i], L'[i]) ∈ L.zip L' := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by rw [List.length_zip]; omega, by simp⟩
      exact ⟨L[i], List.getElem_mem hi, clauseRelB_sound hσ (hall _ hmem)⟩
  · simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hgen
    refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
    · obtain ⟨c', hc', he⟩ := hgen.1 c hc
      exact ⟨c', hc', clauseRelB_sound hσ he⟩
    · obtain ⟨c, hc, he⟩ := hgen.2 c' hc'
      exact ⟨c, hc, clauseRelB_sound hσ he⟩

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

omit [Hashable ι] in
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
      exact ⟨cs', by rw [hm.1], rowsRelB_sound hσ hm.2⟩
  · intro hp
    rcases hr with hr | hr
    · rw [hp] at hr; exact absurd hr (by simp)
    · exact rowsRelB_sound hσ hr

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

/-- An accepted `matchStores` result satisfies the root-independent body check
(proved), so its returned map can be reused on other root pairs via
`checkMap_of_body_roots`. -/
theorem checkMapBody_of_matchStores [Inhabited κ] {G : NormalGraph ι} {H : NormalGraph κ}
    {canon : List κ → List κ} {fuel : Nat} {I : List ι} {A : List κ} {mp : Std.HashMap ι κ}
    (h : matchStores G H canon fuel I A = some mp) :
    checkMapBody G H canon mp = true := by
  unfold matchStores at h
  by_cases hc : checkMap G H canon (propose G H fuel (startPairs G H I A) {}) I A = true
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    rw [h, checkMap_eq_indexed] at hc
    exact (Bool.and_eq_true _ _ |>.mp hc).1
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

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
