import Verification.Programs.TolerantFramesMerge

/-! # Tolerant frames: the merge in parts

`SinglePass.mergeState` is one `do` block. This module states it as the
composition of its parts, each a function of what it reads, so that each
part's theorem is about a term of manageable size: the slots' names and each
predecessor's renaming (`mergeSlots`), each predecessor's facts restated at
the fresh names (`mergeVariants`), the facts every predecessor holds
(`mergeCommon`, `mergeMeet`), the names renamed away (`mergeRenamedAway`), the
facts each predecessor states beyond them (`mergeDiffs`), the weakest bounds
(`mergeBounds`), the entailed bounds (`mergeEntailed`), the guarded joins
(`mergeGuarded`), the fresh names (`mergeFresh`) and the implications
(`mergeImplies`). `mergeState_state` and `mergeState_implies` state that the
merge's result is that composition, by unfolding. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

section Mirror
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- The merge's names: a slot whose predecessors' names agree keeps the
name; a slot whose names differ takes the fresh name of their vector
(`phis`), drawn from `fresh` the first time the vector is met, each
predecessor renaming its name there to it. The result: the next fresh name,
the names, each predecessor's renaming and the vectors' fresh names. -/
def mergeSlots (preds : List State) (width fresh : Nat) :
    Nat × Array Nat × List (Std.HashMap Nat (List Nat)) × Std.HashMap (List Nat) Nat := Id.run do
  let mut fresh := fresh
  let arrs := preds.map (·.names.toArray)
  let mut names : Array Nat := Array.mkEmpty width
  let mut renames : List (Std.HashMap Nat (List Nat)) := arrs.map fun _ => {}
  let mut phis : Std.HashMap (List Nat) Nat := {}
  for i in List.range width do
    let ns := arrs.map (·.getD i 0)
    let n0 := ns.headD 0
    if ns.all (· == n0) then names := names.push n0
    else match phis.get? ns with
      | some φ => names := names.push φ
      | none =>
        names := names.push fresh
        phis := phis.insert ns fresh
        renames := (renames.zip ns).map fun (m, x) => m.insert x (fresh :: m.getD x [])
        fresh := fresh + 1
  return (fresh, names, renames, phis)

/-- Each predecessor's facts about the names it renames, restated at the
fresh names (`Atom.renameEach`), and its equalities (`mergeEqual`). -/
def mergeVariants (preds : List State) (names : Array Nat) (renames : List (Std.HashMap Nat (List Nat))) :
    List (Std.HashSet Atom) :=
  (preds.zip renames).map fun ((st : State), (m : Std.HashMap Nat (List Nat))) =>
    let equal := mergeEqual st names m
    let about := m.fold (fun (acc : List Atom) x _ => st.store.about x ++ acc) []
    (about.foldl (fun (acc : Std.HashSet Atom) a => acc.insertMany (Atom.renameEach m a)) {}).insertMany equal

/-- The first predecessor's store less each fact another lacks
(`Store.diff`). -/
def mergeCommon (preds : List State) : Store := Id.run do
  let s := preds.headD { names := [] }
  let mut met := s.store
  for q in preds.tail do
    for a in (SinglePass.timedKind "merge diff" fun _ => Store.diff met q.store).1 do met := met.remove a
  return met

/-- The restated facts every predecessor states, added. -/
def mergeMeet (met : Store) (variants : List (Std.HashSet Atom)) : Store :=
  let firstV := variants.headD {}
  SinglePass.timedKind "meet" fun _ => firstV.fold (fun (acc : Store) a =>
    if variants.tail.all (·.contains a) then acc.add a else acc) met

/-- The names a predecessor renames that no slot of the merge holds. -/
def mergeRenamedAway (live : Std.HashSet Nat) (renames : List (Std.HashMap Nat (List Nat))) : List Nat :=
  (CertificateProducer.keepFirst {} (renames.flatMap fun (m : Std.HashMap Nat (List Nat)) =>
    m.fold (fun acc x _ => if live.contains x then acc else x :: acc) [])).2.toList

/-- What each predecessor states beyond the met store `met0`: its facts the
met store lacks over names it does not rename, and its restatements the met
store lacks. -/
def mergeDiffs (preds : List State) (renames : List (Std.HashMap Nat (List Nat)))
    (variants : List (Std.HashSet Atom)) (met0 : Store) : List (List Atom) :=
  ((preds.zip renames).zip variants).map
    fun (((st : State), (m : Std.HashMap Nat (List Nat))), (v : Std.HashSet Atom)) =>
      ((SinglePass.timedKind "merge diff" fun _ => Store.diff met0 st.store).2.filter fun a => !a.names.any m.contains) ++
        v.fold (fun acc a => if met0.live.contains a.canon then acc else a :: acc) []

/-- One predecessor's linear bounds by form and condition, the strongest of
each. -/
def boundsOf (d : List Atom) : Std.HashMap (Linear.Form HeapKnowledge.Term × Option Nat × Bool) Int :=
  d.foldl (fun acc a => match a with
    | .index ⟨.linear (.le F d), c, neg⟩ =>
      let F := Linear.normalize F
      acc.insert (F, c, neg) (match acc.get? (F, c, neg) with | some d' => min d d' | none => d)
    | _ => acc) {}

/-- One form's bound every predecessor states, at the weakest of their
bounds, added. -/
def weakestStep (bs : List (Std.HashMap (Linear.Form HeapKnowledge.Term × Option Nat × Bool) Int))
    (acc : Store) (key : Linear.Form HeapKnowledge.Term × Option Nat × Bool) (d : Int) : Store := Id.run do
  let mut weakest := d
  for b in bs do
    match b.get? key with
    | some d' => weakest := max weakest d'
    | none => return acc
  let (F, c, neg) := key
  return acc.add (.index ⟨.linear (.le F weakest), c, neg⟩)

/-- The weakest bounds every predecessor states, added to `met`. -/
def mergeBounds (diffs : List (List Atom)) (met : Store) : Store :=
  match diffs.map boundsOf with
  | b0 :: bs => b0.fold (weakestStep bs) met
  | [] => met

/-- Each predecessor's state at the merge's names. -/
def mergeViews (mergedNames : List Nat) (diffs : List (List Atom)) (met0 : Store) : List State :=
  diffs.map fun d => { names := mergedNames, store := d.foldl Store.add met0 }

/-- The linear bounds over the merge's names one predecessor states and
every predecessor's view holds or entails. -/
def mergeEntailed (live : Std.HashSet Nat) (diffs : List (List Atom)) (views : List State) (met : Store) : Store :=
  SinglePass.timedKind "meet entailed" fun _ => Id.run do
    let mut acc := met
    let mut seen : Std.HashSet Atom := {}
    for d in diffs do
      for a in d do
        if let .index ⟨.linear F, none, _⟩ := a then
          if !seen.contains a && a.names.all live.contains && !acc.holds a then
            seen := seen.insert a
            if views.all fun (qs : State) => qs.store.holds a ||
                HeapKnowledge.entailsKnown (qs.store.linearNear a.names) F then
              -- Its terms defined in every view (`entailDefinedCheck`).
              if views.all fun (qs : State) => SinglePass.entailDefinedCheck qs a F then
                acc := acc.add a
    return acc

/-- The guarded facts a join keeps, at slots. -/
def mergeGuarded (width : Nat) (mergedNames : List Nat) (met0 : Store) (diffs : List (List Atom))
    (views : List State) : List HeapKnowledge.IndexAtom :=
  let tags : List HeapKnowledge.GuardTag := [.null, .undef]
  let tagged := diffs.flatMap fun d => d.filterMap fun a => match a with
    | .value f => if tags.any (fun g => HeapKnowledge.guardTags { values := [f] } f.slot [] g) then some f.slot else none
    | _ => none
  let seeds := (diffs.flatMap fun d => d.flatMap fun a => match a with
    | .index ⟨.guarded .., _, _⟩ | .index ⟨.storeApart .., _, _⟩ | .link _ => a.names
    | _ => [])
  let seeds := if tagged.isEmpty then seeds else seeds ++ tagged ++
    (diffs.flatMap fun d => d.flatMap fun a => if a.names.any tagged.contains then a.names else [])
  let seedSlots := (CertificateProducer.keepFirst {} (seeds.filterMap mergedNames.idxOf?)).2.toList
  if seedSlots.isEmpty then [] else Id.run do
    let projections := views.map fun ps => (SinglePass.materialize ps width seedSlots false).1
    let common := (SinglePass.materialize { names := mergedNames, store := met0 } width seedSlots false).1
    let lowered := projections.map fun (p : HeapKnowledge.Knowledge) =>
      { p with indices := p.indices ++ ((HeapKnowledge.lowerGuards p.links p.indices).filter (!p.indices.contains ·)) }
    let joined := SinglePass.timedKind "meet guarded" fun _ => CertificateProducer.joinGuarded lowered common
    let tagged := SinglePass.timedKind "meet tagged" fun _ =>
      let nullish := ((projections.flatMap fun (o : HeapKnowledge.Knowledge) => o.values.flatMap fun f =>
        (tags.filter fun g => HeapKnowledge.guardTags o f.slot [] g).flatMap fun g =>
          (HeapLinks.aliases o.links f.slot).map (·, g))).eraseDups
      if nullish.isEmpty then [] else
      let candidates := (projections.flatMap fun (p : HeapKnowledge.Knowledge) => p.indices.flatMap fun a =>
        if a.cond.isSome || common.indices.contains a then [] else match a.fact with
        | .guarded .. => []
        | F => (nullish.filter fun (z, _) => F.slots.contains z).map fun (z, g) =>
            ({ fact := .guarded z [] g F } : HeapKnowledge.IndexAtom)).eraseDups
      candidates.filter fun a => projections.all fun (p : HeapKnowledge.Knowledge) =>
        HeapKnowledge.indicesCheckWith (HeapKnowledge.guardTags p) (HeapLinks.aliases p.links) p.links
          p.indices [a] none
    return joined ++ tagged

/-- The guarded facts, renamed from slots to the merge's names, added. -/
def mergeAddGuarded (mergedNames : List Nat) (guarded : List HeapKnowledge.IndexAtom) (met : Store) : Store :=
  guarded.foldl (fun (acc : Store) x => match (Atom.index x).rename (mergedNames[·]?) with
    | some a => acc.add a
    | none => acc) met

/-- A name holds a fresh store where every predecessor's does: each
predecessor's fresh names with their renames, intersected. -/
def mergeFresh (preds : List State) (renames : List (Std.HashMap Nat (List Nat))) : List Nat :=
  let freshLists := (preds.zip renames).map fun ((st : State), (m : Std.HashMap Nat (List Nat))) =>
    st.fresh.flatMap fun x => x :: m.getD x []
  match freshLists with
  | f0 :: fs => f0.filter fun x => fs.all (·.contains x)
  | [] => []

/-- The implications the merge establishes, at its names. -/
def mergeImplies (G : NormalGraph ι) (context : List (Ty ι))
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (mergedNames : List Nat) : List (PromiseCalls.Implication ι) :=
  let width := context.length
  let some_ := edgesIn.any (fun (_, xs, _) => !xs.isEmpty) || Id.run do
    let some (Γ0, _, m0) := edgesIn.head? | return false
    for t in List.range width do
      let A0 := Γ0[PointClaims.slot m0 t]?
      let differs := edgesIn.any fun (Γ, _, m) => match Γ[PointClaims.slot m t]?, A0 with
        | some A, some B => !SinglePass.same A B
        | _, _ => true
      if differs && edgesIn.any (fun (Γ, _, m) => (Γ[PointClaims.slot m t]?).any (BranchRefinement.impossible G · (.boolean true))) then
        return true
    return false
  if !some_ then [] else
    let joinedImpl := SinglePass.timedKind "meet implications" fun _ =>
      CertificateProducer.meetImplications G edgesIn width context
    -- Each kept where every incoming edge establishes it
    -- (`PromiseCalls.impliesCheck`, as an edge into a target carries it).
    let joinedImpl := SinglePass.timedKind "meet implications checked" fun _ => joinedImpl.filter fun x =>
      edgesIn.all fun (Γ, xs, m) => PromiseCalls.impliesCheck G Γ xs m [x]
    (CertificateProducer.keepFirst {} (joinedImpl.filterMap fun (x : PromiseCalls.Implication ι) => do
      pure (⟨← mergedNames[x.test]?, ← mergedNames[x.target]?, x.type⟩ : PromiseCalls.Implication ι))).2.toList

/-- The merge's met store before its joins: the common facts, the restated
facts every predecessor states, the names renamed away dropped. -/
def mergeMet0 (preds : List State) (names : Array Nat) (renames : List (Std.HashMap Nat (List Nat))) : Store :=
  (mergeMeet (mergeCommon preds) (mergeVariants preds names renames)).drop
    (mergeRenamedAway (Std.HashSet.ofList names.toList) renames)

/-- The merge's store, from its parts. -/
def mergeStore (preds : List State) (width : Nat) (names : Array Nat) (renames : List (Std.HashMap Nat (List Nat))) :
    Store :=
  let variants := mergeVariants preds names renames
  let met0 := mergeMet0 preds names renames
  let diffs := mergeDiffs preds renames variants met0
  let views := mergeViews names.toList diffs met0
  mergeAddGuarded names.toList (mergeGuarded width names.toList met0 diffs views)
    (mergeEntailed (Std.HashSet.ofList names.toList) diffs views (mergeBounds diffs met0))

/-- **The merge's state is the composition of its parts**, by unfolding. -/
theorem mergeState_state (G : NormalGraph ι) (context : List (Ty ι)) (preds : List State)
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) (fresh : Nat) :
    (SinglePass.mergeState G context preds edgesIn fresh).state =
      { names := (mergeSlots preds context.length fresh).2.1.toList,
        store := mergeStore preds context.length (mergeSlots preds context.length fresh).2.1
          (mergeSlots preds context.length fresh).2.2.1,
        fresh := mergeFresh preds (mergeSlots preds context.length fresh).2.2.1 } := rfl

/-- The merge's implications, by unfolding. -/
theorem mergeState_implies (G : NormalGraph ι) (context : List (Ty ι)) (preds : List State)
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) (fresh : Nat) :
    (SinglePass.mergeState G context preds edgesIn fresh).implies =
      mergeImplies G context edgesIn (mergeSlots preds context.length fresh).2.1.toList := rfl

/-- The merge's next fresh name, by unfolding. -/
theorem mergeState_fresh (G : NormalGraph ι) (context : List (Ty ι)) (preds : List State)
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) (fresh : Nat) :
    (SinglePass.mergeState G context preds edgesIn fresh).fresh = (mergeSlots preds context.length fresh).1 := rfl

end Mirror

end Verification.TolerantFrames
