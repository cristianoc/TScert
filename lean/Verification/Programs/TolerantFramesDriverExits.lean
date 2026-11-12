import Verification.Programs.TolerantFramesDriverVisit

namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore

section Exits
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

/-- Two exit states agreeing on the walk's arrays an exit's check leaves. -/
structure SameCore (a b : SinglePass.ExitsDone ι G) : Prop where
  incoming : b.incoming = a.incoming
  incomingImpl : b.incomingImpl = a.incomingImpl
  incomingEdges : b.incomingEdges = a.incomingEdges
  indeg : b.indeg = a.indeg
  queue : b.queue = a.queue

theorem SameCore.trans {a b c : SinglePass.ExitsDone ι G} (h1 : SameCore a b) (h2 : SameCore b c) : SameCore a c :=
  ⟨h2.incoming.trans h1.incoming, h2.incomingImpl.trans h1.incomingImpl,
    h2.incomingEdges.trans h1.incomingEdges, h2.indeg.trans h1.indeg, h2.queue.trans h1.queue⟩

theorem sameCore_trace (acc : SinglePass.ExitsDone ι G) (b : Bool) (tr : SinglePass.Trace) :
    SameCore acc (if b = true then { acc with trace := tr } else acc) ∧
      (if b = true then { acc with trace := tr } else acc).edges = acc.edges := by
  split <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem sameCore_unsat {acc a : SinglePass.ExitsDone ι G} (h : SameCore acc a ∧ a.edges = acc.edges) (c : Bool)
    (u : Array (Option Bool)) :
    SameCore acc (if c = true then { a with unsat := u } else a) ∧
      (if c = true then { a with unsat := u } else a).edges = acc.edges := by
  split
  · exact ⟨⟨h.1.incoming, h.1.incomingImpl, h.1.incomingEdges, h.1.indeg, h.1.queue⟩, h.2⟩
  · exact h

theorem exitTypes_core {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {outAll : Thunk HeapKnowledge.Knowledge} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {edgeStore : SinglePass.Store} {pushed isHandler : Bool}
    {observed : Option BranchRefinement.Observation} {first : Bool} {diff : List (Nat × Nat)}
    {acc acc' : SinglePass.ExitsDone ι G}
    (h : SinglePass.exitTypes G I env l en sd outAll t tc Γ names edgeStore pushed isHandler observed first diff acc
      = .ok acc') : SameCore acc acc' ∧ acc'.edges = acc.edges := by
  unfold SinglePass.exitTypes at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩) | cases h

theorem assertionExit_core {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γe : Thunk (List (ProgramTyping.Ty ι))} {names : List Nat} {edgeStore : SinglePass.Store} {pushed : Bool}
    {observed : Option BranchRefinement.Observation} {vacuous : Bool} {acc acc' : SinglePass.ExitsDone ι G}
    (h : SinglePass.assertionExit G env l t tc Γe names edgeStore pushed observed vacuous acc = .ok acc') :
    SameCore acc acc' ∧ acc'.edges = acc.edges := by
  unfold SinglePass.assertionExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩) | cases h

theorem headExit_core {env : SinglePass.WalkEnv ι G I} {l : Nat} {t : Target} {tc : PointClaim ι}
    {Γ : List (ProgramTyping.Ty ι)} {names : List Nat} {edgeStore : SinglePass.Store} {pushed vacuous : Bool}
    {carried : List (PromiseCalls.Implication ι)} {acc acc' : SinglePass.ExitsDone ι G}
    (h : SinglePass.headExit G I env l t tc Γ names edgeStore pushed vacuous carried acc = .ok acc') :
    SameCore acc acc' ∧ acc'.edges = acc.edges.push { source := l, target := t, pushed, carried, meets := !vacuous } := by
  unfold SinglePass.headExit at h
  repeat' (first | split at h | extract_lets at h)
  all_goals first | (cases h; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩) | cases h

theorem pushExit_fields (env : SinglePass.WalkEnv ι G I) (l : Nat) (t : Target) (target : SinglePass.State)
    (carried : List (PromiseCalls.Implication ι)) (Γe : Thunk (List (ProgramTyping.Ty ι))) (names : List Nat)
    (pushed vacuous : Bool) (acc : SinglePass.ExitsDone ι G) :
    (SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).incoming =
        acc.incoming.modify t.label (target :: ·) ∧
      (SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).incomingImpl =
        acc.incomingImpl.modify t.label (carried :: ·) ∧
      (∀ y, y ≠ t.label → (SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).incomingEdges[y]? =
        acc.incomingEdges[y]?) ∧
      (SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).indeg = acc.indeg.modify t.label (· - 1) ∧
      (SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).queue =
        (if (acc.indeg.modify t.label (· - 1))[t.label]! == 0 then t.label :: acc.queue else acc.queue) ∧
      (SinglePass.pushExit env l t target carried Γe names pushed vacuous acc).edges =
        acc.edges.push { source := l, target := t, pushed, carried, meets := !vacuous } := by
  refine ⟨rfl, rfl, fun y hy => ?_, rfl, rfl, rfl⟩
  unfold SinglePass.pushExit
  dsimp only
  split
  · rw [Array.getElem?_modify, if_neg (Ne.symm hy)]
  · rfl

/-- The state an exit carries into a node other than a head
(`exitStep`'s `edgeTransfer` over `edgeStoreOf`), at the exit's context
and names. -/
def exitPushed (env : SinglePass.WalkEnv ι G I) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (ex : SinglePass.Exit) (implies : List (PromiseCalls.Implication ι)) :
    SinglePass.State :=
  let c := env.claimed[l]!
  let Γ := if ex.isHandler then sd.thrownTy.getD [] :: c.context else if ex.pushed then c.type :: c.context
    else c.context
  let names := if ex.isHandler then sd.thrown :: en.entry.names else if ex.pushed then sd.st.result :: en.entry.names
    else en.entry.names
  (SinglePass.edgeTransfer names ex.target.mapping ex.pushed ex.isHandler sd.outFresh en.entry sd.st.result
    (SinglePass.edgeStoreOf G Γ en.entry.store sd.st.store names (sd.st.result :: en.entry.names) c.context.length
      ex.pushed ex.isHandler ex.observed ex.promote) implies).1

/-- **What one exit does to the walk's arrays** (`exitStep`): its target
`x` has a claim; one edge recorded, to its target; into a head nothing
else; into another node a state `exitPushed` and implications come in at
`x`, the merge edges change at `x` only, `x`'s in-degree one less, and `x`
queued where it reaches 0. -/
structure ExitEffect (env : SinglePass.WalkEnv ι G I) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (ex : SinglePass.Exit) (acc acc' : SinglePass.ExitsDone ι G) : Prop where
  claimed : ex.target.label < env.claimed.size
  edges : ∃ e : SinglePass.EdgeWalk ι, acc'.edges = acc.edges.push e ∧ e.target = ex.target
  head : env.isHead[ex.target.label]! = true → SameCore acc acc'
  push : env.isHead[ex.target.label]! = false → ∃ implies carried,
    acc'.incoming = acc.incoming.modify ex.target.label (exitPushed env l en sd ex implies :: ·) ∧
    acc'.incomingImpl = acc.incomingImpl.modify ex.target.label (carried :: ·) ∧
    (∀ y, y ≠ ex.target.label → acc'.incomingEdges[y]? = acc.incomingEdges[y]?) ∧
    acc'.indeg = acc.indeg.modify ex.target.label (· - 1) ∧
    acc'.queue = (if (acc.indeg.modify ex.target.label (· - 1))[ex.target.label]! == 0
      then ex.target.label :: acc.queue else acc.queue)

theorem exitStep_effect {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge}
    {acc acc' : SinglePass.ExitsDone ι G} {exi : SinglePass.Exit × Nat}
    (h : SinglePass.exitStep G I env l en sd ysAll outAll acc exi = .ok acc') :
    ExitEffect env l en sd exi.1 acc acc' := by
  unfold SinglePass.exitStep at h
  extract_lets at h
  split at h
  · cases h
  rename_i tc htc
  extract_lets diff u acc2 typed at h
  generalize ht : typed = T at h
  split at h
  · cases h
  rename_i acc1
  simp only [typed] at ht
  have hp : SameCore acc acc2 ∧ acc2.edges = acc.edges := by
    exact sameCore_unsat (sameCore_trace _ _ _) _ _
  have hc1 : SameCore acc acc1 ∧ acc1.edges = acc.edges := by
    split at ht
    · cases ht; exact hp
    · obtain ⟨h1, h2⟩ := exitTypes_core ht
      exact ⟨hp.1.trans h1, h2.trans hp.2⟩
  extract_lets freshImpl at h
  have hcl : (exi.1.target.label) < env.claimed.size := by
    rcases (Array.getElem?_eq_some_iff.mp htc) with ⟨hlt, -⟩; exact hlt
  split at h
  · rename_i hhead
    obtain ⟨hc2, he2⟩ := headExit_core h
    exact { claimed := hcl, edges := ⟨_, by rw [he2, hc1.2], rfl⟩, head := fun _ => hc1.1.trans hc2,
            push := fun hf => absurd (hhead.symm.trans hf) (by decide) }
  · rename_i hhead
    split at h
    · cases h
    rename_i acc3 hA
    obtain ⟨hc3, he3⟩ := assertionExit_core hA
    split at h
    rename_i target carried hT
    cases h
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pushExit_fields env l _ target carried _ _ _ _ acc3
    have htarget : target = exitPushed env l en sd exi.1 (en.implies ++ freshImpl) := (congrArg Prod.fst hT).symm
    refine { claimed := hcl, edges := ⟨_, by rw [p6, he3, hc1.2], rfl⟩, head := fun hh => absurd hh hhead,
             push := fun _ => ⟨en.implies ++ freshImpl, carried, ?_, ?_, ?_, ?_, ?_⟩ }
    · rw [p1, hc3.incoming, hc1.1.incoming, htarget]
    · rw [p2, hc3.incomingImpl, hc1.1.incomingImpl]
    · intro y hy; rw [p3 y hy, hc3.incomingEdges, hc1.1.incomingEdges]
    · rw [p4, hc3.indeg, hc1.1.indeg]
    · rw [p5, hc3.indeg, hc1.1.indeg, hc3.queue, hc1.1.queue]

omit [Labels ι] in
theorem getD_modify_ne {α : Type} (a : Array α) (x y : Nat) (f : α → α) (d : α) (h : y ≠ x) :
    ((a.modify x f)[y]?).getD d = (a[y]?).getD d := by
  rw [Array.getElem?_modify, if_neg (Ne.symm h)]

omit [Labels ι] in
theorem getD_modify_sub (a : Array Nat) (x : Nat) :
    ((a.modify x (· - 1))[x]?).getD 0 = (a[x]?).getD 0 - 1 := by
  rw [Array.getElem?_modify, if_pos rfl]
  cases a[x]? <;> rfl

omit [Labels ι] in
theorem getD_modify_cons {α : Type} (a : Array (List α)) (x : Nat) (s : α) :
    ((a.modify x (s :: ·))[x]?).getD [] = (if x < a.size then [s] else []) ++ (a[x]?).getD [] := by
  rw [Array.getElem?_modify, if_pos rfl]
  by_cases hx : x < a.size
  · rw [Array.getElem?_eq_getElem hx]; simp [hx]
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hx)]; simp [hx]

/-- A label's in-degree in an array. -/
def dg (a : Array Nat) (y : Nat) : Nat := (a[y]?).getD 0

/-- **What the exits' fold does to the walk's arrays**, over the exits `xs`
with target labels `L`: each target has a claim; the arrays change at the
targets only, keeping their sizes; at each label the states and
implications that came in grow by those the exits pushed there, each an
`exitPushed`; the edges grow by edges to targets; a node other than a
head's in-degree goes down by its count among the targets, and no
in-degree grows; the labels queued in front are targets other than heads
at in-degree 0, distinct where no in-degree is below its count. -/
structure ExitsFold (env : SinglePass.WalkEnv ι G I) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (xs : List SinglePass.Exit) (acc r : SinglePass.ExitsDone ι G) : Prop where
  claimed : ∀ x ∈ xs.map (·.target.label), x < env.claimed.size
  frame : ∀ y, y ∉ xs.map (·.target.label) → r.incoming[y]? = acc.incoming[y]? ∧
    r.incomingImpl[y]? = acc.incomingImpl[y]? ∧ r.incomingEdges[y]? = acc.incomingEdges[y]?
  sizes : r.incoming.size = acc.incoming.size ∧ r.incomingImpl.size = acc.incomingImpl.size
  pushes : ∀ y, ∃ ns nis, (r.incoming[y]?).getD [] = ns ++ (acc.incoming[y]?).getD [] ∧
    (r.incomingImpl[y]?).getD [] = nis ++ (acc.incomingImpl[y]?).getD [] ∧
    (acc.incoming.size = acc.incomingImpl.size → ns.length = nis.length) ∧
    ∀ s ∈ ns, ∃ ex ∈ xs, ex.target.label = y ∧ ∃ imp, s = exitPushed env l en sd ex imp
  edges : ∃ new, r.edges.toList = acc.edges.toList ++ new ∧ ∀ e ∈ new, e.target.label ∈ xs.map (·.target.label)
  degs : ∀ y, env.isHead[y]! = false → dg r.indeg y = dg acc.indeg y - (xs.map (·.target.label)).count y
  mono : ∀ y, dg r.indeg y ≤ dg acc.indeg y
  queue : ∃ new, r.queue = new ++ acc.queue ∧
    (∀ y ∈ new, y ∈ xs.map (·.target.label) ∧ env.isHead[y]! = false ∧ dg r.indeg y = 0) ∧
    ((∀ y, env.isHead[y]! = false → (xs.map (·.target.label)).count y ≤ dg acc.indeg y) → new.Nodup)

theorem ExitsFold.nil (env : SinglePass.WalkEnv ι G I) (l : Nat) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (acc : SinglePass.ExitsDone ι G) : ExitsFold env l en sd [] acc acc where
  claimed := by simp
  frame := fun _ _ => ⟨rfl, rfl, rfl⟩
  sizes := ⟨rfl, rfl⟩
  pushes := fun _ => ⟨[], [], rfl, rfl, fun _ => rfl, by simp⟩
  edges := ⟨[], by simp, by simp⟩
  degs := fun _ _ => by simp
  mono := fun _ => Nat.le_refl _
  queue := ⟨[], rfl, by simp, fun _ => List.nodup_nil⟩

/-- One exit's effect then the rest's fold. -/
theorem ExitsFold.cons {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ex : SinglePass.Exit} {xs : List SinglePass.Exit}
    {acc a r : SinglePass.ExitsDone ι G} (he : ExitEffect env l en sd ex acc a) (hf : ExitsFold env l en sd xs a r) :
    ExitsFold env l en sd (ex :: xs) acc r := by
  -- What the one exit does at a label `y`.
  have hdeg : ∀ y, dg a.indeg y = if y = ex.target.label ∧ env.isHead[y]! = false then dg acc.indeg y - 1
      else dg acc.indeg y := by
    intro y
    cases hh : env.isHead[ex.target.label]! with
    | true =>
      have hy : ¬ (y = ex.target.label ∧ env.isHead[y]! = false) := fun ⟨h1, h2⟩ => by subst h1; rw [hh] at h2; cases h2
      rw [if_neg hy]; unfold dg; rw [(he.head hh).indeg]
    | false =>
      obtain ⟨_, _, -, -, -, h4, -⟩ := he.push hh
      unfold dg; rw [h4]
      by_cases hy : y = ex.target.label
      · subst hy; rw [if_pos ⟨rfl, hh⟩]; exact getD_modify_sub _ _
      · rw [if_neg (fun h => hy h.1)]; exact getD_modify_ne _ _ _ _ _ hy
  have hdeg_le : ∀ y, dg a.indeg y ≤ dg acc.indeg y := fun y => by rw [hdeg y]; split <;> omega
  have hsz : a.incoming.size = acc.incoming.size ∧ a.incomingImpl.size = acc.incomingImpl.size := by
    cases hh : env.isHead[ex.target.label]! with
    | true => rw [(he.head hh).incoming, (he.head hh).incomingImpl]; exact ⟨rfl, rfl⟩
    | false =>
      obtain ⟨_, _, h1, h2, -, -, -⟩ := he.push hh
      rw [h1, h2]; exact ⟨Array.size_modify, Array.size_modify⟩
  refine { claimed := ?_, frame := ?_, sizes := ?_, pushes := ?_, edges := ?_, degs := ?_, mono := ?_, queue := ?_ }
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.claimed
    · exact hf.claimed x hx
  · intro y hy
    have hy1 : y ≠ ex.target.label := fun h => hy (h ▸ List.mem_cons_self ..)
    have hy2 : y ∉ xs.map (·.target.label) := fun h => hy (List.mem_cons_of_mem _ h)
    obtain ⟨f1, f2, f3⟩ := hf.frame y hy2
    rw [f1, f2, f3]
    cases hh : env.isHead[ex.target.label]! with
    | true => have hc := he.head hh; rw [hc.incoming, hc.incomingImpl, hc.incomingEdges]; exact ⟨rfl, rfl, rfl⟩
    | false =>
      obtain ⟨_, _, h1, h2, h3, -, -⟩ := he.push hh
      rw [h1, h2, Array.getElem?_modify, if_neg (Ne.symm hy1), Array.getElem?_modify, if_neg (Ne.symm hy1)]
      exact ⟨rfl, rfl, h3 y hy1⟩
  · rw [hf.sizes.1, hf.sizes.2]; exact hsz
  · intro y
    obtain ⟨ns, nis, g1, g2, g3, g4⟩ := hf.pushes y
    -- The one exit's pushes at `y`.
    have hone : ∃ ns0 nis0, (a.incoming[y]?).getD [] = ns0 ++ (acc.incoming[y]?).getD [] ∧
        (a.incomingImpl[y]?).getD [] = nis0 ++ (acc.incomingImpl[y]?).getD [] ∧
        (acc.incoming.size = acc.incomingImpl.size → ns0.length = nis0.length) ∧
        ∀ s ∈ ns0, ex.target.label = y ∧ ∃ imp, s = exitPushed env l en sd ex imp := by
      cases hh : env.isHead[ex.target.label]! with
      | true =>
        have hc := he.head hh
        exact ⟨[], [], by rw [hc.incoming]; rfl, by rw [hc.incomingImpl]; rfl, fun _ => rfl, by simp⟩
      | false =>
        obtain ⟨imp, car, h1, h2, -, -, -⟩ := he.push hh
        rw [h1, h2]
        by_cases hy : y = ex.target.label
        · subst hy
          rw [getD_modify_cons, getD_modify_cons]
          refine ⟨_, _, rfl, rfl, fun hs => ?_, fun s hs => ?_⟩
          · rw [hs]; split <;> rfl
          · split at hs
            · exact ⟨rfl, imp, List.mem_singleton.mp hs⟩
            · cases hs
        · rw [getD_modify_ne _ _ _ _ _ hy, getD_modify_ne _ _ _ _ _ hy]
          exact ⟨[], [], rfl, rfl, fun _ => rfl, by simp⟩
    obtain ⟨ns0, nis0, o1, o2, o3, o4⟩ := hone
    refine ⟨ns ++ ns0, nis ++ nis0, by rw [g1, o1, List.append_assoc], by rw [g2, o2, List.append_assoc],
      fun hs => ?_, fun s hs => ?_⟩
    · rw [List.length_append, List.length_append, g3 (by rw [hsz.1, hsz.2]; exact hs), o3 hs]
    · rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨e, hex, hey⟩ := g4 s hs
        exact ⟨e, List.mem_cons_of_mem _ hex, hey⟩
      · obtain ⟨hey, hp⟩ := o4 s hs
        exact ⟨ex, List.mem_cons_self .., hey, hp⟩
  · obtain ⟨e0, he0, het⟩ := he.edges
    obtain ⟨new, hn1, hn2⟩ := hf.edges
    refine ⟨e0 :: new, by rw [hn1, he0, Array.toList_push, List.append_assoc]; rfl, fun e he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · rw [het]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hn2 e he')
  · intro y hy
    rw [hf.degs y hy, hdeg y, List.map_cons, List.count_cons]
    by_cases hyx : y = ex.target.label
    · subst hyx; rw [if_pos ⟨rfl, hy⟩]; simp; omega
    · rw [if_neg (fun h => hyx h.1)]
      have : (ex.target.label == y) = false := by simp; exact Ne.symm hyx
      rw [this]; simp
  · intro y; exact Nat.le_trans (hf.mono y) (hdeg_le y)
  · obtain ⟨new, q1, q2, q3⟩ := hf.queue
    -- The one exit's queue.
    have hq : ∃ new0, a.queue = new0 ++ acc.queue ∧ new0.length ≤ 1 ∧
        (∀ y ∈ new0, y = ex.target.label ∧ env.isHead[y]! = false ∧ dg a.indeg y = 0) := by
      cases hh : env.isHead[ex.target.label]! with
      | true => exact ⟨[], by rw [(he.head hh).queue]; rfl, by simp, by simp⟩
      | false =>
        obtain ⟨_, _, -, -, -, h4, h5⟩ := he.push hh
        rw [h5]
        split
        · rename_i h0
          refine ⟨[ex.target.label], rfl, by simp, fun y hy => ?_⟩
          rw [List.mem_singleton.mp hy]
          refine ⟨rfl, hh, ?_⟩
          unfold dg; rw [h4]
          have := beq_iff_eq.mp h0
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] at this
          exact this
        · exact ⟨[], rfl, by simp, by simp⟩
    obtain ⟨new0, r1, rlen, r2⟩ := hq
    refine ⟨new ++ new0, by rw [q1, r1, List.append_assoc], fun y hy => ?_, fun hc => ?_⟩
    · rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨m1, m2, m3⟩ := q2 y hy
        exact ⟨List.mem_cons_of_mem _ m1, m2, m3⟩
      · obtain ⟨m1, m2, m3⟩ := r2 y hy
        refine ⟨m1 ▸ List.mem_cons_self .., m2, ?_⟩
        have := hf.mono y; omega
    · have hc' : ∀ y, env.isHead[y]! = false → (xs.map (·.target.label)).count y ≤ dg a.indeg y := by
        intro y hy
        have h1 := hc y hy
        rw [List.map_cons, List.count_cons] at h1
        rw [hdeg y]
        by_cases hyx : y = ex.target.label
        · subst hyx; rw [if_pos ⟨rfl, hy⟩]; simp at h1; omega
        · rw [if_neg (fun h => hyx h.1)]
          have : (ex.target.label == y) = false := by simp; exact Ne.symm hyx
          rw [this] at h1; simpa using h1
      refine List.nodup_append.mpr ⟨q3 hc', ?_, fun x hx y hy hxy => ?_⟩
      · match new0, rlen with
        | [], _ => exact List.nodup_nil
        | [z], _ => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      · subst hxy
        obtain ⟨m1, m2, m3⟩ := r2 x hy
        have hxin := (q2 x hx).1
        have h1 := hc' x m2
        rw [m3] at h1
        have := List.count_pos_iff.mpr hxin
        omega

/-- **The exits' fold** (`visitExits`' `foldlM` of `exitStep`) gives
`ExitsFold` over its exits (`exitStep_effect`, `ExitsFold.cons`). -/
theorem exitsFold_of {env : SinglePass.WalkEnv ι G I} {l : Nat} {en : SinglePass.Entered ι}
    {sd : SinglePass.StepDone ι G} {ysAll : List (PromiseCalls.Yield ι)} {outAll : Thunk HeapKnowledge.Knowledge} :
    ∀ (es : List (SinglePass.Exit × Nat)) (acc r : SinglePass.ExitsDone ι G),
      es.foldlM (SinglePass.exitStep G I env l en sd ysAll outAll) acc = .ok r →
      ExitsFold env l en sd (es.map (·.1)) acc r
  | [], acc, r, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ExitsFold.nil env l en sd acc
  | e :: es, acc, r, h => by
    rw [List.foldlM_cons] at h
    cases ha : SinglePass.exitStep G I env l en sd ysAll outAll acc e with
    | error stop => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      exact ExitsFold.cons (exitStep_effect ha) (exitsFold_of es a r h)

/-- **A node's exits that return** (`visitExits`): the fold of its exits
from the walk's arrays, queue and in-degrees gives `ExitsFold`. -/
theorem visitExits_fold {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G} {l : Nat}
    {en : SinglePass.Entered ι} {sd : SinglePass.StepDone ι G} {ex : SinglePass.ExitsDone ι G}
    (h : SinglePass.visitExits G I env σ l en sd = .ok ex) :
    ∃ acc0 : SinglePass.ExitsDone ι G, acc0.incoming = σ.walk.incoming ∧ acc0.incomingImpl = σ.walk.incomingImpl ∧
      acc0.incomingEdges = σ.walk.incomingEdges ∧ acc0.edges = σ.walk.edges ∧ acc0.indeg = σ.indeg ∧
      acc0.queue = σ.queue ∧ ExitsFold env l en sd (SinglePass.Exit.ofNode env.nodes[l]!) acc0 ex := by
  unfold SinglePass.visitExits at h
  extract_lets node c at h
  split at h
  extract_lets outAll regional at h
  generalize regional = R at h
  split at h
  · cases h
  · have := exitsFold_of _ _ _ h
    rw [List.zipIdx_map_fst] at this
    refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, this⟩ <;> rfl

end Exits
end Verification.TolerantFrames
