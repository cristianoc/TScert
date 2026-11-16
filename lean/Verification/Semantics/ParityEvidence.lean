import Verification.Semantics.ParityAssertions
import Verification.Semantics.Survival
import Verification.Semantics.RegionBounds

/-! # Parity evidence: substitution, marks and support contexts

The semantic evidence of the design `docs/drafts/parity-interfaces.md`, I5,
that reads no region membership: the construction of a substituted
assertion, checked by the substitution check of `AssertionScopes` (I5,
"Substitution and marks"), the transport of freshness between marks, the
meaning of a rigid path (the note, §4, `rigid(π) ≜ ∃v. □_⊤ (π ≐ v)`), and
support contexts throughout a modality (I5, "Support contexts throughout a
modality"; the note, §5, "Support", "Respect", Theorem "Tolerant frame"). -/
namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

/-! ## Building a substituted assertion -/

/-- Node `i` of `src` under `θ`, its nodes appended to `acc`: the reference
of the new node. Shared subterms are rebuilt where they occur. -/
def substBuild (src : Array AssertionNode) (θ : Substitution) (i : Nat) (acc : Array AssertionNode) :
    Option (Array AssertionNode × Nat) :=
  let push := fun (acc : Array AssertionNode) (n : AssertionNode) => some (acc.push n, acc.size)
  match src[i]? with
  | some .truth => push acc .truth
  | some .falsity => push acc .falsity
  | some (.atom x) => (substAtom θ x).bind fun y => push acc (.atom y)
  | some (.and l r) =>
    if _ : l.index < i ∧ r.index < i then do
      let (acc, l') ← substBuild src θ l.index acc
      let (acc, r') ← substBuild src θ r.index acc
      push acc (.and ⟨l'⟩ ⟨r'⟩)
    else none
  | some (.guarded l r) =>
    if _ : l.index < i ∧ r.index < i then do
      let (acc, l') ← substBuild src θ l.index acc
      let (acc, r') ← substBuild src θ r.index acc
      push acc (.guarded ⟨l'⟩ ⟨r'⟩)
    else none
  | some (.existsValue b) =>
    if _ : b.index < i then do
      let (acc, b') ← substBuild src θ.lift b.index acc
      push acc (.existsValue ⟨b'⟩)
    else none
  | some (.separated p q) => do push acc (.separated (← substPath θ p) (← substPath θ q))
  | some (.apart p q) => do push acc (.apart (← substPath θ p) (← substPath θ q))
  | some (.fresh p) => do push acc (.fresh (← substPath θ p))
  | some (.box Φ b) =>
    if _ : b.index < i then do
      let Ψ ← renameEffect θ Φ
      let (acc, b') ← substBuild src θ.box b.index acc
      push acc (.box Ψ ⟨b'⟩)
    else none
  | none => none
termination_by i

/-- `nodes'` extends `nodes`: it has every node of `nodes` at its index. -/
def AssertionArena.extends (nodes' nodes : Array AssertionNode) : Bool :=
  decide (nodes.size ≤ nodes'.size) && (List.range nodes.size).all fun j => nodes'[j]? == nodes[j]?

/-- **An extended arena satisfies its old nodes as they were.** -/
theorem satNode_extend {nodes nodes' : Array AssertionNode} (he : AssertionArena.extends nodes' nodes = true) :
    ∀ i, i < nodes.size → ∀ η m s, satNode nodes' i η m s ↔ satNode nodes i η m s := by
  have hj : ∀ j, j < nodes.size → nodes'[j]? = nodes[j]? := by
    intro j hjs
    simp only [AssertionArena.extends, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at he
    exact he.2 j hjs
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi η m s
  rw [satNode, satNode, hj i hi]
  cases hn : nodes[i]? with
  | none => exact Iff.rfl
  | some n =>
    cases n with
    | and l r =>
      dsimp only
      apply and_congr
      · by_cases hl : l.index < i
        · simp only [hl, dite_true]; exact ih _ hl (by omega) η m s
        · simp only [hl, dite_false]
      · by_cases hr : r.index < i
        · simp only [hr, dite_true]; exact ih _ hr (by omega) η m s
        · simp only [hr, dite_false]
    | guarded l r =>
      dsimp only
      apply or_congr
      · by_cases hl : l.index < i
        · simp only [hl, dite_true]; exact ih _ hl (by omega) η m s
        · simp only [hl, dite_false]
      · by_cases hr : r.index < i
        · simp only [hr, dite_true]; exact ih _ hr (by omega) η m s
        · simp only [hr, dite_false]
    | existsValue b =>
      dsimp only
      by_cases hb : b.index < i
      · simp only [hb, dite_true]; exact exists_congr fun v => ih _ hb (by omega) _ m s
      · simp only [hb, dite_false]
    | box Φ b =>
      dsimp only
      by_cases hb : b.index < i
      · simp only [hb, dite_true]; exact forall_congr' fun s' => imp_congr_right fun _ => ih _ hb (by omega) η m s'
      · simp only [hb, dite_false]
    | _ => exact Iff.rfl

/-- **Substitution into an assertion** (I5, `substAssertion`): the arena
extended by `A` under `θ`, and the new node's reference. The result is
checked: it extends the arena, it is valid, and its node is `A[θ]`. -/
def substAssertion (arena : AssertionArena) (θ : Substitution) (A : AssertionRef) :
    Except String (AssertionArena × AssertionRef) :=
  match substBuild arena.nodes θ A.index arena.nodes with
  | some (nodes', r) =>
    if A.index < arena.nodes.size && AssertionArena.extends nodes' arena.nodes &&
        substCheck nodes' θ A.index r && AssertionArena.check ⟨nodes'⟩ then
      .ok (⟨nodes'⟩, ⟨r⟩)
    else .error "substAssertion: the substituted assertion is not well formed"
  | none => .error "substAssertion: a slot is outside the substitution"

/-- **Substitution into an assertion is semantic** (I5,
`substAssertion_sound`): the result is a valid extension in which the new
node holds at `source` exactly where `A` holds at `target`. -/
theorem substAssertion_sound {arena arena' : AssertionArena} {θ : Substitution} {A A' : AssertionRef}
    (hc : substAssertion arena θ A = .ok (arena', A')) {target source : Env} {m : Nat} {s : IndexedHeap}
    (hθ : θ.HoldsAt target source s) :
    arena'.Valid ∧ (Sat arena' source m s A' ↔ Sat arena target m s A) := by
  unfold substAssertion at hc
  split at hc
  · rename_i nodes' r _
    split at hc
    · rename_i hok
      cases hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hA, hext⟩, hsub⟩, hvalid⟩ := hok
      refine ⟨AssertionArena.check_valid hvalid, ?_⟩
      have h1 := substCheck_sound nodes' _ A.index r rfl θ target source m s hsub hθ
      exact h1.trans (satNode_extend hext A.index hA target m s)
    · cases hc
  · cases hc

/-! ## Marks -/

/-- **Caller and callee marks** (I5, `MarkEvidence`): the callee's entry
mark is at or above its caller's. -/
structure MarkEvidence where
  caller : Nat
  callee : Nat
  ordered : caller ≤ callee

/-- **Freshness transport is directional** (I5, `fresh_mark_mono`): a spine
fresh for a later callee mark is fresh for the caller. -/
theorem fresh_mark_mono {caller callee : Nat} (hm : caller ≤ callee) {v : Val} (hf : FreshAt callee v) :
    FreshAt caller v :=
  hf.lower hm

theorem freshPath_mark_mono (e : MarkEvidence) {η : Env} {h : Heap} {p : Path}
    (hf : FreshPath η e.callee h p) : FreshPath η e.caller h p := by
  obtain ⟨v, hv, hfv⟩ := hf
  exact ⟨v, hv, fresh_mark_mono e.ordered hfv⟩

/-! ## Rigid paths -/

/-- **The meaning of a rigid path** (I5, `PathRigid`; the note, §4,
`rigid(π)`): the path reads one value after every admissible transition. -/
def PathRigid (p : Path) (η : Env) (s : IndexedHeap) : Prop :=
  ∃ v, ∀ s', Admissible s s' → p.read η s'.h = some v

/-- **The note's `rigid(π) ≜ ∃v. □_⊤ (π ≐ v)` is `PathRigid`**: for an arena
whose node `a` is `∃v. □_⊤ (π' ≐ v)`, `π'` being `π` read under the binder. -/
theorem sat_rigid_iff {arena : AssertionArena} (hv : arena.Valid) {a b c : AssertionRef} {p : Path}
    (ha : arena.nodes[a.index]? = some (.existsValue b)) (hb : arena.nodes[b.index]? = some (.box topEffect c))
    (hc : arena.nodes[c.index]? = some (.atom (.equal ⟨p.root + 1, p.fields⟩ (.path (Path.var 0)))))
    {η : Env} {m : Nat} {s : IndexedHeap} : Sat arena η m s a ↔ PathRigid p η s := by
  rw [sat_exists hv ha]
  have hread : ∀ (v : Val) (h : Heap), (⟨p.root + 1, p.fields⟩ : Path).read (push v η) h = p.read η h :=
    fun _ _ => rfl
  constructor
  · rintro ⟨v, hv'⟩
    refine ⟨v, fun s' hs' => ?_⟩
    have := (sat_atom hc).mp ((sat_box hv hb).mp hv' s' (EffectAction.top hs'))
    obtain ⟨u, hu, hw⟩ := this
    rw [hread] at hu
    simp only [Witness.value, Path.read, Path.var, readPath] at hw
    cases hw
    exact hu
  · rintro ⟨v, hv'⟩
    refine ⟨v, (sat_box hv hb).mpr fun s' hs' => (sat_atom hc).mpr ⟨v, ?_, rfl⟩⟩
    rw [hread]; exact hv' s' hs'.admissible

/-! ## Support contexts and the tolerant frame -/

/-- **A contextual support** (I5, `SupportContext`): a condition on both
endpoints of a transition. -/
abbrev SupportContext := Env → Nat → IndexedHeap → IndexedHeap → Prop

/-- **`S` supports `A` in the context `C`** (the note, §5, Definition
"Support", read in a context; I5, `Supports`): `SupportDomain.Supports`
over indexed states, of `A`'s satisfaction. -/
abbrev Supports (arena : AssertionArena) (C : SupportContext) (S : Footprint) (A : AssertionRef) : Prop :=
  indexed.Supports C (fun η m s => Sat arena η m s A) S

/-- **The condition of a support holds of every action of `Φ` from a state
of `K`** (the note, §5, Theorem "Tolerant frame", its premise on the
condition): `SupportDomain.ConditionOnActions` over indexed states. -/
abbrev ConditionOnActions (arena : AssertionArena) (K : AssertionRef) (Φ : Footprint) (C : SupportContext) : Prop :=
  indexed.ConditionOnActions (fun η m s => Sat arena η m s K) Φ C

/-- **The tolerant frame theorem** (the note, §5, Theorem "Tolerant
frame"): `K ∧ A ⊢ □_Φ A` where `S` supports `A` under a condition holding of
every action of `Φ` from a state of `K`, and `Φ` respects `S` under a query
sound at every state of `K`; `frame_box` over indexed states. -/
theorem tolerant_frame {arena : AssertionArena} {C : SupportContext} {S Φ : Footprint} {K A : AssertionRef}
    {q : SepQuery} (hs : Supports arena C S A) (hr : respects q S Φ = true)
    (hq : ∀ η m s, Sat arena η m s K → q.Sound η s.h) (hc : ConditionOnActions arena K Φ C) :
    ∀ η m s, Sat arena η m s K → Sat arena η m s A → ∀ s', EffectAction Φ η s s' → Sat arena η m s' A :=
  frame_box hs hr hq hc

/-- The references whose nodes are conjuncts of node `k`: `k` itself and,
through `∧`, those of its two sides. -/
def conjuncts (nodes : Array AssertionNode) (k : Nat) : List Nat :=
  k :: match nodes[k]? with
    | some (.and l r) =>
      (if _ : l.index < k then conjuncts nodes l.index else []) ++
        (if _ : r.index < k then conjuncts nodes r.index else [])
    | _ => []
termination_by k

/-- Each conjunct of a node holds where the node does. -/
theorem conjuncts_sat (nodes : Array AssertionNode) :
    ∀ k, ∀ g ∈ conjuncts nodes k, ∀ η m s, satNode nodes k η m s → satNode nodes g η m s := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro g hg η m s hk
  rw [conjuncts] at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hk
  · split at hg
    · rename_i l r hn
      rw [satNode, hn] at hk
      rcases List.mem_append.mp hg with hg | hg
      · split at hg
        · rename_i hl; simp only [hl, dite_true] at hk; exact ih _ hl g hg η m s hk.1
        · cases hg
      · split at hg
        · rename_i hr; simp only [hr, dite_true] at hk; exact ih _ hr g hg η m s hk.2
        · cases hg
    · cases hg

/-- **Finite context evidence** (I5, `ContextEvidence`): the context `true`,
the well-formedness of both states, an invariant conjunct of `K`, and
conjunctions. Weakening through a derivation is the `tolerantFrame` rule's:
its context evidence is checked against an assertion derived from `K`. -/
inductive ContextEvidence where
  | truth
  | wellFormed
  | invariant (g : AssertionRef)
  | conj (a b : ContextEvidence)
  deriving DecidableEq, Repr

/-- The context the evidence denotes: an invariant conjunct holds at both
endpoints. -/
def ContextEvidence.ctx (arena : AssertionArena) : ContextEvidence → SupportContext
  | .truth => fun _ _ _ _ => True
  | .wellFormed => fun _ _ s s' => HeapOk s.n s.W s.h ∧ HeapOk s'.n s'.W s'.h
  | .invariant g => fun η m s s' => Sat arena η m s g ∧ Sat arena η m s' g
  | .conj a b => fun η m s s' => a.ctx arena η m s s' ∧ b.ctx arena η m s s'

/-- The check of context evidence against `K`: an invariant conjunct is a
conjunct of `K` with checked invariance. -/
def ContextEvidence.check (arena : AssertionArena) (K : AssertionRef) : ContextEvidence → Bool
  | .truth | .wellFormed => true
  | .invariant g => (conjuncts arena.nodes K.index).contains g.index && invNode arena.nodes g.index
  | .conj a b => a.check arena K && b.check arena K

/-- **Checked context evidence holds of every action of `Φ` from a state of
`K`.** -/
theorem ContextEvidence.sound {arena : AssertionArena} {K : AssertionRef} {Φ : Footprint} :
    ∀ ev : ContextEvidence, ev.check arena K = true → ConditionOnActions arena K Φ (ev.ctx arena)
  | .truth, _ => fun _ _ _ _ _ _ => trivial
  | .wellFormed, _ => fun _ _ s s' _ _ => ⟨s.ok, s'.ok⟩
  | .invariant g, hc => by
    simp only [ContextEvidence.check, Bool.and_eq_true, List.contains_iff_mem] at hc
    intro η m s s' hK ha
    have hg : Sat arena η m s g := conjuncts_sat arena.nodes K.index g.index hc.1 η m s hK
    exact ⟨hg, invNode_sound arena.nodes g.index hc.2 η m s s' ha.1 hg⟩
  | .conj a b, hc => by
    simp only [ContextEvidence.check, Bool.and_eq_true] at hc
    intro η m s s' hK ha
    exact ⟨a.sound hc.1 η m s s' hK ha, b.sound hc.2 η m s s' hK ha⟩

/-! ## Finite certificates of the modal rules

The general modal rules (the note, §4, laws (c) and (e); §5, Theorem
"Tolerant frame"; §6, Frame⁺) consume finite certificates of effect
inclusion, whole-effect rigidity, support, respect and context. Each
certificate type states its semantic obligation and proves it for every
constructor; the regional instances join as constructors with their proofs,
the rules unchanged. -/

/-- **Effect inclusion under `K`** (the note's `Φ ⊑ Ψ`, law (c)): from a
state of `K`, every action of `Φ` is one of `Ψ`. -/
def Included (arena : AssertionArena) (K : AssertionRef) (Φ Ψ : Footprint) : Prop :=
  ∀ η m s s', Sat arena η m s K → EffectAction Φ η s s' → EffectAction Ψ η s s'

/-! ### The class a region lies in -/

/-- A node stating that the path reads an ordinary array: a dense prefix, a
bounded quantification, a linear fact reading its length, a spine
separation or an apartness naming it. -/
def arrayNode (n : AssertionNode) (π : Path) : Bool :=
  match n with
  | .atom (.dense q _) | .atom (.every q _ _) => q == π
  | .atom (.linear F) => F.vars.contains (π.term .length)
  | .separated q q' | .apart q q' => q == π || q' == π
  | _ => false

theorem arrayNode_sound {arena : AssertionArena} {c : AssertionRef} {n : AssertionNode}
    (hn : arena.nodes[c.index]? = some n) {π : Path} (ha : arrayNode n π = true) {η : Env} {m : Nat}
    {s : IndexedHeap} (hs : Sat arena η m s c) :
    ∃ u st ls, π.read η s.h = some u ∧ spineOf u = some st ∧ s.h[st]? = some (.arr ls) := by
  cases n with
  | atom a =>
    have hs' := (sat_atom hn).mp hs
    cases a <;> simp only [arrayNode, beq_iff_eq, reduceCtorEq] at ha
    · rename_i F
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hs'.1 _ (List.contains_iff_mem.mp ha))
      rw [Path.termAt_term] at hn
      obtain ⟨u, hu, hl⟩ := Option.bind_eq_some_iff.mp hn
      obtain ⟨st, ls, hst, hls, -, -⟩ := lengthOf_spine hl
      exact ⟨u, st, ls, hu, hst, hls⟩
    · subst ha; obtain ⟨w, st, ls, _, hw, hst, hls, -⟩ := hs'; exact ⟨w, st, ls, hw, hst, hls⟩
    · subst ha; obtain ⟨w, st, ls, _, hw, hst, hls, -⟩ := hs'; exact ⟨w, st, ls, hw, hst, hls⟩
  | separated q q' =>
    obtain ⟨u, w, st, t, xs, ys, hu, hw, ⟨hsu, -, hxs⟩, ⟨htw, -, hys⟩, -⟩ := (sat_separated hn).mp hs
    simp only [arrayNode, Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with rfl | rfl
    · exact ⟨u, st, xs, hu, hsu, hxs⟩
    · exact ⟨w, t, ys, hw, htw, hys⟩
  | apart q q' =>
    obtain ⟨u, w, st, t, xs, ys, hu, hw, ⟨hsu, -, hxs⟩, ⟨htw, -, hys⟩, -⟩ := (sat_apart hn).mp hs
    simp only [arrayNode, Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with rfl | rfl
    · exact ⟨u, st, xs, hu, hsu, hxs⟩
    · exact ⟨w, t, ys, hw, htw, hys⟩
  | _ => simp [arrayNode] at ha

/-- **Evidence of the class a region's locations lie in** under `K` (the
note, §3, "Regions": value locations, array spines and view spines partition
the heap): the class every well-formed state gives it (`regionClass`); the
spine at a path a conjunct of `K` shows an ordinary array's (arrays); the
field at a path a conjunct of `K` shows holding a value (values). -/
inductive ClassWitness where
  | intrinsic
  | arrayAt (c : AssertionRef)
  | fieldAt (c : AssertionRef)
  deriving DecidableEq, Repr

def ClassWitness.selector (arena : AssertionArena) (K : AssertionRef) (r : Region) : ClassWitness → Option Selector
  | .intrinsic => regionClass r
  | .arrayAt c =>
    if (conjuncts arena.nodes K.index).contains c.index then
      match r, arena.nodes[c.index]? with
      | .spine x p, some n => if arrayNode n ⟨x, p⟩ then some .arrays else none
      | _, _ => none
    else none
  | .fieldAt c =>
    if (conjuncts arena.nodes K.index).contains c.index then
      match r, arena.nodes[c.index]? with
      | .path x p (.str f), some (.atom (.equal q (.literal v))) =>
        if q == ⟨x, p ++ [f]⟩ && contentsCategory v == .value then some .values else none
      | _, _ => none
    else none

private theorem readPath_snoc (h : Heap) (x : Val) (p : List String) (f : String) :
    readPath h x (p ++ [f]) = (readPath h x p).bind fun v => readPath h v [f] := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih =>
    cases x <;> simp only [List.cons_append, readPath, Option.bind_none]
    split
    · split
      · exact ih _
      · rfl
    · rfl

theorem ClassWitness.sound {arena : AssertionArena} {K : AssertionRef} {r : Region}
    {a : Selector} : ∀ w : ClassWitness, w.selector arena K r = some a →
      ∀ η m s, Sat arena η m s K → ∀ l, r.mem η s.h l = true → (Region.cls a).mem η s.h l = true
  | .intrinsic, h, η, m, s, _, l, hl => regionClass_sound h hl
  | .arrayAt c, h, η, m, s, hK, l, hl => by
    simp only [ClassWitness.selector] at h
    split at h
    · rename_i hc
      have hcs : Sat arena η m s c :=
        conjuncts_sat arena.nodes K.index c.index (List.contains_iff_mem.mp hc) η m s hK
      split at h
      · rename_i x p n hn
        split at h
        · rename_i ha
          cases h
          obtain ⟨u, st, ls, hu, hst, hls⟩ := arrayNode_sound hn ha hcs
          simp only [Region.mem] at hl
          simp only [Path.read] at hu
          rw [hu] at hl
          simp only [elementsOf_spine hst, beq_iff_eq, Option.some.injEq] at hl
          subst hl
          simp [Region.mem, hls, Selector.selects, contentsCategory, Selector.has]
        · cases h
      · cases h
    · cases h
  | .fieldAt c, h, η, m, s, hK, l, hl => by
    simp only [ClassWitness.selector] at h
    split at h
    · rename_i hc
      have hcs : Sat arena η m s c :=
        conjuncts_sat arena.nodes K.index c.index (List.contains_iff_mem.mp hc) η m s hK
      split at h
      · rename_i x p f q v hn
        split at h
        · rename_i hq
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hq
          obtain ⟨rfl, hcat⟩ := hq
          obtain ⟨u, hu, hw⟩ := (sat_atom hn).mp hcs
          simp only [Witness.value, Option.some.injEq] at hw
          subst hw
          simp only [Region.mem] at hl
          split at hl
          · rename_i o ho
            simp only [beq_iff_eq] at hl
            simp only [Path.read, readPath_snoc, ho, Option.bind_some] at hu
            cases o with
            | objAt fs cd oid =>
              simp only [fieldsOf] at hl
              simp only [readPath, hl] at hu
              split at hu
              · rename_i u' hu'
                simp only [Option.some.injEq] at hu
                subst hu
                simp [Region.mem, hu', Selector.selects, hcat, Selector.has]
              · cases hu
            | _ => simp [fieldsOf] at hl
          · cases hl
        · cases h
      · cases h
    · cases h

/-! ### Inclusion -/

/-- Finite evidence of inclusion: equal effects, closed effects in their
order, entrywise region inclusion with a smaller change
(`Footprints.Footprint.le` by `Region.sub`, `Selector.sub` on classes), and
each entry within a class entry of `Ψ`, its class given by a witness under
`K`. -/
inductive InclusionEvidence where
  | refl
  | closed (a b : Footprints.Closed)
  | regions
  | byClass (ws : List ClassWitness)
  deriving DecidableEq, Repr

def InclusionEvidence.check (arena : AssertionArena) (K : AssertionRef) (Φ Ψ : Footprint) :
    InclusionEvidence → Bool
  | .refl => Φ == Ψ
  | .closed a b => Φ == a.fp && Ψ == b.fp && a.le b
  | .regions => Footprint.le (fun _ _ => none) Φ Ψ
  | .byClass ws => (List.range Φ.length).all fun i => match Φ[i]?, ws[i]? with
    | some e, some w => match w.selector arena K e.1 with
      | some a => Ψ.any fun e' => match e'.1 with
        | .cls b => a.sub b && e.2.le e'.2
        | _ => false
      | none => false
    | _, _ => false

theorem InclusionEvidence.sound {arena : AssertionArena} {K : AssertionRef} {Φ Ψ : Footprint} :
    ∀ ev : InclusionEvidence, ev.check arena K Φ Ψ = true → Included arena K Φ Ψ
  | .refl, h => by
    simp only [InclusionEvidence.check, beq_iff_eq] at h
    subst h; exact fun _ _ _ _ _ ha => ha
  | .closed a b, h => by
    simp only [InclusionEvidence.check, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, hle⟩ := h
    exact fun _ _ _ _ _ ha => EffectAction.closed_mono hle ha
  | .regions, h => fun _ _ _ _ _ ha => EffectAction.regions_mono h ha
  | .byClass ws, h => by
    simp only [InclusionEvidence.check, List.all_eq_true, List.mem_range] at h
    intro η m s s' hK ha
    refine EffectAction.mono_entries (fun e he l hl => ?_) ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hc := h i hi
    rw [List.getElem?_eq_getElem hi] at hc
    cases hw : ws[i]? with
    | none => simp [hw] at hc
    | some w =>
      simp only [hw] at hc
      cases ha' : w.selector arena K Φ[i].1 with
      | none => simp [ha'] at hc
      | some a =>
        simp only [ha'] at hc
        obtain ⟨e', he', hc'⟩ := List.any_eq_true.mp hc
        split at hc'
        · rename_i b hb
          simp only [Bool.and_eq_true] at hc'
          refine ⟨e', he', ?_, hc'.2⟩
          rw [hb]
          exact class_subset_sound hc'.1 (w.sound ha' η m s hK l hl)
        · cases hc'

/-! ### Rigidity -/

/-- **Whole-effect rigidity on a domain** (I5, `rigidity_sound`): from a
state of the domain `D`, an action of `Φ` reaches a state of `D`, and two
actions in sequence are one. -/
def RigidOnDomain (arena : AssertionArena) (D : AssertionRef) (Φ : Footprint) : Prop :=
  ∀ η m s₀ s₁ s₂, Sat arena η m s₀ D → EffectAction Φ η s₀ s₁ → EffectAction Φ η s₁ s₂ →
    Sat arena η m s₁ D ∧ EffectAction Φ η s₀ s₂

/-- The path a node states rigid: `∃v. □_⊤ (π ≐ v)` (`sat_rigid_iff`). -/
def rigidPathOf (nodes : Array AssertionNode) (c : AssertionRef) : Option Path :=
  match nodes[c.index]? with
  | some (.existsValue b) => match nodes[b.index]? with
    | some (.box Φ e) => if Φ == topEffect then match nodes[e.index]? with
      | some (.atom (.equal q (.path w))) =>
        if q.root ≠ 0 ∧ w == Path.var 0 then some ⟨q.root - 1, q.fields⟩ else none
      | _ => none else none
    | _ => none
  | _ => none

theorem rigidPathOf_sound {arena : AssertionArena} (hv : arena.Valid) {c : AssertionRef} {π : Path}
    (h : rigidPathOf arena.nodes c = some π) {η : Env} {m : Nat} {s : IndexedHeap} (hs : Sat arena η m s c) :
    PathRigid π η s := by
  unfold rigidPathOf at h
  split at h
  · rename_i b hb
    split at h
    · rename_i Φ e he
      split at h
      · rename_i hΦ
        simp only [beq_iff_eq] at hΦ
        subst hΦ
        split at h
        · rename_i q w hq
          split at h
          · rename_i hw
            obtain ⟨hr, hw⟩ := hw
            simp only [beq_iff_eq] at hw
            subst hw
            cases h
            have hq' : arena.nodes[e.index]? = some (.atom (.equal ⟨(q.root - 1) + 1, q.fields⟩ (.path (Path.var 0)))) := by
              rw [hq]; congr; obtain ⟨r, f⟩ := q; simp only at hr ⊢; congr 1; omega
            exact (sat_rigid_iff hv (p := ⟨q.root - 1, q.fields⟩) hb he hq').mp hs
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Finite evidence of rigidity: a closed effect, on an invariant domain;
and an effect whose every region reads the same locations along its
actions (`stableRegion`), the paths it reads at rigid by conjuncts of the
invariant domain (the note, §3, "Rigid: a spine at a rigid path"). -/
inductive RigidityEvidence where
  | closed (c : Footprints.Closed)
  | stable (rigid : List AssertionRef)
  deriving DecidableEq, Repr

/-- The rigid paths the listed conjuncts of `D` state. -/
def rigidPaths (arena : AssertionArena) (D : AssertionRef) (rigid : List AssertionRef) : Option (List Path) :=
  rigid.mapM fun c => if (conjuncts arena.nodes D.index).contains c.index then rigidPathOf arena.nodes c else none

def RigidityEvidence.check (arena : AssertionArena) (D : AssertionRef) (Φ : Footprint) : RigidityEvidence → Bool
  | .closed c => Φ == c.fp && invNode arena.nodes D.index
  | .stable rigid => invNode arena.nodes D.index && match rigidPaths arena D rigid with
    | some ps => Φ.all fun e => stableRegion (ps.map fun π => (π.root, π.fields)) e.1
    | none => false

private theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h => by simp at h; subst h; simp
  | a :: t, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b0, hb0, t', ht, rfl⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hb0⟩
    · obtain ⟨a', ha', hf⟩ := mapM_mem ht b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hf⟩

theorem RigidityEvidence.sound {arena : AssertionArena} (hv : arena.Valid) {D : AssertionRef} {Φ : Footprint} :
    ∀ ev : RigidityEvidence, ev.check arena D Φ = true → RigidOnDomain arena D Φ
  | .closed c, h => by
    simp only [RigidityEvidence.check, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hinv⟩ := h
    intro η m s₀ s₁ s₂ hD a₁ a₂
    exact ⟨invNode_sound arena.nodes D.index hinv η m s₀ s₁ a₁.admissible hD, EffectAction.closed_trans c a₁ a₂⟩
  | .stable rigid, h => by
    simp only [RigidityEvidence.check, Bool.and_eq_true] at h
    obtain ⟨hinv, hps⟩ := h
    split at hps
    · rename_i ps hps'
      intro η m s₀ s₁ s₂ hD a₁ a₂
      refine ⟨invNode_sound arena.nodes D.index hinv η m s₀ s₁ a₁.admissible hD, ?_⟩
      have hread : ∀ xp ∈ ps.map (fun π => (π.root, π.fields)),
          readPath s₁.h (η xp.1) xp.2 = readPath s₀.h (η xp.1) xp.2 := by
        intro xp hxp
        obtain ⟨π, hπ, rfl⟩ := List.mem_map.mp hxp
        obtain ⟨c, -, hc⟩ := mapM_mem hps' π hπ
        split at hc
        · rename_i hcon
          have hcs := conjuncts_sat arena.nodes D.index c.index (List.contains_iff_mem.mp hcon) η m s₀ hD
          obtain ⟨v, hv'⟩ := rigidPathOf_sound hv hc hcs
          have h1 := hv' s₁ a₁.admissible
          have h0 := hv' s₀ (Admissible.refl s₀)
          simp only [Path.read] at h0 h1
          rw [h0, h1]
        · cases hc
      exact EffectAction.trans_stable (fun e he l hl =>
        region_mem_stable a₁.admissible hread (List.all_eq_true.mp hps e he) l hl) a₁ a₂
    · cases hps

/-! ### Disjointness and respect -/

/-- **Disjointness of two regions under `K`** (the note, §5, Definition
"Respect"): at a state of `K`, no allocated location is in both. -/
def DisjointUnder (arena : AssertionArena) (K : AssertionRef) (r r' : Region) : Prop :=
  ∀ η m s, Sat arena η m s K → ∀ l, l < s.h.length → r.mem η s.h l = true → r'.mem η s.h l = false

/-- Finite evidence of disjointness under `K`: regions in class regions
whose bounds hold no role class in common (`Region.bound`,
`Region.cls_apart_of_bound`), each class by a witness; the
spines of two paths a conjunct separates (`π # π'` or `apart`); the cells of
two paths a conjunct states apart; and either of these in the other order. -/
inductive DisjointEvidence where
  | classes (a b : ClassWitness)
  | spines (c : AssertionRef)
  | cells (c : AssertionRef)
  | swap (d : DisjointEvidence)
  deriving DecidableEq, Repr

/-- The two paths a separating node names. -/
def separatedPaths : Option AssertionNode → Option (Path × Path)
  | some (.separated q q') | some (.apart q q') => some (q, q')
  | _ => none

def DisjointEvidence.check (arena : AssertionArena) (K : AssertionRef) (r r' : Region) : DisjointEvidence → Bool
  | .classes a b => match a.selector arena K r, b.selector arena K r' with
    | some x, some y => ((Region.cls x).bound.inter (Region.cls y).bound).isEmpty
    | _, _ => false
  | .spines c => (conjuncts arena.nodes K.index).contains c.index && match separatedPaths arena.nodes[c.index]? with
    | some (q, q') => r == .spine q.root q.fields && r' == .spine q'.root q'.fields
    | none => false
  | .cells c => (conjuncts arena.nodes K.index).contains c.index && match arena.nodes[c.index]? with
    | some (.apart q q') => r == .pathCells q.root q.fields && r' == .pathCells q'.root q'.fields
    | _ => false
  | .swap d => d.check arena K r' r

theorem DisjointEvidence.sound {arena : AssertionArena} {K : AssertionRef} :
    ∀ {r r' : Region} (ev : DisjointEvidence), ev.check arena K r r' = true → DisjointUnder arena K r r'
  | r, r', .classes a b, h => by
    simp only [DisjointEvidence.check] at h
    split at h
    · rename_i x y hx hy
      intro η m s hK l hlt hl
      cases hm : r'.mem η s.h l
      · rfl
      · exact (Region.cls_apart_of_bound s.ok h (a.sound hx η m s hK l hl) (b.sound hy η m s hK l hm)).elim
    · cases h
  | r, r', .spines c, h => by
    simp only [DisjointEvidence.check, Bool.and_eq_true] at h
    obtain ⟨hc, h⟩ := h
    split at h
    · rename_i q q' hqq
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro η m s hK l hlt hl
      have hcs := conjuncts_sat arena.nodes K.index c.index (List.contains_iff_mem.mp hc) η m s hK
      have hsep : ∃ u w st t, q.read η s.h = some u ∧ q'.read η s.h = some w ∧ spineOf u = some st ∧
          spineOf w = some t ∧ st ≠ t := by
        unfold separatedPaths at hqq
        split at hqq
        · rename_i _ _ hn; cases hqq
          obtain ⟨u, w, st, t, -, -, hu, hw, ⟨hsu, -⟩, ⟨htw, -⟩, hne⟩ := (sat_separated hn).mp hcs
          exact ⟨u, w, st, t, hu, hw, hsu, htw, hne⟩
        · rename_i _ _ hn; cases hqq
          obtain ⟨u, w, st, t, -, -, hu, hw, ⟨hsu, -⟩, ⟨htw, -⟩, hne, -⟩ := (sat_apart hn).mp hcs
          exact ⟨u, w, st, t, hu, hw, hsu, htw, hne⟩
        · cases hqq
      obtain ⟨u, w, st, t, hu, hw, hsu, htw, hne⟩ := hsep
      simp only [Path.read] at hu hw
      simp only [Region.mem, hu, hw, elementsOf_spine hsu, elementsOf_spine htw, beq_iff_eq,
        Option.some.injEq] at hl ⊢
      subst hl
      simpa using hne.symm
    · cases h
  | r, r', .cells c, h => by
    simp only [DisjointEvidence.check, Bool.and_eq_true] at h
    obtain ⟨hc, h⟩ := h
    split at h
    · rename_i q q' hn
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro η m s hK l hlt hl
      have hcs := conjuncts_sat arena.nodes K.index c.index (List.contains_iff_mem.mp hc) η m s hK
      obtain ⟨u, w, s₁, t₁, xs, ys, hu, hw, hau, haw, -, hlist⟩ := (sat_apart hn).mp hcs
      have hcells := (cells_disjoint_iff hau haw).mpr hlist
      simp only [Path.read] at hu hw
      simp only [Region.mem, hu, hw, List.contains_iff_mem] at hl ⊢
      cases hm : (spineCells s.h w).contains (some l)
      · rfl
      · exact absurd (List.contains_iff_mem.mp hm) (hcells l hl)
    · cases h
  | r, r', .swap d, h => by
    intro η m s hK l hlt hl
    cases hm : r'.mem η s.h l
    · rfl
    · have := DisjointEvidence.sound d h η m s hK l hlt hm
      rw [hl] at this; cases this

/-- **Respect, checked as the note defines it** (§5, Definition
"Respect"): disjointness certificates under `K`, read as a separation query
that answers for a pair of regions some certificate checks; the check is
`respects` under that query. -/
structure RespectEvidence where
  disjoint : List DisjointEvidence
  deriving DecidableEq, Repr

/-- The separation query the certificates answer under `K`. -/
def RespectEvidence.query (ev : RespectEvidence) (arena : AssertionArena) (K : AssertionRef) : SepQuery :=
  ⟨fun r r' => ev.disjoint.any fun d => d.check arena K r r'⟩

def RespectEvidence.check (ev : RespectEvidence) (arena : AssertionArena) (K : AssertionRef) (S Φ : Footprint) :
    Bool :=
  respects (ev.query arena K) S Φ

/-- The certificates' query is sound at every state of `K`. -/
theorem RespectEvidence.query_sound {arena : AssertionArena} {K : AssertionRef} (ev : RespectEvidence)
    {η : Env} {m : Nat} {s : IndexedHeap} (hK : Sat arena η m s K) : (ev.query arena K).Sound η s.h := by
  intro r r' l hl hd hr hr'
  obtain ⟨d, -, hdc⟩ := List.any_eq_true.mp hd
  rw [d.sound hdc η m s hK l hl hr] at hr'; cases hr'

/-! ### Supports -/

/-- A location in a region of a `keep` entry of `S` keeps its contents along
a transition within `S`. -/
theorem kept_of_supported {S : Footprint} {η : Env} {s s' : IndexedHeap} (hS : SupportedBy S η s s')
    {r : Region} (hr : (r, .keep) ∈ S) {l : Nat} (hl : r.mem η s.h l = true) {v : Val} (hv : s.h[l]? = some v) :
    s'.h[l]? = some v := by
  obtain ⟨v', hv', hk⟩ := hS _ hr l v hl hv
  simp only [Change.Holds] at hk
  rw [hv', hk]

/-- What a term of a heap-free kind reads of a value: no heap. -/
theorem kindValue_heapFree {k : Term.Kind} (hk : k ≠ .length) (h h' : Heap) (v : Val) :
    kindValue h k v = kindValue h' k v := by
  cases k <;> first | rfl | exact absurd rfl hk

/-- A term at a variable reads that variable's value. -/
theorem termAt_var {η : Env} {h : Heap} {t : Term} (ht : t.path = []) :
    termAt η h t = kindValue h t.kind (η t.slot) := by
  simp only [termAt, ht, readPath, Option.bind_some]

/-- A defined term reads a value neither `null` nor `undefined`. -/
theorem kindValue_nonNullish {h : Heap} {k : Term.Kind} {v : Val} (hk : (kindValue h k v).isSome) :
    nullish v = false := by
  cases k <;> cases v <;> simp_all [kindValue, intValue, lengthOf, viewLengthOf, strLengthOf, nullish, spineOf, fieldsOf]

/-- **A fact stays true when the term increases** (the note, §5, Definition
"Support", the row of a length in an inequality: `δ` is `grow` where the
inequality stays true when the length increases): a `≤` fact each of
whose coefficients of the term is at most zero. -/
def growsWith (F : Linear.Fact Term) (t : Term) : Bool :=
  match F with
  | .le f _ => f.all fun e => e.1 != t || decide (e.2 ≤ 0)
  | .ne _ _ => false

/-- The scalar-length terms of a linear support at variables (the note, §5,
Definition "Support", the rows of an inequality): each term reads a
variable, of a heap-free kind or the length of the array an entry of `S`
changes at most by the length's change, `keep`, or `grow` where the fact
stays true when the length increases (`growsWith`). -/
def lengthsSupported (F : Linear.Fact Term) (S : Footprint) : Bool :=
  F.vars.all fun t => !t.atEntry && t.path.isEmpty &&
    (t.kind != .length || S.contains (.spine t.slot [], .keep) ||
      (growsWith F t && S.contains (.spine t.slot [], .grow)))

/-- **Support of an assertion in a context, by certificate** (the note, §5,
Definition "Support"):
- an invariant assertion, by any `S`;
- a linear fact at variables, by the spines whose lengths it reads, each
  at `keep`, or at `grow` where the fact stays true when the length
  increases (`{x.spine: grow}` supports `n ≤ |x|`, the note's example);
- `dense(z, n)` at a variable `z`, `n` heap-free, by `{z.spine: grow}`
  (the row of `dense(x, n)`);
- `every(z, t, φ)` at a variable `z`, `t` heap-free and `φ` over scalars, by
  `{z.spine: keep, z[cells]: keep}`;
- `x.f ≐ v` for a literal `v`, by `{x.f: keep}`;
- a linear fact at any paths, by `{values: init, spines: keep}`: `init`
  changes no location holding an object, a number or a string;
- a typed array's element `b[i] ≐ ℓ` at a variable `b`, `i` heap-free and
  `ℓ` a literal, by `{b.spine: keep, b[cells]: keep}` (the note, §6,
  Example "A write through a typed array");
- a linear fact reading the current heap, by any `S` containing the support
  the acceptance path produces for it in the empty read context: each
  term's path reads and spine (the note, §5, Definition "Supports of the
  atoms", the rows of an inequality; `IndexFact.support?`), through the
  shared support relation (`IndexFact.support?_supports`,
  `SupportDomain.Supports.pullback`). -/
inductive SupportEvidence where
  | invariant
  | lengths
  | dense
  | everyCells
  | field
  | init
  | viewElement
  | paths
  deriving DecidableEq, Repr

def SupportEvidence.check (arena : AssertionArena) (A : AssertionRef) (S : Footprint) : SupportEvidence → Bool
  | .invariant => invNode arena.nodes A.index
  | .lengths => match arena.nodes[A.index]? with
    | some (.atom (.linear F)) => lengthsSupported F S
    | _ => false
  | .dense => match arena.nodes[A.index]? with
    | some (.atom (.dense z n)) => z.fields.isEmpty && !n.atEntry && n.path.isEmpty && n.kind != .length &&
        S.contains (.spine z.root [], .grow)
    | _ => false
  | .everyCells => match arena.nodes[A.index]? with
    | some (.atom (.every z n body)) => z.fields.isEmpty && !n.atEntry && n.path.isEmpty && n.kind != .length &&
        scalarBody body && S.contains (.spine z.root [], .keep) && S.contains (.pathCells z.root [], .keep)
    | _ => false
  | .field => match arena.nodes[A.index]? with
    | some (.atom (.equal ⟨x, [f]⟩ (.literal _))) => S.contains (.path x [] (.str f), .keep)
    | _ => false
  | .init => match arena.nodes[A.index]? with
    | some (.atom (.linear F)) => F.vars.all (fun t => !t.atEntry) &&
        S.contains (.cls .values, .init) && S.contains (.cls .spines, .keep)
    | _ => false
  | .viewElement => match arena.nodes[A.index]? with
    | some (.atom (.element b t (.literal _))) => b.fields.isEmpty && !t.atEntry && t.path.isEmpty &&
        t.kind != .length && S.contains (.spine b.root [], .keep) && S.contains (.pathCells b.root [], .keep)
    | _ => false
  | .paths => match arena.nodes[A.index]? with
    | some (.atom (.linear F)) => F.vars.all (fun t => !t.atEntry) &&
        match (IndexFact.linear F).support? {} with
        | some T => T.all S.contains
        | none => false
    | _ => false

/-- A term of a linear support at variables reads the same value along a
transition within `S`, or, its length at `grow`, a value no smaller where
the fact stays true when it increases. -/
private theorem lengths_term {F : Linear.Fact Term} {S : Footprint} {η : Env} {s s' : IndexedHeap}
    (hS : SupportedBy S η s s') {t : Term}
    (ht : (!t.atEntry && t.path.isEmpty && (t.kind != .length || S.contains (.spine t.slot [], .keep) ||
      (growsWith F t && S.contains (.spine t.slot [], .grow)))) = true)
    {n : Int} (hn : termAt η s.h t = some n) :
    termAt η s'.h t = some n ∨ (growsWith F t = true ∧ ∃ n', termAt η s'.h t = some n' ∧ n ≤ n') := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem, List.isEmpty_iff] at ht
  obtain ⟨⟨-, hp⟩, hk⟩ := ht
  rw [termAt_var hp] at hn ⊢
  by_cases hl : t.kind = .length
  · rw [hl] at hn ⊢
    obtain ⟨st, ls, hst, hls, rfl, hm⟩ := lengthOf_spine hn
    have hin : (Region.spine t.slot []).mem η s.h st = true := by
      simp [Region.mem, readPath, elementsOf_spine hst]
    rcases hk with (hk | hk) | ⟨hg, hk⟩
    · exact absurd hl hk
    · exact .inl (lengthOf_of_spine hst (kept_of_supported hS hk hin hls) hm)
    · obtain ⟨v', hv', hh⟩ := hS _ hk st _ hin hls
      obtain ⟨ls', rfl, -, hlen⟩ := grow_arr hh
      exact .inr ⟨hg, _, lengthOf_of_spine hst hv' (hlen.2 hm), by have := hlen.1; omega⟩
  · rw [kindValue_heapFree hl s'.h s.h]; exact .inl hn

/-- A form is no larger where each entry's product is no larger. -/
private theorem form_eval_le {f : Linear.Form Term} {g g' : Term → Int}
    (h : ∀ e ∈ f, e.2 * g' e.1 ≤ e.2 * g e.1) : Linear.Form.eval g' f ≤ Linear.Form.eval g f := by
  induction f with
  | nil => exact Int.le_refl _
  | cons e f ih =>
    obtain ⟨x, c⟩ := e
    exact Int.add_le_add (h (x, c) (List.mem_cons_self ..)) (ih fun e he => h e (List.mem_cons_of_mem _ he))

/-- **A linear fact holds where each of its terms reads the same value, or
a value no smaller where the fact stays true when it increases.** -/
private theorem factAt_grows {F : Linear.Fact Term} {val val' : Term → Option Int} (hF : FactAt val F)
    (ht : ∀ t ∈ F.vars, ∀ n, val t = some n →
      val' t = some n ∨ (growsWith F t = true ∧ ∃ n', val' t = some n' ∧ n ≤ n')) : FactAt val' F := by
  have hval : ∀ t ∈ F.vars, ∃ n, val t = some n := fun t h => Option.isSome_iff_exists.mp (hF.1 t h)
  cases F with
  | ne f d =>
    refine factAt_congr (fun t h => ?_) hF
    obtain ⟨n, hn⟩ := hval t h
    rcases ht t h n hn with h' | ⟨hg, -⟩
    · rw [h', hn]
    · simp [growsWith] at hg
  | le f d =>
    refine ⟨fun t h => ?_, Int.le_trans (form_eval_le fun e he => ?_) hF.2⟩
    · obtain ⟨n, hn⟩ := hval t h
      rcases ht t h n hn with h' | ⟨-, n', h', -⟩ <;> simp [h']
    · have hev : e.1 ∈ (Linear.Fact.le f d).vars := List.mem_map_of_mem he
      obtain ⟨n, hn⟩ := hval e.1 hev
      rcases ht e.1 hev n hn with h' | ⟨hg, n', h', hle⟩
      · simp only [h', hn, Int.le_refl]
      · have hc : e.2 ≤ 0 := by
          simp only [growsWith, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hg
          exact (hg e he).resolve_left (fun h => h rfl)
        simp only [h', hn, Option.getD_some]
        exact Int.mul_le_mul_of_nonpos_left hc hle

/-- A path read through locations holding values other than `null` and
`undefined` reads the same along a transition changing value locations at
most by `init` and keeping spines. -/
private theorem readPath_init {η : Env} {s s' : IndexedHeap} (hS : SupportedBy [(.cls .values, .init),
    (.cls .spines, .keep)] η s s') :
    ∀ {p : List String} {v w : Val} (k : Term.Kind), readPath s.h v p = some w → (kindValue s.h k w).isSome →
      readPath s'.h v p = some w
  | [], _, _, _, h, _ => h
  | f :: p, v, w, k, h, hk => by
    cases v with
    | objAt fs cd oid =>
      simp only [readPath] at h ⊢
      split at h
      · rename_i l hl
        split at h
        · rename_i u hu
          have hnn : nullish u = false := by
            cases p with
            | nil => simp only [readPath, Option.some.injEq] at h; subst h; exact kindValue_nonNullish hk
            | cons g p => cases u <;> simp_all [readPath, nullish]
          have hin : (Region.cls .values).mem η s.h l = true := by
            cases u with
            | arr _ =>
              cases p with
              | nil =>
                simp only [readPath, Option.some.injEq] at h; subst h
                cases k <;> simp [kindValue, intValue, lengthOf, viewLengthOf, strLengthOf, spineOf, fieldsOf] at hk
              | cons g p => simp [readPath] at h
            | viewSpine _ _ =>
              cases p with
              | nil =>
                simp only [readPath, Option.some.injEq] at h; subst h
                cases k <;> simp [kindValue, intValue, lengthOf, viewLengthOf, strLengthOf, spineOf, fieldsOf] at hk
              | cons g p => simp [readPath] at h
            | _ => simp [Region.mem, hu, Selector.selects, contentsCategory, Selector.has]
          obtain ⟨u', hu', hc⟩ := hS _ (List.mem_cons_self ..) l u hin hu
          have := hc.init_defined hnn
          subst this
          simp only [hu']
          exact readPath_init hS k h hk
        · cases h
      · cases h
    | _ => simp [readPath] at h

theorem SupportEvidence.sound {arena : AssertionArena} {C : SupportContext} {S : Footprint} {A : AssertionRef} :
    ∀ ev : SupportEvidence, ev.check arena A S = true → Supports arena C S A
  | .invariant, h => fun η m s s' ha _ hA _ => invNode_sound arena.nodes A.index h η m s s' ha hA
  | .lengths, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i F hn
      intro η m s s' _ _ hA hS
      exact (sat_atom hn).mpr (factAt_grows ((sat_atom hn).mp hA) fun t ht _ hn' =>
        lengths_term hS (List.all_eq_true.mp h t ht) hn')
    · cases h
  | .dense, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i z n hn
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.isEmpty_iff,
        List.contains_iff_mem] at h
      obtain ⟨⟨⟨⟨hz, -⟩, hnp⟩, hnk⟩, hst⟩ := h
      intro η m s s' _ _ hA hS
      obtain ⟨w, st, ls, k, hw, hsto, hls, hk, h0, hd⟩ := (sat_atom hn).mp hA
      have hzw : η z.root = w := by
        simp only [Path.read, hz, readPath, Option.some.injEq] at hw; exact hw
      have hin : (Region.spine z.root []).mem η s.h st = true := by
        simp [Region.mem, readPath, hzw, elementsOf_spine hsto]
      obtain ⟨v', hv', hh⟩ := hS _ hst st _ hin hls
      obtain ⟨ls', rfl, hdp, -⟩ := grow_arr hh
      have hk' : termAt η s'.h n = some k := by
        rw [termAt_var hnp] at hk ⊢; rwa [kindValue_heapFree hnk s'.h s.h]
      exact (sat_atom hn).mpr ⟨w, st, ls', k, by rw [← hw, Path.read_heap hz], hsto, hv', hk', h0, hdp _ hd⟩
    · cases h
  | .everyCells, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i z n body hn
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.isEmpty_iff,
        List.contains_iff_mem] at h
      obtain ⟨⟨⟨⟨⟨⟨hz, hne⟩, hnp⟩, hnk⟩, hsc⟩, hst⟩, hcl⟩ := h
      intro η m s s' _ _ hA hS
      obtain ⟨w, st, ls, k, hw, hsto, hls, hk, hall⟩ := (sat_atom hn).mp hA
      have hzw : η z.root = w := by
        simp only [Path.read, hz, readPath, Option.some.injEq] at hw; exact hw
      have hin : (Region.spine z.root []).mem η s.h st = true := by
        simp [Region.mem, readPath, hzw, elementsOf_spine hsto]
      have hls' := kept_of_supported hS hst hin hls
      have hcells : ∀ (i l : Nat), ls[i]? = some (some l) → ∀ u, s.h[l]? = some u → s'.h[l]? = some u := by
        intro i l hi u hu
        have hsto' : (fieldsOf w).lookup arraySpineKey = some st := hsto
        have hmem : (Region.pathCells z.root []).mem η s.h l = true := by
          simp only [Region.mem, readPath, hzw, spineCells, entriesAt, hsto', hls, Option.bind_some,
            spineEntries, Option.getD_some, List.contains_iff_mem, List.mem_append]
          exact .inl (List.mem_of_getElem? hi)
        exact kept_of_supported hS hcl hmem hu
      have hk' : termAt η s'.h n = some k := by
        rw [termAt_var hnp] at hk ⊢; rwa [kindValue_heapFree hnk s'.h s.h]
      refine (sat_atom hn).mpr ⟨w, st, ls, k, by rw [← hw, Path.read_heap hz], hsto, hls', hk',
        fun i hi => ⟨(hall i hi).1, fun F hF => ?_⟩⟩
      refine LinearClause.holdsAt_extend (fun b hb z hz => ?_) ((hall i hi).2 F hF)
      have hsb : scalarBound b = true := List.all_eq_true.mp (List.all_eq_true.mp hsc F hF) b hb
      cases b with
      | index => exact hz
      | elem =>
        simp only [scalarValue, elementInt] at hz ⊢
        split at hz
        · rename_i l hl
          obtain ⟨u, hu, hzu⟩ := Option.bind_eq_some_iff.mp hz
          rw [hcells i l hl u hu]; exact hzu
        · cases hz
      | project k p =>
        cases k <;> cases p <;> simp [scalarBound] at hsb
        simp only [scalarValue] at hz ⊢
        split at hz
        · rename_i l hl
          obtain ⟨u, hu, hzu⟩ := Option.bind_eq_some_iff.mp hz
          simp only [hcells i l hl u hu, Option.bind_some]; exact hzu
        · cases hz
      | free t =>
        simp only [scalarBound, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff] at hsb
        simp only [scalarValue] at hz ⊢
        rw [termAt_var hsb.2] at hz ⊢
        rw [kindValue_heapFree (by rw [hsb.1.2]; decide) s'.h s.h]; exact hz
      | _ => simp [scalarBound] at hsb
    · cases h
  | .field, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i x f v hn
      simp only [List.contains_iff_mem] at h
      intro η m s s' _ _ hA hS
      obtain ⟨u, hu, hw⟩ := (sat_atom hn).mp hA
      refine (sat_atom hn).mpr ⟨u, ?_, hw⟩
      simp only [Path.read] at hu ⊢
      cases hx : η x with
      | objAt fs cd oid =>
        rw [hx] at hu
        simp only [readPath] at hu ⊢
        split at hu
        · rename_i l hl
          split at hu
          · rename_i u0 hu0
            have hin : (Region.path x [] (.str f)).mem η s.h l = true := by
              simp [Region.mem, readPath, hx, fieldsOf, hl]
            rw [kept_of_supported hS h hin hu0]; exact hu
          · cases hu
        · cases hu
      | _ => rw [hx] at hu; simp [readPath] at hu
    · cases h
  | .viewElement, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i b t lit hn
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.isEmpty_iff,
        List.contains_iff_mem] at h
      obtain ⟨⟨⟨⟨⟨hb, _⟩, htp⟩, htk⟩, hst⟩, hcl⟩ := h
      intro η m s s' _ _ hA hS
      obtain ⟨u, ls, k, l, v, hu, hvc, hk, h0, hl, hv, hw⟩ := (sat_atom hn).mp hA
      have hub : η b.root = u := by simp only [Path.read, hb, readPath, Option.some.injEq] at hu; exact hu
      unfold viewCells at hvc
      split at hvc
      · rename_i st hso hds
        obtain ⟨c0, hc0, hent⟩ := Option.bind_eq_some_iff.mp hvc
        have hel : elementsOf u = some st := by
          cases u with
          | objAt fs cd oid =>
            simp only [descriptorSpine] at hds
            split at hds
            · rename_i heq
              cases hds
              simp only [spineOf, fieldsOf] at hso
              cases heq
              simp [elementsOf, hso]
            · cases hds
          | _ => simp [descriptorSpine] at hds
        have hin : (Region.spine b.root []).mem η s.h st = true := by
          simp [Region.mem, readPath, hub, hel]
        have hc0' := kept_of_supported hS hst hin hc0
        have hmem : (Region.pathCells b.root []).mem η s.h l = true := by
          simp only [Region.mem, readPath, hub, spineCells, List.contains_iff_mem, List.mem_append]
          refine .inr ?_
          simp only [hds, entriesAt, hc0, Option.bind_some, hent, Option.getD_some]
          exact List.mem_of_getElem? hl
        have hv' := kept_of_supported hS hcl hmem hv
        have hk' : termAt η s'.h t = some k := by
          rw [termAt_var htp] at hk ⊢; rwa [kindValue_heapFree htk s'.h s.h]
        refine (sat_atom hn).mpr ⟨u, ls, k, l, v, by rw [← hu, Path.read_heap hb], ?_, hk', h0, hl, hv', ?_⟩
        · simp only [viewCells, hso, hds, hc0', Option.bind_some, hent]
        · simpa [Witness.value] using hw
      · cases hvc
    · cases h
  | .paths, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i F hn
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hnow, hT⟩ := h
      split at hT
      · rename_i T hTs
        intro η m s s' ha _ hA hS
        have hsub : ∀ e ∈ T, e ∈ S := fun e he => by simpa using List.all_eq_true.mp hT e he
        have hsup := ((Footprints.IndexFact.support?_supports (ε := ⟨η, s.h⟩) {} _ hTs).pullback indexed).mono hsub
        have hkept : ∀ (h : Heap) t, t ∈ F.vars → termValue ⟨η, s.h⟩ η h t = termAt η h t :=
          fun _ t ht => termValue_now (hnow t ht)
        have hF : (IndexFact.linear F).HoldsAt ⟨η, s.h⟩ η s.h :=
          factAt_congr (fun t ht => hkept s.h t ht) ((sat_atom hn).mp hA)
        have hF' := hsup η m s s' ha (fun _ _ _ _ _ _ _ hf => by cases hf) hF hS
        exact (sat_atom hn).mpr (factAt_congr (fun t ht => (hkept s'.h t ht).symm) hF')
      · cases hT
    · cases h
  | .init, h => by
    simp only [SupportEvidence.check] at h
    split at h
    · rename_i F hn
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      obtain ⟨⟨_, hv⟩, hst⟩ := h
      intro η m s s' _ _ hA hS
      have hS' : SupportedBy [(.cls .values, .init), (.cls .spines, .keep)] η s s' := by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact hS _ hv
        · exact hS _ hst
      have hF := (sat_atom hn).mp hA
      refine (sat_atom hn).mpr (factAt_congr (fun t ht => ?_) hF)
      obtain ⟨n, hn'⟩ := Option.isSome_iff_exists.mp (hF.1 t ht)
      rw [hn']
      simp only [termAt, Option.bind_eq_some_iff] at hn' ⊢
      obtain ⟨w, hw, hk⟩ := hn'
      refine ⟨w, readPath_init hS' t.kind hw (by rw [hk]; rfl), ?_⟩
      cases hkd : t.kind with
      | length =>
        rw [hkd] at hk
        obtain ⟨st, ls, hsto, hls, rfl, hm⟩ := lengthOf_spine hk
        have hin : (Region.cls .spines).mem η s.h st = true := by
          simp [Region.mem, hls, Selector.selects, contentsCategory, Selector.has]
        exact lengthOf_of_spine hsto (kept_of_supported hS hst hin hls) hm
      | _ => rw [hkd] at hk; rwa [kindValue_heapFree (by decide) s'.h s.h]
    · cases h

end Verification.Parity
