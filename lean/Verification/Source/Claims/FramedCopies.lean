import Verification.Source.Claims.FramedKept
import Verification.Source.Claims.FramedCopyDefs

/-! # The slots of a framed call that hold reads of its arguments

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Milestone 2: the protected
reading", the decision's slot copies and the theorem chain's step 7). A
must-analysis over the request's code: an entry `(i, j, π)` of a label's
table states that at every run of the code at that label, slot `i` holds
the value the reads of the keys `π` give from the call's argument `j` at
the entry's heap, while the locations those reads read keep their
contents.

- **The table and its check** (`copiesB`): the start's entries are the
  diagonal below the arity; along every edge of a node (its continuation's
  targets and its handler), each entry of the target's table is read by
  the edge's slot map from an entry of the node's, or, for the value a
  `bind` or `tagBind` edge binds, from the node's expression: a slot
  (`.var i`) copies its entry, a read of a key from a slot
  (`readAt f (.var i)`) extends it by `f`. A value a branch or a handler
  binds has no entry.
- **The proposal** (`copiesOf`): the greatest table the check admits,
  computed by intersecting along the edges from the start's diagonal,
  paths bounded; the empty table where it fails the check, which passes.
- **The invariant** (`CopyInv`, `copyInv_step`, `copies_along`): at every
  state of an execution of the code from its start along which a set of
  locations keeps the entry's heap's contents, a run at a label holds its
  table's entries whose reads read only those locations; a frame also
  tracks the read its expression performs (`Stage`). -/

namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

/-- The slot map reads each slot at its source (proved). -/
theorem envMap_src (m : Option (List Nat)) (L : List Tm) (d : Tm) (i : Nat) :
    envOf (envMap m L d).1 (envMap m L d).2 i = envOf L d (srcOf m i) := by
  cases m with
  | none => rfl
  | some slots =>
    simp only [envMap, envOf, srcOf]
    by_cases hi : i < slots.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : slots.length ≤ i)]

/-! ## The invariant -/

section Inv
variable (Pe : List Tm) (Pk : List (Continuation × Option Target)) (c₀ : ComponentTag) (cp : CopyTable)
  (h₀ : Heap) (ρ₀ : Env) (K : Nat → Prop)

/-- **An entry's reads read only kept locations**: every location the reads
of `π` from argument `j` read at the entry's heap is in `K`. -/
def EntryKept (j : Nat) (π : List PropKey) : Prop := ∀ l w q, ReadsAt h₀ (ρ₀ j) π l w q → K l

/-- **A label's entries hold at slots**: each entry whose reads read only
kept locations has its slot holding the reads' value at the entry's heap. -/
def SlotsHold (l : Nat) (L : List Tm) (d : Tm) : Prop :=
  ∀ e ∈ cp.at l, EntryKept h₀ ρ₀ K e.2.1 e.2.2 → Reads h₀ (ρ₀ e.2.1) e.2.2 (envOf L d e.1)

/-- **A stage of the read of `f` from `m`**: a read of `f` from a value on
`m`'s prototype chain at the entry's heap, or its value. -/
inductive Stage (f : PropKey) (m : Val) : Tm → Prop where
  | read {p : Val} : isVal p = true → (∀ v, ReadKey h₀ f p v → ReadKey h₀ f m v) →
      (∀ l w q, KeyLoc h₀ f p l w q → KeyLoc h₀ f m l w q) → Stage f m (.readAt f p)
  | done {v : Val} : isVal v = true → ReadKey h₀ f m v → Stage f m v

/-- **What a frame's term is**, at a node whose expression is a slot (the
slot's value) or a read of a key from a slot (a stage of the read, where the
locations it reads are kept). -/
def TermHolds (l : Nat) (L : List Tm) (d : Tm) (u : Tm) : Prop :=
  match Pe[l]? with
  | some (.var i) => u = envOf L d i
  | some (.readAt f (.var i)) => (∀ l' w q, KeyLoc h₀ f (envOf L d i) l' w q → K l') → Stage h₀ f (envOf L d i) u
  | _ => True

/-- **The invariant of the copies** at a term of the code's run: a run at a
label, its slots values holding the label's entries; a frame of a node
sharing the frame's continuation and handler, its slots holding the node's
entries and its term what the node's expression makes it; or a value or a
throw of one, which the run returned. -/
def CopyInv (t : Tm) : Prop :=
  (∃ l L d, t = .goto Pe Pk l L d c₀ ∧ SlotVals L d ∧ SlotsHold cp h₀ ρ₀ K l L d) ∨
  (∃ u L d k x l', t = .frame Pe Pk u L d k x c₀ ∧ SlotVals L d ∧ Pk[l']? = some (k, x) ∧
    SlotsHold cp h₀ ρ₀ K l' L d ∧ TermHolds Pe h₀ K l' L d u) ∨
  isVal t = true ∨ ∃ v, t = .throw v ∧ isVal v = true

end Inv

/-- A slot of values is a value (proved). -/
theorem SlotVals.at {L : List Tm} {d : Tm} (hv : SlotVals L d) (i : Nat) : isVal (envOf L d i) = true := by
  rcases getD_mem_or L i d with h | h
  · exact hv.1 _ (by simpa [envOf] using h)
  · simp only [envOf]; rw [h]; exact hv.2

/-- A slot past a value bound in front is the slot before it (proved). -/
theorem envOf_cons (v : Tm) (L : List Tm) (d : Tm) (s : Nat) :
    envOf (v :: L) d (s + 1) = envOf L d s := rfl

/-- **The target's entries along a checked edge** (proved, `edgeOkB`): a
slot map over `L`, or over a value `v` bound in front, holds the target's
entries where the node's slots hold the node's and, for an edge binding the
node's own value, that value is what the node's expression makes it. -/
theorem edge_holds {cp : CopyTable} {h₀ : Heap} {ρ₀ : Env} {K : Nat → Prop} {l : Nat} {e : Tm} {t : Target}
    {L : List Tm} {d : Tm} (hs : SlotsHold cp h₀ ρ₀ K l L d) :
    ∀ (b : Option Bool), edgeOkB cp l e b t = true →
      (b = none → SlotsHold cp h₀ ρ₀ K t.label (envMap t.mapping L d).1 (envMap t.mapping L d).2) ∧
      (∀ v, b = some false → SlotsHold cp h₀ ρ₀ K t.label (envMap t.mapping (v :: L) d).1 (envMap t.mapping (v :: L) d).2) ∧
      (∀ v, b = some true → (∀ j π, boundEntryB cp l e j π = true → EntryKept h₀ ρ₀ K j π → Reads h₀ (ρ₀ j) π v) →
        SlotsHold cp h₀ ρ₀ K t.label (envMap t.mapping (v :: L) d).1 (envMap t.mapping (v :: L) d).2) := by
  intro b hok
  simp only [edgeOkB, List.all_eq_true] at hok
  refine ⟨fun hb => ?_, fun v hb => ?_, fun v hb hv => ?_⟩
  · subst hb
    rintro ⟨i', j, π⟩ hen hk
    have := hok _ hen
    simp only [List.contains_iff_mem] at this
    rw [envMap_src]
    exact hs _ this hk
  · subst hb
    rintro ⟨i', j, π⟩ hen hk
    have := hok _ hen
    rw [envMap_src]
    by_cases hs0 : srcOf t.mapping i' = 0
    · simp [hs0] at this
    · simp only [hs0, if_false, List.contains_iff_mem] at this
      obtain ⟨s', hs'⟩ := Nat.exists_eq_succ_of_ne_zero hs0
      rw [hs'] at this ⊢
      exact hs _ this hk
  · subst hb
    rintro ⟨i', j, π⟩ hen hk
    have := hok _ hen
    rw [envMap_src]
    by_cases hs0 : srcOf t.mapping i' = 0
    · simp only [hs0, if_true, Bool.true_and] at this
      rw [hs0]
      exact hv _ _ this hk
    · simp only [hs0, if_false, List.contains_iff_mem] at this
      obtain ⟨s', hs'⟩ := Nat.exists_eq_succ_of_ne_zero hs0
      rw [hs'] at this ⊢
      exact hs _ this hk


/-- **A checked node's edges** (proved, `copiesB`): at a node of the code,
each of its edges passes the edge's check. -/
theorem copiesB_node {Pe : List Tm} {Pk : List (Continuation × Option Target)} {start arity : Nat}
    {cp : CopyTable} (hcp : copiesB Pe Pk start arity cp = true) (hlen : Pe.length = Pk.length) {l : Nat}
    {k : Continuation} {x : Option Target} (hk : Pk[l]? = some (k, x)) :
    ∃ e, Pe[l]? = some e ∧ ∀ bt ∈ nodeEdges k x, edgeOkB cp l e bt.1 bt.2 = true := by
  have hl : l < Pk.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨e, he⟩ : ∃ e, Pe[l]? = some e := ⟨Pe[l], List.getElem?_eq_getElem (by omega)⟩
  simp only [copiesB, Bool.and_eq_true, List.all_eq_true] at hcp
  have := hcp.2 l (List.mem_range.mpr hl)
  rw [he, hk] at this
  simp only [List.all_eq_true] at this
  exact ⟨e, he, fun bt hbt => this bt hbt⟩

/-- **The start's entries hold** (proved, `copiesB`): the start's entries
are the diagonal, whose slots hold the arguments. -/
theorem copiesB_start {Pe : List Tm} {Pk : List (Continuation × Option Target)} {start arity : Nat}
    {cp : CopyTable} (hcp : copiesB Pe Pk start arity cp = true) {h₀ : Heap} {L : List Tm} {d : Tm}
    {K : Nat → Prop} : SlotsHold cp h₀ (envOf L d) K start L d := by
  simp only [copiesB, Bool.and_eq_true, List.all_eq_true] at hcp
  rintro ⟨i, j, π⟩ hen _
  have := hcp.1 _ hen
  simp only [beq_iff_eq, List.isEmpty_iff, decide_eq_true_eq] at this
  obtain ⟨⟨rfl, rfl⟩, -⟩ := this
  exact .nil _

/-- **Every step keeps the invariant of the copies** (proved, by the step
rules of `goto` and `frame`): an entering step starts the node's stage; a
frame's read steps advance its stage at the kept locations; each edge maps
the slots as its check states (`edge_holds`), the value it binds the
node's slot or read (`boundEntryB`, `reads_snoc`); a value and a throw of
one take no step. -/
theorem copyInv_step {Pe : List Tm} {Pk : List (Continuation × Option Target)} {c₀ : ComponentTag}
    {start arity : Nat} {cp : CopyTable} {h₀ : Heap} {ρ₀ : Env} {K : Nat → Prop}
    (hcp : copiesB Pe Pk start arity cp = true) (hlen : Pe.length = Pk.length) {h h' : Heap} {t t' : Tm}
    (hi : CopyInv Pe Pk c₀ cp h₀ ρ₀ K t) (hs : Step h t h' t') (hk : ∀ l, K l → h[l]? = h₀[l]?)
    (hhv : ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true) : CopyInv Pe Pk c₀ cp h₀ ρ₀ K t' := by
  rcases hi with ⟨l, L, d, rfl, hL, hS⟩ | ⟨u, L, d, k, x, l', rfl, hL, hkx, hS, hT⟩ | hn
  · -- An entering step: the node's stage starts.
    cases hs with
    | gotoEnter he hk' =>
      refine .inr (.inl ⟨_, L, d, _, _, l, rfl, hL, hk', hS, ?_⟩)
      unfold TermHolds
      rw [he]
      split
      · rename_i heq
        cases heq
        simp [instantiate]
      · rename_i heq
        cases heq
        intro _
        simp only [instantiate]
        exact .read (hL.at _) (fun _ h => h) (fun _ _ _ h => h)
      · trivial
  · obtain ⟨e, he, hedges⟩ := copiesB_node hcp hlen hkx
    -- The value a node's own edge binds: the node's slot or read.
    have hbound : ∀ v, isVal v = true → TermHolds Pe h₀ K l' L d v → ∀ j π, boundEntryB cp l' e j π = true →
        EntryKept h₀ ρ₀ K j π → Reads h₀ (ρ₀ j) π v := by
      intro v hv hTv j π hb hke
      unfold TermHolds at hTv
      rw [he] at hTv
      unfold boundEntryB at hb
      split at hb
      · rename_i i
        simp only [List.contains_iff_mem] at hb
        simp only at hTv
        rw [hTv]; exact hS _ hb hke
      · rename_i f i
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hb
        obtain ⟨hlast, hmem⟩ := hb
        have hπ : π = π.dropLast ++ [f] := by
          obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
          simp
        have hke₀ : EntryKept h₀ ρ₀ K j π.dropLast := fun l w q hr =>
          hke l w q (by rw [hπ]; exact readsAt_append [f] hr)
        have hm := hS _ hmem hke₀
        have hst := hTv fun l w q hkl => hke l w q (by rw [hπ]; exact readsAt_of_keyLoc hm hkl)
        cases hst with
        | read hp _ _ => simp [isVal] at hv
        | done _ hr => rw [hπ]; exact reads_snoc hm hr
      · simp at hb
    cases hs with
    | frameC hs' =>
      refine .inr (.inl ⟨_, L, d, k, x, l', rfl, hL, hkx, hS, ?_⟩)
      unfold TermHolds at hT ⊢
      split at hT
      · rw [hT] at hs'; exact absurd hs' (value_no_step (hL.at _))
      · rename_i f i heq
        intro hK
        cases hT hK with
        | read hp hrk hkl =>
          cases hs' with
          | readC hp' => exact absurd hp' (value_no_step hp)
          | readField hl hv =>
            have hv₀ := (hk _ (hK _ _ _ (hkl _ _ _ (.own hl)))).symm.trans hv
            exact .done (hhv _ _ hv) (hrk _ (.own hl hv₀))
          | readProto hn hp' hpv =>
            have hpv₀ := (hk _ (hK _ _ _ (hkl _ _ _ (.proto hn hp')))).symm.trans hpv
            exact .read (hhv _ _ hpv) (fun v hr => hrk v (.proto hn hp' hpv₀ hr))
              (fun l w q hl => hkl l w q (.next hn hp' hpv₀ hl))
          | readMissing hn hp' => exact .done rfl (hrk _ (.missing hn hp'))
        | done hv _ => exact absurd hs' (value_no_step hv)
      · trivial
    | frameRet hv => exact .inr (.inr (.inl hv))
    | frameRaise hr => exact .inr (.inr (.inr ⟨_, rfl, raises_val hr⟩))
    | frameBind hv =>
      exact .inl ⟨_, _, _, rfl, (hL.cons hv).map _,
        (edge_holds hS (some true) (hedges _ (List.mem_append_left _ (List.mem_singleton_self _)))).2.2 _ rfl (hbound _ hv hT)⟩
    | frameEffect hv =>
      exact .inl ⟨_, _, _, rfl, hL.map _, (edge_holds hS none (hedges _ (List.mem_append_left _ (List.mem_singleton_self _)))).1 rfl⟩
    | frameYes =>
      exact .inl ⟨_, _, _, rfl, hL.map _, (edge_holds hS none (hedges _ (List.mem_append_left _ List.mem_cons_self))).1 rfl⟩
    | frameNo =>
      exact .inl ⟨_, _, _, rfl, hL.map _, (edge_holds hS none (hedges _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))).1 rfl⟩
    | frameYesBind =>
      exact .inl ⟨_, _, _, rfl, (hL.cons rfl).map _,
        (edge_holds hS (some false) (hedges _ (List.mem_append_left _ List.mem_cons_self))).2.1 _ rfl⟩
    | frameNoBind =>
      exact .inl ⟨_, _, _, rfl, (hL.cons rfl).map _,
        (edge_holds hS (some false) (hedges _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))).2.1 _ rfl⟩
    | frameTag hv =>
      refine .inl ⟨_, _, _, rfl, (hL.cons hv).map _, ?_⟩
      split
      · exact (edge_holds hS (some true) (hedges _ (List.mem_append_left _ List.mem_cons_self))).2.2 _ rfl (hbound _ hv hT)
      · exact (edge_holds hS (some true) (hedges _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))).2.2 _ rfl (hbound _ hv hT)
    | frameHandle hr =>
      exact .inl ⟨_, _, _, rfl, (hL.cons (raises_val hr)).map _,
        (edge_holds hS (some false) (hedges _ (List.mem_append_right _ (List.mem_singleton_self _)))).2.1 _ rfl⟩
  · rcases hn with hv | ⟨v, rfl, hv⟩
    · exact absurd hs (value_no_step hv)
    · cases hs with | throwC s => exact absurd s (value_no_step hv)


/-- **The invariant of the copies along an execution** (proved,
`copyInv_step` at each step): along an execution of a frame from a reached
state each of whose states that steps keeps the entry's heap's contents at
the locations `K`, where reached states hold values in their heaps, the
invariant at its first state holds at its last. -/
theorem copies_along {τ : Type} {fr : ClientFrame τ} {Pe : List Tm} {Pk : List (Continuation × Option Target)}
    {c₀ : ComponentTag} {start arity : Nat} {cp : CopyTable} {h₀ : Heap} {ρ₀ : Env} {K : Nat → Prop}
    (hcp : copiesB Pe Pk start arity cp = true) (hlen : Pe.length = Pk.length)
    (hhv : ∀ y, fr.Reached y → ∀ (l : Nat) (v : Tm), y.1.s.h[l]? = some v → isVal v = true) :
    ∀ {n : Nat} {a b : Conf × Ghost (fr.F.at fr.C)},
      Ex fr.KStep (fun y => ∀ l, K l → y.1.s.h[l]? = h₀[l]?) n a b → fr.Reached a →
      CopyInv Pe Pk c₀ cp h₀ ρ₀ K a.1.t → CopyInv Pe Pk c₀ cp h₀ ρ₀ K b.1.t
  | _, _, _, .refl _, _, hi => hi
  | _, _, _, .next hqa hab hrest, ha, hi =>
    copies_along hcp hlen hhv hrest (ClientFrame.Reached.step ha hab)
      (copyInv_step hcp hlen hi hab.1.step hqa (hhv _ ha))

end Verification.TolerantFrames.ReadOnly
