import Verification.Semantics.TolerantFrames

/-! # Parity assertions

The assertion language of the note "Tolerant frames"
(`docs/drafts/tolerant-frames-note/note.tex`, §4 "The assertion language"),
represented as the design `docs/drafts/parity-interfaces.md` states it (I4,
"Assertion representation"): one acyclic arena of nodes, each reference
naming an earlier node, and boxes referring to their body.

An assertion is read at a name valuation `η`, an entry mark `m` and an
indexed state `s` (`TolerantFrames.IndexedHeap`): the note's triple
`ρ, m, h ⊨ F`. Atoms read `η` and the heap only. A logical variable bound by
`existsValue` is slot `0` of the valuation its body is read at (`push`); the
outer slots shift by one.

The modality reads one definition of the effect semantics, `EffectAction`,
and the lemmas stated beside it (§ "The effect action"): the role-aware
action of the shared foundation replaces that one section. -/
namespace Verification.Parity
open Verification Footprints HeapKnowledge TolerantFrames

/-! ## The effect action

The one place the parity modules read the meaning of an effect. Every
modal statement goes through `EffectAction` and the lemmas after it, and
every support through `SupportedBy`. -/

/-- **The action of an effect** at a name valuation (the note, §3, "the
effect action" `h →Φ_ρ h'`): an admissible transition whose heaps meet the
effect's postcondition, its regions read at the state it starts from
(`TolerantFrames.Action`). -/
def EffectAction (Φ : Footprint) (η : Env) (s s' : IndexedHeap) : Prop :=
  TolerantFrames.Action Φ η s s'

/-- **A transition within a support** (the note, §5, "Support"): every
location `l` below the first heap's length in a region of an entry `r : δ`
of `S`, read at the first state, changes at most by `δ`
(`Footprints.Supported`). -/
def SupportedBy (S : Footprint) (η : Env) (s s' : IndexedHeap) : Prop :=
  Footprints.Supported S η s.h s'.h

/-- The effect letting every location change: the note's `⊤`. -/
def topEffect : Footprint := Footprints.Closed.top.fp

/-- A region read without the name valuation: classes, every location, a
module cell and their intersections with a class. -/
def regionEnvFree : Region → Bool
  | .cls _ | .all | .cell _ => true
  | .inCls r _ => regionEnvFree r
  | _ => false

/-- An effect every region of which is read without the name valuation. -/
def effectEnvFree (Φ : Footprint) : Bool := Φ.all fun e => regionEnvFree e.1

/-- The slots a region reads its roots at. -/
def regionRoots : Region → List Nat
  | .field x _ | .own x | .elems x | .path x _ _ | .pathOwn x _ | .pathElems x _ => [x]
  | .cls _ | .all | .cell _ => []
  | .inCls r _ => regionRoots r

/-- An effect reading runtime slots below `n` alone. -/
def effectScoped (n : Nat) (Φ : Footprint) : Bool := Φ.all fun e => (regionRoots e.1).all (· < n)

/-- **An ordinary array store stays one** along every admissible
transition: a location holding an array store has the store kind in the
world, which the transition keeps (`HeapOk.kinds`, `WExt_roleAt`). With
tagged stores, the store-category correspondence of the shared foundation
replaces this proof. -/
theorem _root_.Verification.TolerantFrames.Admissible.arrayStore {s s' : IndexedHeap} (ha : Admissible s s')
    {l : Nat} {xs : List (Option Nat)} (hl : s.h[l]? = some (.arr xs)) : ∃ ys, s'.h[l]? = some (.arr ys) := by
  have hk : K s.W .store l := (s.ok.kinds.2.1 l).mpr ⟨xs, hl⟩
  obtain ⟨hle, hx⟩ := ha
  have hk' : K s'.W .store l := by
    unfold K kindAt at hk ⊢
    obtain ⟨r, hr, hrk⟩ := Option.map_eq_some_iff.mp hk
    have := WExt_roleAt hx (show roleAt (trunc s'.n hle s.W) l = some r by rw [roleAt_trunc]; exact hr)
    rw [this]; simp [hrk]
  exact (s'.ok.kinds.2.1 l).mp hk'

/-- **The cells a typed array lists** (the note, §4, "Atoms", the element
of a typed array): today's representation, a host object owning no array
store whose `viewElementsKey` location holds the listing. The tagged view
store of the primitive views replaces this one definition. An ordinary
array lists none here. -/
def viewCells (h : Heap) : Val → Option (List (Option Nat))
  | v@(.objAt fs _ _) =>
    if storeOf v = none ∧ (fs.lookup hostKey).isSome = true then
      match fs.lookup viewElementsKey with
      | some l => match h[l]? with
        | some (.arr ls) => some ls
        | _ => none
      | none => none
    else none
  | _ => none

theorem viewCells_ordinary {h : Heap} {v : Val} {s : Nat} (hs : storeOf v = some s) : viewCells h v = none := by
  cases v <;> simp_all [viewCells]

section Action
variable {Φ : Footprint} {η η' : Env} {s s' s'' : IndexedHeap}

theorem EffectAction.refl (Φ : Footprint) (η : Env) (s : IndexedHeap) : EffectAction Φ η s s :=
  TolerantFrames.Action.refl Φ η s

theorem EffectAction.admissible (h : EffectAction Φ η s s') : Admissible s s' := h.1

/-- Every admissible transition is an action of `⊤`. -/
theorem EffectAction.top (h : Admissible s s') : EffectAction topEffect η s s' := action_top h

private theorem region_mem_envFree {r : Region} (hr : regionEnvFree r = true) (hp : Heap) (l : Nat) :
    r.mem η hp l = r.mem η' hp l := by
  induction r with
  | inCls r _ ih => simp only [Region.mem, ih hr]
  | cls _ => rfl
  | all => rfl
  | cell _ => rfl
  | _ => simp [regionEnvFree] at hr

/-- An effect read without the name valuation acts alike at every valuation. -/
theorem EffectAction.envFree (hΦ : effectEnvFree Φ = true) (h : EffectAction Φ η s s') :
    EffectAction Φ η' s s' := by
  refine ⟨h.1, h.2.1, fun l v hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := h.2.2 l v hv
  refine ⟨v', hv', ha.imp_right fun ⟨e, he, hm, hc⟩ => ⟨e, he, ?_, hc⟩⟩
  have := List.all_eq_true.mp hΦ e he
  rw [← region_mem_envFree this]; exact hm

/-- A closed effect's action is transitive (`TolerantFrames.closed_rigid`):
the note's rigidity, §4, law (e). -/
theorem EffectAction.closed_trans (c : Footprints.Closed) (h₁ : EffectAction c.fp η s s')
    (h₂ : EffectAction c.fp η s' s'') : EffectAction c.fp η s s'' :=
  closed_rigid c η s s' s'' h₁ h₂

/-- Inclusion of closed effects includes their actions
(`TolerantFrames.action_le_closed`): the note's `Φ ⊑ Ψ`, §4, law (c). -/
theorem EffectAction.closed_mono {a b : Footprints.Closed} (hle : a.le b = true) (h : EffectAction a.fp η s s') :
    EffectAction b.fp η s s' :=
  action_le_closed hle h

/-- **An effect with its roots renamed acts as the effect at the renamed
valuation** (`Footprints.Region.mem_rename`). -/
theorem EffectAction.rename_iff (σ : Nat → Nat) :
    EffectAction (Footprint.rename σ Φ) η s s' ↔ EffectAction Φ (fun i => η (σ i)) s s' := by
  have hm : ∀ (r : Region) l, (r.rename σ).mem η s.h l = r.mem (fun i => η (σ i)) s.h l :=
    fun r l => Region.mem_rename σ η s.h l r
  constructor
  · rintro ⟨ha, hl, hp⟩
    refine ⟨ha, hl, fun l v hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := hp l v hv
    refine ⟨v', hv', hal.imp_right fun ⟨e, he, hme, hc⟩ => ?_⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact ⟨e0, he0, by rw [← hm]; exact hme, hc⟩
  · rintro ⟨ha, hl, hp⟩
    refine ⟨ha, hl, fun l v hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := hp l v hv
    refine ⟨v', hv', hal.imp_right fun ⟨e, he, hme, hc⟩ => ?_⟩
    exact ⟨(e.1.rename σ, e.2), List.mem_map.mpr ⟨e, he, rfl⟩, by rw [hm]; exact hme, hc⟩

/-- The class of values and the class of stores share no location. -/
theorem regionClasses_disjoint {l : Nat} (hl : (Region.cls .value).mem η s.h l = true) :
    (Region.cls .store).mem η s.h l = false := by
  simp only [Region.mem] at hl ⊢
  split at hl
  · simp only [Cls.has] at hl ⊢; simpa using hl
  · cases hl

/-- **A transition within an effect is within a support whose every entry
each effect entry either changes less than, or misses** (the note, §5, the
proof of Theorem "Tolerant frame"). -/
theorem supported_of_pairs {S : Footprint} (ha : EffectAction Φ η s s')
    (hp : ∀ e ∈ S, ∀ e' ∈ Φ, e'.2.le e.2 = true ∨ ∀ l, e.1.mem η s.h l = true → e'.1.mem η s.h l = false) :
    SupportedBy S η s s' := by
  intro e he l v hl hv
  obtain ⟨v', hv', hal⟩ := ha.2.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases hal with rfl | ⟨e', he', hm, hc⟩
  · exact Change.Holds.refl _ _ _
  · rcases hp e he e' he' with hle | hd
    · exact hc.mono hle
    · rw [hd l hl] at hm; cases hm

end Action

/-! ## Paths and witnesses -/

/-- A reference to an arena node. -/
structure AssertionRef where
  index : Nat
  deriving DecidableEq, Repr

/-- An ordinary path (the note, §2, "paths" `π`): a root slot and the named
data fields read in turn from its value. -/
structure Path where
  root : Nat
  fields : List String
  deriving DecidableEq, Repr

namespace Path

/-- The variable `x`: the empty path at slot `x`. -/
def var (x : Nat) : Path := ⟨x, []⟩

/-- The value a path reads, where every field it passes is owned. -/
def read (η : Env) (h : Heap) (p : Path) : Option Val := readPath h (η p.root) p.fields

/-- The current term of kind `k` read at the end of the path. -/
def term (k : Term.Kind) (p : Path) : Term := Term.now k p.root p.fields

@[simp] theorem term_atEntry (k : Term.Kind) (p : Path) : (p.term k).atEntry = false := rfl

/-- A path's term denotes what its kind reads of the value the path reads. -/
theorem termAt_term (η : Env) (h : Heap) (k : Term.Kind) (p : Path) :
    termAt η h (p.term k) = (p.read η h).bind (kindValue h k) := rfl

end Path

/-- A witness expression (I4): a path, or a literal source value. -/
inductive Witness where
  | path (p : Path)
  | literal (v : Val)
  deriving DecidableEq

/-- The value a witness denotes, where it denotes one. -/
def Witness.value (η : Env) (h : Heap) : Witness → Option Val
  | .path p => p.read η h
  | .literal v => some v

/-! ## Atoms -/

/-- A variable of a scalar body (I4, "ScalarBody"): the bound index, the
element's scalar value, the element's string length, or a logical scalar
parameter (a slot's own safe integer). The note's `every(z, t, φ)`, §4,
"Atoms": `φ` over scalars. -/
def scalarBound : Bound → Bool
  | .index | .elem => true
  | .project .strLength [] => true
  | .free t => !t.atEntry && t.kind == .value && t.path.isEmpty
  | _ => false

/-- A scalar body: every variable of every clause is scalar. -/
def scalarBody (body : List (LinearClause Bound)) : Bool :=
  body.all fun F => F.vars.all scalarBound

/-- What a scalar variable denotes at index `i` of the store listing `ls`:
the index, the present element's safe integer, the present element's string
length, or the parameter's value. -/
def scalarValue (η : Env) (h : Heap) (ls : List (Option Nat)) (i : Nat) : Bound → Option Int
  | .index => some (i : Int)
  | .elem => elementInt h ls i
  | .project .strLength [] => match ls[i]? with
    | some (some l) => h[l]?.bind strLengthOf
    | _ => none
  | .free t => termAt η h t
  | _ => none

/-- The selected first-order atoms (the note, §4, "Atoms"; I4, `Atom`):
a linear fact over current terms, a path's value, a dense prefix, a kind of
contents, a bounded quantification, a typed-array element, a defined term, a
safe integer, and the double `2^53` past the safe integers. -/
inductive Atom where
  | linear (fact : Linear.Fact Term)
  | equal (path : Path) (value : Witness)
  | dense (path : Path) (bound : Term)
  | contents (path : Path) (kind : CallEffects.ElemPred)
  | every (path : Path) (bound : Term) (body : List (LinearClause Bound))
  | element (path : Path) (index : Term) (value : Witness)
  | defined (term : Term)
  | safeInt (path : Path)
  | pastSafe (path : Path)
  deriving DecidableEq

/-- **The meaning of an atom** (the note, §4, "Atoms": an atom is true only
where every path it reads is defined). -/
def Atom.Holds (η : Env) (h : Heap) : Atom → Prop
  | .linear F => FactAt (termAt η h) F
  | .equal p w => ∃ v, p.read η h = some v ∧ w.value η h = some v
  | .dense p n => ∃ w s ls k, p.read η h = some w ∧ storeOf w = some s ∧ h[s]? = some (.arr ls) ∧
      termAt η h n = some k ∧ 0 ≤ k ∧ DensePrefix k.toNat ls
  | .contents p R => ∃ v, p.read η h = some v ∧ R.mem v = true
  | .every p n body => ∃ w s ls k, p.read η h = some w ∧ storeOf w = some s ∧ h[s]? = some (.arr ls) ∧
      termAt η h n = some k ∧ ∀ i : Nat, (i : Int) < k →
        (∃ l, ls[i]? = some (some l)) ∧ ∀ F ∈ body, F.HoldsAt (scalarValue η h ls i)
  | .element p t w => ∃ u ls k l v, p.read η h = some u ∧ viewCells h u = some ls ∧
      termAt η h t = some k ∧ 0 ≤ k ∧ ls[k.toNat]? = some (some l) ∧ h[l]? = some v ∧ w.value η h = some v
  | .defined t => (termAt η h t).isSome
  | .safeInt p => ∃ v, p.read η h = some v ∧ (intValue v).isSome
  | .pastSafe p => p.read η h = some (.num SafeIntegers.pastSafeBits)

/-- The terms an atom names. -/
def Atom.terms : Atom → List Term
  | .linear F => F.vars
  | .dense _ n => [n]
  | .every _ n body => n :: body.flatMap fun F => F.vars.filterMap fun
      | .free t => some t
      | _ => none
  | .element _ t _ => [t]
  | .defined t => [t]
  | _ => []

/-- Every term of an atom reads the current state: a single-state assertion
names no entry term (I4: `Term.old` belongs to two-state posts), and its
quantified bodies are scalar. -/
def Atom.wellFormed (a : Atom) : Bool :=
  a.terms.all (fun t => !t.atEntry) && match a with
    | .every _ _ body => scalarBody body
    | _ => true

/-- An atom whose truth depends on the name valuation alone: each path it
reads is a variable, and each term a variable's own safe integer or string
length. -/
def Atom.envOnly : Atom → Bool
  | .linear F => F.vars.all fun t => t.envOnly && !t.atEntry
  | .equal p w => p.fields.isEmpty && match w with
    | .path q => q.fields.isEmpty
    | .literal _ => true
  | .contents p _ => p.fields.isEmpty
  | .defined t => t.envOnly && !t.atEntry
  | .safeInt p => p.fields.isEmpty
  | .pastSafe p => p.fields.isEmpty
  | _ => false

/-- A path through no field reads its root's value in every heap. -/
theorem Path.read_nil {η : Env} {h : Heap} {p : Path} (hp : p.fields = []) : p.read η h = some (η p.root) := by
  obtain ⟨r, f⟩ := p; subst hp; rfl

theorem Path.read_heap {η : Env} {h h' : Heap} {p : Path} (hp : p.fields = []) : p.read η h = p.read η h' := by
  rw [Path.read_nil hp, Path.read_nil hp]

private theorem termAt_envOnly {η : Env} {h h' : Heap} {t : Term} (ht : t.envOnly = true) (he : t.atEntry = false) :
    termAt η h t = termAt η h' t := by
  have := termValue_envOnly (ε := ⟨η, h⟩) (ρ := η) (h := h) (h' := h') ht
  rwa [termValue_now he, termValue_now he] at this

/-- **An atom reading the name valuation alone holds in every heap.** -/
theorem Atom.holds_envOnly {a : Atom} (ha : a.envOnly = true) {η : Env} {h h' : Heap} :
    a.Holds η h ↔ a.Holds η h' := by
  cases a with
  | linear F =>
    have he : ∀ t ∈ F.vars, termAt η h' t = termAt η h t := fun t ht => by
      have := List.all_eq_true.mp ha t ht
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact termAt_envOnly this.1 this.2
    exact ⟨fun hf => factAt_congr he hf, fun hf => factAt_congr (fun t ht => (he t ht).symm) hf⟩
  | equal p w =>
    simp only [Atom.envOnly, Bool.and_eq_true, List.isEmpty_iff] at ha
    obtain ⟨hp, hw⟩ := ha
    have hw' : w.value η h = w.value η h' := by
      cases w with
      | path q => simp only [List.isEmpty_iff] at hw; exact Path.read_heap hw
      | literal _ => rfl
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') hp, hw']
  | contents p R =>
    simp only [Atom.envOnly, List.isEmpty_iff] at ha
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') ha]
  | defined t =>
    simp only [Atom.envOnly, Bool.and_eq_true, Bool.not_eq_true'] at ha
    simp only [Atom.Holds, termAt_envOnly (h := h) (h' := h') ha.1 ha.2]
  | safeInt p =>
    simp only [Atom.envOnly, List.isEmpty_iff] at ha
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') ha]
  | pastSafe p =>
    simp only [Atom.envOnly, List.isEmpty_iff] at ha
    simp only [Atom.Holds, Path.read_heap (h := h) (h' := h') ha]
  | _ => simp [Atom.envOnly] at ha

/-! ## Separation and freshness -/

/-- `π # π'` (the note, §4, "Satisfaction"): the two paths read ordinary
arrays, their stores ordinary array stores, at different locations. -/
def Separated (η : Env) (h : Heap) (p q : Path) : Prop :=
  ∃ u w s t xs ys, p.read η h = some u ∧ q.read η h = some w ∧ storeOf u = some s ∧ storeOf w = some t ∧
    h[s]? = some (.arr xs) ∧ h[t]? = some (.arr ys) ∧ s ≠ t

/-- `apart(π, π')` (the note, §4, "Satisfaction"): `π # π'`, and the stores
of the two arrays list no common element cell. -/
def Apart (η : Env) (h : Heap) (p q : Path) : Prop :=
  ∃ u w s t xs ys, p.read η h = some u ∧ q.read η h = some w ∧ storeOf u = some s ∧ storeOf w = some t ∧
    s ≠ t ∧ h[s]? = some (.arr xs) ∧ h[t]? = some (.arr ys) ∧ ∀ l, some l ∈ xs → some l ∉ ys

/-- `fresh(π)` (the note, §4, "Satisfaction"): the store of the array the
path reads is at or above the entry mark. -/
def FreshPath (η : Env) (m : Nat) (h : Heap) (p : Path) : Prop :=
  ∃ v, p.read η h = some v ∧ FreshAt m v

/-! ## The arena -/

/-- An arena node (the note, §4, "Syntax"; I4, `AssertionNode`): sharing is
the representation of the note's ordinary syntax. `guarded g A` is the
note's `g ∨ A` with `g` invariant; `existsValue A` binds logical slot `0`;
`box Φ A` is `□_Φ A`. -/
inductive AssertionNode where
  | truth
  | falsity
  | atom (a : Atom)
  | and (left right : AssertionRef)
  | guarded (guard body : AssertionRef)
  | existsValue (body : AssertionRef)
  | separated (left right : Path)
  | apart (left right : Path)
  | fresh (path : Path)
  | box (effect : Footprint) (body : AssertionRef)
  deriving DecidableEq

/-- Finite immutable nodes. -/
structure AssertionArena where
  nodes : Array AssertionNode

/-- **Satisfaction of node `i`** (the note, §4, "Satisfaction"). A reference
not below its user denotes `False`; a valid arena has none. -/
def satNode (nodes : Array AssertionNode) (i : Nat) (η : Env) (m : Nat) (s : IndexedHeap) : Prop :=
  match nodes[i]? with
  | none => False
  | some .truth => True
  | some .falsity => False
  | some (.atom a) => a.Holds η s.h
  | some (.and l r) =>
    (if _ : l.index < i then satNode nodes l.index η m s else False) ∧
      (if _ : r.index < i then satNode nodes r.index η m s else False)
  | some (.guarded g b) =>
    (if _ : g.index < i then satNode nodes g.index η m s else False) ∨
      (if _ : b.index < i then satNode nodes b.index η m s else False)
  | some (.existsValue b) =>
    ∃ v : Val, if _ : b.index < i then satNode nodes b.index (push v η) m s else False
  | some (.separated p q) => Separated η s.h p q
  | some (.apart p q) => Apart η s.h p q
  | some (.fresh p) => FreshPath η m s.h p
  | some (.box Φ b) =>
    ∀ s', EffectAction Φ η s s' → if _ : b.index < i then satNode nodes b.index η m s' else False
termination_by i

/-- `η, m, s ⊨ a`. -/
def Sat (arena : AssertionArena) (η : Env) (m : Nat) (s : IndexedHeap) (a : AssertionRef) : Prop :=
  satNode arena.nodes a.index η m s

/-! ## Invariant assertions -/

/-- **Checked invariance** (the note, §4, "Invariant assertions": `F ⊢ □_⊤ F`):
`true`, `false`, atoms reading the name valuation alone, separation of
variables, freshness of a variable, a box of `⊤`, and the connectives over
invariant assertions. -/
def invNode (nodes : Array AssertionNode) (i : Nat) : Bool :=
  match nodes[i]? with
  | some .truth | some .falsity => true
  | some (.atom a) => a.envOnly
  | some (.and l r) | some (.guarded l r) =>
    (if _ : l.index < i then invNode nodes l.index else false) &&
      (if _ : r.index < i then invNode nodes r.index else false)
  | some (.existsValue b) => if _ : b.index < i then invNode nodes b.index else false
  | some (.separated p q) => p.fields.isEmpty && q.fields.isEmpty
  | some (.fresh p) => p.fields.isEmpty
  | some (.box Φ _) => Φ == topEffect
  | _ => false
termination_by i

/-- **Checked invariance is invariance.** -/
theorem invNode_sound (nodes : Array AssertionNode) :
    ∀ i, invNode nodes i = true → Invariant (satNode nodes i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi η m s s' ha hs
  rw [invNode] at hi
  rw [satNode] at hs ⊢
  split at hi
  · rename_i hn; rw [hn] at hs ⊢; exact hs
  · rename_i hn; rw [hn] at hs; exact hs.elim
  · rename_i a hn
    rw [hn] at hs ⊢
    exact (Atom.holds_envOnly hi).mp hs
  · rename_i l r hn
    rw [hn] at hs ⊢
    simp only [Bool.and_eq_true] at hi
    obtain ⟨hl, hr⟩ := hi
    refine ⟨?_, ?_⟩
    · split at hl
      · rename_i hli; simp only [hli, dite_true] at hs ⊢; exact ih _ hli hl η m s s' ha hs.1
      · cases hl
    · split at hr
      · rename_i hri; simp only [hri, dite_true] at hs ⊢; exact ih _ hri hr η m s s' ha hs.2
      · cases hr
  · rename_i l r hn
    rw [hn] at hs ⊢
    simp only [Bool.and_eq_true] at hi
    obtain ⟨hl, hr⟩ := hi
    rcases hs with hs | hs
    · refine .inl ?_
      split at hl
      · rename_i hli; simp only [hli, dite_true] at hs ⊢; exact ih _ hli hl η m s s' ha hs
      · cases hl
    · refine .inr ?_
      split at hr
      · rename_i hri; simp only [hri, dite_true] at hs ⊢; exact ih _ hri hr η m s s' ha hs
      · cases hr
  · rename_i b hn
    rw [hn] at hs ⊢
    split at hi
    · rename_i hbi
      obtain ⟨v, hv⟩ := hs
      simp only [hbi, dite_true] at hv
      exact ⟨v, by simp only [hbi, dite_true]; exact ih _ hbi hi _ m s s' ha hv⟩
    · cases hi
  · rename_i p q hn
    rw [hn] at hs ⊢
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hi
    obtain ⟨u, w, a, b, xs, ys, hu, hw, hsa, hsb, hxa, hyb, hne⟩ := hs
    obtain ⟨xs', hx'⟩ := ha.arrayStore hxa
    obtain ⟨ys', hy'⟩ := ha.arrayStore hyb
    exact ⟨u, w, a, b, xs', ys', by rw [Path.read_heap hi.1]; exact hu, by rw [Path.read_heap hi.2]; exact hw,
      hsa, hsb, hx', hy', hne⟩
  · rename_i p hn
    rw [hn] at hs ⊢
    simp only [List.isEmpty_iff] at hi
    obtain ⟨v, hv, hf⟩ := hs
    exact ⟨v, by rw [Path.read_heap hi]; exact hv, hf⟩
  · rename_i Φ b hn
    rw [hn] at hs ⊢
    simp only [beq_iff_eq] at hi
    subst hi
    intro s'' ha'
    exact hs s'' (EffectAction.top (ha.trans ha'.admissible))
  · cases hi

/-! ## Validity -/

/-- The references of a node precede it. -/
def AssertionNode.refsBelow (i : Nat) : AssertionNode → Bool
  | .and l r | .guarded l r => decide (l.index < i) && decide (r.index < i)
  | .existsValue b | .box _ b => decide (b.index < i)
  | _ => true

/-- **A well-formed node** (I4, `AssertionArena.Valid`): its references
precede it, its atoms read the current state with scalar quantified bodies,
and a guard has checked invariance. -/
def AssertionNode.wellFormed (nodes : Array AssertionNode) (i : Nat) (n : AssertionNode) : Bool :=
  n.refsBelow i && match n with
    | .atom a => a.wellFormed
    | .guarded g _ => invNode nodes g.index
    | _ => true

/-- Every node of the arena is well formed. -/
def AssertionArena.Valid (arena : AssertionArena) : Prop :=
  ∀ (i : Nat) (n : AssertionNode), arena.nodes[i]? = some n → n.wellFormed arena.nodes i = true

/-- The executable check of validity. -/
def AssertionArena.check (arena : AssertionArena) : Bool :=
  (List.range arena.nodes.size).all fun i => match arena.nodes[i]? with
    | some n => n.wellFormed arena.nodes i
    | none => true

theorem AssertionArena.check_valid {arena : AssertionArena} (hc : arena.check = true) : arena.Valid := by
  intro i n hn
  have hi : i < arena.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
  have := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simpa only [hn] using this

theorem AssertionArena.Valid.refs {arena : AssertionArena} (hv : arena.Valid) {i : Nat} {n : AssertionNode}
    (hn : arena.nodes[i]? = some n) : n.refsBelow i = true := by
  have := hv i n hn
  simp only [AssertionNode.wellFormed, Bool.and_eq_true] at this
  exact this.1

/-! ## Interpretation lemmas -/

section Interpretation
variable {arena : AssertionArena} {η : Env} {m : Nat} {s : IndexedHeap} {a : AssertionRef}

theorem sat_truth (hn : arena.nodes[a.index]? = some .truth) : Sat arena η m s a := by
  unfold Sat; rw [satNode, hn]; trivial

theorem sat_falsity (hn : arena.nodes[a.index]? = some .falsity) : ¬ Sat arena η m s a := by
  unfold Sat; rw [satNode, hn]; exact id

theorem sat_atom {x : Atom} (hn : arena.nodes[a.index]? = some (.atom x)) :
    Sat arena η m s a ↔ x.Holds η s.h := by
  unfold Sat; rw [satNode, hn]

theorem sat_and {l r : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.and l r)) :
    Sat arena η m s a ↔ Sat arena η m s l ∧ Sat arena η m s r := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, Bool.and_eq_true, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb.1, hb.2, dite_true]

theorem sat_guarded {g b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.guarded g b)) :
    Sat arena η m s a ↔ Sat arena η m s g ∨ Sat arena η m s b := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, Bool.and_eq_true, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb.1, hb.2, dite_true]

theorem sat_exists {b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.existsValue b)) :
    Sat arena η m s a ↔ ∃ v : Val, Sat arena (push v η) m s b := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb, dite_true]

theorem sat_separated {p q : Path} (hn : arena.nodes[a.index]? = some (.separated p q)) :
    Sat arena η m s a ↔ Separated η s.h p q := by
  unfold Sat; rw [satNode, hn]

theorem sat_apart {p q : Path} (hn : arena.nodes[a.index]? = some (.apart p q)) :
    Sat arena η m s a ↔ Apart η s.h p q := by
  unfold Sat; rw [satNode, hn]

theorem sat_fresh {p : Path} (hn : arena.nodes[a.index]? = some (.fresh p)) :
    Sat arena η m s a ↔ FreshPath η m s.h p := by
  unfold Sat; rw [satNode, hn]

theorem sat_box {Φ : Footprint} {b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.box Φ b)) :
    Sat arena η m s a ↔ ∀ s', EffectAction Φ η s s' → Sat arena η m s' b := by
  have hb := hv.refs hn
  simp only [AssertionNode.refsBelow, decide_eq_true_eq] at hb
  unfold Sat; rw [satNode, hn]; simp only [hb, dite_true]

/-- **A box is the note's modality**: `Sat` of `box Φ A` is `TolerantFrames.Box`
of `A`'s satisfaction, through `EffectAction`. -/
theorem sat_box_iff_Box {Φ : Footprint} {b : AssertionRef} (hv : arena.Valid)
    (hn : arena.nodes[a.index]? = some (.box Φ b)) :
    Sat arena η m s a ↔ Box Φ (fun η m s => Sat arena η m s b) η m s :=
  sat_box hv hn

/-- A guard of a valid arena is invariant. -/
theorem guard_invariant {g b : AssertionRef} (hv : arena.Valid) (hn : arena.nodes[a.index]? = some (.guarded g b)) :
    Invariant (fun η m s => Sat arena η m s g) := by
  have := hv _ _ hn
  simp only [AssertionNode.wellFormed, Bool.and_eq_true] at this
  exact invNode_sound arena.nodes g.index this.2

/-- **Definedness**: a linear atom defines each of its terms. -/
theorem sat_linear_defined {F : Linear.Fact Term} (hn : arena.nodes[a.index]? = some (.atom (.linear F)))
    (hs : Sat arena η m s a) : ∀ t ∈ F.vars, (termAt η s.h t).isSome :=
  ((sat_atom hn).mp hs).1

/-- An assertion's satisfaction reads the state's heap and the entry mark
alone: two states with one heap satisfy the same atoms. -/
theorem atom_heap {x : Atom} {s' : IndexedHeap} (hh : s.h = s'.h) : x.Holds η s.h ↔ x.Holds η s'.h := by
  rw [hh]

end Interpretation

end Verification.Parity
