import Verification.Paper.TolerantFrames.ReadOnlyRegion

/-! # Read-only handles: the rule and its lemmas

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, section
"What the Lean states"), over the region of `ReadOnlyRegion`: a state is the
paper's indexed state with the ghost state and the values the frames of code
that is not the package's hold; a part is a site (or `out`), a kind of the
world and a key; a protocol `Ψ_P` gives each part a change; the action of
`Φ ⊕_P Ψ_P` bounds the locations of `R_P` by `Ψ_P` at their parts and every
other location by `Φ`.

- (L1) `outside_step`: a step of code that is not the package's, meeting
  the trust row and changing only storage its frames reach, leaves every
  location of `R_P` unchanged and keeps (M) and (P2).
- (L3) `Leads.trans`: inside a call, the action of `Φ ⊕_P Ψ_P` with the
  history's growth is transitive when `Φ` is rigid and `Ψ_P ⊑ Φ`.
- (L2) `Run.bound`: a run of code that is not the package's inside a call,
  outside steps and member calls bounded by their certificates, changes
  every location of `R_P` within `Ψ_P` and keeps the region.
- (L4) `Run.keeps`: an invariant of `G_P` every outside step keeps
  survives such a run; one whose support lies in `R_P` (`SupportInR`), or
  whose support read at each state does (`SupportAt`, `InvIn`), is one.
- (O) `ownership`: storage an admitted install makes the support read stays
  in `R_P` for the rest of the call.
- The rule (`readOnly_rule`) and its consequence, Proposition "Read-only
  reliance" of the Read-only frames note: a fact whose support meets the
  premise location by location (`Framed`: `Ψ` at a location of `R_P`, `Φ`
  at any other) holds after the run (`readOnly_rely`, the bound route), by
  the definition of support the tolerant frame (`frame_step`) reads; an
  invariant of `G_P` held with its support in `R_P` holds after it
  (`readOnly_guarantee`, the guarantee route).

The trust row is a hypothesis on outside steps (`OutsideStep.row`), as are
three properties of the language's steps: a step changes only storage its
frames reach (`OutsideStep.reach`), leaves in storage it changes or
allocates only references to such storage (`OutsideStep.writes`), and
reaches afterwards only storage it reached or allocated
(`OutsideStep.noForge`). `ReadOnlyOutside` proves the three of the
calculus's steps at the roots of outside code. A member's certificate (`Member`) is a hypothesis: the pass's
checks are what establish it. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

variable {P : Package}

/-! ## States and parts -/

/-- **A state** (the draft, "What the Lean states"): the paper's indexed
state (budget, world, heap), the ghost state, and the values the frames of
code that is not the package's hold. -/
structure St (P : Package) where
  s : IndexedHeap
  g : Ghost P
  roots : List Val

/-- **A part** (the draft, "Parts and the protocol"): a site or `out`, a
kind of the Tolerant frames note's world and, for a field location, its key. -/
structure Part (P : Package) where
  site : Option P.Site
  kind : Option Kind
  key : Option PropKey

/-- A location's part at a state. -/
def St.part (st : St P) (l : Nat) : Part P := ⟨st.g.site l, kindAt st.s.W l, st.g.key l⟩

/-- **A protocol** `Ψ_P`: a change for each part. -/
abbrev Protocol (P : Package) := Part P → Change

/-- **A transition keeping the marks**: admissible, every old location's
site and key fixed (the marks fixed at allocation, the draft's (M)). -/
def Kept (st st' : St P) : Prop :=
  Admissible st.s st'.s ∧ ∀ l, l < st.s.h.length → st'.g.site l = st.g.site l ∧ st'.g.key l = st.g.key l

theorem Kept.refl (st : St P) : Kept st st := ⟨Admissible.refl _, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Kept.trans {st₁ st₂ st₃ : St P} (h₁ : Kept st₁ st₂) (h₂ : Kept st₂ st₃) : Kept st₁ st₃ := by
  refine ⟨WorldReach.trans h₁.1 h₂.1, fun l hl => ?_⟩
  have hl₂ : l < st₂.s.h.length := Nat.lt_of_lt_of_le hl h₁.1.length_le
  exact ⟨(h₂.2 l hl₂).1.trans (h₁.2 l hl).1, (h₂.2 l hl₂).2.trans (h₁.2 l hl).2⟩

/-- **An admissible transition keeps each old location's kind.** -/
theorem kindAt_kept {s s' : IndexedHeap} (ha : Admissible s s') {l : Nat} (hl : l < s.h.length) :
    kindAt s'.W l = kindAt s.W l := by
  obtain ⟨hle, hx⟩ := ha
  have hlen : l < (entries (trunc s'.n hle s.W)).length := by
    have := s.ok.1.1
    simp only [toList, List.length_map] at this
    simpa [entries_trunc] using this ▸ hl
  rw [WExt_kindAt hx hlen, kindAt_trunc]

theorem Kept.part {st st' : St P} (hk : Kept st st') {l : Nat} (hl : l < st.s.h.length) :
    st'.part l = st.part l := by
  simp only [St.part, (hk.2 l hl).1, (hk.2 l hl).2, kindAt_kept hk.1 hl]

theorem Kept.origin {st st' : St P} (hk : Kept st st') {l : Nat} (hl : l < st.s.h.length) :
    st'.g.origin l = st.g.origin l := by
  simp only [Ghost.origin, (hk.2 l hl).1]

/-! ## The action of `Φ ⊕_P Ψ_P` -/

/-- **The bound on a location** (the draft, "The bound on `R_P`"): a
location of `R_P` changes within `Ψ_P` at its part, any other within `Φ`,
regions read at the entry state. -/
def Bounded (Φ : Footprint) (Ψ : Protocol P) (ρ : Env) (st : St P) (l : Nat) (v v' : Val) : Prop :=
  (st.g.InR l → (Ψ (st.part l)).Holds st.s.h.length v v') ∧ (¬ st.g.InR l → Allowed Φ ρ st.s.h l v v')

/-- **The action of `Φ ⊕_P Ψ_P`**: a transition keeping the marks whose
every old location changes within its bound. -/
def OAction (Φ : Footprint) (Ψ : Protocol P) (ρ : Env) (st st' : St P) : Prop :=
  Kept st st' ∧ ∀ l v, st.s.h[l]? = some v → ∃ v', st'.s.h[l]? = some v' ∧ Bounded Φ Ψ ρ st l v v'

/-- **`Ψ_P ⊑ Φ`** (the draft, (L3)): a change within `Ψ_P` at a location of
`R_P` is one `Φ` allows there. -/
def PsiWithin (Φ : Footprint) (Ψ : Protocol P) (ρ : Env) : Prop :=
  ∀ (st : St P) l v v', st.g.InR l → st.s.h[l]? = some v → (Ψ (st.part l)).Holds st.s.h.length v v' →
    Allowed Φ ρ st.s.h l v v'

/-- Where `Ψ_P ⊑ Φ`, an action of `Φ ⊕_P Ψ_P` is one of `Φ`. -/
theorem OAction.action {Φ : Footprint} {Ψ : Protocol P} {ρ : Env} {st st' : St P} (hle : PsiWithin Φ Ψ ρ)
    (ha : OAction Φ Ψ ρ st st') : TolerantFrames.Action Φ ρ st.s st'.s := by
  refine ⟨ha.1.1, ha.1.1.length_le, fun l v hv => ?_⟩
  obtain ⟨v', hv', hb⟩ := ha.2 l v hv
  refine ⟨v', hv', ?_⟩
  by_cases hr : st.g.InR l
  · exact hle st l v v' hr hv (hb.1 hr)
  · exact hb.2 hr

/-- **The relation `s ⇝ s'` inside a call at depth `d`** (the draft, (L3)):
an action of `Φ ⊕_P Ψ_P` at the regions of `s`, the history growing. -/
def Leads (d : Nat) (Φ : Footprint) (Ψ : Protocol P) (ρ : Env) (st st' : St P) : Prop :=
  OAction Φ Ψ ρ st st' ∧ Grows d st.g st'.g

/-- **(L3) Rigidity**: inside a call, `⇝` is transitive when `Φ` is rigid
and `Ψ_P ⊑ Φ`. A location of `R_P` at the first state stays in it (the
region only grows, `InR.mono`) and composes its two changes at its part,
which the marks and the world fix (`Change.Holds.trans`); any other
location composes within `Φ`, by `Φ`'s rigidity applied to the two steps as
actions of `Φ`. -/
theorem Leads.trans {d : Nat} {Φ : Footprint} {Ψ : Protocol P} {ρ : Env} {st₁ st₂ st₃ : St P}
    (hΦ : Rigid Φ ρ) (hle : PsiWithin Φ Ψ ρ) (h₁ : Leads d Φ Ψ ρ st₁ st₂) (h₂ : Leads d Φ Ψ ρ st₂ st₃) :
    Leads d Φ Ψ ρ st₁ st₃ := by
  have hc := hΦ _ _ _ (h₁.1.action hle) (h₂.1.action hle)
  refine ⟨⟨h₁.1.1.trans h₂.1.1, fun l v₁ hv₁ => ?_⟩, h₁.2.trans h₂.2⟩
  have hl : l < st₁.s.h.length := (List.getElem?_eq_some_iff.mp hv₁).1
  obtain ⟨v₂, hv₂, hb₁⟩ := h₁.1.2 l v₁ hv₁
  obtain ⟨v₃, hv₃, hb₂⟩ := h₂.1.2 l v₂ hv₂
  refine ⟨v₃, hv₃, fun hr => ?_, fun hr => ?_⟩
  · have hr₂ : st₂.g.InR l := InR.mono h₁.2 (h₁.1.1.2 l hl).1 hr
    have hp : st₂.part l = st₁.part l := h₁.1.1.part hl
    exact Change.Holds.trans h₁.1.1.1.length_le (hb₁.1 hr) (hp ▸ hb₂.1 hr₂)
  · obtain ⟨v₃', hv₃', hal⟩ := hc.2.2 l v₁ hv₁
    rw [hv₃] at hv₃'
    cases hv₃'
    exact hal

/-- The effect letting every allocated location change: `⊤`. -/
def topAll : Footprint := [(.all, .any)]

theorem allowed_topAll {ρ : Env} {h : Heap} {l : Nat} {v : Val} (hv : h[l]? = some v) (v' : Val) :
    Allowed topAll ρ h l v v' :=
  .inr ⟨(.all, .any), List.mem_singleton_self _,
    by simpa [Region.mem] using (List.getElem?_eq_some_iff.mp hv).1, trivial⟩

/-- `⊤` is rigid. -/
theorem rigid_topAll (ρ : Env) : Rigid topAll ρ := by
  intro s₁ s₂ s₃ h₁ h₂
  refine ⟨WorldReach.trans h₁.1 h₂.1, Nat.le_trans h₁.2.1 h₂.2.1, fun l v hv => ?_⟩
  obtain ⟨v₂, hv₂, -⟩ := h₁.2.2 l v hv
  obtain ⟨v₃, hv₃, -⟩ := h₂.2.2 l v₂ hv₂
  exact ⟨v₃, hv₃, allowed_topAll hv v₃⟩

/-- Every protocol is within `⊤`. -/
theorem psiWithin_topAll (Ψ : Protocol P) (ρ : Env) : PsiWithin topAll Ψ ρ :=
  fun _ _ _ v' _ hv _ => allowed_topAll hv v'

/-- **(L3) at `⊤`**: an unknown callback's bound, `⊤ ⊕_P Ψ_P`, is rigid
inside a call, for every protocol. -/
theorem Leads.trans_top {d : Nat} {Ψ : Protocol P} {ρ : Env} {st₁ st₂ st₃ : St P}
    (h₁ : Leads d topAll Ψ ρ st₁ st₂) (h₂ : Leads d topAll Ψ ρ st₂ st₃) : Leads d topAll Ψ ρ st₁ st₃ :=
  Leads.trans (rigid_topAll ρ) (psiWithin_topAll Ψ ρ) h₁ h₂

/-! ## Outside steps -/

/-- A transition changes the location `l`. -/
def Changes (st st' : St P) (l : Nat) : Prop := ∃ v, st.s.h[l]? = some v ∧ st'.s.h[l]? ≠ some v

theorem unchanged_of {st st' : St P} {l : Nat} {v : Val} (hn : ¬ Changes st st' l) (hv : st.s.h[l]? = some v) :
    st'.s.h[l]? = some v :=
  Classical.byContradiction fun h => hn ⟨v, hv, h⟩

/-- **The storage the trust row protects at a state** (the draft, Trust):
an exposed location that has crossed read-only, and released or outside
storage an incoming read-only crossing protects, recorded in the history. -/
def RowProtects (g : Ghost P) (l : Nat) : Prop := (g.origin l = some .exposed ∧ g.E l) ∨ (g.Lent l ∧ g.Prot l)

/-- **The join of two protocols**, part by part. -/
def Protocol.join (Ψ Θ : Protocol P) : Protocol P := fun p => Change.max (Ψ p) (Θ p)

theorem Change.le_max_left (a b : Change) : a.le (Change.max a b) = true := by
  unfold Change.max Change.le
  split <;> simp_all <;> omega

theorem Change.le_max_right (a b : Change) : b.le (Change.max a b) = true := by
  unfold Change.max Change.le
  split <;> simp_all <;> omega

/-- **The client obligation `Θ` at a step** (the draft, Trust, the row's
client obligation; read-only is `Θ = keep`): the step changes the storage
the row protects within `Θ` at its part. It is trust: a hypothesis on
outside steps. `Θ` is an effect of the same kind as `Ψ_P`. -/
def Row (Θ : Protocol P) (st st' : St P) : Prop :=
  ∀ l v, RowProtects st.g l → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v'

/-- **(M), the clauses an outside step reads**: no local or internal
location is reachable from a frame of code that is not the package's. -/
def MarksOk (st : St P) : Prop :=
  ∀ l, ReachesFrom P.ofC st.s.h st.roots l → st.g.origin l ≠ some .local ∧ st.g.origin l ≠ some .internal

/-- **(P2) Confinement**: an exposed location reachable from a frame of code
that is not the package's has crossed read-only. -/
def Confined (st : St P) : Prop :=
  ∀ l, ReachesFrom P.ofC st.s.h st.roots l → st.g.origin l = some .exposed → st.g.E l

/-- **(M), its storage clause**: storage that references a location of a
local site through a field, a spine or an element cell is itself of a local
site; local storage is held by no other storage. -/
def LocalClosed (st : St P) : Prop :=
  ∀ w u, st.s.h[w]? = some u → ∀ a l, next u a = some l → st.g.origin l = some .local →
    st.g.origin w = some .local

/-- **(M), its clause on a closure's bindings**: no value a closure of
outside code or a bound function held in storage binds (a capture, a node
expression's value, a saved target, receiver or argument) reaches a
location of a local site in its paths' first location step. With
`LocalClosed`, no path from such a binding reaches local storage
(`binding_no_local`). -/
def BindingsClosed (st : St P) : Prop :=
  ∀ (w : Nat) (u : Val), st.s.h[w]? = some u → ∀ x ∈ codeVals P.ofC u, ∀ l, Leaves P.ofC x l →
    st.g.origin l ≠ some .local

/-- **No path from a binding of a closure of outside code reaches local
storage**: every location such a path passes is not local, the first by
`BindingsClosed`, each next one because non-local storage references no
local storage (`LocalClosed`) and its own bindings none (`BindingsClosed`). -/
theorem binding_no_local {st : St P} (hl : LocalClosed st) (hb : BindingsClosed st) {w : Nat} {u x : Val}
    (hu : st.s.h[w]? = some u) (hx : x ∈ codeVals P.ofC u) {l : Nat} (hr : Reaches P.ofC st.s.h x l) :
    st.g.origin l ≠ some .local := by
  have key : ∀ (π : List Label) (v : Val) (l : Nat),
      (∀ l', Leaves P.ofC v l' → st.g.origin l' ≠ some .local) → Follows P.ofC st.s.h v π l →
        st.g.origin l ≠ some .local := by
    intro π
    induction π with
    | nil => intro _ _ _ hf; exact hf.elim
    | cons a π ih =>
      intro v l hv hf
      cases π with
      | nil => exact hv l (Leaves.of_next hf)
      | cons b π =>
        obtain ⟨v₀, hs, hf⟩ := hf
        refine ih v₀ l (fun l' hl' => ?_) hf
        rcases hs with ⟨l₀, hn, hl₀⟩ | ⟨i, rfl, hc⟩
        · have h₀ := hv l₀ (Leaves.of_next hn)
          rcases hl'.cases with ⟨a', hn'⟩ | ⟨y, hy, hly⟩
          · exact fun hloc => h₀ (hl l₀ v₀ hl₀ a' l' hn' hloc)
          · exact hb l₀ v₀ hl₀ y hy l' hly
        · exact hv l' (Leaves.code (List.mem_of_getElem? hc) hl')
  obtain ⟨π, hf⟩ := hr
  exact key π x l (fun l' hl' => hb w u hu x hx l' hl') hf

/-- **The frames' values are valid references** (`RootsOk` of the paper's
model, identities aside): every reference other than an identity that a
value of a frame of code that is not the package's holds has the role its
position demands. No path follows an identity. -/
def RootsValid (st : St P) : Prop := ∀ r ∈ st.roots, RefsOkN st.s.W r

/-- **A step of code that is not the package's**: it keeps the marks and
the ghost history; what it allocates is outside storage; it changes only
storage its frames reach, its frames reach afterwards only storage they
reached or it allocated, and what it leaves in storage it changes or
allocates references only such storage; and it meets the trust row. -/
structure OutsideStep (Θ : Protocol P) (st st' : St P) : Prop where
  kept : Kept st st'
  exposed : st'.g.E = st.g.E
  calls : st'.g.A = st.g.A
  record : st'.g.B = st.g.B
  fresh : ∀ l, st.s.h.length ≤ l → st'.g.site l = none
  reach : ∀ l, Changes st st' l → ReachesFrom P.ofC st.s.h st.roots l
  noForge : ∀ l, ReachesFrom P.ofC st'.s.h st'.roots l → ReachesFrom P.ofC st.s.h st.roots l ∨ st.s.h.length ≤ l
  row : Row Θ st st'
  valid : RootsValid st'
  writes : ∀ (w : Nat) (u : Val), ¬ (∃ v : Val, st.s.h[w]? = some v ∧ st'.s.h[w]? = some v) → st'.s.h[w]? = some u →
    ∀ l, Leaves P.ofC u l → ReachesFrom P.ofC st.s.h st.roots l ∨ st.s.h.length ≤ l

theorem OutsideStep.origin {st st' : St P} {Θ : Protocol P} (ho : OutsideStep Θ st st') (l : Nat) :
    st'.g.origin l = st.g.origin l ∨ st'.g.origin l = none := by
  by_cases hl : l < st.s.h.length
  · exact .inl (ho.kept.origin hl)
  · exact .inr (by simp [Ghost.origin, ho.fresh l (Nat.le_of_not_lt hl)])

/-- **(L1) Outside step**: from a state meeting (M) and (P2), a step of code
that is not the package's changes every location of `R_P` within `Θ`, and
keeps (M) and (P2). A local location is out of its frames' reach (M); an exposed one it
reaches has crossed (P2) and the row protects it; released and outside
storage of `R_P` the row protects. -/
theorem outside_step {st st' : St P} {Θ : Protocol P} (ho : OutsideStep Θ st st') (hm : MarksOk st) (hc : Confined st) :
    (∀ l v, st.g.InR l → st.s.h[l]? = some v →
      ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v') ∧
      MarksOk st' ∧ Confined st' := by
  refine ⟨fun l v hr hv => ?_, fun l hr' => ?_, fun l hr' he => ?_⟩
  · by_cases hch : Changes st st' l
    · have hreach := ho.reach l hch
      rcases hr with h | h | ⟨hL, hp⟩
      · exact ((hm l hreach).1 h).elim
      · exact ho.row l v (.inl ⟨h, hc l hreach h⟩) hv
      · exact ho.row l v (.inr ⟨hL, hp⟩) hv
    · exact ⟨v, unchanged_of hch hv, Change.Holds.refl _ _ _⟩
  · rcases ho.origin l with ho' | ho'
    · rw [ho']
      rcases ho.noForge l hr' with hr | hl
      · exact hm l hr
      · have : st'.g.origin l = none := by simp [Ghost.origin, ho.fresh l hl]
        rw [ho'] at this; simp [this]
    · rw [ho']; simp
  · rcases ho.origin l with ho' | ho'
    · rw [ho'] at he
      rw [ho.exposed]
      rcases ho.noForge l hr' with hr | hl
      · exact hc l hr he
      · have : st'.g.origin l = none := by simp [Ghost.origin, ho.fresh l hl]
        rw [ho'] at this; simp [this] at he
    · rw [ho'] at he; cases he

/-- **An outside step keeps (M)'s storage clause**: what it leaves in
storage it changes or allocates references only what its frames reached,
none of it local (M), or what it allocated, outside storage; every other
location keeps its contents, its references' sites and its own. -/
theorem outside_localClosed {st st' : St P} {Θ : Protocol P} (ho : OutsideStep Θ st st') (hm : MarksOk st)
    (hv : RootsValid st) (hl : LocalClosed st) : LocalClosed st' := by
  intro w u hu a l hn hloc
  by_cases hs : ∃ v, st.s.h[w]? = some v ∧ st'.s.h[w]? = some v
  · obtain ⟨v, hv₀, hv₁⟩ := hs
    rw [hu] at hv₁
    cases hv₁
    have hw : w < st.s.h.length := (List.getElem?_eq_some_iff.mp hv₀).1
    have hl' : l < st.s.h.length := next_lt (RefsOk.refsOkN (contents_valid hw hv₀)) hn
    rw [ho.kept.origin hl'] at hloc
    rw [ho.kept.origin hw]
    exact hl w _ hv₀ a l hn hloc
  · rcases ho.writes w u hs hu l (Leaves.of_next hn) with hr | hf
    · obtain ⟨r, hr', π, hf⟩ := hr
      have hl' : l < st.s.h.length := follows_lt (hv r hr') hf
      rw [ho.kept.origin hl'] at hloc
      exact absurd hloc ((hm l ⟨r, hr', π, hf⟩).1)
    · have : st'.g.origin l = none := by simp [Ghost.origin, ho.fresh l hf]
      rw [this] at hloc; cases hloc

/-- **An outside step keeps (M)'s clause on bindings**: what it leaves in
storage it changes or allocates reaches, in its paths' first location
steps, only what its frames reached, none of it local (M), or what it
allocated; every other location keeps its contents and its references'
sites. -/
theorem outside_bindingsClosed {st st' : St P} {Θ : Protocol P} (ho : OutsideStep Θ st st') (hm : MarksOk st)
    (hv : RootsValid st) (hb : BindingsClosed st) : BindingsClosed st' := by
  intro w u hu x hx l hl hloc
  by_cases hs : ∃ v, st.s.h[w]? = some v ∧ st'.s.h[w]? = some v
  · obtain ⟨v, hv₀, hv₁⟩ := hs
    rw [hu] at hv₁
    cases hv₁
    have hw : w < st.s.h.length := (List.getElem?_eq_some_iff.mp hv₀).1
    have hl' : l < st.s.h.length :=
      Leaves.lt (s := st.s) (codeVals_refsOkN (RefsOk.refsOkN (contents_valid hw hv₀)) hx) hl
    rw [ho.kept.origin hl'] at hloc
    exact hb w _ hv₀ x hx l hl hloc
  · rcases ho.writes w u hs hu l (Leaves.code hx hl) with hr | hf
    · obtain ⟨r, hr', π, hf⟩ := hr
      have hl' : l < st.s.h.length := follows_lt (hv r hr') hf
      rw [ho.kept.origin hl'] at hloc
      exact absurd hloc ((hm l ⟨r, hr', π, hf⟩).1)
    · have : st'.g.origin l = none := by simp [Ghost.origin, ho.fresh l hf]
      rw [this] at hloc; cases hloc

/-! ## Runs of code that is not the package's -/

/-- **The invariants of a state inside a call at depth `d`**: at least `d ≥
1` calls of the package active, a uniform history, (M), (P2), and valid
references in the frames of code that is not the package's. -/
structure Ok (d : Nat) (st : St P) : Prop where
  pos : 0 < d
  len : d ≤ st.g.A.length
  uniform : st.g.Uniform
  marks : MarksOk st
  confined : Confined st
  valid : RootsValid st
  localClosed : LocalClosed st
  bindings : BindingsClosed st

/-- **The invariants of states at any depth**: a uniform history, (M),
(P2), and valid references in the frames of code that is not the package's.
Inside a call they are `Ok` with its depth (`Inv.ok`); outside every call
they are what the next entry needs. -/
structure Inv (st : St P) : Prop where
  uniform : st.g.Uniform
  marks : MarksOk st
  confined : Confined st
  valid : RootsValid st
  localClosed : LocalClosed st
  bindings : BindingsClosed st

theorem Ok.inv {d : Nat} {st : St P} (hok : Ok d st) : Inv st :=
  ⟨hok.uniform, hok.marks, hok.confined, hok.valid, hok.localClosed, hok.bindings⟩

theorem Inv.ok {d : Nat} {st : St P} (hi : Inv st) (hd : 0 < d) (hl : d ≤ st.g.A.length) : Ok d st :=
  ⟨hd, hl, hi.uniform, hi.marks, hi.confined, hi.valid, hi.localClosed, hi.bindings⟩

/-- **The bound a run gives `R_P`** (the draft, (L2)): the marks kept, the
history growing, and every location of `R_P` at the first state changed
within `Ψ_P` at its part. -/
def RBound (Ψ : Protocol P) (d : Nat) (st st' : St P) : Prop :=
  Kept st st' ∧ Grows d st.g st'.g ∧ ∀ l v, st.g.InR l → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Ψ (st.part l)).Holds st.s.h.length v v'

theorem RBound.refl {Ψ : Protocol P} {d : Nat} {st : St P} (hok : Ok d st) : RBound Ψ d st st :=
  ⟨Kept.refl st, Grows.refl hok.pos hok.len, fun _ v _ hv => ⟨v, hv, Change.Holds.refl _ _ _⟩⟩

theorem RBound.trans {Ψ : Protocol P} {d : Nat} {st₁ st₂ st₃ : St P} (h₁ : RBound Ψ d st₁ st₂)
    (h₂ : RBound Ψ d st₂ st₃) : RBound Ψ d st₁ st₃ := by
  refine ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun l v₁ hr hv₁ => ?_⟩
  have hl : l < st₁.s.h.length := (List.getElem?_eq_some_iff.mp hv₁).1
  obtain ⟨v₂, hv₂, hc₁⟩ := h₁.2.2 l v₁ hr hv₁
  have hr₂ : st₂.g.InR l := InR.mono h₁.2.1 (h₁.1.2 l hl).1 hr
  obtain ⟨v₃, hv₃, hc₂⟩ := h₂.2.2 l v₂ hr₂ hv₂
  rw [h₁.1.part hl] at hc₂
  exact ⟨v₃, hv₃, Change.Holds.trans h₁.1.1.length_le hc₁ hc₂⟩

/-- **A bound at a smaller protocol is one at a larger** (`RBound.mono`). -/
theorem RBound.mono {Ψ Ψ' : Protocol P} (hle : ∀ p, (Ψ p).le (Ψ' p) = true) {d : Nat} {st st' : St P}
    (h : RBound Ψ d st st') : RBound Ψ' d st st' :=
  ⟨h.1, h.2.1, fun l v hr hv =>
    let ⟨v', hv', hc⟩ := h.2.2 l v hr hv
    ⟨v', hv', Change.Holds.mono (hle _) hc⟩⟩

theorem Ghost.prot_congr {g g' : Ghost P} (hA : g'.A = g.A) (hB : g'.B = g.B) (l : Nat) :
    g'.Prot l ↔ g.Prot l := by
  simp only [Ghost.Prot, hA, hB]

theorem Ghost.uniform_congr {g g' : Ghost P} (hA : g'.A = g.A) (hB : g'.B = g.B) (hu : g.Uniform) :
    g'.Uniform := by
  intro X hX l
  rw [hA] at hX
  exact (hu X hX l).trans (Ghost.prot_congr hA hB l).symm

/-- **An outside step keeps the invariants at any depth** ((L1) and the
clauses of (M)): its history fields are fixed. -/
theorem outside_inv {st st' : St P} {Θ : Protocol P} (ho : OutsideStep Θ st st') (hi : Inv st) : Inv st' :=
  have h := outside_step ho hi.marks hi.confined
  ⟨Ghost.uniform_congr ho.calls ho.record hi.uniform, h.2.1, h.2.2, ho.valid,
    outside_localClosed ho hi.marks hi.valid hi.localClosed, outside_bindingsClosed ho hi.marks hi.valid hi.bindings⟩

/-- An outside step bounds `R_P` by every protocol `Ψ` with `Θ ⊑ Ψ`
(`Ψ_P ⊔ Θ`), and keeps the invariants. -/
theorem outside_bound {Ψ : Protocol P} {d : Nat} {st st' : St P} {Θ : Protocol P}
    (hΘ : ∀ p, (Θ p).le (Ψ p) = true) (ho : OutsideStep Θ st st') (hok : Ok d st) :
    RBound Ψ d st st' ∧ Ok d st' := by
  obtain ⟨hun, hm, hc⟩ := outside_step ho hok.marks hok.confined
  have hg : Grows d st.g st'.g :=
    ⟨hok.pos, hok.len, by rw [ho.calls]; exact hok.len, ho.record,
      fun l hp => (Ghost.prot_congr ho.calls ho.record l).mpr hp, fun l he => by rw [ho.exposed]; exact he⟩
  exact ⟨⟨ho.kept, hg, fun l v hr hv =>
      let ⟨v', hv', hθ⟩ := hun l v hr hv
      ⟨v', hv', hθ.mono (hΘ _)⟩⟩,
    ⟨hok.pos, hg.len', Ghost.uniform_congr ho.calls ho.record hok.uniform, hm, hc, ho.valid,
      outside_localClosed ho hok.marks hok.valid hok.localClosed,
      outside_bindingsClosed ho hok.marks hok.valid hok.bindings⟩⟩

/-- **A member's certificate** (the draft, "The protocol" and (L4)): a
member's call inside a call at depth `d`, each run of code that is not the
package's it makes inside it, one call deeper, related by `Inner`. Checked with every such run
bounded on `R_P` by `Ψ_P`, its call bounds `R_P` by `Ψ_P` and keeps the
invariants; with every such run keeping an invariant of `G_P`, its call
keeps it. The pass's checks are what establish a certificate. -/
structure Member (P : Package) (Ψ : Protocol P) (G : (St P → Prop) → Prop) where
  Call : Nat → (St P → St P → Prop) → St P → St P → Prop
  bound : ∀ (d : Nat) (Inner : St P → St P → Prop),
    (∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') →
      ∀ st st', Call d Inner st st' → Ok d st → RBound Ψ d st st' ∧ Ok d st'
  keeps : ∀ I, G I → ∀ (d : Nat) (Inner : St P → St P → Prop),
    (∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') →
    (∀ t t', Inner t t' → Ok (d + 1) t → I t → I t') →
      ∀ st st', Call d Inner st st' → Ok d st → I st → I st'

/-- **A run of code that is not the package's inside a call at depth `d`**:
a sequence of outside steps and member calls, each member call's own runs
of code that is not the package's related by `Inner` one call deeper. -/
inductive RunAt (Θ Ψ : Protocol P) (G : (St P → Prop) → Prop) (Inner : Nat → St P → St P → Prop) (d : Nat) :
    St P → St P → Prop
  | nil (st : St P) : RunAt Θ Ψ G Inner d st st
  | outside {st st' st'' : St P} : OutsideStep Θ st st' → RunAt Θ Ψ G Inner d st' st'' → RunAt Θ Ψ G Inner d st st''
  | member {st st' st'' : St P} (m : Member P Ψ G) : m.Call d (Inner (d + 1)) st st' →
      RunAt Θ Ψ G Inner d st' st'' → RunAt Θ Ψ G Inner d st st''

/-- **A run within a budget of nested member calls `k`**. -/
def Run (Θ Ψ : Protocol P) (G : (St P → Prop) → Prop) : Nat → Nat → St P → St P → Prop
  | 0 => RunAt Θ Ψ G fun _ _ _ => False
  | k + 1 => RunAt Θ Ψ G (Run Θ Ψ G k)

theorem RunAt.bound {Θ Ψ : Protocol P} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {G : (St P → Prop) → Prop} {Inner : Nat → St P → St P → Prop}
    (hI : ∀ d t t', Inner d t t' → Ok d t → RBound Ψ d t t' ∧ Ok d t') {d : Nat} {st st' : St P}
    (hr : RunAt Θ Ψ G Inner d st st') (hok : Ok d st) : RBound Ψ d st st' ∧ Ok d st' := by
  induction hr with
  | nil st => exact ⟨RBound.refl hok, hok⟩
  | outside ho _ ih =>
    obtain ⟨b₁, ok₁⟩ := outside_bound hΘ ho hok
    obtain ⟨b₂, ok₂⟩ := ih ok₁
    exact ⟨b₁.trans b₂, ok₂⟩
  | member m hc _ ih =>
    obtain ⟨b₁, ok₁⟩ := m.bound _ _ (fun t t' h ho => hI _ t t' h ho) _ _ hc hok
    obtain ⟨b₂, ok₂⟩ := ih ok₁
    exact ⟨b₁.trans b₂, ok₂⟩

/-- **(L2) Outside run**: a run of code that is not the package's inside a
call of the package, from a state meeting the invariants, changes every
location of `R_P` within `Ψ_P` at its part, keeps each in the region of
every later state, and keeps the invariants. By induction on the budget,
the member calls by their certificates, whose own runs of code that is not
the package's are bounded at a smaller budget. -/
theorem Run.bound {Θ Ψ : Protocol P} {G : (St P → Prop) → Prop} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) :
    ∀ (k d : Nat) (st st' : St P), Run Θ Ψ G k d st st' → Ok d st → RBound Ψ d st st' ∧ Ok d st'
  | 0, _, _, _, hr, hok => RunAt.bound hΘ (fun _ _ _ h _ => h.elim) hr hok
  | k + 1, _, _, _, hr, hok => RunAt.bound hΘ (fun d t t' h ho => Run.bound hΘ k d t t' h ho) hr hok

/-! ## Invariants -/

/-- **An invariant whose support lies in `R_P`, tolerating `Θ`** (the
draft, (L4), `supp(I) ⊆ R_P`): a transition keeping the marks that changes
every location of `R_P` within `Θ` keeps it. -/
def SupportInR (Θ : Protocol P) (I : St P → Prop) : Prop :=
  ∀ st st', I st → Kept st st' → (∀ l v, st.g.InR l → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v') → I st'

/-- **An invariant every outside step keeps**, from a state meeting the
invariants of states at some depth: the premise (L4) reads of outside steps. -/
def OutsideKeeps (Θ : Protocol P) (I : St P → Prop) : Prop :=
  ∀ (d : Nat) (st st' : St P), OutsideStep Θ st st' → Ok d st → I st → I st'

/-- An invariant whose support lies in `R_P` is kept by every outside step
(L1). -/
theorem SupportInR.outside {Θ : Protocol P} {I : St P → Prop} (hs : SupportInR Θ I) : OutsideKeeps Θ I :=
  fun _ _ _ ho hok hi => hs _ _ hi ho.kept (outside_step ho hok.marks hok.confined).1

/-- **The support of an invariant, read at each state** (the Read-only
frames note, Proposition "Read-only reliance", "whose support, read at `s`,
lies in `R_C` and allows `Θ_C`"): `supp st` holds the locations the
invariant reads at `st`. A transition keeping the marks that changes each
of them within `Θ` at its part keeps the invariant (`keeps`) and makes it
read no location it did not read before (`stays`). -/
structure SupportAt (Θ : Protocol P) (I : St P → Prop) (supp : St P → Nat → Prop) : Prop where
  keeps : ∀ st st', I st → Kept st st' → (∀ l v, supp st l → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v') → I st'
  stays : ∀ st st', I st → Kept st st' → (∀ l v, supp st l → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v') → ∀ l, supp st' l → supp st l

/-- **The invariant with its support in `R_P`**: it holds, and every location
its support reads at the state is allocated and in `R_P`. A member keeping it
keeps the invariant and its support in the region, a replacing write among
its steps (the guarantee's check of the members' writes). -/
def InvIn (I : St P → Prop) (supp : St P → Nat → Prop) (st : St P) : Prop :=
  I st ∧ ∀ l, supp st l → l < st.s.h.length ∧ st.g.InR l

/-- **An outside step keeps an invariant whose support lies in `R_P`**,
read at each state: the step changes every location of `R_P` within `Θ`
(L1), so each location the support reads, and the invariant holds after it;
the support then reads only locations it read before, which stay in the
region, the history growing (`InR.mono`). -/
theorem SupportAt.outside {Θ : Protocol P} {I : St P → Prop} {supp : St P → Nat → Prop}
    (hs : SupportAt Θ I supp) : OutsideKeeps Θ (InvIn I supp) := by
  intro d st st' ho hok hi
  have hun := (outside_step ho hok.marks hok.confined).1
  have hb : ∀ l v, supp st l → st.s.h[l]? = some v →
      ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v' :=
    fun l v hl hv => hun l v (hi.2 l hl).2 hv
  have hg : Grows d st.g st'.g :=
    ⟨hok.pos, hok.len, by rw [ho.calls]; exact hok.len, ho.record,
      fun l hp => (Ghost.prot_congr ho.calls ho.record l).mpr hp, fun l he => by rw [ho.exposed]; exact he⟩
  refine ⟨hs.keeps st st' hi.1 ho.kept hb, fun l hl => ?_⟩
  obtain ⟨hlt, hr⟩ := hi.2 l (hs.stays st st' hi.1 ho.kept hb l hl)
  exact ⟨Nat.lt_of_lt_of_le hlt ho.kept.1.length_le, InR.mono hg (ho.kept.2 l hlt).1 hr⟩

theorem RunAt.keeps {Θ Ψ : Protocol P} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {G : (St P → Prop) → Prop}
    {I : St P → Prop} (hG : G I) (hs : OutsideKeeps Θ I) {Inner : Nat → St P → St P → Prop}
    (hIb : ∀ d t t', Inner d t t' → Ok d t → RBound Ψ d t t' ∧ Ok d t')
    (hIk : ∀ d t t', Inner d t t' → Ok d t → I t → I t') {d : Nat} {st st' : St P}
    (hr : RunAt Θ Ψ G Inner d st st') (hok : Ok d st) (hi : I st) : I st' := by
  induction hr with
  | nil st => exact hi
  | outside ho _ ih =>
    exact ih (outside_bound hΘ ho hok).2 (hs _ _ _ ho hok hi)
  | member m hc _ ih =>
    have ok₁ := (m.bound _ _ (fun t t' h ho => hIb _ t t' h ho) _ _ hc hok).2
    exact ih ok₁ (m.keeps I hG _ _ (fun t t' h ho => hIb _ t t' h ho) (fun t t' h ho => hIk _ t t' h ho) _ _ hc hok hi)

/-- **(L4) The handle invariant across a run**: an invariant of `G_P` that
every outside step keeps (one whose support lies in `R_P`,
`SupportInR.outside`, or whose support read at each state does,
`SupportAt.outside`) and that holds where the run starts holds where it
ends. Each member's call keeps it by `G_P`, its runs of code that is not the
package's by the induction. -/
theorem Run.keeps {Θ Ψ : Protocol P} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {G : (St P → Prop) → Prop}
    {I : St P → Prop} (hG : G I) (hs : OutsideKeeps Θ I) :
    ∀ (k d : Nat) (st st' : St P), Run Θ Ψ G k d st st' → Ok d st → I st → I st'
  | 0, _, _, _, hr, hok, hi =>
    RunAt.keeps hΘ hG hs (fun _ _ _ h _ => h.elim) (fun _ _ _ h _ _ => h.elim) hr hok hi
  | k + 1, _, _, _, hr, hok, hi =>
    RunAt.keeps hΘ hG hs (fun d t t' h ho => Run.bound hΘ k d t t' h ho)
      (fun d t t' h ho => Run.keeps hΘ hG hs k d t t' h ho) hr hok hi

/-! ## Ownership -/

/-- **An admitted install** (the draft, (O), *Ownership of installed
storage*): every location the support reads through the installed value is
of an exposed site (a copy made in the call among them) or in `R_P` at the
write. -/
def Admitted (st : St P) (L : Nat → Prop) : Prop := ∀ l, L l → st.g.origin l = some .exposed ∨ st.g.InR l

/-- **(O) Ownership**: the locations an admitted install makes the support
read stay in `R_P` at every later state of the call, each a state reached by
a transition keeping the marks with the history growing. -/
theorem ownership {d : Nat} {st t : St P} {L : Nat → Prop} (ha : Admitted st L)
    (hL : ∀ l, L l → l < st.s.h.length) (hk : Kept st t) (hg : Grows d st.g t.g) : ∀ l, L l → t.g.InR l := by
  intro l hl
  have hr : st.g.InR l := (ha l hl).elim (fun h => .inr (.inl h)) id
  exact InR.mono hg (hk.2 l (hL l hl)).1 hr

/-- **A member's write keeps the invariant's support in `R_P`** (the
guarantee's check at a write, a replacing write among them): where the
invariant holds after the step and every location its support reads
afterwards was read before, is in `R_P` afterwards (a copy of an exposed
site), or was admitted by (O) at the write, its support stays in `R_P`. -/
theorem InvIn.of_step {I : St P → Prop} {supp : St P → Nat → Prop} {d : Nat} {t t' : St P}
    (hi : InvIn I supp t) (hk : Kept t t') (hg : Grows d t.g t'.g) (hI : I t')
    (hnew : ∀ l, supp t' l → l < t'.s.h.length ∧
      (supp t l ∨ t'.g.InR l ∨ (Admitted t (· = l) ∧ l < t.s.h.length))) :
    InvIn I supp t' := by
  refine ⟨hI, fun l hl => ⟨(hnew l hl).1, ?_⟩⟩
  rcases (hnew l hl).2 with hs | hr | ⟨ha, hlt⟩
  · obtain ⟨hlt, hr⟩ := hi.2 l hs
    exact InR.mono hg (hk.2 l hlt).1 hr
  · exact hr
  · exact ownership ha (fun _ h => h ▸ hlt) hk hg l rfl

/-! ## The rule and its consequence -/

/-- **Read-only frame** (the draft, the rule): a call of code that is not
the package's, inside a call at depth `d`, whose run bounds the heap by its
own effect `Φ` (its normal effect at a normal exit, `Φᵉ` at an exceptional
one), is an action of `Φ ⊕_P Ψ_P`, the history growing. -/
theorem readOnly_rule {Θ Ψ : Protocol P} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {G : (St P → Prop) → Prop} {Φ : Footprint} {ρ : Env} {k d : Nat}
    {st st' : St P} (hΦ : TolerantFrames.Action Φ ρ st.s st'.s) (hr : Run Θ Ψ G k d st st') (hok : Ok d st) :
    Leads d Φ Ψ ρ st st' := by
  obtain ⟨⟨hk, hg, hb⟩, -⟩ := Run.bound hΘ k d st st' hr hok
  refine ⟨⟨hk, fun l v hv => ?_⟩, hg⟩
  obtain ⟨v', hv', ha⟩ := hΦ.2.2 l v hv
  refine ⟨v', hv', fun hR => ?_, fun _ => ha⟩
  obtain ⟨v'', hv'', hc⟩ := hb l v hR hv
  rw [hv'] at hv''
  cases hv''
  exact hc

/-- **The domain of the rule's states**: a state's heap, and the
transitions keeping the marks. -/
def states (P : Package) : SupportDomain (St P) := ⟨fun st => st.s.h, Kept⟩

/-- **The premise of Proposition "Read-only reliance"** (the Read-only
frames note), location by location: each allocated location `l` of each
region `(r : δ)` of the support, read at the state, meets
`Ψ(part(l)) ⊑ δ` if `l ∈ R_P`, and `γ ⊑ δ` for each entry `(r' : γ)` of
`Φ` with `l ∈ r'` otherwise. `Ψ` is the protocol the rule bounds `R_P` by,
`Ψ_P ⊔ Θ_P`. -/
def Framed (Φ : Footprint) (Ψ : Protocol P) (S : Footprint) (ρ : Env) (st : St P) : Prop :=
  ∀ e ∈ S, ∀ l, l < st.s.h.length → e.1.mem ρ st.s.h l = true →
    (st.g.InR l → (Ψ (st.part l)).le e.2 = true) ∧
      (¬ st.g.InR l → ∀ f ∈ Φ, f.1.mem ρ st.s.h l = true → f.2.le e.2 = true)

/-- **An action of `Φ ⊕_P Ψ` meets every support the premise holds of**:
a location of `R_P` changes within `Ψ` at its part, within the region's
change; any other within an entry of `Φ` covering it, within the region's
change, or not at all. -/
theorem supported_of_framed {Φ : Footprint} {Ψ : Protocol P} {S : Footprint} {ρ : Env} {st st' : St P}
    (hf : Framed Φ Ψ S ρ st) (ha : OAction Φ Ψ ρ st st') : Supported S ρ st.s.h st'.s.h := by
  intro e he l v hm hv
  have hl : l < st.s.h.length := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨hin, hout⟩ := hf e he l hl hm
  obtain ⟨v', hv', hb⟩ := ha.2 l v hv
  refine ⟨v', hv', ?_⟩
  by_cases hr : st.g.InR l
  · exact (hb.1 hr).mono (hin hr)
  · rcases hb.2 hr with rfl | ⟨f, hfΦ, hfm, hh⟩
    · exact Change.Holds.refl _ _ _
    · exact hh.mono (hout hr f hfΦ hfm)

/-- **The tolerant frame at `Φ ⊕_P Ψ`** (the Tolerant frames note, Theorem
"Tolerant frame", `frame_step`, at this action): an assertion holds after
every action of `Φ ⊕_P Ψ` meeting its support's condition, its support
meeting the premise location by location. -/
theorem readOnly_frame {Φ : Footprint} {Ψ : Protocol P} {C : ConditionOn (St P)} {A : AssertionOn (St P)}
    {S : Footprint} (hs : (states P).Supports C A S) {ρ : Env} {m : Nat} {st st' : St P}
    (hf : Framed Φ Ψ S ρ st) (ha : OAction Φ Ψ ρ st st') (hc : C ρ m st st') (hA : A ρ m st) : A ρ m st' :=
  hs ρ m st st' ha.1 hc hA (supported_of_framed hf ha)

/-- **Read-only reliance, the bound route** (the Read-only frames note,
Proposition "Read-only reliance"; the Tolerant frames note, Proposition
"Reliance"): a call of code that is not the package's, inside a call of the
package at depth `d`, from a state meeting the invariants, whose run bounds
the heap by its own effect `Φ`, keeps every fact whose support meets the
premise location by location, at `Ψ = Ψ_P ⊔ Θ_P`. -/
theorem readOnly_rely {Θ Ψ : Protocol P} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {G : (St P → Prop) → Prop}
    {C : ConditionOn (St P)} {A : AssertionOn (St P)} {Φ S : Footprint} (hs : (states P).Supports C A S)
    {ρ : Env} {m k d : Nat} {st st' : St P} (hΦ : TolerantFrames.Action Φ ρ st.s st'.s)
    (hr : Run Θ Ψ G k d st st') (hok : Ok d st) (hf : Framed Φ Ψ S ρ st) (hc : C ρ m st st')
    (hA : A ρ m st) : A ρ m st' :=
  readOnly_frame hs hf (readOnly_rule hΘ hΦ hr hok).1 hc hA

/-- **Read-only reliance, the guarantee route** (the Read-only frames note,
Proposition "Read-only reliance"): an invariant of `G_P`, held with its
support in `R_P` (`InvIn`, the members' guarantee), whose support read at
each state allows `Θ` (`SupportAt`), holds after such a run. -/
theorem readOnly_guarantee {Θ Ψ : Protocol P} (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {G : (St P → Prop) → Prop}
    {I : St P → Prop} {supp : St P → Nat → Prop} (hG : G (InvIn I supp)) (hs : SupportAt Θ I supp)
    {k d : Nat} {st st' : St P} (hr : Run Θ Ψ G k d st st') (hok : Ok d st) (hi : InvIn I supp st) :
    I st' :=
  (Run.keeps hΘ hG hs.outside k d st st' hr hok hi).1

end Verification.TolerantFrames.ReadOnly
