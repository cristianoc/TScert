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
- (L4) `Run.keeps`: an invariant of `G_P` whose support lies in `R_P`
  survives such a run.
- (O) `ownership`: storage an admitted install makes the support read stays
  in `R_P` for the rest of the call.
- The rule (`readOnly_rule`) and its consequence (`readOnly_rely`): a fact
  supported inside `R_P` at the parts' changes holds after the run, by the
  definition of support the tolerant frame (`frame_step`) reads.

The trust row is a hypothesis on outside steps (`OutsideStep.row`), as are
two properties of the language's steps the model does not state: a step
changes only storage its frames reach (`OutsideStep.reach`), and reaches
afterwards only storage it reached or allocated (`OutsideStep.noForge`). A
member's certificate (`Member`) is a hypothesis: the pass's checks are what
establish it. -/
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
kind of Paper I's world and, for a field location, its key. -/
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

/-- **The trust row `T_P` at a step**: the step changes no storage the row
protects. It is trust: a hypothesis on outside steps. -/
def Row (st st' : St P) : Prop := ∀ l, RowProtects st.g l → ¬ Changes st st' l

/-- **(M), the clauses an outside step reads**: no local or internal
location is reachable from a frame of code that is not the package's. -/
def MarksOk (st : St P) : Prop :=
  ∀ l, ReachesFrom st.s.h st.roots l → st.g.origin l ≠ some .local ∧ st.g.origin l ≠ some .internal

/-- **(P2) Confinement**: an exposed location reachable from a frame of code
that is not the package's has crossed read-only. -/
def Confined (st : St P) : Prop :=
  ∀ l, ReachesFrom st.s.h st.roots l → st.g.origin l = some .exposed → st.g.E l

/-- **A step of code that is not the package's**: it keeps the marks and
the ghost history; what it allocates is outside storage; it changes only
storage its frames reach, and its frames reach afterwards only storage they
reached or it allocated; and it meets the trust row. -/
structure OutsideStep (st st' : St P) : Prop where
  kept : Kept st st'
  exposed : st'.g.E = st.g.E
  calls : st'.g.A = st.g.A
  record : st'.g.B = st.g.B
  fresh : ∀ l, st.s.h.length ≤ l → st'.g.site l = none
  reach : ∀ l, Changes st st' l → ReachesFrom st.s.h st.roots l
  noForge : ∀ l, ReachesFrom st'.s.h st'.roots l → ReachesFrom st.s.h st.roots l ∨ st.s.h.length ≤ l
  row : Row st st'

theorem OutsideStep.origin {st st' : St P} (ho : OutsideStep st st') (l : Nat) :
    st'.g.origin l = st.g.origin l ∨ st'.g.origin l = none := by
  by_cases hl : l < st.s.h.length
  · exact .inl (ho.kept.origin hl)
  · exact .inr (by simp [Ghost.origin, ho.fresh l (Nat.le_of_not_lt hl)])

/-- **(L1) Outside step**: from a state meeting (M) and (P2), a step of code
that is not the package's changes no location of `R_P`, and keeps (M) and
(P2). A local location is out of its frames' reach (M); an exposed one it
reaches has crossed (P2) and the row protects it; released and outside
storage of `R_P` the row protects. -/
theorem outside_step {st st' : St P} (ho : OutsideStep st st') (hm : MarksOk st) (hc : Confined st) :
    (∀ l, st.g.InR l → ¬ Changes st st' l) ∧ MarksOk st' ∧ Confined st' := by
  refine ⟨fun l hr hch => ?_, fun l hr' => ?_, fun l hr' he => ?_⟩
  · have hreach := ho.reach l hch
    rcases hr with h | h | ⟨hL, hp⟩
    · exact (hm l hreach).1 h
    · exact ho.row l (.inl ⟨h, hc l hreach h⟩) hch
    · exact ho.row l (.inr ⟨hL, hp⟩) hch
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

/-! ## Runs of code that is not the package's -/

/-- **The invariants of a state inside a call at depth `d`**: at least `d ≥
1` calls of the package active, a uniform history, (M) and (P2). -/
structure Ok (d : Nat) (st : St P) : Prop where
  pos : 0 < d
  len : d ≤ st.g.A.length
  uniform : st.g.Uniform
  marks : MarksOk st
  confined : Confined st

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

theorem Ghost.prot_congr {g g' : Ghost P} (hA : g'.A = g.A) (hB : g'.B = g.B) (l : Nat) :
    g'.Prot l ↔ g.Prot l := by
  simp only [Ghost.Prot, hA, hB]

theorem Ghost.uniform_congr {g g' : Ghost P} (hA : g'.A = g.A) (hB : g'.B = g.B) (hu : g.Uniform) :
    g'.Uniform := by
  intro X hX l
  rw [hA] at hX
  exact (hu X hX l).trans (Ghost.prot_congr hA hB l).symm

/-- An outside step bounds `R_P` by `Ψ_P` (it changes none of it) and keeps
the invariants. -/
theorem outside_bound {Ψ : Protocol P} {d : Nat} {st st' : St P} (ho : OutsideStep st st') (hok : Ok d st) :
    RBound Ψ d st st' ∧ Ok d st' := by
  obtain ⟨hun, hm, hc⟩ := outside_step ho hok.marks hok.confined
  have hg : Grows d st.g st'.g :=
    ⟨hok.pos, hok.len, by rw [ho.calls]; exact hok.len, ho.record,
      fun l hp => (Ghost.prot_congr ho.calls ho.record l).mpr hp, fun l he => by rw [ho.exposed]; exact he⟩
  exact ⟨⟨ho.kept, hg, fun l v hr hv => ⟨v, unchanged_of (hun l hr) hv, Change.Holds.refl _ _ _⟩⟩,
    ⟨hok.pos, hg.len', Ghost.uniform_congr ho.calls ho.record hok.uniform, hm, hc⟩⟩

/-- **A member's certificate** (the draft, "The protocol" and (L4)): a
member's call, each run of code that is not the package's it makes inside
it, one call deeper, related by `Inner`. Checked with every such run
bounded on `R_P` by `Ψ_P`, its call bounds `R_P` by `Ψ_P` and keeps the
invariants; with every such run keeping an invariant of `G_P`, its call
keeps it. The pass's checks are what establish a certificate. -/
structure Member (P : Package) (Ψ : Protocol P) (G : (St P → Prop) → Prop) where
  Call : (St P → St P → Prop) → St P → St P → Prop
  bound : ∀ (d : Nat) (Inner : St P → St P → Prop),
    (∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') →
      ∀ st st', Call Inner st st' → Ok d st → RBound Ψ d st st' ∧ Ok d st'
  keeps : ∀ I, G I → ∀ (d : Nat) (Inner : St P → St P → Prop),
    (∀ t t', Inner t t' → Ok (d + 1) t → I t → I t') →
      ∀ st st', Call Inner st st' → Ok d st → I st → I st'

/-- **A run of code that is not the package's inside a call at depth `d`**:
a sequence of outside steps and member calls, each member call's own runs
of code that is not the package's related by `Inner` one call deeper. -/
inductive RunAt (Ψ : Protocol P) (G : (St P → Prop) → Prop) (Inner : Nat → St P → St P → Prop) (d : Nat) :
    St P → St P → Prop
  | nil (st : St P) : RunAt Ψ G Inner d st st
  | outside {st st' st'' : St P} : OutsideStep st st' → RunAt Ψ G Inner d st' st'' → RunAt Ψ G Inner d st st''
  | member {st st' st'' : St P} (m : Member P Ψ G) : m.Call (Inner (d + 1)) st st' →
      RunAt Ψ G Inner d st' st'' → RunAt Ψ G Inner d st st''

/-- **A run within a budget of nested member calls `k`**. -/
def Run (Ψ : Protocol P) (G : (St P → Prop) → Prop) : Nat → Nat → St P → St P → Prop
  | 0 => RunAt Ψ G fun _ _ _ => False
  | k + 1 => RunAt Ψ G (Run Ψ G k)

theorem RunAt.bound {Ψ : Protocol P} {G : (St P → Prop) → Prop} {Inner : Nat → St P → St P → Prop}
    (hI : ∀ d t t', Inner d t t' → Ok d t → RBound Ψ d t t' ∧ Ok d t') {d : Nat} {st st' : St P}
    (hr : RunAt Ψ G Inner d st st') (hok : Ok d st) : RBound Ψ d st st' ∧ Ok d st' := by
  induction hr with
  | nil st => exact ⟨RBound.refl hok, hok⟩
  | outside ho _ ih =>
    obtain ⟨b₁, ok₁⟩ := outside_bound ho hok
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
theorem Run.bound {Ψ : Protocol P} {G : (St P → Prop) → Prop} :
    ∀ (k d : Nat) (st st' : St P), Run Ψ G k d st st' → Ok d st → RBound Ψ d st st' ∧ Ok d st'
  | 0, _, _, _, hr, hok => RunAt.bound (fun _ _ _ h _ => h.elim) hr hok
  | k + 1, _, _, _, hr, hok => RunAt.bound (fun d t t' h ho => Run.bound k d t t' h ho) hr hok

/-! ## Invariants -/

/-- **An invariant whose support lies in `R_P`** (the draft, (L4),
`supp(I) ⊆ R_P`): a transition keeping the marks that changes no location
of `R_P` keeps it. -/
def SupportInR (I : St P → Prop) : Prop :=
  ∀ st st', I st → Kept st st' → (∀ l, st.g.InR l → ¬ Changes st st' l) → I st'

theorem RunAt.keeps {Ψ : Protocol P} {G : (St P → Prop) → Prop} {I : St P → Prop} (hG : G I)
    (hs : SupportInR I) {Inner : Nat → St P → St P → Prop}
    (hIb : ∀ d t t', Inner d t t' → Ok d t → RBound Ψ d t t' ∧ Ok d t')
    (hIk : ∀ d t t', Inner d t t' → Ok d t → I t → I t') {d : Nat} {st st' : St P}
    (hr : RunAt Ψ G Inner d st st') (hok : Ok d st) (hi : I st) : I st' := by
  induction hr with
  | nil st => exact hi
  | outside ho _ ih =>
    have hun := (outside_step ho hok.marks hok.confined).1
    exact ih (outside_bound (Ψ := Ψ) ho hok).2 (hs _ _ hi ho.kept hun)
  | member m hc _ ih =>
    have ok₁ := (m.bound _ _ (fun t t' h ho => hIb _ t t' h ho) _ _ hc hok).2
    exact ih ok₁ (m.keeps I hG _ _ (fun t t' h ho => hIk _ t t' h ho) _ _ hc hok hi)

/-- **(L4) The handle invariant across a run**: an invariant of `G_P` whose
support lies in `R_P` and that holds where the run starts holds where it
ends. Each member's call keeps it by `G_P`, its runs of code that is not
the package's by the induction, and every outside step changes no location
of its support (L1). -/
theorem Run.keeps {Ψ : Protocol P} {G : (St P → Prop) → Prop} {I : St P → Prop} (hG : G I)
    (hs : SupportInR I) :
    ∀ (k d : Nat) (st st' : St P), Run Ψ G k d st st' → Ok d st → I st → I st'
  | 0, _, _, _, hr, hok, hi => RunAt.keeps hG hs (fun _ _ _ h _ => h.elim) (fun _ _ _ h _ _ => h.elim) hr hok hi
  | k + 1, _, _, _, hr, hok, hi =>
    RunAt.keeps hG hs (fun d t t' h ho => Run.bound k d t t' h ho) (fun d t t' h ho => Run.keeps hG hs k d t t' h ho)
      hr hok hi

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

/-! ## The rule and its consequence -/

/-- **Read-only frame** (the draft, the rule): a call of code that is not
the package's, inside a call at depth `d`, whose run bounds the heap by its
own effect `Φ` (its normal effect at a normal exit, `Φᵉ` at an exceptional
one), is an action of `Φ ⊕_P Ψ_P`, the history growing. -/
theorem readOnly_rule {Ψ : Protocol P} {G : (St P → Prop) → Prop} {Φ : Footprint} {ρ : Env} {k d : Nat}
    {st st' : St P} (hΦ : TolerantFrames.Action Φ ρ st.s st'.s) (hr : Run Ψ G k d st st') (hok : Ok d st) :
    Leads d Φ Ψ ρ st st' := by
  obtain ⟨⟨hk, hg, hb⟩, -⟩ := Run.bound k d st st' hr hok
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

/-- **The frame's premise** (the draft, "At a callback"): each location a
support region reads at the state is in `R_P`, and `Ψ_P`'s change at its
part is within the region's (`Ψ_P ◁ S` on `R_P`). -/
def Inside (Ψ : Protocol P) (S : Footprint) (ρ : Env) (st : St P) : Prop :=
  ∀ e ∈ S, ∀ l, e.1.mem ρ st.s.h l = true → st.g.InR l ∧ (Ψ (st.part l)).le e.2 = true

/-- A transition bounding `R_P` by `Ψ_P` meets every support inside `R_P`. -/
theorem supported_of_inside {Ψ : Protocol P} {S : Footprint} {ρ : Env} {st st' : St P}
    (hi : Inside Ψ S ρ st)
    (hb : ∀ l v, st.g.InR l → st.s.h[l]? = some v →
      ∃ v', st'.s.h[l]? = some v' ∧ (Ψ (st.part l)).Holds st.s.h.length v v') :
    Supported S ρ st.s.h st'.s.h := by
  intro e he l v hm hv
  obtain ⟨hr, hle⟩ := hi e he l hm
  obtain ⟨v', hv', hc⟩ := hb l v hr hv
  exact ⟨v', hv', hc.mono hle⟩

/-- **The tolerant frame at `Φ ⊕_P Ψ_P`** (Paper I, Theorem "Tolerant
frame", `frame_step`, at this action): an assertion with a support inside
`R_P` holds after every action of `Φ ⊕_P Ψ_P` meeting the support's
condition, whatever `Φ`. -/
theorem readOnly_frame {Φ : Footprint} {Ψ : Protocol P} {C : ConditionOn (St P)} {A : AssertionOn (St P)}
    {S : Footprint} (hs : (states P).Supports C A S) {ρ : Env} {m : Nat} {st st' : St P}
    (hi : Inside Ψ S ρ st) (ha : OAction Φ Ψ ρ st st') (hc : C ρ m st st') (hA : A ρ m st) : A ρ m st' :=
  hs ρ m st st' ha.1 hc hA (supported_of_inside hi fun l v hr hv => by
    obtain ⟨v', hv', hb⟩ := ha.2 l v hv
    exact ⟨v', hv', hb.1 hr⟩)

/-- **The rule's consequence** (the draft, "The consequence"; Paper I,
Proposition "Reliance"): a fact whose support lies inside `R_P`, with
`Ψ_P ◁ S`, holds after every run of code that is not the package's inside a
call of the package, from a state meeting the invariants. -/
theorem readOnly_rely {Ψ : Protocol P} {G : (St P → Prop) → Prop} {C : ConditionOn (St P)}
    {A : AssertionOn (St P)} {S : Footprint} (hs : (states P).Supports C A S) {ρ : Env} {m k d : Nat}
    {st st' : St P} (hr : Run Ψ G k d st st') (hok : Ok d st) (hi : Inside Ψ S ρ st) (hc : C ρ m st st')
    (hA : A ρ m st) : A ρ m st' := by
  obtain ⟨⟨hk, -, hb⟩, -⟩ := Run.bound k d st st' hr hok
  exact hs ρ m st st' hk hc hA (supported_of_inside hi hb)

end Verification.TolerantFrames.ReadOnly
