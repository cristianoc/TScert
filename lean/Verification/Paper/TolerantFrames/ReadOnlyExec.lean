import Verification.Paper.TolerantFrames.ReadOnlyOutside

/-! # Read-only handles: actual executions as runs of outside code

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "What the
Lean states", "Actual executions"), over the paper model's reduction
(`Step`), at a component `C` of a family read as a package (`F.at C`).

- **A configuration** (`Conf`) is an indexed heap and a term valid at its
  world; an actual step (`AStep`) is a step of the calculus between their
  heaps whose world transition is admissible.
- **The lifted state** of a configuration with a ghost (`lift`) has as its
  roots the values at the positions of the term's frames that run no code
  of `C` (`rootsOf`), the hypothesis "a state's roots are its term's
  roots" holding by definition.
- **An outside step** (`outsideStep_of_step`): an actual step whose active
  frame runs no code of `C`, with the ghost the step's allocation extends
  (`Ghost.alloc`), meets `OutsideStep` given the client obligation `Row`
  alone: its marks are kept, its history fields fixed and what it
  allocates is outside storage by the construction of the ghost, and
  `reach`, `writes`, `noForge` and `valid` are the calculus's
  (`outsideStep_reach`, `outsideStep_writes`, `outsideStep_noForge`,
  `rootsValid_of_term`).
- **The history of an execution** (`Ghost.next`): the call structure is
  read from the number of blocks of `C`'s frames on the evaluation path
  (`depthC`). An entry pushes the protected set, then the incoming values
  cross; an exit, normal or exceptional, lets the outgoing values cross,
  then pops, `B` keeping the popped set's locations `C`'s frames,
  bindings and storage hold (`Held`). No other transition adds to the
  protected set.
- **The decomposition** (`run_of_exec`): an actual execution inside a
  call of `C` at depth `d`, every step obeying the call discipline (`Disc`),
  is a run of code that is not `C`'s (`Run`): its outside steps are
  `OutsideStep`s, and each call of `C` from outside code is a call of the
  member certified for the code it enters (`Cert.member`), whose steps are
  checked steps (`PkgStep`) and whose runs of outside code one call deeper
  are again such runs. Then (L2) holds of the execution
  (`exec_bound`).
- **The invariants at every depth** (`XStep.inv`, `Ex.inv`): every step of
  an execution keeps the invariants of states (`Inv`), a return to code
  outside every call of `C` included, so from a start meeting them
  (`Inv.of_lent`) each state inside a call is `Ok` at its depth, the entry
  conditions of every call. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-! ## Configurations and their lifted states -/

/-- **A configuration**: an indexed heap and a term valid at its world. -/
structure Conf where
  s : IndexedHeap
  t : Tm
  ok : RefsOk s.W t

/-- **An actual step**: a step of the calculus between the configurations'
heaps, whose world transition is admissible (what a safe execution's step
gives, `SafePostW`). -/
structure AStep (x y : Conf) : Prop where
  step : Step x.s.h x.t y.s.h y.t
  adm : Admissible x.s y.s

variable {F : Family} {C : Nat} {c : ComponentTag}

/-- **The roots of outside code at a term**: the values at the positions
of the frames that run no code of `C`, the top segment's run by `c`. -/
noncomputable def rootsOf (F : Family) (C : Nat) (c : ComponentTag) (t : Tm) : List Val :=
  vals (F.ofC C) F.realm (!F.ofC C c) false t

/-- **The lifted state** of a configuration with a ghost: its roots are its
term's. -/
noncomputable def lift (F : Family) (C : Nat) (c : ComponentTag) (x : Conf) (g : Ghost (F.at C)) : St (F.at C) :=
  ⟨x.s, g, rootsOf F C c x.t⟩

/-- **A term whose active frame runs no code of `C`.** -/
def OutsideAt (F : Family) (C : Nat) (c : ComponentTag) (t : Tm) : Prop := ¬ F.Runs (activeTag F.realm c false t) C

/-- **A step whose active frame runs no code of `C`.** -/
def Outside (F : Family) (C : Nat) (c : ComponentTag) (x : Conf) : Prop := OutsideAt F C c x.t

/-! ## The ghost a step's allocation extends -/

namespace Ghost
variable {P : Package}

/-- **The ghost after an allocation**: every location below `n`, the old
heap's length, keeps its site; a location at or above `n` takes the site
given. -/
def alloc (g : Ghost P) (n : Nat) (site : Nat → Option P.Site) : Ghost P :=
  { g with site := fun l => if l < n then g.site l else site l }

@[simp] theorem alloc_A {g : Ghost P} {n : Nat} {site : Nat → Option P.Site} :
    (g.alloc n site).A = g.A := rfl

theorem alloc_old {g : Ghost P} {n : Nat} {site : Nat → Option P.Site} {l : Nat}
    (hl : l < n) : (g.alloc n site).site l = g.site l := by
  simp [alloc, hl]

end Ghost

/-! ## An actual outside step -/

/-- **An actual step of outside code is an outside step** (the draft,
"Actual executions"): its marks are kept and its history fields fixed by
the ghost's construction, what it allocates is outside storage, its world
transition is the execution's, and `reach`, `writes`, `noForge` and
`valid` are the calculus's. The client obligation `Row` is the one
hypothesis. -/
theorem outsideStep_of_step {Θ : Protocol (F.at C)} {x y : Conf} {g : Ghost (F.at C)}
    (hs : AStep x y) (hact : Outside F C c x)
    (hrow : Row Θ (lift F C c x g) (lift F C c y (g.alloc x.s.h.length (fun _ => none)))) :
    OutsideStep Θ (lift F C c x g) (lift F C c y (g.alloc x.s.h.length (fun _ => none))) where
  kept := ⟨hs.adm, fun _ hl => Ghost.alloc_old hl⟩
  exposed := rfl
  calls := rfl
  record := rfl
  fresh := fun l hl => by
    change x.s.h.length ≤ l at hl
    simp [lift, Ghost.alloc, Nat.not_lt.mpr hl]
  reach := outsideStep_reach hs.step hact rfl
  noForge := outsideStep_noForge hs.step hact rfl rfl
  row := hrow
  valid := rootsValid_of_term (P := F.at C) (st := lift F C c y _) rfl y.ok
  writes := outsideStep_writes hs.step hact rfl

/-! ## The call structure -/

/-- **The blocks of a list**: its maximal runs of `true`, each counted at
its last element. -/
def blocks : List Bool → Nat
  | [] => 0
  | b :: bs => (if b && !(bs.head?.getD false) then 1 else 0) + blocks bs

/-- **The calls of `C` active at a term**: the blocks of frames running
`C`'s code on its evaluation path, the top segment's among them. A call of
a closure of `C` from outside code adds one; a return or a throw out of the
last frame of `C`'s innermost block removes it. -/
noncomputable def depthC (F : Family) (C : Nat) (c : ComponentTag) (t : Tm) : Nat :=
  blocks ((path F.realm c false t).map fun p => F.ofC C p.1)

/-- **A family whose realm has no tag reads its calls with no realm**
(proved, `path_noRealm`). -/
theorem depthC_noRealm (hrn : ∀ t, F.realm.tags t = false) (t : Tm) :
    depthC F C c t = blocks ((path Realm.empty c false t).map fun p => F.ofC C p.1) := by
  unfold depthC; rw [path_noRealm hrn]

/-- A family whose realm has no tag reads its active frame with no realm
(proved, `path_noRealm`). -/
theorem outsideAt_noRealm (hrn : ∀ t, F.realm.tags t = false) (t : Tm) :
    OutsideAt F C c t ↔ ¬ F.Runs (activeTag Realm.empty c false t) C := by
  unfold OutsideAt activeTag; rw [path_noRealm hrn]

/-- **The call discipline of a step** (hypothesis): a step whose active
frame runs no code of `C` keeps the calls of `C` active or enters one; a
step of `C`'s code keeps them or leaves one. -/
def Disc (F : Family) (C : Nat) (c : ComponentTag) (x y : Conf) : Prop :=
  (Outside F C c x → depthC F C c x.t ≤ depthC F C c y.t ∧ depthC F C c y.t ≤ depthC F C c x.t + 1) ∧
  (¬ Outside F C c x → depthC F C c y.t ≤ depthC F C c x.t ∧ depthC F C c x.t ≤ depthC F C c y.t + 1)

/-- **The kind of a step**: a step of outside code, the entry of a call of
`C`, a step inside one, or its exit. -/
inductive Kind where
  | outside
  | enter
  | body
  | exit
  deriving DecidableEq

open Classical in
/-- The kind of a step from the term `t` to `t'`, read from its active frame
and the calls of `C` active before and after it. -/
noncomputable def stepKind (F : Family) (C : Nat) (c : ComponentTag) (t t' : Tm) : Kind :=
  if OutsideAt F C c t ∧ depthC F C c t' = depthC F C c t then .outside
  else if depthC F C c t < depthC F C c t' then .enter
  else if depthC F C c t' < depthC F C c t then .exit
  else .body

/-- The kind of a step between configurations: its terms'. -/
noncomputable def kind (F : Family) (C : Nat) (c : ComponentTag) (x y : Conf) : Kind := stepKind F C c x.t y.t

theorem stepKind_conf {F : Family} {C : Nat} {c : ComponentTag} {x y : Conf} :
    stepKind F C c x.t y.t = kind F C c x y := rfl

/-! ## The history of an execution -/

namespace Ghost
variable {P : Package}

/-- **An entry**: the protected set pushed. -/
def enter (g : Ghost P) : Ghost P := { g with A := g.A ++ [g.Prot] }

/-- **A sequence of crossings** at the heap `h`, in order. -/
def crosses (tv : TypeView) (h : Heap) : List (Crossing tv) → Ghost P → Ghost P
  | [], g => g
  | x :: xs, g => crosses tv h xs (g.cross tv x.dir x.ty h x.val)

/-- **An exit**, normal or exceptional: the top set popped, `B` the popped
set's locations `held` holds when no call stays active. -/
def pop (held : Nat → Prop) (g : Ghost P) : Ghost P :=
  { g with A := g.A.dropLast, B := exitRecord g g.A.dropLast (g.A.getLastD fun _ => False) held }

theorem crosses_site {tv : TypeView} {h : Heap} :
    ∀ (xs : List (Crossing tv)) (g : Ghost P), (crosses tv h xs g).site = g.site
  | [], _ => rfl
  | _ :: xs, _ => crosses_site xs _

theorem crosses_len {tv : TypeView} {h : Heap} :
    ∀ (xs : List (Crossing tv)) (g : Ghost P), (crosses tv h xs g).A.length = g.A.length
  | [], _ => rfl
  | _ :: xs, g => (crosses_len xs _).trans (by simp [Ghost.cross, Ghost.add])

theorem crosses_E {tv : TypeView} {h : Heap} :
    ∀ (xs : List (Crossing tv)) (g : Ghost P) {l : Nat}, g.E l → (crosses tv h xs g).E l
  | [], _, _, he => he
  | _ :: xs, _, _, he => crosses_E xs _ (.inl he)

/-- **The crossings update `E`**: every exposed location a crossing reaches
read-only at the heap is in `E` after them. -/
theorem crosses_covers {tv : TypeView} {h : Heap} :
    ∀ (xs : List (Crossing tv)) (g : Ghost P), ∀ x ∈ xs, ∀ l, ReachRO tv P.ofC x.ty h x.val l →
      g.origin l = some .exposed → (crosses tv h xs g).E l
  | [], _, _, hx, _, _, _ => by cases hx
  | y :: xs, g, x, hx, l, hr, he => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact crosses_E xs _ (.inr ⟨hr, he⟩)
    · exact crosses_covers xs _ x hx l hr he

theorem crosses_hsteps {tv : TypeView} {d : Nat} {h : Heap} :
    ∀ (xs : List (Crossing tv)) (g : Ghost P), d ≤ g.A.length → HSteps tv d g (crosses tv h xs g)
  | [], g, _ => .refl g
  | x :: xs, g, hd =>
    have hl : d ≤ (g.cross tv x.dir x.ty h x.val).A.length := by simpa [Ghost.cross, Ghost.add] using hd
    .step h (.cross g x.dir x.ty x.val) hl (crosses_hsteps xs _ hl)

theorem pop_hstep {tv : TypeView} {h : Heap} {held : Nat → Prop} {g : Ghost P} (hA : g.A ≠ []) :
    HStep tv h g (g.pop held) := by
  have he : g.A = g.A.dropLast ++ [g.A.getLastD fun _ => False] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hA]
    exact (List.dropLast_concat_getLast hA).symm
  exact .exit g .normal held _ _ he

end Ghost

theorem HSteps.trans {P : Package} {tv : TypeView} {d : Nat} {g₁ g₂ g₃ : Ghost P} (h₁ : HSteps tv d g₁ g₂)
    (h₂ : HSteps tv d g₂ g₃) : HSteps tv d g₁ g₃ := by
  induction h₁ with
  | refl => exact h₂
  | step h hs hl _ ih => exact .step h hs hl (ih h₂)

/-- **What `C` holds at a configuration** (the draft, Holds): a location
reachable from a value at a position of `C`'s code, a closure of `C`'s
bindings among them, or from storage a site of `C` allocated. -/
def HeldAt (F : Family) (C : Nat) (c : ComponentTag) (h : Heap) (t : Tm) (g : Ghost (F.at C)) (l : Nat) : Prop :=
  ReachesFrom (fun t => !F.ofC C t) h (vals (fun t => !F.ofC C t) F.realm (F.ofC C c) false t) l ∨
    ∃ w u, (g.site w).isSome ∧ h[w]? = some u ∧ Leaves (fun t => !F.ofC C t) u l

/-- What `C` holds at a configuration: at its heap and term. -/
def Held (F : Family) (C : Nat) (c : ComponentTag) (y : Conf) (g : Ghost (F.at C)) (l : Nat) : Prop :=
  HeldAt F C c y.s.h y.t g l

/-- **What the checks give at a step of `C`'s code** (the interface of the
checks (S), (K) and (O)): the sites of the locations it allocates
and its crossings, in order. -/
structure CheckData (P : Package) (tv : TypeView) where
  site : Nat → Option P.Site
  xs : List (Crossing tv)

variable {tv : TypeView}

/-- The ghost after a step's allocation, before its history transitions. -/
noncomputable def midOf (chk : Conf → Conf → CheckData (F.at C) tv) (x y : Conf) (g : Ghost (F.at C)) : Ghost (F.at C) :=
  g.alloc x.s.h.length (chk x y).site

/-- **The ghost after a step of outside code**: it allocates outside
storage; while no call of `C` is active (`A` empty) it also removes from
`B` each location `C` no longer holds (`Held`, `HStep.drop`). -/
noncomputable def outsideNextAt (F : Family) (C : Nat) (c : ComponentTag)
    (len : Nat) (h' : Heap) (t' : Tm) (g : Ghost (F.at C)) : Ghost (F.at C) :=
  let g₁ := g.alloc len (fun _ => none)
  if g.A = [] then { g₁ with B := fun l => g₁.B l ∧ HeldAt F C c h' t' g₁ l } else g₁

/-- The ghost after a step of outside code between configurations. -/
noncomputable def outsideNext (F : Family) (C : Nat) (c : ComponentTag)
    (x y : Conf) (g : Ghost (F.at C)) : Ghost (F.at C) :=
  outsideNextAt F C c x.s.h.length y.s.h y.t g

theorem outsideNextAt_A {len : Nat} {h' : Heap} {t' : Tm} {g : Ghost (F.at C)} :
    (outsideNextAt F C c len h' t' g).A = g.A := by
  unfold outsideNextAt; split <;> rfl

theorem outsideNext_A {x y : Conf} {g : Ghost (F.at C)} :
    (outsideNext F C c x y g).A = g.A := by
  unfold outsideNext outsideNextAt; split <;> rfl

theorem outsideNext_of_ne {x y : Conf} {g : Ghost (F.at C)} (hA : g.A ≠ []) :
    outsideNext F C c x y g = g.alloc x.s.h.length (fun _ => none) := by
  unfold outsideNext outsideNextAt; simp [hA]

/-- **The trim is the history's `drop`**: outside every call of `C`, the
ghost after an outside step is its allocation followed by `HStep.drop` at
what `C` holds after the step. -/
theorem outsideNext_drop {tv : TypeView} {x y : Conf} {g : Ghost (F.at C)}
    (hA : g.A = []) :
    HStep tv y.s.h (g.alloc x.s.h.length (fun _ => none)) (outsideNext F C c x y g) := by
  unfold outsideNext outsideNextAt; simp only [hA, ite_true]
  exact .drop _ _ hA

/-- **The trim keeps the invariants**: outside every call of `C` the history
is uniform whatever `B` is, and no other invariant reads `B`. -/
theorem Inv.trim {P : Package} {st : St P} (hA : st.g.A = []) (B : Nat → Prop) (hi : Inv st) :
    Inv ⟨st.s, { st.g with B := B }, st.roots⟩ :=
  ⟨Ghost.uniform_empty (g := { st.g with B := B }) hA, hi.marks, hi.confined, hi.valid, hi.localClosed,
    hi.bindings⟩

/-- **The ghost after a step** (the draft, "Actual executions"): an outside
step allocates outside storage, and outside every call of `C` keeps in `B`
only what `C` holds; an entry pushes the protected set, then its incoming
values cross; a step inside a call lets its values cross; an exit lets its
outgoing values cross, then pops. -/
noncomputable def Ghost.stepAt (F : Family) (C : Nat) (c : ComponentTag) (d : CheckData (F.at C) tv)
    (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) (g : Ghost (F.at C)) : Ghost (F.at C) :=
  match stepKind F C c t t' with
  | .outside => outsideNextAt F C c h.length h' t' g
  | .enter => Ghost.crosses tv h' d.xs (g.alloc h.length d.site).enter
  | .body => Ghost.crosses tv h' d.xs (g.alloc h.length d.site)
  | .exit => (Ghost.crosses tv h' d.xs (g.alloc h.length d.site)).pop
      (HeldAt F C c h' t' (g.alloc h.length d.site))

/-- The ghost after a step between configurations, at what the checks give
of it. -/
noncomputable def Ghost.next (F : Family) (C : Nat) (c : ComponentTag) (chk : Conf → Conf → CheckData (F.at C) tv)
    (x y : Conf) (g : Ghost (F.at C)) : Ghost (F.at C) :=
  Ghost.stepAt F C c (chk x y) x.s.h x.t y.s.h y.t g

/-- **What the checks (S), (K) and (O) establish of a step of `C`'s code**
(hypothesis, their interface): the fields of `PkgStep` that read the
step's own code. -/
structure PkgProps {P : Package} (tv : TypeView) (st st' : St P) (mid : Ghost P) (xs : List (Crossing tv)) :
    Prop where
  crossOk : ∀ c ∈ xs, CrossOk tv mid st'.s.h c
  gives : ∀ r ∈ st'.roots, r ∈ st.roots ∨ ∃ c ∈ xs, c.val = r
  stores : ∀ w u, ReachesFrom P.ofC st'.s.h st'.roots w → st'.s.h[w]? = some u → ¬ Same st.s.h st'.s.h w →
    ∃ c ∈ xs, c.val = u
  localStores : ∀ w u, ¬ Same st.s.h st'.s.h w → st'.s.h[w]? = some u → ∀ a l, next u a = some l →
    mid.origin l = some .local → mid.origin w = some .local
  localBindings : ∀ w u, ¬ Same st.s.h st'.s.h w → st'.s.h[w]? = some u → ∀ x ∈ codeVals P.ofC u, ∀ l,
    Leaves P.ofC x l → mid.origin l ≠ some .local

/-- **The hypothesis on a step of an execution**: the client obligation at
a step of outside code, the checks at a step of `C`'s code. -/
def StepHyp (Θ : Protocol (F.at C)) (chk : Conf → Conf → CheckData (F.at C) tv) (x y : Conf) (g : Ghost (F.at C)) :
    Prop :=
  if kind F C c x y = .outside then Row Θ (lift F C c x g) (lift F C c y (Ghost.next F C c chk x y g))
  else PkgProps tv (lift F C c x g) (lift F C c y (Ghost.next F C c chk x y g)) (midOf chk x y g) (chk x y).xs

/-- **A checked step of `C`'s code** at depth `d`: its ghost is built from
the call structure, its checks are the hypothesis. A step inside a call
or an entry needs `d` calls active before it, an exit `d + 1`. -/
noncomputable def pkgStep_of {chk : Conf → Conf → CheckData (F.at C) tv} {d : Nat} {x y : Conf} {g : Ghost (F.at C)}
    (hs : AStep x y) (hk : kind F C c x y ≠ .outside)
    (hp : PkgProps tv (lift F C c x g) (lift F C c y (Ghost.next F C c chk x y g)) (midOf chk x y g) (chk x y).xs)
    (hd : d ≤ g.A.length) (hx : kind F C c x y = .exit → d + 1 ≤ g.A.length) :
    PkgStep tv d (lift F C c x g) (lift F C c y (Ghost.next F C c chk x y g)) where
  adm := hs.adm
  mid := midOf chk x y g
  sites := fun _ hl => Ghost.alloc_old hl
  midE := rfl
  midA := rfl
  midB := rfl
  hist := by
    simp only [lift]
    unfold Ghost.next Ghost.stepAt
    have hm : (midOf chk x y g).A.length = g.A.length := rfl
    split
    · exact (hk ‹_›).elim
    · refine .step y.s.h (.enter _) (by simp; omega) (Ghost.crosses_hsteps _ _ ?_)
      simp; omega
    · exact Ghost.crosses_hsteps _ _ (by omega)
    · have h1 := hx ‹_›
      have hl := Ghost.crosses_len (h := y.s.h) (chk x y).xs (midOf chk x y g)
      refine (Ghost.crosses_hsteps _ _ (by omega)).trans (.step y.s.h (Ghost.pop_hstep ?_) ?_ (.refl _))
      · intro he; rw [he] at hl; simp at hl; omega
      · simp [Ghost.pop]; omega
  xs := (chk x y).xs
  covers := by
    intro e he l hr hexp
    simp only [lift]
    simp only [Ghost.next]
    unfold Ghost.stepAt
    split
    · exact (hk ‹_›).elim
    · exact Ghost.crosses_covers _ _ e he l hr hexp
    · exact Ghost.crosses_covers _ _ e he l hr hexp
    · exact Ghost.crosses_covers _ _ e he l hr hexp
  crossOk := hp.crossOk
  gives := hp.gives
  stores := hp.stores
  valid := rootsValid_of_term (P := F.at C) (st := lift F C c y _) rfl y.ok
  localStores := hp.localStores
  localBindings := hp.localBindings

/-! ## A member certified for its calls -/

/-- **A member's certificate** (the interface of the certified effects, the
draft's Ψ and guarantees), for the steps of a checked component-step
relation `R`: for the calls `Call` of one member, its certified effect
`eff`, within `Ψ_C` part by part; the soundness of that effect over each
call whose steps are in `R` (`certified`, what the pass's check of the
member's body establishes); and each invariant of `G_C` kept by each step
in `R` (`tolerant`, Tolerant invariant). At `R = StepRel.checked tv` the
steps are every checked step (`PkgStep`). -/
structure Cert {P : Package} {tv : TypeView} (R : StepRel P tv) (Ψ : Protocol P) (G : (St P → Prop) → Prop)
    (Call : Nat → St P → St P → Prop) where
  eff : Protocol P
  within : ∀ p, (eff p).le (Ψ p) = true
  certified : ∀ (d : Nat) (Inner : St P → St P → Prop),
    (∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') →
    ∀ st st', MemberRunOf R Inner d st st' → Call d st st' → Ok d st → ∀ l v, st.g.InR l → st.s.h[l]? = some v →
      ∃ v', st'.s.h[l]? = some v' ∧ (eff (st.part l)).Holds st.s.h.length v v'
  tolerant : ∀ I, G I → ∀ (d : Nat) t t', R.Rel d t t' → Ok d t → I t → I t'

/-- **The member a certificate gives**: its call is a run of steps in `R`
that is one of the member's calls. -/
def Cert.member {P : Package} {R : StepRel P tv} {Ψ : Protocol P} {G : (St P → Prop) → Prop}
    {Call : Nat → St P → St P → Prop} (k : Cert R Ψ G Call) : Member P Ψ G where
  Call d Inner st st' := MemberRunOf R Inner d st st' ∧ Call d st st'
  bound d Inner hI st st' hr hok := by
    obtain ⟨ok', hk, hg⟩ := MemberRun.ok hI hr.1 hok
    refine ⟨⟨hk, hg, fun l v hR hv => ?_⟩, ok'⟩
    obtain ⟨v', hv', hc⟩ := k.certified d Inner hI st st' hr.1 hr.2 hok l v hR hv
    exact ⟨v', hv', hc.mono (k.within _)⟩
  keeps I hG d Inner hI hIk st st' hr hok hi :=
    MemberRun.keeps hI hIk (fun t t' hp ho => k.tolerant I hG d t t' hp ho) hr.1 hok hi

/-! ## Executions -/

/-- **An execution** of the step relation `R` whose every state a step
leaves meets `q`. -/
inductive Ex {α : Type} (R : α → α → Prop) (q : α → Prop) : Nat → α → α → Prop
  | refl (a : α) : Ex R q 0 a a
  | next {n : Nat} {a b e : α} : q a → R a b → Ex R q n b e → Ex R q (n + 1) a e

namespace Ex
variable {α : Type} {R : α → α → Prop} {q q' : α → Prop}

theorem mono (hq : ∀ a, q a → q' a) : ∀ {n : Nat} {a b : α}, Ex R q n a b → Ex R q' n a b
  | _, _, _, .refl a => .refl a
  | _, _, _, .next ha hr he => .next (hq _ ha) hr (mono hq he)

/-- **The first state meeting `p`** splits an execution ending in one. -/
theorem first {p : α → Prop} : ∀ {n : Nat} {a e : α}, Ex R q n a e → p e →
    ∃ b n₁ n₂, Ex R (fun x => q x ∧ ¬ p x) n₁ a b ∧ p b ∧ Ex R q n₂ b e ∧ n₁ + n₂ = n
  | _, _, _, .refl a, hp => ⟨a, 0, 0, .refl a, hp, .refl a, rfl⟩
  | _, a, _, .next (n := n) ha hr he, hp => by
    by_cases hpa : p a
    · exact ⟨a, 0, n + 1, .refl a, hpa, .next ha hr he, by omega⟩
    · obtain ⟨b, n₁, n₂, h₁, hb, h₂, hn⟩ := first he hp
      exact ⟨b, n₁ + 1, n₂, .next ⟨ha, hpa⟩ hr h₁, hb, h₂, by omega⟩

/-- **An invariant carried by every step** from a state meeting `q`. -/
theorem carry {r : α → Prop} (hr : ∀ a b, q a → R a b → r a → r b) :
    ∀ {n : Nat} {a e : α}, Ex R q n a e → r a → r e
  | _, _, _, .refl _, h => h
  | _, _, _, .next ha hab he, h => carry hr he (hr _ _ ha hab h)

theorem stop {n : Nat} {a e : α} (he : Ex R q n a e) (hq : ¬ q a) : n = 0 ∧ a = e := by
  cases he with
  | refl => exact ⟨rfl, rfl⟩
  | next ha _ _ => exact (hq ha).elim

theorem zero {a e : α} (he : Ex R q 0 a e) : a = e := by
  cases he; rfl

end Ex

/-! ## The decomposition -/

/-- The code of a run not yet entered: its nodes and continuations. -/
abbrev Code := List Tm × List (ControlFlow.Continuation × Option ControlFlow.Target)

/-- **The code a step enters**: the graph of the innermost frame on the
path, when it is a run not yet entered. -/
def entered (c : ComponentTag) (t : Tm) : Option Code :=
  match (path Realm.empty c false t).head? with
  | some (_, .goto E K _ _ _ _) => some (E, K)
  | _ => none

section Decomposition
variable (F C c) (Θ : Protocol (F.at C)) (chk : Conf → Conf → CheckData (F.at C) tv)

/-- **A step of an execution with its ghost**: an actual step obeying the
call discipline, the ghost after it the history's (`Ghost.next`), and the
step's hypothesis at its ghost (`StepHyp`). -/
def XStep (a b : Conf × Ghost (F.at C)) : Prop :=
  AStep a.1 b.1 ∧ Disc F C c a.1 b.1 ∧ b.2 = Ghost.next F C c chk a.1 b.1 a.2 ∧ StepHyp (c := c) Θ chk a.1 b.1 a.2

/-- The calls of `C` active at a state of an execution. -/
noncomputable abbrev δ (a : Conf × Ghost (F.at C)) : Nat := depthC F C c a.1.t

/-- **A state a call at depth `d` leaves**: the call active. -/
def QCall (d : Nat) (a : Conf × Ghost (F.at C)) : Prop := d + 1 ≤ δ F C c a

/-- **An actual call of the code `m` at depth `d`**, from a state meeting
`Adm`: the lifted states of an execution whose first step enters `m` from
a state with `d` calls of `C` active, and which ends at the first state
with `d` calls active again, its exit. The certificates are indexed by
these entries and traces: `Adm` names the states an execution of the claim
reaches (`ClientFrame.Reached`), so a certificate is asked only of the
calls such an execution makes. -/
def CallOf (Adm : Conf × Ghost (F.at C) → Prop) (m : Option Code) (d : Nat) (st st' : St (F.at C)) : Prop :=
  ∃ a a₁ b n, Adm a ∧ XStep F C c Θ chk a a₁ ∧ entered c a₁.1.t = m ∧ Ex (XStep F C c Θ chk) (QCall F C c d) n a₁ b ∧
    δ F C c a = d ∧ δ F C c a₁ = d + 1 ∧ δ F C c b = d ∧ st = lift F C c a.1 a.2 ∧ st' = lift F C c b.1 b.2

/-- **A state a run of outside code at depth `d` leaves**: at least `d`
calls active, its active frame outside `C` when exactly `d` are. -/
def QRun (d : Nat) (a : Conf × Ghost (F.at C)) : Prop :=
  d ≤ δ F C c a ∧ (δ F C c a = d → Outside F C c a.1)

end Decomposition

variable {Θ Ψ : Protocol (F.at C)} {G : (St (F.at C) → Prop) → Prop} {chk : Conf → Conf → CheckData (F.at C) tv}

theorem kind_spec (x y : Conf) :
    (kind F C c x y = .outside → Outside F C c x ∧ depthC F C c y.t = depthC F C c x.t) ∧
    (kind F C c x y = .enter → depthC F C c x.t < depthC F C c y.t) ∧
    (kind F C c x y = .exit → depthC F C c y.t < depthC F C c x.t) ∧
    (kind F C c x y = .body → depthC F C c y.t = depthC F C c x.t ∧ ¬ Outside F C c x) := by
  unfold kind stepKind
  by_cases h₁ : OutsideAt F C c x.t ∧ depthC F C c y.t = depthC F C c x.t
  · rw [ite_eq_left h₁]; refine ⟨fun _ => h₁, ?_, ?_, ?_⟩ <;> simp
  · simp only [h₁, ite_false]
    by_cases h₂ : depthC F C c x.t < depthC F C c y.t
    · simp [h₂]
    · by_cases h₃ : depthC F C c y.t < depthC F C c x.t
      · simp [h₂, h₃]
      · simp only [h₂, h₃, ite_false]
        refine ⟨by simp, by simp, by simp, fun _ => ⟨by omega, fun ho => h₁ ⟨ho, by omega⟩⟩⟩

theorem kind_outside {x y : Conf} (ho : Outside F C c x) (he : depthC F C c y.t = depthC F C c x.t) :
    kind F C c x y = .outside := by
  simp [kind, stepKind, show OutsideAt F C c x.t from ho, he]

theorem kind_ne_outside {x y : Conf} (h : ¬ (Outside F C c x ∧ depthC F C c y.t = depthC F C c x.t)) :
    kind F C c x y ≠ .outside := by
  intro hk; exact h ((kind_spec x y).1 hk)

/-- **The history follows the calls**: every step of an execution keeps
the number of sets of `A` the number of calls of `C` active plus `off`. -/
theorem XStep.len {off : Nat} {a b : Conf × Ghost (F.at C)} (hx : XStep F C c Θ chk a b)
    (hl : a.2.A.length = δ F C c a + off) : b.2.A.length = δ F C c b + off := by
  obtain ⟨-, hd, hg, -⟩ := hx
  rw [hg]
  have hm : (midOf chk a.1 b.1 a.2).A.length = a.2.A.length := rfl
  have hs := kind_spec (F := F) (C := C) (c := c) a.1 b.1
  simp only [δ] at hl ⊢
  cases hk : stepKind F C c a.1.t b.1.t with
  | outside =>
    have := (hs.1 hk).2
    simp only [Ghost.next, Ghost.stepAt, hk, outsideNextAt_A]; omega
  | enter =>
    have := hs.2.1 hk
    have : depthC F C c b.1.t ≤ depthC F C c a.1.t + 1 := by
      by_cases ho : Outside F C c a.1
      · exact (hd.1 ho).2
      · have := (hd.2 ho).1; omega
    simp only [Ghost.next, Ghost.stepAt, hk, Ghost.enter, Ghost.crosses_len, List.length_append, Ghost.alloc_A, List.length_singleton]
    omega
  | exit =>
    have := hs.2.2.1 hk
    have : depthC F C c a.1.t ≤ depthC F C c b.1.t + 1 := by
      by_cases ho : Outside F C c a.1
      · have := (hd.1 ho).1; omega
      · exact (hd.2 ho).2
    simp only [Ghost.next, Ghost.stepAt, hk, Ghost.pop, List.length_dropLast, Ghost.crosses_len, Ghost.alloc_A]
    omega
  | body =>
    have := (hs.2.2.2 hk).1
    simp only [Ghost.next, Ghost.stepAt, hk, Ghost.crosses_len, Ghost.alloc_A]; omega

theorem Run.nil' {k d : Nat} (st : St (F.at C)) : Run Θ Ψ G k d st st := by
  cases k <;> exact RunAt.nil st

theorem Run.outside' {k d : Nat} {st st' st'' : St (F.at C)} (ho : OutsideStep Θ st st') (hr : Run Θ Ψ G k d st' st'') :
    Run Θ Ψ G k d st st'' := by
  cases k <;> exact RunAt.outside ho hr

theorem kind_enter {x y : Conf} (h : depthC F C c x.t < depthC F C c y.t) : kind F C c x y = .enter := by
  have : ¬ (OutsideAt F C c x.t ∧ depthC F C c y.t = depthC F C c x.t) := fun h' => by omega
  simp [kind, stepKind, this, h]

theorem hyp_row {x y : Conf} {g : Ghost (F.at C)} (hk : kind F C c x y = .outside)
    (hh : StepHyp (c := c) Θ chk x y g) : Row Θ (lift F C c x g) (lift F C c y (Ghost.next F C c chk x y g)) := by
  unfold StepHyp at hh; rw [ite_eq_left hk] at hh; exact hh

theorem hyp_props {x y : Conf} {g : Ghost (F.at C)} (hk : kind F C c x y ≠ .outside)
    (hh : StepHyp (c := c) Θ chk x y g) :
    PkgProps tv (lift F C c x g) (lift F C c y (Ghost.next F C c chk x y g)) (midOf chk x y g) (chk x y).xs := by
  unfold StepHyp at hh; rw [ite_eq_right hk] at hh; exact hh

/-- **The checked steps of an execution**: at `R = StepRel.checked tv`, a
step of `C`'s code is its checked step itself; `decompose`, `exec_bound`,
`exec_keeps` and `exec_rely` at it are the results over every `PkgStep`. -/
def XStep.checked {d : Nat} {a b : Conf × Ghost (F.at C)} (_ : XStep F C c Θ chk a b)
    (p : PkgStep tv d (lift F C c a.1 a.2) (lift F C c b.1 b.2)) :
    (StepRel.checked tv).Rel d (lift F C c a.1 a.2) (lift F C c b.1 b.2) := p

section Decompose
variable {R : StepRel (F.at C) tv} {Adm : Conf × Ghost (F.at C) → Prop}
  (hAdm : ∀ a b, Adm a → XStep F C c Θ chk a b → Adm b)
  (certs : (m : Option Code) → Cert R Ψ G (CallOf F C c Θ chk Adm m))
  (mk : ∀ {d : Nat} {a b : Conf × Ghost (F.at C)}, XStep F C c Θ chk a b →
    PkgStep tv d (lift F C c a.1 a.2) (lift F C c b.1 b.2) → R.Rel d (lift F C c a.1 a.2) (lift F C c b.1 b.2))
include hAdm certs mk

/-- **An actual execution is a run of outside code** (the draft, "Actual
executions"). An execution inside a call of `C` at depth `d` (`QRun`), from
and to a state with `d` calls active, whose every set of the history is a
call of `C` active (`off` sets more, fixed), is a run within the budget of
its length (`Run`): a step of outside code keeping the calls is an outside
step (`outsideStep_of_step`); an entry and the execution up to the first
state with `d` calls active again is a call of the member certified for
the code it enters (`Cert.member`). Inside such a call at depth `d`
(`QCall`), every step of `C`'s code is a checked step (`pkgStep_of`), and
an execution from a state whose active frame is outside `C` up to the
first state of `C`'s code with `d + 1` calls active is a run of outside
code one call deeper. By strong induction on the length. -/
theorem decompose (off : Nat) : ∀ n : Nat,
    (∀ (d : Nat) (a e : Conf × Ghost (F.at C)), 0 < d → Ex (XStep F C c Θ chk) (QRun F C c d) n a e → Adm a →
      δ F C c a = d → δ F C c e = d → a.2.A.length = δ F C c a + off →
      ∀ k, n ≤ k → Run Θ Ψ G k d (lift F C c a.1 a.2) (lift F C c e.1 e.2)) ∧
    (∀ (d : Nat) (a e : Conf × Ghost (F.at C)), Ex (XStep F C c Θ chk) (QCall F C c d) n a e → Adm a →
      δ F C c a = d + 1 → δ F C c e = d → a.2.A.length = δ F C c a + off →
      ∀ k, n ≤ k → MemberRunOf R (Run Θ Ψ G k (d + 1)) d (lift F C c a.1 a.2) (lift F C c e.1 e.2)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  -- The number of sets of the history follows the calls along an execution.
  have hlen : ∀ {q : Conf × Ghost (F.at C) → Prop} {m : Nat} {a b : Conf × Ghost (F.at C)},
      Ex (XStep F C c Θ chk) q m a b → a.2.A.length = δ F C c a + off → b.2.A.length = δ F C c b + off :=
    fun hx hl => hx.carry (r := fun x => x.2.A.length = δ F C c x + off) (fun _ _ _ hs h => hs.len h) hl
  -- The states of an execution from a state meeting `Adm` meet it.
  have hcar : ∀ {q : Conf × Ghost (F.at C) → Prop} {m : Nat} {a b : Conf × Ghost (F.at C)},
      Ex (XStep F C c Θ chk) q m a b → Adm a → Adm b :=
    fun hx ha => hx.carry (r := Adm) (fun x y _ hxy hx' => hAdm x y hx' hxy) ha
  refine ⟨fun d a e hd0 hex hAa hda hde hl k hk => ?_, fun d a e hex hAa hda hde hl k hk => ?_⟩
  · cases hex with
    | refl => exact Run.nil' _
    | next hq hx hrest =>
      rename_i m b
      obtain ⟨hs, hdisc, hg, hh⟩ := hx
      have ho : Outside F C c a.1 := hq.2 hda
      have h1 := hdisc.1 ho
      by_cases heq : depthC F C c b.1.t = depthC F C c a.1.t
      · -- A step of outside code.
        have hk' := kind_outside ho heq
        have hA : a.2.A ≠ [] := by
          intro h; rw [h] at hl; simp only [δ, List.length_nil] at hl hda; omega
        have hb : b.2 = a.2.alloc a.1.s.h.length (fun _ => none) := by
          rw [hg]; simp only [Ghost.next, Ghost.stepAt, stepKind_conf, hk']; exact outsideNext_of_ne hA
        have hrow := hyp_row hk' hh
        rw [← hg, hb] at hrow
        have hos := outsideStep_of_step hs ho hrow
        rw [← hb] at hos
        exact Run.outside' hos ((ih m (by omega)).1 d b e hd0 hrest (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩)
          (by simp only [δ] at hda ⊢; omega) hde
          (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) k (by omega))
      · -- The entry of a call of `C`.
        have hlt : depthC F C c a.1.t < depthC F C c b.1.t := by omega
        have hk' := kind_enter hlt
        have hne : kind F C c a.1 b.1 ≠ .outside := by rw [hk']; simp
        have hpk := pkgStep_of (d := d) hs hne (hyp_props hne hh) (by simp only [δ] at hl hda; omega)
          (fun h => by rw [hk'] at h; cases h)
        rw [← hg] at hpk
        have hdb : δ F C c b = d + 1 := by simp only [δ] at hda ⊢; omega
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨w, n₁, n₂, h₁, hw, h₂, hn⟩ := hrest.first (p := fun x => δ F C c x ≤ d) (by omega)
        have hdw : d ≤ δ F C c w := h₁.carry (r := fun x => d ≤ δ F C c x) (by
          rintro x y ⟨-, hnx⟩ ⟨-, hd', -, -⟩ hx
          simp only [δ] at hnx hx ⊢
          by_cases hox : Outside F C c x.1
          · have := (hd'.1 hox).1; omega
          · have := (hd'.2 hox).2; omega) (by omega)
        have hdw' : δ F C c w = d := by have hw' : δ F C c w ≤ d := hw; omega
        have hM := (ih n₁ (by omega)).2 d b w (h₁.mono fun x hx => by
          simp only [QCall]; simp only [QRun] at hx; omega) (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩) hdb hdw'
          (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) k' (by omega)
        have hcall : (certs (entered c b.1.t)).member.Call d (Run Θ Ψ G k' (d + 1))
            (lift F C c a.1 a.2) (lift F C c w.1 w.2) :=
          ⟨.step (mk ⟨hs, hdisc, hg, hh⟩ hpk) hM, a, b, w, n₁, hAa, ⟨hs, hdisc, hg, hh⟩, rfl, h₁.mono fun x hx => by
            simp only [QCall]; simp only [QRun] at hx; omega, hda, hdb, hdw', rfl, rfl⟩
        exact RunAt.member _ hcall ((ih n₂ (by omega)).1 d w e hd0 h₂ (hcar h₁ (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩)) hdw' hde
          (hlen h₁ (XStep.len ⟨hs, hdisc, hg, hh⟩ hl)) (k' + 1) (by omega))
  · by_cases ho : Outside F C c a.1
    · -- A run of outside code one call deeper, up to the first state of `C`'s code with `d + 1` calls.
      let p : Conf × Ghost (F.at C) → Prop := fun x => (δ F C c x ≤ d + 1 ∧ ¬ Outside F C c x.1) ∨ δ F C c x ≤ d
      obtain ⟨v, n₁, n₂, h₁, hv, h₂, hn⟩ := hex.first (p := p) (.inr (by omega))
      have hdv : d + 1 ≤ δ F C c v := h₁.carry (r := fun x => d + 1 ≤ δ F C c x) (by
          rintro x y ⟨-, hnx⟩ ⟨-, hd', -, -⟩ hx
          by_cases hox : Outside F C c x.1
          · have := (hd'.1 hox).1; simp only [δ] at hx ⊢; omega
          · have := (hd'.2 hox).2
            have h3 : ¬ (δ F C c x ≤ d + 1) := fun h => hnx (.inl ⟨h, hox⟩)
            simp only [δ] at hx h3 ⊢; omega) (by omega)
      have hv' : δ F C c v = d + 1 ∧ ¬ Outside F C c v.1 := by
        rcases hv with ⟨h, h'⟩ | h
        · exact ⟨by omega, h'⟩
        · omega
      have hn₁ : n₁ ≠ 0 := by
        rintro rfl
        have := h₁.zero; subst this; exact hv'.2 ho
      have hn₂ : n₂ ≠ 0 := by
        rintro rfl
        have := h₂.zero; subst this; omega
      have hin := (ih n₁ (by omega)).1 (d + 1) a v (by omega) (h₁.mono fun x ⟨hx₁, hx₂⟩ => by
          unfold QRun
          exact ⟨hx₁, fun he => Classical.byContradiction fun hno => hx₂ (.inl ⟨by omega, hno⟩)⟩) hAa hda hv'.1 hl k (by omega)
      exact .inner (by simp only [δ] at hl hda; simp only [lift]; omega) hin
        ((ih n₂ (by omega)).2 d v e h₂ (hcar h₁ hAa) hv'.1 hde (hlen h₁ hl) k (by omega))
    · cases hex with
      | refl => omega
      | next hq hx hrest =>
        rename_i m b
        obtain ⟨hs, hdisc, hg, hh⟩ := hx
        have h2 := hdisc.2 ho
        have hne : kind F C c a.1 b.1 ≠ .outside := kind_ne_outside fun h => ho h.1
        have hpk := pkgStep_of (d := d) hs hne (hyp_props hne hh) (by simp only [δ] at hl hda; omega)
          (fun _ => by simp only [δ] at hl hda; omega)
        rw [← hg] at hpk
        by_cases hbe : depthC F C c b.1.t = d
        · -- The exit of the call.
          obtain ⟨-, rfl⟩ := hrest.stop (by simp only [QCall, δ]; omega)
          exact .step (mk ⟨hs, hdisc, hg, hh⟩ hpk) (.nil _)
        · exact .step (mk ⟨hs, hdisc, hg, hh⟩ hpk) ((ih m (by omega)).2 d b e hrest (hAdm _ _ hAa ⟨hs, hdisc, hg, hh⟩)
            (by simp only [δ] at hda ⊢; omega) hde
            (XStep.len ⟨hs, hdisc, hg, hh⟩ hl) k (by omega))

/-- **(L2) of an actual execution**: an execution inside a call of `C`, as
in `decompose`, from a state meeting the invariants, changes every location
of `R_C` within `Ψ_C` at its part and keeps the invariants. -/
theorem exec_bound (hΘ : ∀ p, (Θ p).le (Ψ p) = true) (off : Nat) {d n : Nat} {a e : Conf × Ghost (F.at C)}
    (hex : Ex (XStep F C c Θ chk) (QRun F C c d) n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2)) :
    RBound Ψ d (lift F C c a.1 a.2) (lift F C c e.1 e.2) ∧ Ok d (lift F C c e.1 e.2) :=
  Run.bound hΘ n d _ _ ((decompose hAdm certs mk off n).1 d a e hok.pos hex hAa hda hde hl n (Nat.le_refl _)) hok

/-- **(L4) of an actual execution**: an invariant of `G_C` that every
outside step keeps survives such an execution. -/
theorem exec_keeps (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {I : St (F.at C) → Prop} (hG : G I) (hout : OutsideKeeps Θ I)
    (off : Nat) {d n : Nat} {a e : Conf × Ghost (F.at C)}
    (hex : Ex (XStep F C c Θ chk) (QRun F C c d) n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2)) (hi : I (lift F C c a.1 a.2)) :
    I (lift F C c e.1 e.2) :=
  Run.keeps hΘ hG hout n d _ _ ((decompose hAdm certs mk off n).1 d a e hok.pos hex hAa hda hde hl n (Nat.le_refl _)) hok hi

/-- **The rule's consequence over an actual execution**: the call's run
bounding the heap by its own effect `Φ`, a fact whose support meets the
premise of Proposition "Read-only reliance" location by location holds
after such an execution. -/
theorem exec_rely (hΘ : ∀ p, (Θ p).le (Ψ p) = true) {Cn : ConditionOn (St (F.at C))}
    {A : AssertionOn (St (F.at C))} {Φ S : Footprint} (hsup : (states (F.at C)).Supports Cn A S) {ρ : Env}
    {mm : Nat} (off : Nat) {d n : Nat} {a e : Conf × Ghost (F.at C)}
    (hex : Ex (XStep F C c Θ chk) (QRun F C c d) n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2))
    (hΦ : TolerantFrames.Action Φ ρ a.1.s e.1.s)
    (hf : Framed Φ Ψ S ρ (lift F C c a.1 a.2)) (hc : Cn ρ mm (lift F C c a.1 a.2) (lift F C c e.1 e.2))
    (hA : A ρ mm (lift F C c a.1 a.2)) : A ρ mm (lift F C c e.1 e.2) :=
  readOnly_rely hΘ hsup hΦ ((decompose hAdm certs mk off n).1 d a e hok.pos hex hAa hda hde hl n (Nat.le_refl _)) hok hf hc hA

end Decompose

/-- **(L2) over every checked step** (the instance `StepRel.checked`): with a
certificate for each code over every `PkgStep`, `exec_bound` at the checked
steps themselves. -/
theorem exec_bound_checked {Adm : Conf × Ghost (F.at C) → Prop} (hAdm : ∀ a b, Adm a → XStep F C c Θ chk a b → Adm b)
    (certs : (m : Option Code) → Cert (StepRel.checked tv) Ψ G (CallOf F C c Θ chk Adm m))
    (hΘ : ∀ p, (Θ p).le (Ψ p) = true) (off : Nat) {d n : Nat} {a e : Conf × Ghost (F.at C)}
    (hex : Ex (XStep F C c Θ chk) (QRun F C c d) n a e) (hAa : Adm a) (hda : δ F C c a = d) (hde : δ F C c e = d)
    (hl : a.2.A.length = δ F C c a + off) (hok : Ok d (lift F C c a.1 a.2)) :
    RBound Ψ d (lift F C c a.1 a.2) (lift F C c e.1 e.2) ∧ Ok d (lift F C c e.1 e.2) :=
  exec_bound hAdm certs (fun hx p => XStep.checked hx p) hΘ off hex hAa hda hde hl hok

/-! ## The invariants at every depth -/

/-- **Every step of an execution keeps the invariants of states**, at any
depth, a return to code outside every call of `C` included: a step of
outside code is an outside step (`outsideStep_of_step`, `outside_inv`); a
step of `C`'s code, an exit to depth `0` among them, is a checked step at
depth `0` (`pkgStep_of`, `pkg_step_inv`). -/
theorem XStep.inv {off : Nat} {a b : Conf × Ghost (F.at C)} (hx : XStep F C c Θ chk a b)
    (hl : a.2.A.length = δ F C c a + off) (hi : Inv (lift F C c a.1 a.2)) : Inv (lift F C c b.1 b.2) := by
  obtain ⟨hs, -, hg, hh⟩ := hx
  obtain ⟨b, g'⟩ := b
  simp only at hg ⊢
  subst hg
  by_cases hk : kind F C c a.1 b = .outside
  · have hrow := hyp_row hk hh
    have hn : Ghost.next F C c chk a.1 b a.2 = outsideNext F C c a.1 b a.2 := by
      simp only [Ghost.next, Ghost.stepAt, stepKind_conf, hk]; rfl
    rw [hn] at hrow ⊢
    by_cases hA : a.2.A = []
    · -- Outside every call: the step with its allocation, then the trim of `B`.
      have hrow' : Row Θ (lift F C c a.1 a.2)
          (lift F C c b (a.2.alloc a.1.s.h.length (fun _ => none))) := by
        unfold outsideNext outsideNextAt at hrow; simp only [hA, ite_true] at hrow
        exact hrow
      have h₁ := outside_inv (outsideStep_of_step hs ((kind_spec a.1 b).1 hk).1 hrow') hi
      unfold outsideNext outsideNextAt; simp only [hA, ite_true]
      exact Inv.trim (st := lift F C c b (a.2.alloc a.1.s.h.length (fun _ => none))) hA _ h₁
    · rw [outsideNext_of_ne hA] at hrow ⊢
      exact outside_inv (outsideStep_of_step hs ((kind_spec a.1 b).1 hk).1 hrow) hi
  · refine pkg_step_inv (pkgStep_of (d := 0) hs hk (hyp_props hk hh) (Nat.zero_le _) fun hx => ?_) hi
    have := (kind_spec (F := F) (C := C) (c := c) a.1 b).2.2.1 hx
    simp only [δ] at hl; omega

/-- **The invariants along an execution** (the draft, "What acceptance
reads of the rule", 5): from a state meeting them, whose history has one
set per call of `C` active, every later state meets them with one set per
call, and so at every state inside a call of `C` they are `Ok` at its
depth: the entry conditions of each call, every later entry included. -/
theorem Ex.inv {q : Conf × Ghost (F.at C) → Prop} {n : Nat} {a e : Conf × Ghost (F.at C)}
    (hex : Ex (XStep F C c Θ chk) q n a e) (hl : a.2.A.length = δ F C c a) (hi : Inv (lift F C c a.1 a.2)) :
    e.2.A.length = δ F C c e ∧ Inv (lift F C c e.1 e.2) ∧
      (0 < δ F C c e → Ok (δ F C c e) (lift F C c e.1 e.2)) := by
  have h := hex.carry (r := fun a => a.2.A.length = δ F C c a + 0 ∧ Inv (lift F C c a.1 a.2))
    (fun _ _ _ hx ⟨hl, hi⟩ => ⟨XStep.len hx hl, XStep.inv hx hl hi⟩) ⟨hl, hi⟩
  exact ⟨h.1, h.2, fun hd => h.2.ok hd (by simp only [lift]; omega)⟩

end Verification.TolerantFrames.ReadOnly
