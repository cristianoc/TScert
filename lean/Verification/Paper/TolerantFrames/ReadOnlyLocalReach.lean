import Verification.Paper.TolerantFrames.ReadOnlyWriteKinds
import Verification.Paper.TolerantFrames.ReadOnlyPublic
import Verification.Paper.TolerantFrames.ReadOnlyIncoming

/-! # Read-only handles: the local lemma at the base of a call

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Charges", `local_reach`). A run of a
term from a heap `h₀` changes an old location only where the term's values
at `h₀` reach it, through every location, closure capture, node
expression value and bound function part: the base of the call, the values
the call passed. Where the old locations of a set of sites hold only values
whose every first location is of a site of the set, and the call's values
too, every old location the run changes is of a site of the set.

- **A run of the calculus over heaps of values** (`ValRun`): steps, each
  from a heap whose locations hold values.
- **Every component's code as outside code** (`allC`): with no tag the
  package's, the values of a term (`vals allC true`) are all of its values,
  a closure's captures and node expressions included, and every step is a
  step of outside code. The base's no-forgery (`step_noForge`) and the
  located change (`step_reach`) then hold of every step.
- **No forgery along a run** (`valRun_noForge`): what the values of the
  run's term reach after it, they reached before it or it allocated.
- **A set of sites the values meet in depth** (`DeepIn`, `HeapDeep`): every
  first location of every value a value's code holds is of a site of the
  set; at the old locations of its sites, the heap holds such values. Reach
  from such a value stays among its sites (`reach_deep`).
- **The local lemma** (`local_reach`): a step of a run from `h₀` that
  changes a location `l < |h₀|` changes one of a site of the set.
- **A step of charged code in the run** (`stepWithin_reach`, with
  `stepWithin_charged`): a step of the run from a term meeting the residual
  invariant whose innermost frame's code's charges are among `K` is within
  the protocol from `K` and the set, below `|h₀|`.
- **The flow gives both premises** (`deepIn_of_vj`, `heapDeep_of_heapInv`):
  for a set holding the values' sets, closed under the heap of sites'
  contents and under the capture slots of the codes whose tokens it holds
  (`CapClosed`), where the closures have their codes' layouts (`LayDeep`)
  and the node expressions of the flow's codes hold no located value
  (`CodesLowered`).
- **The frame a step runs in** (`Fits.frameIn`, `frameKinds_flow`): the
  innermost frame of a fitting term runs a code the flow proposes for, so
  its charges are among the flow's codes'.
- **The residual invariant along a program** (`wok_program`, `wok_initial`):
  every state of a public call meets it from initial configurations that
  do; an initial configuration's term does.
- **The active redex of outside code** (`active_vals`, `redex_arg_root`):
  the values at its positions are values at positions of outside code of
  the term; an argument of a call there is a root or holds no location. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-- **Every tag's code as outside code**: no tag is the package's. -/
def allC : ComponentTag → Bool := fun _ => false

/-- **A run of the calculus over heaps of values**: steps, each from a heap
whose every location holds a value. -/
inductive ValRun : Heap → Tm → Heap → Tm → Prop where
  | refl {h : Heap} {t : Tm} : ValRun h t h t
  | step {h h₁ h₂ : Heap} {t t₁ t₂ : Tm} : (∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) →
      Step h t h₁ t₁ → ValRun h₁ t₁ h₂ t₂ → ValRun h t h₂ t₂

/-- A run only grows the heap (proved). -/
theorem ValRun.length_le {h h' : Heap} {t t' : Tm} (hr : ValRun h t h' t') : h.length ≤ h'.length := by
  induction hr with
  | refl => exact Nat.le_refl _
  | step _ hs _ ih => exact Nat.le_trans (Footprints.step_length_le hs) ih

/-- **No forgery along a run** (proved, `step_noForge` at each step with
every tag's code as outside code): every location the values of the run's
last term reach at its last heap was reached by the first term's values at
the first heap, or is fresh. -/
theorem valRun_noForge {h h' : Heap} {t t' : Tm} (hr : ValRun h t h' t') :
    ∀ l, ReachesFrom allC h' (vals allC Realm.empty true false t') l → ReachesFrom allC h (vals allC Realm.empty true false t) l ∨ h.length ≤ l := by
  induction hr with
  | refl => exact fun l hl => .inl hl
  | step hh hs hr ih =>
    intro l hl
    rcases ih l hl with hl₁ | hl₁
    · exact step_noForge (ofC := allC) (rl := Realm.empty) (nk := false) (fun _ h => by cases h) hh hs none rfl l hl₁
    · exact .inr (Nat.le_trans (Footprints.step_length_le hs) hl₁)

/-! ## Row (b) on standard natives, as an invariant of a native's run -/

/-- **A closure of the realm's code**: graph code tagged with a tag of the
realm. -/
def RealmFn (rl : Realm) (f : Val) : Prop :=
  ∃ fs ar E K s caps k rest comp oid, f = .objAt fs (.graph ar E K s caps k rest comp) oid ∧ rl.tags comp = true

/-- **A step of the native's own code** in the run of its call: every frame
on the evaluation path of the call's term is a frame of the realm's code
(the call itself, before its entry, included). A step inside a function the
native called is that function's. -/
def ownStep (rl : Realm) (t : Tm) : Bool :=
  (path Realm.empty none false t).dropLast.all fun p => rl.tags p.1

/-- **The run of a call of a native** from `h₀`, with the locations its own
steps allocated: steps, each from a heap of values, a step of the
native's own code adding the locations it allocates. -/
inductive NativeRun (rl : Realm) (h₀ : Heap) (t₀ : Tm) : Heap → Tm → List Nat → Prop where
  | start : NativeRun rl h₀ t₀ h₀ t₀ []
  | step {h h' : Heap} {t t' : Tm} {A : List Nat} : NativeRun rl h₀ t₀ h t A →
      (∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) → Step h t h' t' →
      NativeRun rl h₀ t₀ h' t' (if ownStep rl t then A ++ List.range' h.length (h'.length - h.length) else A)

/-- **Row (b) of the trust on standard natives** (Read-only frames, the
natives item, approved by the owner on 2026-11-21), stated of every run of
a call of a closure of the realm's code, receiver and actuals its operands
(the callee left out), at each step of the native's own code:

- *stores*: into storage that existed before the call it stores a value
  reaching no location (a primitive), or, into a location its operands
  reach, a value reaching only locations its operands reach or locations
  allocated during the run ("it stores only primitives and values its
  receiver and arguments reach; it keeps no argument beyond what its
  receiver and arguments reach or its result");
- *calls*: a function of code other than the realm's that it calls is one
  its operands reach, or one reached from storage allocated during the run
  by the functions it called; and the values it passes reach no storage its
  own steps allocated ("it calls out only through the function arguments it
  is given, and only during its run": in the calculus a later call is one
  through storage the native kept, which the stores exclude). -/
def NativeRowB (rl : Realm) : Prop :=
  ∀ (h₀ : Heap) (f r : Val) (args : List Tm) (h h' : Heap) (t t' : Tm) (A : List Nat),
    RealmFn rl f → isVal r = true → (∀ a ∈ args, isVal a = true) →
    (∀ (l : Nat) (v : Val), h₀[l]? = some v → isVal v = true) →
    NativeRun rl h₀ (.invoke f r args) h t A → (∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) →
    Step h t h' t' → ownStep rl t = true →
    (∀ l v, l < h₀.length → h'[l]? = some v → h[l]? ≠ some v →
      (∀ l', ¬ Reaches allC h v l') ∨
      (ReachesFrom allC h (r :: args) l ∧
        ∀ l', Reaches allC h v l' → ReachesFrom allC h (r :: args) l' ∨ h₀.length ≤ l')) ∧
    (∀ g r' args', (activeFrame none t).2 = .invoke g r' args' → isVal g = true → ¬ RealmFn rl g →
      (∃ u ∈ r :: args, ∃ x, ValReach allC h u x ∧ CodeReach allC x g) ∨
      (∃ l u x, h₀.length ≤ l ∧ l ∉ A ∧ h[l]? = some u ∧ ValReach allC h u x ∧ CodeReach allC x g)) ∧
    (∀ g r' args', (activeFrame none t).2 = .invoke g r' args' → isVal g = true → ¬ RealmFn rl g →
      ∀ x ∈ r' :: args', ∀ l', Reaches allC h x l' → l' ∉ A)

/-- **A changed location is one step from a value of the term** (proved,
`step_reach` with every tag's code as outside code). -/
theorem step_changed_reached {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') {l : Nat} {v : Val}
    (hv : h[l]? = some v) (hne : h'[l]? ≠ some v) : ReachesFrom allC h (vals allC Realm.empty true false t) l := by
  obtain ⟨u, hu, a, hn⟩ := step_reach (ofC := allC) (rl := Realm.empty) hs none false rfl hv hne
  exact ⟨u, hu, [a], hn⟩

variable {α : Type}

/-- **A value meets a set of sites in depth**: every first location of
every value its code holds (captures and node expressions of every
closure, parts of every bound function, `CodeReach allC`) is of a site of
the set. -/
def DeepIn (site : Nat → α) (L : List α) (v : Val) : Prop :=
  ∀ w, CodeReach allC v w → ∀ a l, next w a = some l → site l ∈ L

/-- **A heap meets a set of sites in depth**: each location of a site of
the set holds a value meeting it in depth. -/
def HeapDeep (site : Nat → α) (L : List α) (h : Heap) : Prop :=
  ∀ l v, h[l]? = some v → site l ∈ L → DeepIn site L v

theorem DeepIn.code {site : Nat → α} {L : List α} {v x : Val} (hv : DeepIn site L v)
    (hx : x ∈ codeVals allC v) : DeepIn site L x :=
  fun w hw => hv w (.step hx hw)

/-- **Reach in depth** (proved, by induction on the path): in a heap
meeting a set of sites in depth, a value meeting it in depth reaches only
locations of its sites. -/
theorem reach_deep {site : Nat → α} {L : List α} {h : Heap} (hH : HeapDeep site L h) :
    ∀ (π : List Label) {v : Val} {l : Nat}, DeepIn site L v → Follows allC h v π l → site l ∈ L
  | [], _, _, _, hf => hf.elim
  | [a], _, _, hv, hf => hv _ (.refl _) a _ hf
  | a :: b :: π, _, _, hv, ⟨v₀, hs, hf⟩ => by
    refine reach_deep hH (b :: π) ?_ hf
    rcases hs with ⟨l₀, hn, hl₀⟩ | ⟨i, -, hi⟩
    · exact hH l₀ v₀ hl₀ (hv _ (.refl _) a l₀ hn)
    · exact hv.code (List.mem_of_getElem? hi)

/-- **The local lemma** (proved, the draft's `local_reach`): a step of a run
from `h₀` whose last heap holds values changes an old location `l < |h₀|`
only where its site is in a set of sites that `h₀` meets in depth and the
run's first term's values meet in depth: the step changes a location one
step from a value of its term (`step_changed_reached`), which the first
term's values reached at `h₀` (`valRun_noForge`, the location being old),
so a location of a site of the set (`reach_deep`). -/
theorem local_reach {site : Nat → α} {L : List α} {h₀ h h' : Heap} {u₀ u u' : Tm}
    (hr : ValRun h₀ u₀ h u) (hs : Step h u h' u') (hH : HeapDeep site L h₀)
    (hroots : ∀ x ∈ vals allC Realm.empty true false u₀, DeepIn site L x)
    {l : Nat} {v : Val} (hlt : l < h₀.length) (hv : h[l]? = some v) (hne : h'[l]? ≠ some v) :
    site l ∈ L := by
  rcases valRun_noForge hr l (step_changed_reached hs hv hne) with ⟨x, hx, π, hf⟩ | hfresh
  · exact reach_deep hH π (hroots x hx) hf
  · exact absurd hlt (Nat.not_lt.mpr hfresh)

/-- **A step of charged code in a run is within the protocol from its
charges and the set at every location** (proved, `local_reach` gives
`stepAll_charged`'s held sites): at a step of a run from `h₀`, from a term
meeting the residual invariant, with valid references, whose innermost
frame's code's charges are among `K`, at states whose ghost keeps the
sites of `h₀`'s locations, every location below `|h₀|` changes within
the protocol from `K` and a set of sites `h₀` and the run's first term's
values meet in depth. -/
theorem stepAll_reach {P : Package} [DecidableEq P.Site] [Hashable P.Site] [LawfulHashable (Option P.Site)]
    {K₀ K : List Charge} {L : Sites P} {site : Nat → Option P.Site} {h₀ : Heap} {u₀ : Tm}
    {st st' : St P} {t t' : Tm} (hr : ValRun h₀ u₀ st.s.h t) (hs : Step st.s.h t st'.s.h t')
    (hw : WOk t) (hk : writesK t ⊆ K₀) (hrefs : RefsOk st.s.W t) (hK : frameKinds K₀ (activeFrame none t).1 ⊆ K)
    (hH : HeapDeep site L h₀) (hroots : ∀ x ∈ vals allC Realm.empty true false u₀, DeepIn site L x)
    (hsite : ∀ l, l < h₀.length → st.g.site l = site l) :
    StepAll (probeProtocol K L) h₀.length st st' :=
  stepAll_charged hs hw hk hrefs hK fun l _ hlt hv hne _ => by
    rw [hsite l hlt]; exact local_reach hr hs hH hroots hlt hv hne

/-- **A step of charged code in a run is within the protocol from its
charges and the set** (proved, `local_reach` gives `stepWithin_charged`'s
held sites): at a step of a run from `h₀`, from a term meeting the residual
invariant, with valid references, whose innermost frame's code's charges
are among `K`, at states whose ghost keeps the sites of `h₀`'s locations,
every location of `R_P` below `|h₀|` changes within the protocol from `K`
and a set of sites `h₀` and the run's first term's values meet in depth. -/
theorem stepWithin_reach {P : Package} [DecidableEq P.Site] [Hashable P.Site] [LawfulHashable (Option P.Site)]
    {K₀ K : List Charge} {L : Sites P} {site : Nat → Option P.Site} {h₀ : Heap} {u₀ : Tm}
    {st st' : St P} {t t' : Tm} (hr : ValRun h₀ u₀ st.s.h t) (hs : Step st.s.h t st'.s.h t')
    (hw : WOk t) (hk : writesK t ⊆ K₀) (hrefs : RefsOk st.s.W t) (hK : frameKinds K₀ (activeFrame none t).1 ⊆ K)
    (hH : HeapDeep site L h₀) (hroots : ∀ x ∈ vals allC Realm.empty true false u₀, DeepIn site L x)
    (hsite : ∀ l, l < h₀.length → st.g.site l = site l) :
    StepWithin (probeProtocol K L) h₀.length st st' :=
  (stepAll_reach hr hs hw hk hrefs hK hH hroots hsite).within

/-! ## The values of a flow meet a closed set in depth -/

section Flow
variable {P : Package} {Fl : Flow P} {g : Ghost P} {n : Nat}

/-- **The values of lowered code**: spines with no cell, at any position
(proved, by induction on the term): lowered code holds no object, no view
spine and no run, and the code parts of the closures it creates are
variables or primitive values. -/
theorem codePart_vals {t : Tm} (h : CodePart t) (o : Bool) : vals allC Realm.all o true t = [] := by
  rcases h with ⟨i, rfl⟩ | hp
  · simp [vals]
  · cases t <;> simp_all [primVal, vals]

theorem lowered_vals_all : ∀ (e : Tm), Lowered Fl e → ∀ (o : Bool) (x : Val), x ∈ vals allC Realm.all o true e →
    ∃ ls, x = .arr ls ∧ ∀ y ∈ ls, y = none := by
  intro e
  induction e using Tm.induct
  all_goals intro h o x hx
  case makeBound t r pre ns args _ _ _ iha =>
    simp only [Lowered, loweredArgs_iff] at h
    simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap, codePart_vals h.1, codePart_vals h.2.1,
      List.not_mem_nil, false_or] at hx
    rcases hx with ⟨a, ha, hx⟩ | ⟨a, ha, hx⟩
    · rw [codePart_vals (h.2.2.1 a ha)] at hx; cases hx
    · exact iha a ha (h.2.2.2 a ha) o x hx
  case makeGraph n E K s caps k r comp ns args ihE _ iha =>
    simp only [Lowered, loweredArgs_iff] at h
    simp only [vals, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp only [valsArgs_eq, List.mem_append, List.mem_flatMap] at hx
        rcases hx with ⟨e, he, hx⟩ | ⟨a, ha, hx⟩
        · exact ihE e he (h.2.1 e he) true x hx
        · rw [codePart_vals (h.2.2.1 a ha)] at hx; cases hx
      · cases hx
    · simp only [valsArgs_eq, List.mem_flatMap] at hx
      obtain ⟨a, ha, hx⟩ := hx
      exact iha a ha (h.2.2.2 a ha) o x hx
  all_goals simp only [Lowered, loweredArgs_iff, vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at h hx
  all_goals grind

variable (P) in
/-- **The layouts of the closures of `C`'s code** a predicate gives: arity,
rest, number of captures and entry label, for each code's closures. -/
def LayOf (Lay : Code → Nat × Bool × Nat × Nat → Prop) (y : Val) : Prop :=
  ∀ fs ar E K s caps k rest comp oid, y = .objAt fs (.graph ar E K s caps k rest comp) oid →
    P.ofC comp = true → Lay (E, K) (ar, rest, caps.length, s)

/-- **Every closure of `C`'s code within a value has its code's layout.** -/
def LayDeep (P : Package) (Lay : Code → Nat × Bool × Nat × Nat → Prop) (v : Val) : Prop :=
  ∀ w, Within P v w → LayOf P Lay w

variable (Fl) in
/-- **A set closed under captures**: for each code whose token the set
holds, the sites of each capture slot at its entry, at each layout of its
closures. -/
def CapClosed (Lay : Code → Nat × Bool × Nat × Nat → Prop) (L : Sites P) : Prop :=
  ∀ m ar rest nc s π, Lay m (ar, rest, nc, s) → Fl.code m entryCx = some π → π.tok ∈ L →
    ∀ j, j < nc → Sub (π.env s (capSlot ar rest j)) L

variable (Fl) in
/-- **The codes a flow proposes for hold no located value**: the values of
each of their node expressions are spines with no cell, as the values of
lowered code are (`lowered_vals_all`). -/
def CodesLowered : Prop :=
  ∀ m c π, Fl.code m c = some π → ∀ e ∈ m.1, ∀ x ∈ vals allC Realm.all true true e, ∃ ls, x = .arr ls ∧ ∀ y ∈ ls, y = none

variable (Fl g n) in
/-- A value meeting a set within `L`, its closures at their layouts, or a
spine with no cell. -/
def GoodIn (Lay : Code → Nat × Bool × Nat × Nat → Prop) (L : Sites P) (v : Val) : Prop :=
  (∃ S, Sub S L ∧ VJ Fl g n S v ∧ LayDeep P Lay v) ∨ ∃ ls, v = .arr ls ∧ ∀ y ∈ ls, y = none

/-- **The values a good value holds are good** (proved, by induction on the
value): a bound function's parts and a closure of outside code's captures
meet its set (`VJ.boundPart`, `VJ.capOut`); a closure of `C`'s code's
captures meet its capture slots at its entry (`VJ.capC`), within `L` where
`L` holds its token (`CapClosed`); the node expressions of a closure are
lowered, whose values are spines with no cell. -/
theorem goodIn_vals_vj {Lay : Code → Nat × Bool × Nat × Nat → Prop} {L : Sites P} (hcap : CapClosed Fl Lay L)
    (hlow : CodesLowered Fl) :
    ∀ (y : Val) (S : Sites P), Sub S L → VJ Fl g n S y → LayDeep P Lay y →
      ∀ x ∈ vals allC Realm.all true true y, GoodIn Fl g n Lay L x := by
  intro y
  induction y using Tm.induct
  all_goals intro S hS hv hl x hx
  -- Terms that are no value.
  all_goals try (exfalso; have := hv.val; simp [isVal] at this; done)
  -- Values holding nothing else.
  all_goals try (simp [vals] at hx; done)
  all_goals try (simp [vals] at hx; subst hx; exact .inl ⟨S, hS, hv, hl⟩)
  case objBound fs oid t r pre iht ihr ihp =>
    simp only [vals, ite_true, List.mem_cons, List.mem_append, valsArgs_eq, List.mem_flatMap] at hx
    have hl' : ∀ u ∈ t :: r :: pre, LayDeep P Lay u := fun u hu w hw => hl w (.bound hu hw)
    rcases hx with rfl | (hx | hx) | ⟨a, ha, hx⟩
    · exact .inl ⟨S, hS, hv, hl⟩
    · exact iht S hS (hv.boundPart (by simp)) (hl' t (by simp)) x hx
    · exact ihr S hS (hv.boundPart (by simp)) (hl' r (by simp)) x hx
    · exact ihp a ha S hS (hv.boundPart (by simp [ha])) (hl' a (by simp [ha])) x hx
  case objGraph fs oid ar E K s caps k rest comp ihE ihc =>
    simp only [vals, allC, ite_true, Bool.false_eq_true, ite_false, List.mem_cons, List.mem_append, valsArgs_eq,
      List.mem_flatMap] at hx
    rcases hx with rfl | ⟨e, he, hx⟩ | ⟨a, ha, hx⟩
    · exact .inl ⟨S, hS, hv, hl⟩
    · -- A node expression's values.
      cases hc : P.ofC comp with
      | false =>
        obtain ⟨ls, rfl, hls⟩ :=
          lowered_vals_all e ((hv.inner _ (.refl _)).2.2.1 fs ar E K s caps k rest comp oid rfl hc e he) true x hx
        exact .inr ⟨ls, rfl, hls⟩
      | true =>
        obtain ⟨π, hπ, -⟩ := hv.entryC hc
        obtain ⟨ls, rfl, hls⟩ := hlow (E, K) entryCx π hπ e he x hx
        exact .inr ⟨ls, rfl, hls⟩
    · -- A capture.
      have hla : LayDeep P Lay a := fun w hw => hl w (.cap ha hw)
      cases hc : P.ofC comp with
      | false => exact ihc a ha S hS (hv.capOut hc ha) hla x hx
      | true =>
        obtain ⟨π, hπ, htok⟩ := (hv.fns _ (.refl _) fs ar E K s caps k rest comp oid rfl).1 hc
        obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
        have hlt : i < caps.length := (List.getElem?_eq_some_iff.mp hi).1
        exact ihc a ha _ (hcap (E, K) ar rest caps.length s π (hl _ (.refl _) fs ar E K s caps k rest comp oid rfl hc)
          hπ (hS _ htok) i hlt) ((hv.capC hc hπ).1 i a hi) hla x hx

/-- **The values a good value holds are good** (proved, `goodIn_vals_vj`). -/
theorem goodIn_vals {Lay : Code → Nat × Bool × Nat × Nat → Prop} {L : Sites P} (hcap : CapClosed Fl Lay L)
    (hlow : CodesLowered Fl) {y : Val} (hy : GoodIn Fl g n Lay L y) :
    ∀ x ∈ vals allC Realm.all true true y, GoodIn Fl g n Lay L x := by
  rcases hy with ⟨S, hS, hv, hl⟩ | ⟨ls, rfl, hls⟩
  · exact goodIn_vals_vj hcap hlow y S hS hv hl
  · intro x hx; simp [vals] at hx; subst hx; exact .inr ⟨ls, rfl, hls⟩

/-- **A good value meets `L` in depth** (proved, along the code steps by
`goodIn_vals`): each value its code holds is good, and a good value's
first locations are of sites of `L`. -/
theorem GoodIn.deepIn {Lay : Code → Nat × Bool × Nat × Nat → Prop} {L : Sites P} (hcap : CapClosed Fl Lay L)
    (hlow : CodesLowered Fl) {v : Val} (hv : GoodIn Fl g n Lay L v) : DeepIn g.site L v := by
  intro w hw
  induction hw with
  | refl v₁ =>
    intro a l hn
    rcases hv with ⟨S, hS, hvj, -⟩ | ⟨ls, rfl, hls⟩
    · exact hS _ (hvj.sites l (Leaves.of_next hn))
    · exfalso
      cases a with
      | cell i =>
        simp only [next, spineEntries] at hn
        cases hi : ls[i]? with
        | none => simp [hi] at hn
        | some y => rw [hls y (List.mem_of_getElem? hi)] at hi; simp [hi] at hn
      | _ => simp [next, Footprints.fieldsOf, HeapKnowledge.descriptorSpine] at hn
  | @step v₁ x₁ w₁ hx _ ih =>
    refine ih ?_
    cases v₁ with
    | objAt fs cc i => exact goodIn_vals hcap hlow hv x₁ (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hx)
    | _ => simp [codeVals] at hx

/-- **A value of the flow meets a closed set in depth** (proved,
`GoodIn.deepIn`): a value meeting a set within `L` whose closures of `C`'s
code have their codes' layouts, where `L` is closed under captures and the
flow's codes are lowered. -/
theorem deepIn_of_vj {Lay : Code → Nat × Bool × Nat × Nat → Prop} {L S : Sites P} (hcap : CapClosed Fl Lay L)
    (hlow : CodesLowered Fl) {v : Val} (hv : VJ Fl g n S v) (hS : Sub S L) (hl : LayDeep P Lay v) :
    DeepIn g.site L v :=
  GoodIn.deepIn hcap hlow (.inl ⟨S, hS, hv, hl⟩)

/-- **A heap meeting the flow meets a closed set in depth** (proved): each
location of a site of `L` holds a value meeting its site's contents, within
`L` where `L` is closed under contents. -/
theorem heapDeep_of_heapInv {Lay : Code → Nat × Bool × Nat × Nat → Prop} {L : Sites P} {h : Heap}
    (hcap : CapClosed Fl Lay L) (hlow : CodesLowered Fl) (hH : HeapInv Fl g h)
    (hcl : ∀ s ∈ L, Sub (Fl.H.contents s) L) (hl : ∀ (w : Nat) (u : Val), h[w]? = some u → LayDeep P Lay u) :
    HeapDeep g.site L h :=
  fun w u hw hs => deepIn_of_vj hcap hlow (hH w u hw) (hcl _ hs) (hl w u hw)

end Flow

/-! ## The frames a step runs in -/

section Frames
variable {P : Package} {Fl : Flow P} {V : Sites P → Val → Prop}

variable (Fl) in
/-- **A frame of `C`'s code runs a code the flow proposes for.** -/
def FrameIn (cur : Option FrameKey) : Prop :=
  ∀ m comp kx, cur = some ((m, comp), kx) → P.ofC comp = true → ∃ c π, Fl.code m c = some π

theorem frameIn_args {cur : Option FrameKey} {t₀ : Tm} {xs : List Tm} (hc : FrameIn Fl cur)
    (ih : ∀ x ∈ xs, FrameIn Fl (activeFrame cur x).1) : FrameIn Fl (activeArgs cur t₀ xs).1 := by
  rcases activeArgs_split (cur := cur) (t := t₀) xs with ⟨he, _⟩ | ⟨x, hx, he, _⟩
  · rw [he]; exact hc
  · rw [he]; exact ih x hx

/-- **The innermost frame of a fitting term runs a code of the flow**
(proved, by induction on `Fits`; the draft's `segFrames` at the segment's
codes taken to be every code of the flow): read from a frame `cur` outside
it that runs one, the innermost frame around the term's next redex runs a
code the flow proposes for where it runs `C`'s code (`Fits.frameC`). -/
theorem Fits.frameIn : ∀ {Γ a o S t}, Fits Fl V Γ a o S t → ∀ cur, FrameIn Fl cur → FrameIn Fl (activeFrame cur t).1 := by
  intro Γ a o S t h
  induction h with
  | val hv _ _ => intro cur hc; cases ‹Tm› <;> simp_all [activeFrame, isVal]
  | var _ _ _ => intro cur hc; simpa [activeFrame] using hc
  | invoke _ _ _ _ _ _ _ _ ihf ihr iha =>
    intro cur hc; simp only [activeFrame]
    split
    · exact ihf cur hc
    · split
      · exact ihr cur hc
      · exact frameIn_args hc fun x hx => iha x hx cur hc
  | invokeC σ c π Sa Sr _ hfn _ _ _ _ _ _ _ _ _ ihr iha =>
    intro cur hc
    simp only [activeFrame, hfn.val, Bool.true_eq_false, ite_false]
    split
    · exact ihr cur hc
    · exact frameIn_args hc fun x hx => by
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
        exact iha i x hi cur hc
  | construct _ _ _ _ _ _ _ ihf iha =>
    intro cur hc; simp only [activeFrame]
    split
    · exact ihf cur hc
    · exact frameIn_args hc fun x hx => iha x hx cur hc
  | letE _ _ _ ihx _ =>
    intro cur hc; simp only [activeFrame]; split
    · exact ihx cur hc
    · exact hc
  | spread _ _ _ ih | readAt _ _ _ _ _ ih | test _ _ ih | lenOf _ _ ih | throw _ _ ih =>
    intro cur hc; simp only [activeFrame]; split
    · exact ih cur hc
    · exact hc
  | ite _ _ _ _ ihc _ _ =>
    intro cur hc; simp only [activeFrame]; split
    · exact ihc cur hc
    · exact hc
  | makeAbsent _ _ _ _ _ ih | makeView _ _ _ _ _ _ ih | makeBound _ _ _ _ _ _ _ _ _ ih
  | makeGraphC _ _ _ _ _ _ _ _ _ _ _ _ ih | makeGraphOut _ _ _ _ _ _ _ _ _ _ _ _ ih | arrLit _ _ _ _ _ ih =>
    intro cur hc; simp only [activeFrame]
    exact frameIn_args hc fun x hx => ih x hx cur hc
  | indexAt _ _ _ _ _ _ ihx ihk | writeAt _ _ _ _ ihx ihk | arith _ _ _ ihx ihk | elemAt _ _ _ _ ihx ihk
  | merge _ _ _ _ _ _ _ _ ihx ihk | makeKey _ _ _ _ _ ihx ihk =>
    intro cur hc; simp only [activeFrame]; split
    · exact ihx cur hc
    · split
      · exact ihk cur hc
      · exact hc
  | setElem _ _ _ _ _ _ _ ihx ihi ihv =>
    intro cur hc; simp only [activeFrame]; split
    · exact ihx cur hc
    · split
      · exact ihi cur hc
      · split
        · exact ihv cur hc
        · exact hc
  | gotoC _ _ _ _ _ _ _ _ | gotoOut _ _ _ _ _ => intro cur hc; simpa [activeFrame] using hc
  | frameC c π _ _ hcode _ _ _ _ _ _ _ ih =>
    intro cur _; simp only [activeFrame]
    exact ih _ fun m comp kx he _ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      exact ⟨c, π, hcode⟩
  | frameOut hc' _ _ _ _ _ _ ih =>
    intro cur _; simp only [activeFrame]
    exact ih _ fun m comp kx he hcomp => by
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      rw [hc'] at hcomp; cases hcomp

end Frames

/-- **A frame of the flow's code has its charges among the flow's**
(proved): a code the finite flow proposes for is one of its codes. -/
theorem frameKinds_flow {P : Package} [DecidableEq P.Site] {F : FFlow P} {K₀ : List Charge}
    {cur : Option FrameKey} (hc : FrameIn F.flow cur) (hC : ∀ key, cur = some key → P.ofC key.1.2 = true) :
    frameKinds K₀ cur ⊆ K₀ ++ flowKinds F := by
  intro k hk
  cases cur with
  | none => exact List.mem_append_left _ hk
  | some key =>
    obtain ⟨⟨m, comp⟩, kx⟩ := key
    obtain ⟨c, π, hπ⟩ := hc m comp kx rfl (hC _ rfl)
    obtain ⟨fc, hfc, -⟩ := FFlow.code_at hπ
    obtain ⟨l, hl, -⟩ := FFlow.at_mem hfc
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(m, l), hl, hk⟩)

/-! ## The residual invariant along a program -/

namespace FrameCore
variable {τ : Type} {core : FrameCore τ}

/-- **The residual invariant along an execution** (proved, `step_wok` at
each step): from a state whose term meets it at a heap of plain values,
every state of an execution of steps keeping the obligation does. -/
theorem wok_ex {q : Conf × Ghost (core.F.at core.C) → Prop} {n : Nat} {a b : Conf × Ghost (core.F.at core.C)}
    (hex : Ex core.KStep q n a b) (ha : WOk a.1.t ∧ HeapW a.1.s.h) : WOk b.1.t ∧ HeapW b.1.s.h :=
  hex.carry (r := fun x : Conf × Ghost (core.F.at core.C) => WOk x.1.t ∧ HeapW x.1.s.h)
    (fun _ _ _ hxy hx => have := step_wok hxy.1.step hx.2 hx.1; ⟨this.1, this.2.1⟩) ha

/-- **The residual invariant at a public call** (proved, the draft's
`wok_program`, `wok_ex` along the call's execution and its entering step):
from initial configurations meeting it, the state a public call enters
meets it. -/
theorem wok_program {Init : Conf → Prop} {m : Code} {x₀ : Conf} {n : Nat} {x a₁ : Conf × Ghost (core.F.at core.C)}
    (hinit : ∀ x, Init x → WOk x.t ∧ HeapW x.s.h) (h : core.PublicCall Init m x₀ n x a₁) :
    WOk a₁.1.t ∧ HeapW a₁.1.s.h :=
  wok_ex h.ex (hinit x₀ h.1)

end FrameCore

/-- **An initial configuration's term meets the residual invariant**
(proved, `lowered_wok`): the initialization's run, its node expressions
meeting it, at plain slots and the default `undefined`, and the client's
lowered source, in its scope. -/
theorem wok_initial {P : Package} {Fl : Flow P} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {l : Nat} {L : List Tm} {c : ComponentTag} {client : Tm} (hE : ∀ e ∈ E, WOk e) (hL : ∀ v ∈ L, Plain v)
    (hc : Lowered Fl client) :
    WOk (.letE (.goto E K l L .undef c) client) := by
  simp only [WOk, wOks_iff, plainArgs_iff]
  exact ⟨⟨hE, hL, rfl, trivial⟩, lowered_wok client hc⟩

/-! ## The values at the active redex of outside code -/

section Active
variable {ofC : ComponentTag → Bool}

/-- **The active redex of outside code holds roots** (proved, by induction
on the term, following `activeFrame`): where the innermost frame around the
next redex runs outside code, every value at a position of the redex is a
value at a position of outside code of the term, read from the frame `cur`
outside it. -/
theorem active_vals : ∀ (t : Tm) (cur : Option FrameKey) (p : Option FrameKey × Tm), activeFrame cur t = p →
    ofC (frameTag p.1) = false → ∀ x ∈ vals ofC Realm.empty true false p.2, x ∈ vals ofC Realm.empty (!ofC (frameTag cur)) false t := by
  have hargs : ∀ (xs : List Tm) (T : Tm) (cur : Option FrameKey) (p : Option FrameKey × Tm),
      (∀ a ∈ xs, ∀ cur p, activeFrame cur a = p → ofC (frameTag p.1) = false →
        ∀ x ∈ vals ofC Realm.empty true false p.2, x ∈ vals ofC Realm.empty (!ofC (frameTag cur)) false a) →
      activeArgs cur T xs = p → ofC (frameTag p.1) = false → ∀ x ∈ vals ofC Realm.empty true false p.2,
        x ∈ vals ofC Realm.empty (!ofC (frameTag cur)) false T ∨ ∃ a ∈ xs, x ∈ vals ofC Realm.empty (!ofC (frameTag cur)) false a := by
    intro xs T cur p ih hp hc x hx
    rcases activeArgs_split (cur := cur) (t := T) xs with ⟨he, _⟩ | ⟨a, ha, he, _⟩
    · rw [he] at hp; subst hp; simp only at hc hx; exact .inl (by simpa [hc] using hx)
    · rw [he] at hp; exact .inr ⟨a, ha, ih a ha cur p hp hc x hx⟩
  intro t
  induction t using Tm.induct
  all_goals intro cur p hp hc x hx
  all_goals simp only [activeFrame] at hp
  all_goals repeat' split at hp
  -- The redex runs in `cur`: the term itself.
  all_goals try (subst hp; simpa [hc] using hx)
  -- A redex inside a subterm.
  case invoke.isTrue f r args ihf _ _ _ => have := ihf cur p hp hc x hx; simp [vals, this]
  case invoke.isFalse.isTrue f r args _ ihr _ _ _ => have := ihr cur p hp hc x hx; simp [vals, this]
  case invoke.isFalse.isFalse f r args _ _ iha _ _ =>
    rcases hargs args _ cur p iha hp hc x hx with h | ⟨a, ha, h⟩
    · simpa [vals] using h
    · simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr ⟨a, ha, h⟩
  case construct.isTrue f args ihf _ _ => have := ihf cur p hp hc x hx; simp [vals, this]
  case construct.isFalse f args _ iha _ =>
    rcases hargs args _ cur p iha hp hc x hx with h | ⟨a, ha, h⟩
    · simpa [vals] using h
    · simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr ⟨a, ha, h⟩
  -- A redex inside a list of arguments.
  all_goals try (rcases hargs _ _ cur p (by assumption) hp hc x hx with h | ⟨a, ha, h⟩
                 · exact h
                 · first
                   | exact vals_makeAt (mem_valsArgs_of ha h)
                   | exact mem_valsArgs_of ha h
                   | (simp only [vals, List.mem_append]; exact .inr (mem_valsArgs_of ha h)))
  -- A frame's running term.
  case frame =>
    rename_i E K t L d k xx comp ihE iht ihL ihd
    simp only [vals, List.mem_append]
    exact .inr (iht _ p hp hc x hx)
  -- A redex inside a subterm.
  all_goals (simp only [vals, List.mem_append]
             first
               | solve_by_elim [Or.inl, Or.inr]
               | exact .inl (.inl (by solve_by_elim))
               | exact .inl (.inr (by solve_by_elim)))

/-- **An argument at the active redex of outside code is a root or holds no
location** (proved, `active_vals`): an object, a spine or a view spine
among the arguments of the call the next step reduces, in a frame of
outside code, is a value at a position of outside code; any other value
reaches no location. -/
theorem redex_arg_root {t f r v : Tm} {args : List Tm} (hc : ofC (frameTag (activeFrame none t).1) = false)
    (hp : (activeFrame none t).2 = .invoke f r args ∨ (activeFrame none t).2 = .construct f args) (hv : v ∈ args) :
    v ∈ vals ofC Realm.empty (!ofC (frameTag none)) false t ∨ ∀ l, ¬ Leaves ofC v l := by
  cases hl : LocatedVal v
  · refine .inr fun l ⟨w, hw, a, hn⟩ => ?_
    have hcv : codeVals ofC v = [] := by cases v <;> simp_all [LocatedVal, codeVals]
    cases hw with
    | refl => cases v <;> cases a <;> simp_all [LocatedVal, next, Footprints.fieldsOf, HeapKnowledge.descriptorSpine, spineEntries]
    | step hx _ => rw [hcv] at hx; cases hx
  · have hself : v ∈ vals ofC Realm.empty true false v := by
      cases v <;> simp_all [LocatedVal, vals_objAt]
      all_goals simp [vals]
    refine .inl (active_vals t none _ rfl hc v ?_)
    rcases hp with hp | hp <;> rw [hp] <;> simp only [vals, List.mem_append, valsArgs_eq, List.mem_flatMap]
    · exact .inr ⟨v, hv, hself⟩
    · exact .inr ⟨v, hv, hself⟩

end Active

end Verification.TolerantFrames.ReadOnly
