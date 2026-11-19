import Verification.Paper.TolerantFrames.ReadOnlyStepWrites
import Verification.Paper.TolerantFrames.ReadOnlyCert

/-! # Read-only handles: a frame's writes are its code's

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Charges", `residual_charged`). The
charges of a set of codes are the kinds their node expressions' writes may
change (`writesK`, `codeKinds`); this module proves that a step of a frame
changes an old location only at a kind its code's charges hold.

- **The residual invariant** (`WOk`): at every run of graph code in a
  term, the writes its running term may still perform are among its code's
  (`frame E K t …`: `writesK t ⊆ codeKinds E`), and the slots, captures and
  bound parts a term carries perform none. Every step keeps it
  (`step_wok`), with a heap whose every value performs none (`HeapW`): a
  step's writes are among those of the term it steps from, an entered node
  instantiates its code's expression with values, and a value performs no
  write.
- **The active redex's writes** (`active_writes`): the writes of the term
  the next step reduces are among the charges of the innermost frame's
  code.
- **The written location's kind** (`slotKind_sound`): a writing redex
  whose references are valid writes a location of a kind its write may
  change (`writeKinds`).
- **A step's changes are its code's charges** (`step_kind_charged`): at a
  step from a term meeting the invariant, with valid references, every old
  location the step changes has a kind the innermost frame's code's charges
  hold. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-! ## The invariant -/

mutual
/-- **The residual invariant**: at every run of graph code in the term, the
writes its running term may still perform are among its code's; the slots
of a run, the captures of a closure and the parts of a bound function
perform none, and meet the invariant. -/
def WOk : Tm → Prop
  | .frame E _ t L d _ _ _ =>
    writesK t ⊆ E.flatMap writesK ∧ WOk t ∧ WOks E ∧ PlainArgs L ∧ (writesK d = [] ∧ WOk d)
  | .goto E _ _ L d _ => WOks E ∧ PlainArgs L ∧ (writesK d = [] ∧ WOk d)
  | .objAt _ (.bound t r pre) _ => (writesK t = [] ∧ WOk t) ∧ (writesK r = [] ∧ WOk r) ∧ PlainArgs pre
  | .objAt _ (.graph _ E _ _ caps _ _ _) _ => WOks E ∧ PlainArgs caps
  | .makeAt (.bound t r pre) _ xs =>
    ((writesK t = [] ∧ WOk t) ∧ (writesK r = [] ∧ WOk r) ∧ PlainArgs pre) ∧ WOks xs
  | .makeAt (.graph _ E _ _ caps _ _ _) _ xs => (WOks E ∧ PlainArgs caps) ∧ WOks xs
  | .makeAt .absent _ xs => WOks xs
  | .makeAt (.view _ _ _) _ xs => WOks xs
  | .arrLit xs => WOks xs
  | .invoke f r args => WOk f ∧ WOk r ∧ WOks args
  | .construct f args => WOk f ∧ WOks args
  | .letE a b => WOk a ∧ WOk b
  | .indexAt a b => WOk a ∧ WOk b
  | .writeAt _ a b => WOk a ∧ WOk b
  | .arith _ a b => WOk a ∧ WOk b
  | .elemAt a b => WOk a ∧ WOk b
  | .merge _ a b => WOk a ∧ WOk b
  | .makeKey a b => WOk a ∧ WOk b
  | .ite a b c => WOk a ∧ WOk b ∧ WOk c
  | .setElem a b c => WOk a ∧ WOk b ∧ WOk c
  | .readAt _ a => WOk a
  | .test _ a => WOk a
  | .lenOf a => WOk a
  | .spread a => WOk a
  | .throw a => WOk a
  | _ => True
termination_by structural t => t

/-- The invariant at each term of a list. -/
def WOks : List Tm → Prop
  | [] => True
  | x :: xs => WOk x ∧ WOks xs
termination_by structural xs => xs

/-- Each term of a list performs no write and meets the invariant. -/
def PlainArgs : List Tm → Prop
  | [] => True
  | x :: xs => (writesK x = [] ∧ WOk x) ∧ PlainArgs xs
termination_by structural xs => xs
end

/-- **A plain term**: it performs no write and meets the invariant. -/
def Plain (t : Tm) : Prop := writesK t = [] ∧ WOk t

@[simp] theorem wOks_iff : ∀ {xs : List Tm}, WOks xs ↔ ∀ x ∈ xs, WOk x
  | [] => by simp [WOks]
  | x :: xs => by simp [WOks, wOks_iff]

@[simp] theorem plainArgs_iff : ∀ {xs : List Tm}, PlainArgs xs ↔ ∀ x ∈ xs, Plain x
  | [] => by simp [PlainArgs]
  | x :: xs => by simp [PlainArgs, plainArgs_iff, Plain]

/-- **A heap of plain values**. -/
def HeapW (h : Heap) : Prop := ∀ v ∈ h, Plain v

/-- A value performs no write. -/
theorem writesK_val {v : Tm} (hv : isVal v = true) : writesK v = [] := by
  cases v <;> simp_all [isVal, writesK]

/-- A value meeting the invariant is plain. -/
theorem Plain.of_val {v : Tm} (hv : isVal v = true) (hw : WOk v) : Plain v := ⟨writesK_val hv, hw⟩

/-! ## Substitution and instantiation keep the invariant -/

theorem flatMap_congr_mem {α β : Type} {xs : List α} {f g : α → List β} (h : ∀ x ∈ xs, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- **Substituting a plain term** keeps the invariant and the writes
(proved, by induction on the term). -/
theorem subst_wok {a : Tm} (ha : Plain a) (u : Tm) :
    ∀ j, (WOk u → WOk (subst j a u)) ∧ writesK (subst j a u) = writesK u := by
  induction u using Tm.induct with
  | var i =>
    intro j; simp only [subst]
    split
    · exact ⟨fun _ => ha.2, by rw [ha.1]; simp [writesK]⟩
    · split <;> simp [WOk, writesK]
  | objGraph fs oid n E K s caps k r comp _ ihc =>
    intro j
    simp only [subst, WOk, wOks_iff, plainArgs_iff, Plain, writesK, substArgs_eq_map, List.mem_map]
    refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, trivial⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨((ihc x hx j).2).trans (h2 x hx).1, (ihc x hx j).1 (h2 x hx).2⟩
  | _ =>
    intro j
    simp only [subst, WOk, writesK, substArgs_eq_map, wOks_iff, plainArgs_iff, Plain, List.mem_map,
      List.flatMap_map, writesKs_eq] at *
    first
      | trivial
      | (refine ⟨?_, ?_⟩ <;> grind [flatMap_congr_mem])

/-- **Instantiating with plain values** keeps the invariant and the writes
(proved, by induction on the term). -/
theorem instantiate_wok {ρ : Env} (hρ : ∀ i, Plain (ρ i)) (u : Tm) :
    ∀ d, (WOk u → WOk (instantiate d ρ u)) ∧ writesK (instantiate d ρ u) = writesK u := by
  induction u using Tm.induct with
  | var i =>
    intro d; simp only [instantiate]
    split
    · simp [WOk, writesK]
    · exact ⟨fun _ => (hρ _).2, by rw [(hρ _).1]; simp [writesK]⟩
  | _ =>
    intro d
    simp only [instantiate, WOk, writesK, instantiateArgs_eq_map, wOks_iff, plainArgs_iff, Plain, List.mem_map,
      List.flatMap_map, writesKs_eq] at *
    first
      | trivial
      | (refine ⟨?_, ?_⟩ <;> grind [flatMap_congr_mem])

/-! ## Every step keeps the invariant -/

/-- A thrown value is plain (proved, by induction on `Raises`). -/
theorem raises_plain {t v : Tm} (hr : Raises t v) (ht : WOk t) : Plain v := by
  induction hr with
  | throwV hv _ => exact Plain.of_val hv (by simpa [WOk] using ht)
  | callArg _ _ hai _ _ ih =>
    simp only [WOk, wOks_iff] at ht; exact ih (ht.2.2 _ (List.mem_of_getElem? hai))
  | constructArg _ hai _ _ ih =>
    simp only [WOk, wOks_iff] at ht; exact ih (ht.2 _ (List.mem_of_getElem? hai))
  | @makeArg c _ _ _ _ _ hai _ _ ih =>
    cases c <;> simp only [WOk, wOks_iff] at ht
    all_goals first | exact ih (ht _ (List.mem_of_getElem? hai)) | exact ih (ht.2 _ (List.mem_of_getElem? hai))
  | arrArg hai _ _ ih =>
    simp only [WOk, wOks_iff] at ht; exact ih (ht _ (List.mem_of_getElem? hai))
  | _ => (try simp only [WOk] at ht); grind

/-- The elements a spine reads from a plain heap are plain. -/
theorem readElems_plain {h : Heap} (hh : HeapW h) {ls : List (Option Nat)} {vs : List Tm}
    (hr : readElems h ls = some vs) : ∀ v ∈ vs, Plain v := by
  intro v hv
  rcases readElems_mem hr v hv with rfl | ⟨l, _, hl⟩
  · exact ⟨rfl, trivial⟩
  · exact hh v (List.mem_of_getElem? hl)

theorem HeapW.append {h xs : Heap} (hh : HeapW h) (hx : ∀ v ∈ xs, Plain v) : HeapW (h ++ xs) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hh v hv
  · exact hx v hv

theorem HeapW.set {h : Heap} (hh : HeapW h) {v : Tm} (hv : Plain v) (l : Nat) : HeapW (h.set l v) := by
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with hw | rfl
  · exact hh w hw
  · exact hv

theorem HeapW.get {h : Heap} (hh : HeapW h) {l : Nat} {v : Tm} (hv : h[l]? = some v) : Plain v :=
  hh v (List.mem_of_getElem? hv)

theorem plain_undef : Plain .undef := ⟨rfl, trivial⟩

/-- The slots a target's map gives a run are plain where the run's are. -/
theorem envMap_plain {m : Option (List Nat)} {L : List Tm} {d : Tm} (hL : ∀ x ∈ L, Plain x) (hd : Plain d) :
    (∀ x ∈ (envMap m L d).1, Plain x) ∧ Plain (envMap m L d).2 := by
  have hget : ∀ i, Plain (L.getD i d) := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases hi : L[i]? with
    | none => exact hd
    | some x => exact hL x (List.mem_of_getElem? hi)
  cases m with
  | none => exact ⟨hL, hd⟩
  | some slots =>
    simp only [envMap, List.mem_map]
    exact ⟨fun _ ⟨i, _, he⟩ => he ▸ hget i, hget 0⟩

/-- A run's environment is plain where its slots and default are. -/
theorem envOf_plain {L : List Tm} {d : Tm} (hL : ∀ x ∈ L, Plain x) (hd : Plain d) (i : Nat) :
    Plain (envOf L d i) := by
  simp only [envOf]
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => exact hd
  | some x => exact hL x (List.mem_of_getElem? hi)

theorem parameters_plain : ∀ (n : Nat) {args : List Tm}, (∀ x ∈ args, Plain x) →
    ∀ x ∈ CallArguments.parameters n args, Plain x
  | 0, _, _ => by simp [CallArguments.parameters]
  | n + 1, [], _ => by
    intro x hx
    simp only [CallArguments.parameters, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact plain_undef
    · exact parameters_plain n (by simp) x hx
  | n + 1, a :: args, ha => by
    intro x hx
    simp only [CallArguments.parameters, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha _ (by simp)
    · exact parameters_plain n (fun y hy => ha y (by simp [hy])) x hx

/-- **Invoking graph code** yields a run of its code at plain slots. -/
theorem graphEntry_wok {n : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {s : Nat} {caps : List Tm} {self : Tm} {rest : Bool} {comp : ComponentTag} {recv : Tm} {args : List Tm}
    (hE : ∀ e ∈ E, WOk e) (hc : ∀ x ∈ caps, Plain x) (hs : Plain self) (hr : Plain recv)
    (ha : ∀ x ∈ args, Plain x) :
    WOk (CallArguments.graphEntry n E K s caps self rest comp recv args) ∧
      writesK (CallArguments.graphEntry n E K s caps self rest comp recv args) = [] := by
  have hp := parameters_plain n ha
  have hL : ∀ x ∈ recv :: CallArguments.parameters n args ++ (caps ++ [self]), Plain x := by
    intro x hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | hx | rfl
    · exact hr
    · exact hp x hx
    · exact hc x hx
    · exact hs
  cases rest with
  | false =>
    simp only [CallArguments.graphEntry, WOk, writesK, wOks_iff, plainArgs_iff]
    exact ⟨⟨hE, hL, trivial, trivial⟩, trivial⟩
  | true =>
    simp only [CallArguments.graphEntry, WOk, writesK, wOks_iff, plainArgs_iff, writesKs_eq, List.append_nil]
    refine ⟨⟨fun x hx => (ha x (List.mem_of_mem_drop hx)).2, hE, ?_, trivial, trivial⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, trivial⟩
      · exact hL x hx
    · simp only [List.flatMap_eq_nil_iff]
      exact fun x hx => (ha x (List.mem_of_mem_drop hx)).1

theorem set_wok {xs : List Tm} {i : Nat} {a' : Tm} (hx : ∀ x ∈ xs, WOk x) (ha : WOk a') :
    ∀ x ∈ xs.set i a', WOk x := fun x hx' => (List.mem_or_eq_of_mem_set hx').elim (hx x) (· ▸ ha)

theorem set_writes {xs : List Tm} {i : Nat} {a a' : Tm} (hai : xs[i]? = some a) (ha : writesK a' ⊆ writesK a) :
    (xs.set i a').flatMap writesK ⊆ xs.flatMap writesK := by
  intro q hq
  obtain ⟨x, hx, hqx⟩ := List.mem_flatMap.mp hq
  rcases List.mem_or_eq_of_mem_set hx with hx | he
  · exact List.mem_flatMap.mpr ⟨x, hx, hqx⟩
  · exact List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? hai, ha (he ▸ hqx)⟩

/-- **Every step keeps the invariant** (proved, by induction on the step):
the term it steps to meets it, the heap stays plain, and the writes the
term may still perform are among those of the term it stepped from. -/
theorem step_wok {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hh : HeapW h) (ht : WOk t) :
    WOk t' ∧ HeapW h' ∧ writesK t' ⊆ writesK t := by
  induction hs with
  | callArg _ _ hai _ _ ih =>
    simp only [WOk, wOks_iff, writesK, writesKs_eq] at ht ⊢
    obtain ⟨w, hw, hk⟩ := ih hh (ht.2.2 _ (List.mem_of_getElem? hai))
    refine ⟨⟨ht.1, ht.2.1, set_wok ht.2.2 w⟩, hw, ?_⟩
    have := set_writes hai hk
    intro q hq; simp only [List.mem_append] at hq ⊢; grind
  | letV hv =>
    simp only [WOk] at ht
    refine ⟨(subst_wok (Plain.of_val hv ht.1) _ 0).1 ht.2, hh, ?_⟩
    rw [(subst_wok (Plain.of_val hv ht.1) _ 0).2]; intro q hq; simp only [writesK, List.mem_append]; exact .inr hq
  | callBound _ _ =>
    simp only [WOk, wOks_iff, plainArgs_iff, Plain] at ht
    obtain ⟨⟨⟨ht0, ht1⟩, ⟨hr0, hr1⟩, hp⟩, _, hargs⟩ := ht
    refine ⟨?_, hh, ?_⟩
    · simp only [WOk, wOks_iff, List.mem_append]
      exact ⟨ht1, hr1, fun x hx => hx.elim (fun hx => (hp x hx).2) (hargs x)⟩
    · intro q hq
      simp only [writesK, writesKs_eq, List.flatMap_append, List.mem_append, ht0, hr0,
        List.not_mem_nil, false_or] at hq ⊢
      rcases hq with hq | hq
      · obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
        rw [(hp x hx).1] at hq; cases hq
      · exact .inr hq
  | callSpread _ _ he _ hr =>
    subst he
    simp only [WOk, wOks_iff, List.mem_append, List.mem_cons] at ht
    have hv := readElems_plain hh hr
    refine ⟨?_, hh, ?_⟩
    · simp only [WOk, wOks_iff, List.mem_append]
      refine ⟨ht.1, ht.2.1, fun x hx => ?_⟩
      rcases hx with (hx | hx) | hx
      · exact ht.2.2 x (.inl hx)
      · exact (hv x hx).2
      · exact ht.2.2 x (.inr (.inr hx))
    · intro q hq
      simp only [writesK, writesKs_eq, List.flatMap_append, List.flatMap_cons, List.mem_append] at hq ⊢
      rcases hq with (hq | hq) | ((hq | hq) | hq)
      · exact .inl (.inl hq)
      · exact .inl (.inr hq)
      · exact .inr (.inl hq)
      · obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
        rw [(hv x hx).1] at hq; cases hq
      · exact .inr (.inr (.inr hq))
  | constructSpread _ he _ hr =>
    subst he
    simp only [WOk, wOks_iff, List.mem_append, List.mem_cons] at ht
    have hv := readElems_plain hh hr
    refine ⟨?_, hh, ?_⟩
    · simp only [WOk, wOks_iff, List.mem_append]
      refine ⟨ht.1, fun x hx => ?_⟩
      rcases hx with (hx | hx) | hx
      · exact ht.2 x (.inl hx)
      · exact (hv x hx).2
      · exact ht.2 x (.inr (.inr hx))
    · intro q hq
      simp only [writesK, writesKs_eq, List.flatMap_append, List.flatMap_cons, List.mem_append] at hq ⊢
      rcases hq with hq | ((hq | hq) | hq)
      · exact .inl hq
      · exact .inr (.inl hq)
      · obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
        rw [(hv x hx).1] at hq; cases hq
      · exact .inr (.inr (.inr hq))
  | arrSpread he _ hr =>
    subst he
    simp only [WOk, wOks_iff, List.mem_append, List.mem_cons] at ht
    have hv := readElems_plain hh hr
    refine ⟨?_, hh, ?_⟩
    · simp only [WOk, wOks_iff, List.mem_append]
      intro x hx
      rcases hx with (hx | hx) | hx
      · exact ht x (.inl hx)
      · exact (hv x hx).2
      · exact ht x (.inr (.inr hx))
    · intro q hq
      simp only [writesK, writesKs_eq, List.flatMap_append, List.flatMap_cons, List.mem_append] at hq ⊢
      rcases hq with (hq | hq) | hq
      · exact .inl hq
      · obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
        rw [(hv x hx).1] at hq; cases hq
      · exact .inr (.inr hq)
  | @makeArg c _ _ _ _ _ _ _ hai _ _ ih =>
    cases c <;> simp only [WOk, wOks_iff, writesK, writesKs_eq] at ht ⊢
    all_goals first
      | (obtain ⟨w, hw, hk⟩ := ih hh (ht _ (List.mem_of_getElem? hai))
         exact ⟨set_wok ht w, hw, set_writes hai hk⟩)
      | (obtain ⟨w, hw, hk⟩ := ih hh (ht.2 _ (List.mem_of_getElem? hai))
         exact ⟨⟨ht.1, set_wok ht.2 w⟩, hw, set_writes hai hk⟩)
  | @makeFields c _ vs _ hv _ =>
    have hp : ∀ x ∈ vs, Plain x := fun x hx => Plain.of_val (hv x hx) (by
      cases c <;> simp only [WOk, wOks_iff] at ht
      all_goals first | exact ht x hx | exact ht.2 x hx)
    refine ⟨?_, HeapW.append (HeapW.append hh hp) (by simp [Plain, WOk, writesK]), by simp [writesK]⟩
    cases c <;> simp only [WOk] at ht ⊢
    all_goals first | trivial | exact ht.1
  | readField _ hl | readProto _ _ hl =>
    first
    | exact ⟨(hh.get hl).2, hh, by rw [(hh.get hl).1]; exact List.nil_subset _⟩
    | exact ⟨(hh.get hl).2, hh, by simp only [writesK]; rw [(hh.get hl).1]; exact List.nil_subset _⟩
  | indexField _ _ hl =>
    exact ⟨(hh.get hl).2, hh, by rw [(hh.get hl).1]; exact List.nil_subset _⟩
  | indexProto _ _ _ hl =>
    simp only [WOk] at ht
    refine ⟨⟨(hh.get hl).2, ht.2⟩, hh, ?_⟩
    have := (hh.get hl).1
    intro q hq; simp_all [writesK]
  | writeField hv =>
    simp only [WOk] at ht
    exact ⟨trivial, hh.set (Plain.of_val hv ht.2) _, List.nil_subset _⟩
  | testV _ => exact ⟨by split <;> trivial, hh, by split <;> exact List.nil_subset _⟩
  | iteT | iteF =>
    simp only [WOk] at ht
    first
    | exact ⟨ht.2.1, hh, fun q hq => by simp only [writesK, List.mem_append]; exact .inl (.inr hq)⟩
    | exact ⟨ht.2.2, hh, fun q hq => by simp only [writesK, List.mem_append]; exact .inr hq⟩
  | arithV hb =>
    obtain ⟨_, _, hv⟩ := binop_result hb
    rcases hv with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨trivial, hh, List.nil_subset _⟩
  | arrAlloc hv _ =>
    simp only [WOk, wOks_iff] at ht
    exact ⟨trivial, hh.append fun x hx => Plain.of_val (hv x hx) (ht x hx), List.nil_subset _⟩
  | arrAllocThrow _ _ | arithThrow _ | lenStrThrow _ =>
    exact ⟨trivial, hh.append (by simp [Plain, WOk, writesK]), by simp [thrownError, writesK]⟩
  | elemRead _ hl => exact ⟨(hh.get hl).2, hh, by rw [(hh.get hl).1]; exact List.nil_subset _⟩
  | elemStr =>
    refine ⟨?_, hh, ?_⟩ <;> (unfold codeUnitAt; split) <;> first | trivial | exact List.nil_subset _
  | setPresent hv =>
    simp only [WOk] at ht
    exact ⟨trivial, hh.set (Plain.of_val hv ht.2.2) _, List.nil_subset _⟩
  | setGrow hv =>
    simp only [WOk] at ht
    exact ⟨trivial, hh.append (by simpa using Plain.of_val hv ht.2.2), List.nil_subset _⟩
  | mergeV _ _ hm =>
    have hp : ∀ p ∈ _, Plain (Prod.snd p) := fun p hp => by
      rcases mergeParts_vals hm p hp with he | ⟨hm, hv⟩ | ⟨_, he⟩
      · rw [he]; exact plain_undef
      · exact hh _ hm
      · rw [he]; exact ⟨rfl, trivial⟩
    refine ⟨?_, hh, ?_⟩
    · simp only [WOk, wOks_iff, List.mem_map]
      rintro _ ⟨p, hp', rfl⟩; exact (hp p hp').2
    · intro q hq
      simp only [writesK, writesKs_eq, List.flatMap_map, List.mem_flatMap] at hq
      obtain ⟨p, hp', hq⟩ := hq
      rw [(hp p hp').1] at hq; cases hq
  | callGraph hr hargs _ =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht
    refine (fun hg => ⟨hg.1, hh, by rw [hg.2]; exact List.nil_subset _⟩)
      (graphEntry_wok ht.1.1 ht.1.2 ⟨rfl, ?_⟩ (Plain.of_val hr ht.2.1) (fun x hx => Plain.of_val (hargs x hx) (ht.2.2 x hx)))
    simp only [WOk, wOks_iff, plainArgs_iff]; exact ht.1
  | constructGraph hargs =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht
    refine (fun hg => ⟨hg.1, hh, by rw [hg.2]; exact List.nil_subset _⟩)
      (graphEntry_wok ht.1.1 ht.1.2 ⟨rfl, ?_⟩ plain_undef (fun x hx => Plain.of_val (hargs x hx) (ht.2 x hx)))
    simp only [WOk, wOks_iff, plainArgs_iff]; exact ht.1
  | gotoEnter he hk =>
    rename_i E l e K k x h L d comp
    simp only [WOk, wOks_iff, plainArgs_iff] at ht ⊢
    have hwe := ht.1 _ (List.mem_of_getElem? he)
    have hi := (instantiate_wok (envOf_plain ht.2.1 ht.2.2) e 0).2
    refine ⟨⟨?_, (instantiate_wok (envOf_plain ht.2.1 ht.2.2) e 0).1 hwe, ht.1, ht.2.1, ht.2.2⟩, hh, List.nil_subset _⟩
    rw [hi]
    intro q hq; exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? he, hq⟩
  | frameC _ ih =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht ⊢
    obtain ⟨w, hw, hk⟩ := ih hh ht.2.1
    exact ⟨⟨hk.trans ht.1, w, ht.2.2⟩, hw, List.nil_subset _⟩
  | frameRet hv =>
    simp only [WOk] at ht
    exact ⟨ht.2.1, hh, by rw [writesK_val hv]; exact List.nil_subset _⟩
  | frameRaise hr =>
    simp only [WOk] at ht
    have hp := raises_plain hr ht.2.1
    exact ⟨hp.2, hh, by simp only [writesK]; rw [hp.1]; exact List.nil_subset _⟩
  | frameHandle hr =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht
    have hp := raises_plain hr ht.2.1
    simp only [WOk, wOks_iff, plainArgs_iff]
    refine ⟨⟨ht.2.2.1, (envMap_plain ?_ ht.2.2.2.2).1, (envMap_plain ?_ ht.2.2.2.2).2⟩, hh, List.nil_subset _⟩
    all_goals
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact ht.2.2.2.1 x hx
  | frameBind hv | frameTag hv =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht ⊢
    refine ⟨⟨ht.2.2.1, (envMap_plain ?_ ht.2.2.2.2).1, (envMap_plain ?_ ht.2.2.2.2).2⟩, hh, List.nil_subset _⟩
    all_goals
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Plain.of_val hv ht.2.1
      · exact ht.2.2.2.1 x hx
  | frameEffect | frameYes | frameNo =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht ⊢
    exact ⟨⟨ht.2.2.1, (envMap_plain ht.2.2.2.1 ht.2.2.2.2).1, (envMap_plain ht.2.2.2.1 ht.2.2.2.2).2⟩, hh,
      List.nil_subset _⟩
  | frameYesBind | frameNoBind =>
    simp only [WOk, wOks_iff, plainArgs_iff] at ht ⊢
    refine ⟨⟨ht.2.2.1, (envMap_plain ?_ ht.2.2.2.2).1, (envMap_plain ?_ ht.2.2.2.2).2⟩, hh, List.nil_subset _⟩
    all_goals
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, trivial⟩
      · exact ht.2.2.2.1 x hx
  | makeKeyV _ _ =>
    simp only [WOk, wOks_iff, writesK, writesKs_eq] at ht ⊢
    exact ⟨by simpa using ht.2, hh, fun q hq => by simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hq; exact List.mem_append_right _ hq⟩
  | _ =>
    simp only [WOk, wOks_iff, writesK, writesKs_eq] at ht ⊢
    first
    | (rename_i ih; obtain ⟨w, hw, hk⟩ := ih hh (by grind)
       refine ⟨by grind, hw, ?_⟩
       intro q hq; (try simp only [List.mem_append] at hq ⊢); grind)
    | (refine ⟨by first | trivial | grind, by first | exact hh | grind, ?_⟩
       intro q hq; (try simp only [writesK] at hq ⊢); (try simp only [List.mem_append] at hq ⊢)
       first | simp at hq | grind)
    | fail "LEFT"

/-! ## The active redex's writes -/

/-- **The charges of a frame**: those of its code, the kinds its node
expressions' writes may change; `K₀` outside every frame. -/
def frameKinds (K₀ : List (Option Verification.Kind)) : Option FrameKey → List (Option Verification.Kind)
  | none => K₀
  | some key => codeKinds key.1.1

/-- **The active redex's writes are its frame's charges** (proved, by
induction on the term): in a term meeting the invariant whose writes are
among the charges of the frame `cur` around it, the writes of the term the
next step reduces are among the charges of the innermost frame around it. -/
theorem active_writes (K₀ : List (Option Verification.Kind)) (t : Tm) :
    ∀ cur, WOk t → writesK t ⊆ frameKinds K₀ cur →
      writesK (activeFrame cur t).2 ⊆ frameKinds K₀ (activeFrame cur t).1 := by
  have hlist : ∀ (xs : List Tm) (t₀ : Tm) cur, (∀ x ∈ xs, ∀ cur, WOk x → writesK x ⊆ frameKinds K₀ cur →
      writesK (activeFrame cur x).2 ⊆ frameKinds K₀ (activeFrame cur x).1) →
      (∀ x ∈ xs, WOk x) → (∀ x ∈ xs, writesK x ⊆ frameKinds K₀ cur) → writesK t₀ ⊆ frameKinds K₀ cur →
      writesK (activeArgs cur t₀ xs).2 ⊆ frameKinds K₀ (activeArgs cur t₀ xs).1 := by
    intro xs t₀ cur ih hw hk h₀
    rcases activeArgs_split (cur := cur) (t := t₀) xs with ⟨he, _⟩ | ⟨x, hx, he, _⟩
    · rw [he]; exact h₀
    · rw [he]; exact ih x hx cur (hw x hx) (hk x hx)
  induction t using Tm.induct with
  | frame E K t L d k x comp _ iht _ _ =>
    intro cur hw _
    simp only [WOk] at hw
    simp only [activeFrame]
    exact iht _ hw.2.1 hw.1
  | invoke f r args ihf ihr iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    split
    · exact ihf cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihr cur hw.2.1 (fun q hq => hk (by simp [hq]))
      · exact hlist _ _ cur iha hw.2.2
          (fun x hx q hq => hk (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hq⟩)))
          (by simpa [writesK, writesKs_eq] using hk)
  | construct f args ihf iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    split
    · exact ihf cur hw.1 (fun q hq => hk (by simp [hq]))
    · exact hlist _ _ cur iha hw.2
        (fun x hx q hq => hk (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hq⟩)))
          (by simpa [writesK, writesKs_eq] using hk)
  | letE a b iha _ =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · exact hk
  | makeBound t r pre ns args _ _ _ iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    exact hlist _ _ cur iha hw.2 (fun x hx q hq => hk (by simp only [List.mem_flatMap]; exact ⟨x, hx, hq⟩))
      (by simpa [writesK, writesKs_eq] using hk)
  | alloc ns args iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    exact hlist _ _ cur iha hw (fun x hx q hq => hk (by simp only [List.mem_flatMap]; exact ⟨x, hx, hq⟩))
      (by simpa [writesK, writesKs_eq] using hk)
  | makeView s f n ns args iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    exact hlist _ _ cur iha hw (fun x hx q hq => hk (by simp only [List.mem_flatMap]; exact ⟨x, hx, hq⟩))
      (by simpa [writesK, writesKs_eq] using hk)
  | makeGraph n E K s caps k r comp ns args _ _ iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    exact hlist _ _ cur iha hw.2 (fun x hx q hq => hk (by simp only [List.mem_flatMap]; exact ⟨x, hx, hq⟩))
      (by simpa [writesK, writesKs_eq] using hk)
  | arrLit inits iha =>
    intro cur hw hk
    simp only [WOk, wOks_iff] at hw
    simp only [writesK, writesKs_eq] at hk
    simp only [activeFrame]
    exact hlist _ _ cur iha hw (fun x hx q hq => hk (by simp only [List.mem_flatMap]; exact ⟨x, hx, hq⟩))
      (by simpa [writesK, writesKs_eq] using hk)
  | read f a ih =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact ih cur hw (fun q hq => hk (by simp [hq]))
    · exact hk
  | test k a ih =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact ih cur hw (fun q hq => hk (by simp [hq]))
    · exact hk
  | lenOf a ih =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact ih cur hw (fun q hq => hk (by simp [hq]))
    · exact hk
  | spread a ih =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact ih cur hw (fun q hq => hk (by simp [hq]))
    · exact hk
  | throw a ih =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact ih cur hw (fun q hq => hk (by simp [hq]))
    · exact hk
  | index a b iha ihb =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihb cur hw.2 (fun q hq => hk (by simp [hq]))
      · exact hk
  | write f a b iha ihb =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihb cur hw.2 (fun q hq => hk (by simp [hq]))
      · exact hk
  | arith op a b iha ihb =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihb cur hw.2 (fun q hq => hk (by simp [hq]))
      · exact hk
  | elemAt a b iha ihb =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihb cur hw.2 (fun q hq => hk (by simp [hq]))
      · exact hk
  | merge d a b iha ihb =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihb cur hw.2 (fun q hq => hk (by simp [hq]))
      · exact hk
  | makeKey a b iha ihb =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihb cur hw.2 (fun q hq => hk (by simp [hq]))
      · exact hk
  | ite c a b ihc _ _ =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact ihc cur hw.1 (fun q hq => hk (by simp [hq]))
    · exact hk
  | setElem a i v iha ihi ihv =>
    intro cur hw hk
    simp only [WOk] at hw
    simp only [writesK] at hk
    simp only [activeFrame]
    split
    · exact iha cur hw.1 (fun q hq => hk (by simp [hq]))
    · split
      · exact ihi cur hw.2.1 (fun q hq => hk (by simp [hq]))
      · split
        · exact ihv cur hw.2.2 (fun q hq => hk (by simp [hq]))
        · exact hk
  | _ => intro cur _ hk; simpa [activeFrame] using hk

/-! ## The written location's kind -/

/-- **The active term's references are the term's** (proved, by induction
on the term). -/
theorem refs_active (t : Tm) : ∀ cur, ∀ r ∈ refs (activeFrame cur t).2, r ∈ refs t := by
  have hlist : ∀ (xs : List Tm) (t₀ : Tm) cur, (∀ x ∈ xs, ∀ cur, ∀ r ∈ refs (activeFrame cur x).2, r ∈ refs x) →
      ∀ r ∈ refs (activeArgs cur t₀ xs).2, r ∈ refs t₀ ∨ ∃ x ∈ xs, r ∈ refs x := by
    intro xs t₀ cur ih r hr
    rcases activeArgs_split (cur := cur) (t := t₀) xs with ⟨he, _⟩ | ⟨x, hx, he, _⟩
    · rw [he] at hr; exact .inl hr
    · rw [he] at hr; exact .inr ⟨x, hx, ih x hx cur r hr⟩
  induction t using Tm.induct with
  | frame E K t L d k x comp _ iht _ _ =>
    intro cur r hr; simp only [activeFrame] at hr; simp only [refs, refsArgs_eq, List.mem_append]
    exact .inl (.inl (.inr (iht _ r hr)))
  | invoke f r args ihf ihr iha | construct f args ihf iha | makeBound _ _ _ _ args _ _ _ iha
  | alloc _ args iha | makeView _ _ _ _ args iha | makeGraph _ _ _ _ _ _ _ _ _ args _ _ iha | arrLit args iha =>
    intro cur r' hr
    simp only [activeFrame] at hr
    repeat' split at hr
    all_goals first
      | (have := ihf _ r' hr; simp only [refs, refsArgs_eq, List.mem_append]; grind)
      | (have := ihr _ r' hr; simp only [refs, refsArgs_eq, List.mem_append]; grind)
      | (rcases hlist _ _ cur iha r' hr with h | ⟨x, hx, h⟩
         · exact h
         · simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; grind)
  | _ =>
    intro cur r' hr
    simp only [activeFrame] at hr
    repeat' split at hr
    all_goals first
      | exact hr
      | (rename_i ih; have := ih _ r' hr; simp only [refs, List.mem_append]; grind)
      | (simp only [refs, List.mem_append]; grind)

/-- **A writing redex writes a location of a kind its writes may change**
(proved): a field write under the key `k` writes a slot of a role of
`slotBound k` (`field_bound`), an element store an element cell, in a world
in which the redex's references are valid. -/
theorem slotKind_sound {n : Nat} {W : WorldT n} {l : Nat} {r : Tm} (hw : WriteRedex l r) (hr : RefsOk W r) :
    kindAt W l ∈ writesK r := by
  match r, hw with
  | .writeAt k (.objAt fs c oid) y, hw =>
    have hv : RefsOk W (.objAt fs c oid) := fun x hx => hr x (by simp only [refs, List.mem_append]; exact .inl hx)
    obtain ⟨role, hrole, hb⟩ := Footprints.field_bound hv (k := k) (l := l) (by simpa [Footprints.fieldsOf, WriteRedex] using hw)
    simp only [kindAt, hrole, Option.map_some, writesK, List.mem_append]
    exact .inl (.inl (roleKinds_mem hb))
  | .setElem (.arr ls) (.num b) y, hw =>
    have hv : RefsOk W (.arr ls) := fun x hx => hr x (by simp only [refs, List.mem_append]; exact .inl (.inl hx))
    have hrole := RefsOk_arr_iff.mp hv l (Kinds.elemLoc_mem (by simpa [WriteRedex] using hw))
    simp [kindAt, hrole, Role.kind, writesK]

/-- **A step's changes are its code's charges** (proved): at a step from a
term meeting the invariant whose writes outside every frame are among
`K₀`, with valid references, every old location the step changes has a
kind among the charges of the innermost frame's code: the step writes it at
its active redex (`step_writes_active`), of a kind that redex's writes may
change (`slotKind_sound`), which are its frame's charges
(`active_writes`). -/
theorem step_kind_charged {K₀ : List (Option Verification.Kind)} {h h' : Heap} {t t' : Tm}
    (hs : Step h t h' t') (hw : WOk t) (hk : writesK t ⊆ K₀) {n : Nat} {W : WorldT n} (hr : RefsOk W t)
    {l : Nat} {v : Val} (hv : h[l]? = some v) (hne : h'[l]? ≠ some v) :
    kindAt W l ∈ frameKinds K₀ (activeFrame none t).1 :=
  active_writes K₀ t none hw hk
    (slotKind_sound (step_writes_active hs hv hne none) fun x hx => hr x (refs_active t none x hx))

/-! ## The protocol at a charged part -/

/-- **A charged part changes by any change** (proved): at a part whose kind
the charges hold and whose site, where local, the held set holds, the
protocol from charges is `any`. -/
theorem probeProtocol_charged {P : Package} [DecidableEq P.Site] [Hashable P.Site]
    [LawfulHashable (Option P.Site)] {K : List (Option Verification.Kind)} {held : Sites P} {p : Part P}
    (hk : p.kind ∈ K) (hl : p.site.any (fun s => P.mark s = .local) = true → p.site ∈ held) :
    probeProtocol K held p = .any := by
  simp only [probeProtocol]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have := hl hc.1
    simp [Std.HashSet.contains_ofList, this] at hc
  · simp [hk]

/-- **A step of charged code is within the protocol from charges**
(proved, `step_kind_charged`, `probeProtocol_charged`): at a step from a
term meeting the invariant, with valid references, whose innermost frame's
code's charges are among `K`, and whose every changed old location of a
local site below `b` has a site the held set holds (what the local lemma
gives), every location of `R_P` below `b` changes within the protocol from
the charges `K` and the held set. -/
theorem stepWithin_charged {P : Package} [DecidableEq P.Site] [Hashable P.Site] [LawfulHashable (Option P.Site)]
    {K₀ K : List (Option Verification.Kind)} {held : Sites P} {b : Nat} {st st' : St P} {t t' : Tm}
    (hs : Step st.s.h t st'.s.h t') (hw : WOk t) (hk : writesK t ⊆ K₀) (hr : RefsOk st.s.W t)
    (hK : frameKinds K₀ (activeFrame none t).1 ⊆ K)
    (hloc : ∀ l v, l < b → st.g.InR l → st.s.h[l]? = some v → st'.s.h[l]? ≠ some v →
      (st.g.site l).any (fun s => P.mark s = .local) = true → st.g.site l ∈ held) :
    StepWithin (probeProtocol K held) b st st' := by
  intro l v hb hR hv
  have hl' : l < st'.s.h.length :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hv).1 (Footprints.step_length_le hs)
  obtain ⟨v', hv'⟩ : ∃ v', st'.s.h[l]? = some v' := ⟨_, List.getElem?_eq_getElem hl'⟩
  refine ⟨v', hv', ?_⟩
  by_cases he : v' = v
  · subst he; exact Footprints.Change.Holds.refl _ _ _
  · have hne : st'.s.h[l]? ≠ some v := by rw [hv']; exact fun h => he (Option.some.inj h)
    rw [probeProtocol_charged (hK (step_kind_charged hs hw hk hr hv hne)) (hloc l v hb hR hv hne)]
    trivial

/-- A part of lowered code a closure or a bound function holds, a variable
or a primitive value, is plain. -/
theorem CodePart.plain {t : Tm} (h : CodePart t) : Plain t := by
  rcases h with ⟨i, rfl⟩ | hp
  · exact ⟨rfl, trivial⟩
  · cases t <;> simp_all [primVal, Plain, writesK, WOk]

/-- **Lowered code meets the residual invariant** (proved, by induction on
the term): it holds no run, and the parts of the closures and bound
functions it creates are variables or primitive values. -/
theorem lowered_wok {P : Package} {Fl : Flow P} (e : Tm) : Lowered Fl e → WOk e := by
  induction e using Tm.induct with
  | makeBound t r pre ns args _ _ _ iha =>
    intro h
    simp only [Lowered, loweredArgs_iff] at h
    simp only [WOk, wOks_iff, plainArgs_iff]
    exact ⟨⟨(CodePart.plain h.1), (CodePart.plain h.2.1), fun x hx => CodePart.plain (h.2.2.1 x hx)⟩,
      fun x hx => iha x hx (h.2.2.2 x hx)⟩
  | makeGraph n E K s caps k r comp ns args ihE _ iha =>
    intro h
    simp only [Lowered, loweredArgs_iff] at h
    simp only [WOk, wOks_iff, plainArgs_iff]
    exact ⟨⟨fun x hx => ihE x hx (h.2.1 x hx), fun x hx => CodePart.plain (h.2.2.1 x hx)⟩,
      fun x hx => iha x hx (h.2.2.2 x hx)⟩
  | _ =>
    intro h
    simp only [Lowered, loweredArgs_iff] at h
    try simp only [WOk, wOks_iff]
    try grind

/-! ## Along the frame's executions -/

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **The residual invariant at every reached state** (proved, `step_wok`
along the execution): from calls whose term meets it at a heap of plain
values, every reached state's term meets it at a heap of plain values. -/
theorem wok_reached
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → WOk a.1.t ∧ HeapW a.1.s.h)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : WOk b.1.t ∧ HeapW b.1.s.h := by
  obtain ⟨a, n, hc, hs, hex⟩ := hb
  refine hex.carry (r := fun x : Conf × Ghost (fr.F.at fr.C) => WOk x.1.t ∧ HeapW x.1.s.h) ?_ (hst a hc hs)
  intro x y _ hxy hx
  have := step_wok hxy.1.step hx.2 hx.1
  exact ⟨this.1, this.2.1⟩

end ClientFrame

end Verification.TolerantFrames.ReadOnly
