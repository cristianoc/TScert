import Verification.Paper.TolerantFrames.ReadOnlyLocalReach

/-! # Read-only handles: the layouts of a component's closures

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Charges", the discharge of
`local_reach`'s premises). The closure of sites $`\overline{S}`$ reads a
code's capture slots at the layout its closures have (`tokenCaps`, one
layout per code of the finite flow, `lay`); the local lemma's premises
hold where every closure of `C`'s code has its code's layout
(`LayDeep`), the set is closed under captures (`CapClosed`) and the
node expressions of the flow's codes hold no located value
(`CodesLowered`).

- **Layout provenance** (`layP q`): every closure a term holds or creates,
  in the code of its values and runs included, meets `q` at its code, tag
  and layout (its arity, rest, number of captures and entry label). A heap
  meets it (`HeapLay q`) when every value it holds does. **Every step
  keeps it** (`step_layP`): a step builds its result from the term's
  subterms, the code of the closures it calls and the heap's values, and
  allocating a closure keeps its layout.
- **The layouts of a flow** (`layAt`, `layQ`): a code's layout is the one
  `lay` gives its first entry; a closure of `C`'s code meets `layQ` where
  its layout is its code's. A value meeting it has `LayDeep`
  (`layDeep_of_layP`).
- **Along the frame's executions** (`ClientFrame.lay_reached`,
  `FrameCore.lay_program`, `lay_initial`, the draft's `layouts_reached`):
  every state reached from states meeting layout provenance meets it; an
  initial configuration does where the initialization's code does and the
  client is lowered source, which creates no closure of `C`'s code.
- **The closure check gives `CapClosed`** (`capClosed_of_lay`): a set
  passing `capClosedB` at `tokenCaps` is closed under captures at the
  layouts `lay` states, where every code's tokens are sites (`tokensSomeB`).
- **The flow's codes hold no located value**, decided (`codesLoweredB`,
  `codesLoweredB_sound`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-- **A closure's layout**: its arity, its rest, its number of captures and
its entry label. -/
abbrev Layout := Nat × Bool × Nat × Nat

/-! ## Layout provenance -/

mutual
/-- **Layout provenance**: every closure a term holds or creates meets `q`
at its code, tag and layout, the code of its values and runs included. -/
def layP (q : Code → ComponentTag → Layout → Bool) : Tm → Bool
  | .invoke f r args => layP q f && layP q r && layPs q args
  | .construct f args => layP q f && layPs q args
  | .letE a b => layP q a && layP q b
  | .objAt _ (.bound t r pre) _ => layP q t && layP q r && layPs q pre
  | .objAt _ (.graph ar E K s caps _ rest c) _ => q (E, K) c (ar, rest, caps.length, s) && layPs q E && layPs q caps
  | .makeAt (.bound t r pre) _ xs => layP q t && layP q r && layPs q pre && layPs q xs
  | .makeAt (.graph ar E K s caps _ rest c) _ xs =>
    q (E, K) c (ar, rest, caps.length, s) && layPs q E && layPs q caps && layPs q xs
  | .makeAt .absent _ xs => layPs q xs
  | .makeAt (.view _ _ _) _ xs => layPs q xs
  | .readAt _ a => layP q a
  | .indexAt a b => layP q a && layP q b
  | .writeAt _ a b => layP q a && layP q b
  | .test _ a => layP q a
  | .ite x a b => layP q x && layP q a && layP q b
  | .arith _ a b => layP q a && layP q b
  | .arrLit xs => layPs q xs
  | .elemAt a b => layP q a && layP q b
  | .setElem a b x => layP q a && layP q b && layP q x
  | .lenOf a => layP q a
  | .spread a => layP q a
  | .throw a => layP q a
  | .merge _ a b => layP q a && layP q b
  | .makeKey a b => layP q a && layP q b
  | .goto E _ _ L d _ => layPs q E && layPs q L && layP q d
  | .frame E _ t L d _ _ _ => layPs q E && layP q t && layPs q L && layP q d
  | _ => true
termination_by structural t => t

def layPs (q : Code → ComponentTag → Layout → Bool) : List Tm → Bool
  | [] => true
  | x :: xs => layP q x && layPs q xs
termination_by structural xs => xs
end

variable {q : Code → ComponentTag → Layout → Bool}

@[simp] theorem layPs_eq (q : Code → ComponentTag → Layout → Bool) (xs : List Tm) : layPs q xs = xs.all (layP q) := by
  induction xs <;> simp_all [layPs]

/-- **A heap meeting layout provenance**: every value it holds does. -/
def HeapLay (q : Code → ComponentTag → Layout → Bool) (h : Heap) : Prop := ∀ v ∈ h, layP q v = true

/-! ## Substitution, heaps and throws keep it -/

theorem subst_layP {a : Tm} (ha : layP q a = true) :
    ∀ (b : Tm) (j : Nat), layP q b = true → layP q (subst j a b) = true := by
  intro b
  induction b using Tm.induct
  all_goals intro j hb
  all_goals simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hb
  all_goals simp only [subst, layP, layPs_eq, substArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.length_map]
  all_goals first
    | (split <;> (try split) <;> first | rfl | exact ha)
    | grind

theorem instantiate_layP {ρ : Env} (hρ : ∀ i, layP q (ρ i) = true) :
    ∀ (b : Tm) (d : Nat), layP q b = true → layP q (instantiate d ρ b) = true := by
  intro b
  induction b using Tm.induct
  all_goals intro d hb
  all_goals simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hb
  all_goals simp only [instantiate, layP, layPs_eq, instantiateArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.length_map]
  all_goals first
    | (split <;> first | rfl | exact hρ _)
    | grind

theorem HeapLay.append {h xs : Heap} (hh : HeapLay q h) (hx : ∀ v ∈ xs, layP q v = true) : HeapLay q (h ++ xs) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hh v hv
  · exact hx v hv

theorem HeapLay.set {h : Heap} {l : Nat} {v : Tm} (hh : HeapLay q h) (hv : layP q v = true) :
    HeapLay q (h.set l v) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact hh x hx
  · exact hv

theorem HeapLay.get {h : Heap} {l : Nat} {v : Tm} (hh : HeapLay q h) (hl : h[l]? = some v) : layP q v = true :=
  hh v (List.mem_of_getElem? hl)

theorem readElems_layP {h : Heap} (hh : HeapLay q h) :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs → ∀ v ∈ vs, layP q v = true
  | [], vs, hr => by simp [readElems] at hr; subst hr; simp
  | none :: ls, vs, hr => by
    simp only [readElems, Option.map_eq_some_iff] at hr
    obtain ⟨ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rfl
    · exact readElems_layP hh hws v hv
  | some l :: ls, vs, hr => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨w, hw, ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hh.get hw
    · exact readElems_layP hh hws v hv

theorem mergeParts_layP {h : Heap} (hh : HeapLay q h) {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hm : mergeParts h d a b = some ps) : ∀ x ∈ ps.map Prod.snd, layP q x = true := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  rcases Verification.mergeParts_vals hm p hp with he | ⟨hm', -⟩ | ⟨u, he⟩
  · rw [he]; rfl
  · exact hh _ hm'
  · rw [he]; rfl

theorem layP_makeAt {c : CallCode} {ns : List PropKey} {xs : List Tm} :
    layP q (.makeAt c ns xs) = true ↔ layP q (.objAt [] c 0) = true ∧ ∀ x ∈ xs, layP q x = true := by
  cases c <;> simp [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true, and_assoc]

/-- **A thrown value meets layout provenance** where the throwing term
does. -/
theorem raises_layP {t v : Tm} (hr : Raises t v) (hp : layP q t = true) : layP q v = true := by
  induction hr
  case callArg ha _ _ ih =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ih (hp.2 _ (List.mem_of_getElem? ha))
  case constructArg ha _ _ ih =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ih (hp.2 _ (List.mem_of_getElem? ha))
  case makeArg ha _ _ ih =>
    exact ih ((layP_makeAt.mp hp).2 _ (List.mem_of_getElem? ha))
  case arrArg ha _ _ ih =>
    simp only [layP, layPs_eq, List.all_eq_true] at hp
    exact ih (hp _ (List.mem_of_getElem? ha))
  all_goals simp_all [layP]

theorem envMap_layP {m : Option (List Nat)} {L : List Tm} {d : Tm} (hL : ∀ x ∈ L, layP q x = true)
    (hd : layP q d = true) : (∀ x ∈ (envMap m L d).1, layP q x = true) ∧ layP q (envMap m L d).2 = true := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases envMap_mem (.inl hx) with hx | rfl
    · exact hL x hx
    · exact hd
  · rcases envMap_mem (m := m) (L := L) (d := d) (.inr rfl) with hx | hx
    · exact hL _ hx
    · rw [hx]; exact hd

theorem envMap_cons_layP {m : Option (List Nat)} {v : Tm} {L : List Tm} {d : Tm} (hv : layP q v = true)
    (hL : ∀ x ∈ L, layP q x = true) (hd : layP q d = true) :
    (∀ x ∈ (envMap m (v :: L) d).1, layP q x = true) ∧ layP q (envMap m (v :: L) d).2 = true :=
  envMap_layP (fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact hL x hx) hd

theorem graphEntry_layP {n : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {s : Nat} {caps : List Tm} {self : Tm} {rest : Bool} {comp : ComponentTag} {recv : Tm} {args : List Tm}
    (hE : ∀ x ∈ E, layP q x = true) (hc : ∀ x ∈ caps, layP q x = true) (hs : layP q self = true)
    (hr : layP q recv = true) (ha : ∀ x ∈ args, layP q x = true) :
    layP q (CallArguments.graphEntry n E K s caps self rest comp recv args) = true := by
  have hpar : ∀ x ∈ CallArguments.parameters n args, layP q x = true := fun x hx =>
    (Kinds.parameters_mem hx).elim (ha x) (fun h => h ▸ rfl)
  have hdrop : ∀ x ∈ args.drop n, layP q x = true := fun x hx => ha x (List.mem_of_mem_drop hx)
  have hv : layP q (.var 0) = true := rfl
  unfold CallArguments.graphEntry
  split <;> simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_append]
    <;> grind

/-! ## Every step keeps it -/

/-- **Every step keeps layout provenance** (proved, by induction on the
step): the result of a step and the heap after it meet `q` where the term
and the heap before it do. -/
theorem step_layP {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    layP q t = true → HeapLay q h → layP q t' = true ∧ HeapLay q h' := by
  induction hs
  all_goals intro hp hh
  case makeArg ha _ _ ih =>
    rw [layP_makeAt] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case makeFields =>
    rw [layP_makeAt] at hp
    refine ⟨?_, (hh.append hp.2).append (by simp [layP])⟩
    rename_i c _ _ _ _ _
    cases c <;> simp_all [layP]
  case callArg ha _ _ ih =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case constructArg ha _ _ ih =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case arrArg ha _ _ ih =>
    simp only [layP, layPs_eq, List.all_eq_true] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp _ (List.mem_of_getElem? ha)) hh
    exact ⟨all_set' hp h1, h2⟩
  -- A step inside an evaluation context.
  all_goals try (
    rename_i ih
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    have ⟨h1, h2⟩ := ih (by grind) hh
    exact ⟨by grind, h2⟩)
  -- A redex on an unchanged heap.
  all_goals try (
    refine ⟨?_, hh⟩
    simp_all [layP]
    done)
  case callSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_layP hh hre
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨⟨hp.1, by grind⟩, hh⟩
  case constructSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_layP hh hre
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨⟨hp.1, by grind⟩, hh⟩
  case arrSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_layP hh hre
    simp only [layP, layPs_eq, List.all_eq_true, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨by grind, hh⟩
  case readField hv => exact ⟨hh.get hv, hh⟩
  case elemRead hv => exact ⟨hh.get hv, hh⟩
  case indexField hv => exact ⟨hh.get hv, hh⟩
  case readProto hp' => exact ⟨by simp only [layP]; exact hh.get hp', hh⟩
  case indexProto hp' =>
    simp only [layP, Bool.and_eq_true] at hp ⊢
    exact ⟨⟨hh.get hp', hp.2⟩, hh⟩
  case writeField =>
    simp only [layP, Bool.and_eq_true] at hp
    exact ⟨rfl, hh.set hp.2⟩
  case setPresent =>
    simp only [layP, Bool.and_eq_true] at hp
    exact ⟨rfl, hh.set hp.2⟩
  case setGrow =>
    simp only [layP, Bool.and_eq_true] at hp
    exact ⟨rfl, hh.append (by simpa using hp.2)⟩
  case arrAlloc =>
    simp only [layP, layPs_eq, List.all_eq_true] at hp
    exact ⟨rfl, hh.append hp⟩
  case testV => exact ⟨by split <;> rfl, hh⟩
  case elemStr => exact ⟨by simp only [codeUnitAt]; split <;> rfl, hh⟩
  case arithV hb =>
    obtain ⟨-, -, hres⟩ := binop_result hb
    exact ⟨by rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl, hh⟩
  case mergeV hm =>
    simp only [layP, layPs_eq, List.all_eq_true]
    exact ⟨mergeParts_layP hh hm, hh⟩
  case callGraph =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ⟨graphEntry_layP (by grind) (by grind)
      (by simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true]; grind) (by grind) (by grind), hh⟩
  case constructGraph =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ⟨graphEntry_layP (by grind) (by grind)
      (by simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true]; grind) rfl (by grind), hh⟩
  case gotoEnter he _ =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    have henv : ∀ i, layP q (envOf _ _ i) = true := fun i => by
      rcases getD_mem_or _ i _ with h | h
      · simp only [envOf]; exact hp.1.2 _ h
      · simp only [envOf]; rw [h]; exact hp.2
    have hi := instantiate_layP henv _ 0 (hp.1.1 _ (List.mem_of_getElem? he))
    exact ⟨by grind, hh⟩
  case letV =>
    simp only [layP, Bool.and_eq_true] at hp
    exact ⟨subst_layP hp.1 _ 0 hp.2, hh⟩
  case frameHandle hr =>
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    have hv := raises_layP hr hp.1.1.2
    have hL := (List.forall_mem_cons (p := fun x => layP q x = true)).mpr ⟨hv, hp.1.2⟩
    have hm := envMap_layP (m := ‹ControlFlow.Target›.mapping) hL hp.2
    exact ⟨by grind, hh⟩
  case frameRaise hr =>
    simp only [layP, Bool.and_eq_true] at hp ⊢
    exact ⟨raises_layP hr hp.1.1.2, hh⟩
  -- A fresh error thrown.
  all_goals try exact ⟨by simp [layP, thrownError], hh.append (by simp [layP])⟩
  -- A run's next node, its environment mapped from the frame's.
  all_goals
    simp only [layP, layPs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    first
      | exact ⟨⟨⟨hp.1.1.1, (envMap_layP hp.1.2 hp.2).1⟩, (envMap_layP hp.1.2 hp.2).2⟩, hh⟩
      | exact ⟨⟨⟨hp.1.1.1, (envMap_cons_layP hp.1.1.2 hp.1.2 hp.2).1⟩, (envMap_cons_layP hp.1.1.2 hp.1.2 hp.2).2⟩, hh⟩
      | exact ⟨⟨⟨hp.1.1.1, (envMap_cons_layP rfl hp.1.2 hp.2).1⟩, (envMap_cons_layP rfl hp.1.2 hp.2).2⟩, hh⟩

/-! ## The values a value holds, and lowered source -/

/-- **A value a term holds meets layout provenance** where the term does
(proved). -/
theorem vals_layP {ofC : ComponentTag → Bool} (t : Tm) :
    ∀ o, layP q t = true → ∀ u ∈ vals ofC o t, layP q u = true := by
  induction t using Tm.induct
  all_goals intro o hp u hu
  all_goals simp only [vals, valsArgs_eq] at hu
  all_goals (repeat' split at hu)
  all_goals (try simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    false_or, or_false] at hu)
  all_goals (try (subst hu; exact hp))
  all_goals (try (rcases hu with rfl | hu; exact hp))
  all_goals (try (subst hu; simp [layP]))
  all_goals (simp only [layP, layPs_eq, List.all_eq_true, Bool.and_eq_true] at hp; grind [layP])

/-- **A value a value holds meets layout provenance** (proved). -/
theorem Within.layP {P : Package} {v w : Val} (hw : Within P v w) (hv : ReadOnly.layP q v = true) :
    ReadOnly.layP q w = true := by
  induction hw with
  | refl => exact hv
  | cap hu _ ih =>
    simp only [ReadOnly.layP, layPs_eq, List.all_eq_true, Bool.and_eq_true] at hv
    exact ih (hv.2 _ hu)
  | code hu _ ih =>
    simp only [ReadOnly.layP, layPs_eq, List.all_eq_true, Bool.and_eq_true] at hv
    simp only [valsArgs_eq, List.mem_flatMap] at hu
    obtain ⟨e, he, hu⟩ := hu
    exact ih (vals_layP e true (hv.1.2 e he) _ hu)
  | bound hu _ ih =>
    simp only [ReadOnly.layP, layPs_eq, List.all_eq_true, Bool.and_eq_true] at hv
    simp only [List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · exact ih hv.1.1
    · exact ih hv.1.2
    · exact ih (hv.2 _ hu)

/-- A part of a closure's code holds no closure (proved). -/
theorem CodePart.layP {t : Tm} (h : CodePart t) : ReadOnly.layP q t = true := by
  rcases h with ⟨i, rfl⟩ | hp
  · rfl
  · cases t <;> simp_all [primVal, ReadOnly.layP]

/-- **Lowered source meets layout provenance** where `q` holds at outside
code (proved, by induction on the term): every closure lowered source
creates is outside code. -/
theorem layP_of_loweredSrc {ofC : ComponentTag → Bool} (hq : ∀ m c l, ofC c = false → q m c l = true) :
    ∀ (t : Tm), LoweredSrc ofC t → layP q t = true := by
  intro t
  induction t using Tm.induct
  all_goals intro h
  all_goals simp only [LoweredSrc, loweredSrcArgs_iff] at h
  all_goals simp only [layP, layPs_eq, List.all_eq_true, Bool.and_eq_true]
  all_goals first
    | trivial
    | grind [CodePart.layP]

/-! ## The layouts of a flow -/

section Flow
variable {P : Package} [DecidableEq P.Site]

/-- The first entry of a list at a key, read from the keys zipped with a
second list (proved, by induction on the lists): the entry of the first
list at that key and the second list's element beside it. -/
theorem look_zip {α β γ : Type} [DecidableEq α] : ∀ (xs : List (α × β)) (ys : List γ) {a : α} {c : γ},
    look a ((xs.map Prod.fst).zip ys) = some c → ∃ b, ((a, b), c) ∈ xs.zip ys ∧ look a xs = some b
  | [], _, _, _, h => by simp [look] at h
  | _ :: _, [], _, _, h => by simp [look] at h
  | (a', b') :: xs, c' :: ys, a, c, h => by
    by_cases ha : a' = a
    · subst ha
      simp only [look, List.map_cons, List.zip_cons_cons, List.find?_cons, decide_true, Option.map_some,
        Option.some.injEq] at h
      subst h
      exact ⟨b', by simp, by simp [look]⟩
    · simp only [look, List.map_cons, List.zip_cons_cons, List.find?_cons, ha, decide_false] at h
      obtain ⟨b, hm, hl⟩ := look_zip xs ys h
      refine ⟨b, by simp [hm], ?_⟩
      simpa [look, List.find?_cons, ha] using hl

/-- **A code's layout** in a flow: the one `lay` gives the code's first
entry (`look`, as `FFlow.ctxs` reads the code's contexts). -/
def layAt (F : FFlow P) (lay : List Layout) (m : Code) : Option Layout := look m ((F.codes.map Prod.fst).zip lay)

/-- **A closure has its code's layout**, decided: a closure of outside code
has any; one of `C`'s code the one `layAt` gives. -/
def layQ (F : FFlow P) (lay : List Layout) : Code → ComponentTag → Layout → Bool :=
  fun m c l => !P.ofC c || decide (layAt F lay m = some l)

omit [DecidableEq P.Site] in
/-- **A value meeting layout provenance at a flow's layouts has them in
depth** (proved): every closure of `C`'s code it holds has its code's
layout. -/
theorem layDeep_of_layP {F : FFlow P} {lay : List Layout} {v : Val} (h : layP (layQ F lay) v = true) :
    LayDeep P (fun m l => layAt F lay m = some l) v := by
  intro w hw fs ar E K s caps k rest comp oid he hc
  have hw' := Within.layP hw h
  subst he
  simp only [layP, layQ, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq, Bool.and_eq_true] at hw'
  exact hw'.1.1

/-- **Tokens are sites**, decided: every context of every code of the flow
has a token. -/
def tokensSomeB (F : FFlow P) : Bool := F.codes.all fun mc => mc.2.all fun c => c.2.tok.isSome

omit [DecidableEq P.Site] in
theorem tokensSomeB_sound {F : FFlow P} (h : tokensSomeB F = true) :
    ∀ m cs, (m, cs) ∈ F.codes → ∀ c ∈ cs, c.2.tok.isSome = true := by
  simp only [tokensSomeB, List.all_eq_true] at h
  exact fun m cs hm c hc => h (m, cs) hm c hc

variable [Hashable P.Site]

omit [Hashable P.Site] in
/-- **The closure check gives closure under captures at the flow's
layouts** (proved, the draft's `capClosed_of_lay`): a set passing
`capClosedB` at `tokenCaps` holds, for each code whose token it holds, the
sites of each capture slot at its entry at the layout `lay` gives the
code's first entry, which is where the code's proposals are read; every
token is a site. -/
theorem capClosed_of_lay {F : FFlow P} {lay : List Layout} {S T : Sites P}
    (h : capClosedB F (tokenCaps F lay) S T = true) (htok : tokensSomeB F = true) :
    CapClosed F.flow (fun m l => layAt F lay m = some l) T := by
  intro m ar rest nc s π hlay hπ hT j hj
  obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hπ
  obtain ⟨cs, hz, hcs⟩ := look_zip F.codes lay hlay
  have hctx : (entryCx, fc) ∈ cs := by
    have := FFlow.at_ctxs hfc
    simpa [FFlow.ctxs, hcs] using this
  have hsome := tokensSomeB_sound htok m cs (List.of_mem_zip hz).1 _ hctx
  refine Sub.trans ?_ ((capClosedB_sound h).2 _ hT).2
  intro x hx
  have hne : fc.tok.isNone = false := by cases e : fc.tok <;> simp_all
  simp only [tokenCaps, FCode.flow, hne, ite_false, Bool.false_eq_true]
  refine List.mem_flatMap.mpr ⟨((m, cs), (ar, rest, nc, s)), hz, ?_⟩
  have hany : cs.any (fun c => c.2.tok == fc.tok) = true := List.any_eq_true.mpr ⟨_, hctx, by simp⟩
  simp only [hany, ite_true, codeCaptureSites]
  exact List.mem_flatMap.mpr ⟨(entryCx, fc), hctx, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩⟩

/-- A spine with no cell, decided. -/
def spineB : Val → Bool
  | .arr ls => ls.all Option.isNone
  | _ => false

/-- **The flow's codes hold no located value**, decided: each value of
each node expression of each code the flow proposes for is a spine with no
cell. -/
def codesLoweredB (F : FFlow P) : Bool := F.codes.all fun mc => mc.1.1.all fun e => (vals allC true e).all spineB

omit [Hashable P.Site] in
/-- **The check is sound** (proved): the node expressions of every code
the flow proposes for hold no located value. -/
theorem codesLoweredB_sound {F : FFlow P} (h : codesLoweredB F = true) : CodesLowered F.flow := by
  intro m c π hπ e he x hx
  obtain ⟨fc, hfc, -⟩ := FFlow.code_at hπ
  obtain ⟨l, hl, -⟩ := FFlow.at_mem hfc
  simp only [codesLoweredB, List.all_eq_true] at h
  have := h _ hl e he x hx
  cases x <;> simp only [spineB, Bool.false_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at this
  exact ⟨_, rfl, this⟩

omit [Hashable P.Site] in
/-- **The local lemma's heap premise from the checks** (proved,
`heapDeep_of_heapInv`): a heap meeting the flow and layout provenance at
its layouts meets in depth a set passing the closure check. -/
theorem heapDeep_of_checks {F : FFlow P} {lay : List Layout} {S T : Sites P} {g : Ghost P} {h : Heap}
    (hT : capClosedB F (tokenCaps F lay) S T = true) (htok : tokensSomeB F = true) (hlow : codesLoweredB F = true)
    (hH : HeapInv F.flow g h) (hl : HeapLay (layQ F lay) h) : HeapDeep g.site T h :=
  heapDeep_of_heapInv (capClosed_of_lay hT htok) (codesLoweredB_sound hlow) hH
    (fun s hs => ((capClosedB_sound hT).2 s hs).1) (fun _ _ hw => layDeep_of_layP (hl.get hw))

omit [Hashable P.Site] in
/-- **The local lemma's root premise from the checks** (proved,
`deepIn_of_vj`): a value meeting a set within one passing the closure
check, and layout provenance at the flow's layouts, meets it in depth. -/
theorem deepIn_of_checks {F : FFlow P} {lay : List Layout} {S T S' : Sites P} {g : Ghost P} {n : Nat} {v : Val}
    (hT : capClosedB F (tokenCaps F lay) S T = true) (htok : tokensSomeB F = true) (hlow : codesLoweredB F = true)
    (hv : VJ F.flow g n S' v) (hS : Sub S' T) (hl : layP (layQ F lay) v = true) : DeepIn g.site T v :=
  deepIn_of_vj (capClosed_of_lay hT htok) (codesLoweredB_sound hlow) hv hS (layDeep_of_layP hl)

end Flow

/-! ## Along the frame's executions -/

namespace ClientFrame
variable {τ : Type} {fr : ClientFrame τ}

/-- **Layout provenance at every reached state** (proved, `step_layP` along
the execution, the draft's `layouts_reached`): from calls whose term and
heap meet it, every reached state's do. -/
theorem lay_reached
    (hst : ∀ (a : Conf × Ghost (fr.F.at fr.C)), fr.Call a.1.s.n a.1.s.W a.1.s.h a.1.t →
      fr.start a.1.s.n a.1.s.W a.1.s.h a.1.t a.2 → layP q a.1.t = true ∧ HeapLay q a.1.s.h)
    {b : Conf × Ghost (fr.F.at fr.C)} (hb : fr.Reached b) : layP q b.1.t = true ∧ HeapLay q b.1.s.h := by
  obtain ⟨a, n, hc, hs, hex⟩ := hb
  exact hex.carry (r := fun x : Conf × Ghost (fr.F.at fr.C) => layP q x.1.t = true ∧ HeapLay q x.1.s.h)
    (fun _ _ _ hxy hx => step_layP hxy.1.step hx.1 hx.2) (hst a hc hs)

end ClientFrame

namespace FrameCore
variable {τ : Type} {core : FrameCore τ}

/-- **Layout provenance along an execution** (proved, `step_layP` at each
step). -/
theorem lay_ex {r : Conf × Ghost (core.F.at core.C) → Prop} {n : Nat} {a b : Conf × Ghost (core.F.at core.C)}
    (hex : Ex core.KStep r n a b) (ha : layP q a.1.t = true ∧ HeapLay q a.1.s.h) :
    layP q b.1.t = true ∧ HeapLay q b.1.s.h :=
  hex.carry (r := fun x : Conf × Ghost (core.F.at core.C) => layP q x.1.t = true ∧ HeapLay q x.1.s.h)
    (fun _ _ _ hxy hx => step_layP hxy.1.step hx.1 hx.2) ha

/-- **Layout provenance at a public call** (proved, `lay_ex` along the
call's execution and its entering step): from initial configurations
meeting it, the state a public call enters meets it. -/
theorem lay_program {Init : Conf → Prop} {m : Code} {x₀ : Conf} {n : Nat} {x a₁ : Conf × Ghost (core.F.at core.C)}
    (hinit : ∀ x, Init x → layP q x.t = true ∧ HeapLay q x.s.h) (h : core.PublicCall Init m x₀ n x a₁) :
    layP q a₁.1.t = true ∧ HeapLay q a₁.1.s.h :=
  lay_ex h.ex (hinit x₀ h.1)

end FrameCore

/-- **An initial configuration meets layout provenance** (proved,
`layP_of_loweredSrc`): the initialization's run, its node expressions and
slots meeting it, and the client's lowered source, which creates closures
of outside code only. -/
theorem lay_initial {ofC : ComponentTag → Bool} (hq : ∀ m c l, ofC c = false → q m c l = true) {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat} {L : List Tm} {c : ComponentTag}
    {client : Tm} (hE : ∀ e ∈ E, layP q e = true) (hL : ∀ v ∈ L, layP q v = true) (hc : LoweredSrc ofC client) :
    layP q (.letE (.goto E K l L .undef c) client) = true := by
  simp only [layP, layPs_eq, List.all_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hE, hL⟩, trivial⟩, layP_of_loweredSrc hq client hc⟩

end Verification.TolerantFrames.ReadOnly
