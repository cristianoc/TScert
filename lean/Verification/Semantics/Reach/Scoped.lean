import Verification.Semantics.Reach.Steps

/-! # Closed terms stay closed

A step from a closed term over a closed heap gives a closed term over a
closed heap (`step_scoped`), and instantiating a closed environment closes
a term (`instantiate_scoped`). -/

namespace Verification.TolerantFrames.Reach

open Verification

theorem all_set' {P : Tm → Prop} {xs : List Tm} {i : Nat} {b : Tm} (h : ∀ x ∈ xs, P x) (hb : P b) :
    ∀ x ∈ xs.set i b, P x := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx
  · exact hb

/-- **A closed term at a greater depth** (proved). -/
theorem _root_.Verification.Scoped.mono {t : Tm} {d d' : Nat} (h : Scoped d t) (hd : d ≤ d') : Scoped d' t := by
  induction t using Tm.induct generalizing d d' <;> simp only [Scoped, scopedArgs_iff] at h ⊢
  case letE x b ihx ihb => exact ⟨ihx h.1 hd, ihb h.2 (by omega)⟩
  all_goals first
    | omega
    | trivial
    | grind

/-- **Substituting a closed value keeps a term closed below a depth**
(proved). -/
theorem subst_scoped {a : Tm} (ha : Scoped 0 a) :
    ∀ (b : Tm) (j d : Nat), Scoped (d + 1) b → j ≤ d → Scoped d (subst j a b) := by
  intro b
  induction b using Tm.induct
  all_goals intro j d hb hj
  all_goals simp only [Scoped, scopedArgs_iff, subst, substArgs_eq_map, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at hb ⊢
  case var i =>
    by_cases hij : i = j
    · subst hij; simp only [beq_self_eq_true, ite_true]; exact ha.mono (Nat.zero_le _)
    · have : (i == j) = false := by simp [hij]
      simp only [this, Bool.false_eq_true, ite_false]
      split <;> simp only [Scoped] <;> omega
  case letE x b ihx ihb => exact ⟨ihx j d hb.1 hj, ihb (j + 1) (d + 1) hb.2 (by omega)⟩
  all_goals grind

/-- **Instantiating at closed values closes a term below its depth**
(proved): every variable at or past the depth is replaced. -/
theorem instantiate_scoped {ρ : Env} (hρ : ∀ i, Scoped 0 (ρ i)) :
    ∀ (b : Tm) (d : Nat), Scoped d (instantiate d ρ b) := by
  intro b
  induction b using Tm.induct
  all_goals intro d
  all_goals simp only [Scoped, scopedArgs_iff, instantiate, instantiateArgs_eq_map, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  case var i =>
    split
    · simp only [Scoped]; omega
    · exact (hρ _).mono (Nat.zero_le _)
  all_goals grind

theorem readElems_scoped {h : Heap} (hh : ∀ v ∈ h, Scoped 0 v) :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs → ∀ v ∈ vs, Scoped 0 v
  | [], vs, hr => by intro v hv; simp [readElems] at hr; subst hr; cases hv
  | none :: ls, vs, hr => by
    simp only [readElems, Option.map_eq_some_iff] at hr
    obtain ⟨ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · trivial
    · exact readElems_scoped hh hws v hv
  | some l :: ls, vs, hr => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨w, hw, ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hh _ (List.mem_of_getElem? hw)
    · exact readElems_scoped hh hws v hv

theorem scoped_makeAt {c : CallCode} {ns : List PropKey} {xs : List Tm} :
    Scoped 0 (.makeAt c ns xs) ↔ Scoped 0 (.objAt [] c 0) ∧ ∀ x ∈ xs, Scoped 0 x := by
  cases c <;> simp [Scoped, scopedArgs_iff, and_assoc]

/-- **A thrown value is closed** where the throwing term is (proved). -/
theorem raises_scoped {t v : Tm} (hr : Raises t v) (hp : Scoped 0 t) : Scoped 0 v := by
  induction hr
  case callArg ha _ _ ih =>
    simp only [Scoped, scopedArgs_iff] at hp
    exact ih (hp.2.2 _ (List.mem_of_getElem? ha))
  case constructArg ha _ _ ih =>
    simp only [Scoped, scopedArgs_iff] at hp
    exact ih (hp.2 _ (List.mem_of_getElem? ha))
  case makeArg ha _ _ ih =>
    exact ih ((scoped_makeAt.mp hp).2 _ (List.mem_of_getElem? ha))
  case arrArg ha _ _ ih =>
    simp only [Scoped, scopedArgs_iff] at hp
    exact ih (hp _ (List.mem_of_getElem? ha))
  all_goals simp_all [Scoped]

theorem envMap_scoped {m : Option (List Nat)} {L : List Tm} {d : Tm}
    (hL : ∀ x ∈ L, Scoped 0 x) (hd : Scoped 0 d) :
    (∀ x ∈ (envMap m L d).1, Scoped 0 x) ∧ Scoped 0 (envMap m L d).2 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases envMap_mem (.inl hx) with hx | rfl
    · exact hL x hx
    · exact hd
  · rcases envMap_mem (m := m) (L := L) (d := d) (.inr rfl) with hx | hx
    · exact hL _ hx
    · rw [hx]; exact hd

theorem graphEntry_scoped {n : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {s : Nat} {caps : List Tm} {self : Tm}
    {rest : Bool} {comp : ComponentTag} {recv : Tm} {args : List Tm}
    (hc : ∀ x ∈ caps, Scoped 0 x) (hs : Scoped 0 self) (hr : Scoped 0 recv) (ha : ∀ x ∈ args, Scoped 0 x) :
    Scoped 0 (CallArguments.graphEntry n E K s caps self rest comp recv args) := by
  have hpar : ∀ x ∈ CallArguments.parameters n args, Scoped 0 x := fun x hx =>
    (Kinds.parameters_mem hx).elim (ha x) (fun h => h ▸ trivial)
  have hall : ∀ x ∈ recv :: CallArguments.parameters n args ++ (caps ++ [self]), Scoped 0 x := by
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with (rfl | hx) | hx | rfl | hx
    · exact hr
    · exact hpar x hx
    · exact hc x hx
    · exact hs
    · cases hx
  unfold CallArguments.graphEntry
  split
  · simp only [Scoped, scopedArgs_iff]
    exact ⟨hall, trivial⟩
  · simp only [Scoped, scopedArgs_iff]
    refine ⟨fun x hx => ha x (List.mem_of_mem_drop hx), fun x hx => ?_, trivial⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [Scoped]
    · exact (hall x hx).mono (Nat.zero_le _)

set_option maxHeartbeats 1000000 in
/-- **Every step keeps the term and the heap closed** (proved): a step
substitutes closed values, instantiates node expressions at closed
environments and stores closed values. -/
theorem step_scoped {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    Scoped 0 t → (∀ v ∈ h, Scoped 0 v) → Scoped 0 t' ∧ ∀ v ∈ h', Scoped 0 v := by
  have happ : ∀ {h xs : Heap}, (∀ v ∈ h, Scoped 0 v) → (∀ v ∈ xs, Scoped 0 v) → ∀ v ∈ h ++ xs, Scoped 0 v :=
    fun hh hx v hv => (List.mem_append.mp hv).elim (hh v) (hx v)
  have hset : ∀ {h : Heap} {l : Nat} {v : Tm}, (∀ v ∈ h, Scoped 0 v) → Scoped 0 v → ∀ x ∈ h.set l v, Scoped 0 x :=
    fun hh hv x hx => (List.mem_or_eq_of_mem_set hx).elim (hh x) (fun h => h ▸ hv)
  induction hs
  all_goals intro hp hh
  case makeArg ha _ _ ih =>
    rw [scoped_makeAt] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case makeFields =>
    rw [scoped_makeAt] at hp
    refine ⟨?_, happ (happ hh hp.2) (by simp [Scoped])⟩
    rename_i c _ _ _ _ _
    cases c <;> simp_all [Scoped]
  case callArg ha _ _ ih =>
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, hp.2.1, all_set' hp.2.2 h1⟩, h2⟩
  case constructArg ha _ _ ih =>
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case arrArg ha _ _ ih =>
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp _ (List.mem_of_getElem? ha)) hh
    exact ⟨all_set' hp h1, h2⟩
  -- A step inside an evaluation context.
  all_goals try (
    rename_i ih
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    have ⟨h1, h2⟩ := ih (by grind) hh
    exact ⟨by grind, h2⟩)
  -- A redex on an unchanged heap.
  all_goals try (
    refine ⟨?_, hh⟩
    simp_all [Scoped]
    done)
  case callSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_scoped hh hre
    simp only [Scoped, scopedArgs_iff, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨⟨hp.1, hp.2.1, by grind⟩, hh⟩
  case constructSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_scoped hh hre
    simp only [Scoped, scopedArgs_iff, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨⟨hp.1, by grind⟩, hh⟩
  case arrSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_scoped hh hre
    simp only [Scoped, scopedArgs_iff, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨by grind, hh⟩
  case readField hv => exact ⟨hh _ (List.mem_of_getElem? hv), hh⟩
  case elemRead hv => exact ⟨hh _ (List.mem_of_getElem? hv), hh⟩
  case indexField hv => exact ⟨hh _ (List.mem_of_getElem? hv), hh⟩
  case readProto hp' => exact ⟨by simp only [Scoped]; exact hh _ (List.mem_of_getElem? hp'), hh⟩
  case indexProto hp' =>
    simp only [Scoped] at hp ⊢
    exact ⟨⟨hh _ (List.mem_of_getElem? hp'), hp.2⟩, hh⟩
  case writeField =>
    simp only [Scoped] at hp
    exact ⟨trivial, hset hh hp.2⟩
  case setPresent =>
    simp only [Scoped] at hp
    exact ⟨trivial, hset hh hp.2.2⟩
  case setGrow =>
    simp only [Scoped] at hp
    exact ⟨by simp [Scoped], happ hh (by simpa using hp.2.2)⟩
  case arrAlloc =>
    simp only [Scoped, scopedArgs_iff] at hp
    exact ⟨trivial, happ hh hp⟩
  case testV => exact ⟨by split <;> trivial, hh⟩
  case elemStr => exact ⟨by simp only [codeUnitAt]; split <;> trivial, hh⟩
  case arithV hb =>
    obtain ⟨-, -, hres⟩ := binop_result hb
    exact ⟨by rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial, hh⟩
  case mergeV hm =>
    simp only [Scoped, scopedArgs_iff, List.mem_map]
    refine ⟨?_, hh⟩
    rintro x ⟨p, hp', rfl⟩
    rcases Verification.mergeParts_vals hm p hp' with he | ⟨hm', -⟩ | ⟨u, he⟩
    · rw [he]; trivial
    · exact hh _ hm'
    · rw [he]; trivial
  case callGraph =>
    simp only [Scoped, scopedArgs_iff] at hp
    exact ⟨graphEntry_scoped hp.1 (by simp only [Scoped, scopedArgs_iff]; exact hp.1) hp.2.1 hp.2.2, hh⟩
  case constructGraph =>
    simp only [Scoped, scopedArgs_iff] at hp
    exact ⟨graphEntry_scoped hp.1 (by simp only [Scoped, scopedArgs_iff]; exact hp.1) trivial hp.2, hh⟩
  case gotoEnter he _ =>
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    have henv : ∀ i, Scoped 0 (envOf _ _ i) := fun i => by
      rcases getD_mem_or _ i _ with h | h
      · simp only [envOf]; exact hp.1 _ h
      · simp only [envOf]; rw [h]; exact hp.2
    exact ⟨⟨instantiate_scoped henv _ 0, hp.1, hp.2⟩, hh⟩
  case letV =>
    simp only [Scoped] at hp
    exact ⟨subst_scoped hp.1 _ 0 0 hp.2 (Nat.le_refl _), hh⟩
  case frameHandle hr =>
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    have hv := raises_scoped hr hp.1
    have hL : ∀ x ∈ _ :: _, Scoped 0 x := (List.forall_mem_cons (p := fun x => Scoped 0 x)).mpr ⟨hv, hp.2.1⟩
    have hm := envMap_scoped (m := ‹ControlFlow.Target›.mapping) hL hp.2.2
    exact ⟨⟨hm.1, hm.2⟩, hh⟩
  case frameRaise hr =>
    simp only [Scoped] at hp ⊢
    exact ⟨raises_scoped hr hp.1, hh⟩
  case callBound =>
    simp only [Scoped, scopedArgs_iff, List.mem_append] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, fun x hx => hx.elim (hp.1.2.2 x) (hp.2.2 x)⟩, hh⟩
  -- A fresh error thrown.
  all_goals try exact ⟨by simp [Scoped, thrownError], happ hh (by simp [Scoped])⟩
  -- A run's next node, its environment mapped from the frame's.
  all_goals
    simp only [Scoped, scopedArgs_iff] at hp ⊢
    first
      | exact ⟨⟨(envMap_scoped hp.2.1 hp.2.2).1, (envMap_scoped hp.2.1 hp.2.2).2⟩, hh⟩
      | exact ⟨⟨(envMap_scoped (List.forall_mem_cons.mpr ⟨hp.1, hp.2.1⟩) hp.2.2).1,
          (envMap_scoped (List.forall_mem_cons.mpr ⟨hp.1, hp.2.1⟩) hp.2.2).2⟩, hh⟩
      | exact ⟨⟨(envMap_scoped (List.forall_mem_cons.mpr ⟨(show Scoped 0 Tm.tru from trivial), hp.2.1⟩) hp.2.2).1,
          (envMap_scoped (List.forall_mem_cons.mpr ⟨(show Scoped 0 Tm.tru from trivial), hp.2.1⟩) hp.2.2).2⟩, hh⟩
      | exact ⟨⟨(envMap_scoped (List.forall_mem_cons.mpr ⟨(show Scoped 0 Tm.fls from trivial), hp.2.1⟩) hp.2.2).1,
          (envMap_scoped (List.forall_mem_cons.mpr ⟨(show Scoped 0 Tm.fls from trivial), hp.2.1⟩) hp.2.2).2⟩, hh⟩

end Verification.TolerantFrames.Reach
