import Verification.Paper.TolerantFrames.ReadOnlyRuns

/-! # Read-only handles: the code a tag stands for

The note "Read-only frames" (`docs/drafts/readonly-frames-note/note.tex`,
Assumption "Clients": code outside a component enters it only through its
interface) and the draft "Read-only handles" (`docs/drafts/readonly-handles.md`,
"The framed claim"). A component's tag is ghost (`SameRun`): no reduction
reads it. The claim about a component's code reads a tag as naming code of
that component, so the executions it is about are those in which every code
carrying a tag of the component is the component's own.

- **Code provenance** (`prov ok`): every code a term holds, the code of
  each closure (`CallCode.graph`) and of each run (`Tm.goto`, `Tm.frame`),
  in the code of its values and runs included, meets `ok` at its tag. A heap
  meets it (`HeapProv ok`) when every value it holds does.
- **Every step keeps it** (`step_prov`): a step builds its result from the
  term's subterms, the code of the closures it calls and the values the heap
  holds, so every code of the result is a code of the term or of the heap,
  at the same tag. Code outside a component therefore creates no closure
  tagged with the component but one of the component's own codes. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification

/-! ## Code provenance -/

mutual
/-- **Code provenance**: every code a term holds meets `ok` at its tag, the
code of its values and runs included. -/
def prov (ok : Code → ComponentTag → Bool) : Tm → Bool
  | .invoke f r args => prov ok f && prov ok r && provs ok args
  | .construct f args => prov ok f && provs ok args
  | .letE a b => prov ok a && prov ok b
  | .objAt _ (.bound t r pre) _ => prov ok t && prov ok r && provs ok pre
  | .objAt _ (.graph _ E K _ caps _ _ c) _ => ok (E, K) c && provs ok E && provs ok caps
  | .makeAt (.bound t r pre) _ xs => prov ok t && prov ok r && provs ok pre && provs ok xs
  | .makeAt (.graph _ E K _ caps _ _ c) _ xs => ok (E, K) c && provs ok E && provs ok caps && provs ok xs
  | .makeAt .absent _ xs => provs ok xs
  | .makeAt (.view _ _ _) _ xs => provs ok xs
  | .readAt _ a => prov ok a
  | .indexAt a b => prov ok a && prov ok b
  | .writeAt _ a b => prov ok a && prov ok b
  | .test _ a => prov ok a
  | .ite x a b => prov ok x && prov ok a && prov ok b
  | .arith _ a b => prov ok a && prov ok b
  | .arrLit xs => provs ok xs
  | .elemAt a b => prov ok a && prov ok b
  | .setElem a b x => prov ok a && prov ok b && prov ok x
  | .lenOf a => prov ok a
  | .spread a => prov ok a
  | .throw a => prov ok a
  | .merge _ a b => prov ok a && prov ok b
  | .makeKey a b => prov ok a && prov ok b
  | .goto E K _ L d c => ok (E, K) c && provs ok E && provs ok L && prov ok d
  | .frame E K t L d _ _ c => ok (E, K) c && provs ok E && prov ok t && provs ok L && prov ok d
  | _ => true
termination_by structural t => t

def provs (ok : Code → ComponentTag → Bool) : List Tm → Bool
  | [] => true
  | x :: xs => prov ok x && provs ok xs
termination_by structural xs => xs
end

@[simp] theorem provs_eq (ok : Code → ComponentTag → Bool) (xs : List Tm) : provs ok xs = xs.all (prov ok) := by
  induction xs <;> simp_all [provs]

/-- **A heap meeting code provenance**: every value it holds does. -/
def HeapProv (ok : Code → ComponentTag → Bool) (h : Heap) : Prop := ∀ v ∈ h, prov ok v = true

/-! ## Substitution, heaps and throws keep it -/

theorem subst_prov {ok : Code → ComponentTag → Bool} {a : Tm} (ha : prov ok a = true) :
    ∀ (b : Tm) (j : Nat), prov ok b = true → prov ok (subst j a b) = true := by
  intro b
  induction b using Tm.induct
  all_goals intro j hb
  all_goals simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hb
  all_goals simp only [subst, prov, provs_eq, substArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  all_goals first
    | (split <;> (try split) <;> first | rfl | exact ha)
    | grind

theorem instantiate_prov {ok : Code → ComponentTag → Bool} {ρ : Env} (hρ : ∀ i, prov ok (ρ i) = true) :
    ∀ (b : Tm) (d : Nat), prov ok b = true → prov ok (instantiate d ρ b) = true := by
  intro b
  induction b using Tm.induct
  all_goals intro d hb
  all_goals simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hb
  all_goals simp only [instantiate, prov, provs_eq, instantiateArgs_eq_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  all_goals first
    | (split <;> first | rfl | exact hρ _)
    | grind

theorem HeapProv.append {ok : Code → ComponentTag → Bool} {h xs : Heap} (hh : HeapProv ok h)
    (hx : ∀ v ∈ xs, prov ok v = true) : HeapProv ok (h ++ xs) := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hh v hv
  · exact hx v hv

theorem HeapProv.set {ok : Code → ComponentTag → Bool} {h : Heap} {l : Nat} {v : Tm} (hh : HeapProv ok h)
    (hv : prov ok v = true) : HeapProv ok (h.set l v) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact hh x hx
  · exact hv

theorem HeapProv.get {ok : Code → ComponentTag → Bool} {h : Heap} {l : Nat} {v : Tm} (hh : HeapProv ok h)
    (hl : h[l]? = some v) : prov ok v = true :=
  hh v (List.mem_of_getElem? hl)

theorem readElems_prov {ok : Code → ComponentTag → Bool} {h : Heap} (hh : HeapProv ok h) :
    ∀ {ls : List (Option Nat)} {vs : List Tm}, readElems h ls = some vs → ∀ v ∈ vs, prov ok v = true
  | [], vs, hr => by simp [readElems] at hr; subst hr; simp
  | none :: ls, vs, hr => by
    simp only [readElems, Option.map_eq_some_iff] at hr
    obtain ⟨ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rfl
    · exact readElems_prov hh hws v hv
  | some l :: ls, vs, hr => by
    simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨w, hw, ws, hws, rfl⟩ := hr
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hh.get hw
    · exact readElems_prov hh hws v hv

theorem mergeParts_prov {ok : Code → ComponentTag → Bool} {h : Heap} (hh : HeapProv ok h) {d : List PropKey}
    {a b : Tm} {ps : List (PropKey × Tm)} (hm : mergeParts h d a b = some ps) :
    ∀ x ∈ ps.map Prod.snd, prov ok x = true := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  rcases Verification.mergeParts_vals hm p hp with he | ⟨hm', -⟩ | ⟨u, he⟩
  · rw [he]; rfl
  · exact hh _ hm'
  · rw [he]; rfl

theorem prov_makeAt {ok : Code → ComponentTag → Bool} {c : CallCode} {ns : List PropKey} {xs : List Tm} :
    prov ok (.makeAt c ns xs) = true ↔ prov ok (.objAt [] c 0) = true ∧ ∀ x ∈ xs, prov ok x = true := by
  cases c <;> simp [prov, provs_eq, Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem all_set' {P : Tm → Prop} {xs : List Tm} {i : Nat} {b : Tm} (h : ∀ x ∈ xs, P x) (hb : P b) :
    ∀ x ∈ xs.set i b, P x := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx
  · exact hb

/-- **A thrown value meets code provenance** where the throwing term does. -/
theorem raises_prov {ok : Code → ComponentTag → Bool} {t v : Tm} (hr : Raises t v) (hp : prov ok t = true) :
    prov ok v = true := by
  induction hr
  case callArg ha _ _ ih =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ih (hp.2 _ (List.mem_of_getElem? ha))
  case constructArg ha _ _ ih =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ih (hp.2 _ (List.mem_of_getElem? ha))
  case makeArg ha _ _ ih =>
    exact ih ((prov_makeAt.mp hp).2 _ (List.mem_of_getElem? ha))
  case arrArg ha _ _ ih =>
    simp only [prov, provs_eq, List.all_eq_true] at hp
    exact ih (hp _ (List.mem_of_getElem? ha))
  all_goals simp_all [prov]

theorem envMap_prov {ok : Code → ComponentTag → Bool} {m : Option (List Nat)} {L : List Tm} {d : Tm}
    (hL : ∀ x ∈ L, prov ok x = true) (hd : prov ok d = true) :
    (∀ x ∈ (envMap m L d).1, prov ok x = true) ∧ prov ok (envMap m L d).2 = true := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases envMap_mem (.inl hx) with hx | rfl
    · exact hL x hx
    · exact hd
  · rcases envMap_mem (m := m) (L := L) (d := d) (.inr rfl) with hx | hx
    · exact hL _ hx
    · rw [hx]; exact hd

theorem envMap_cons_prov {ok : Code → ComponentTag → Bool} {m : Option (List Nat)} {v : Tm} {L : List Tm} {d : Tm}
    (hv : prov ok v = true) (hL : ∀ x ∈ L, prov ok x = true) (hd : prov ok d = true) :
    (∀ x ∈ (envMap m (v :: L) d).1, prov ok x = true) ∧ prov ok (envMap m (v :: L) d).2 = true :=
  envMap_prov (fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact hL x hx) hd

theorem graphEntry_prov {ok : Code → ComponentTag → Bool} {n : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {s : Nat} {caps : List Tm} {self : Tm}
    {rest : Bool} {comp : ComponentTag} {recv : Tm} {args : List Tm} (hok : ok (E, K) comp = true)
    (hE : ∀ x ∈ E, prov ok x = true) (hc : ∀ x ∈ caps, prov ok x = true) (hs : prov ok self = true)
    (hr : prov ok recv = true) (ha : ∀ x ∈ args, prov ok x = true) :
    prov ok (CallArguments.graphEntry n E K s caps self rest comp recv args) = true := by
  have hpar : ∀ x ∈ CallArguments.parameters n args, prov ok x = true := fun x hx =>
    (Kinds.parameters_mem hx).elim (ha x) (fun h => h ▸ rfl)
  have hdrop : ∀ x ∈ args.drop n, prov ok x = true := fun x hx => ha x (List.mem_of_mem_drop hx)
  have hv : prov ok (.var 0) = true := rfl
  unfold CallArguments.graphEntry
  split <;> simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_append]
    <;> grind

/-! ## Every step keeps it -/

/-- **Every step keeps code provenance** (proved): the result of a step and
the heap after it meet `ok` where the term and the heap before it do. -/
theorem step_prov {ok : Code → ComponentTag → Bool} {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    prov ok t = true → HeapProv ok h → prov ok t' = true ∧ HeapProv ok h' := by
  induction hs
  all_goals intro hp hh
  case makeArg ha _ _ ih =>
    rw [prov_makeAt] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case makeFields =>
    rw [prov_makeAt] at hp
    refine ⟨?_, (hh.append hp.2).append (by simp [prov])⟩
    rename_i c _ _ _ _ _
    cases c <;> simp_all [prov]
  case callArg ha _ _ ih =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case constructArg ha _ _ ih =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp.2 _ (List.mem_of_getElem? ha)) hh
    exact ⟨⟨hp.1, all_set' hp.2 h1⟩, h2⟩
  case arrArg ha _ _ ih =>
    simp only [prov, provs_eq, List.all_eq_true] at hp ⊢
    obtain ⟨h1, h2⟩ := ih (hp _ (List.mem_of_getElem? ha)) hh
    exact ⟨all_set' hp h1, h2⟩
  -- A step inside an evaluation context.
  all_goals try (
    rename_i ih
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    have ⟨h1, h2⟩ := ih (by grind) hh
    exact ⟨by grind, h2⟩)
  -- A redex on an unchanged heap.
  all_goals try (
    refine ⟨?_, hh⟩
    simp_all [prov]
    done)
  case callSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_prov hh hre
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨⟨hp.1, by grind⟩, hh⟩
  case constructSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_prov hh hre
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨⟨hp.1, by grind⟩, hh⟩
  case arrSpread =>
    rename_i heq _ hre
    subst heq
    have hvs := readElems_prov hh hre
    simp only [prov, provs_eq, List.all_eq_true, List.mem_append, List.mem_cons] at hp ⊢
    exact ⟨by grind, hh⟩
  case readField hv => exact ⟨hh.get hv, hh⟩
  case elemRead hv => exact ⟨hh.get hv, hh⟩
  case indexField hv => exact ⟨hh.get hv, hh⟩
  case readProto hp' => exact ⟨by simp only [prov]; exact hh.get hp', hh⟩
  case indexProto hp' =>
    simp only [prov, Bool.and_eq_true] at hp ⊢
    exact ⟨⟨hh.get hp', hp.2⟩, hh⟩
  case writeField =>
    simp only [prov, Bool.and_eq_true] at hp
    exact ⟨rfl, hh.set hp.2⟩
  case setPresent =>
    simp only [prov, Bool.and_eq_true] at hp
    exact ⟨rfl, hh.set hp.2⟩
  case setGrow =>
    simp only [prov, Bool.and_eq_true] at hp
    exact ⟨rfl, hh.append (by simpa using hp.2)⟩
  case arrAlloc =>
    simp only [prov, provs_eq, List.all_eq_true] at hp
    exact ⟨rfl, hh.append hp⟩
  case testV => exact ⟨by split <;> rfl, hh⟩
  case elemStr => exact ⟨by simp only [codeUnitAt]; split <;> rfl, hh⟩
  case arithV hb =>
    obtain ⟨-, -, hres⟩ := binop_result hb
    exact ⟨by rcases hres with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl, hh⟩
  case mergeV hm =>
    simp only [prov, provs_eq, List.all_eq_true]
    exact ⟨mergeParts_prov hh hm, hh⟩
  case callGraph =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ⟨graphEntry_prov (by grind) (by grind) (by grind)
      (by simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true]; grind) (by grind) (by grind), hh⟩
  case constructGraph =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp
    exact ⟨graphEntry_prov (by grind) (by grind) (by grind)
      (by simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true]; grind) rfl (by grind), hh⟩
  case gotoEnter he _ =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    have henv : ∀ i, prov ok (envOf _ _ i) = true := fun i => by
      rcases getD_mem_or _ i _ with h | h
      · simp only [envOf]; exact hp.1.2 _ h
      · simp only [envOf]; rw [h]; exact hp.2
    have hi := instantiate_prov henv _ 0 (hp.1.1.2 _ (List.mem_of_getElem? he))
    exact ⟨by grind, hh⟩
  case letV =>
    simp only [prov, Bool.and_eq_true] at hp
    exact ⟨subst_prov hp.1 _ 0 hp.2, hh⟩
  case frameHandle hr =>
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    have hv := raises_prov hr hp.1.1.2
    have hL := (List.forall_mem_cons (p := fun x => prov ok x = true)).mpr ⟨hv, hp.1.2⟩
    have hm := envMap_prov (m := ‹ControlFlow.Target›.mapping) hL hp.2
    exact ⟨by grind, hh⟩
  case frameRaise hr =>
    simp only [prov, Bool.and_eq_true] at hp ⊢
    exact ⟨raises_prov hr hp.1.1.2, hh⟩
  -- A fresh error thrown.
  all_goals try exact ⟨by simp [prov, thrownError], hh.append (by simp [prov])⟩
  -- A run's next node, its environment mapped from the frame's.
  all_goals
    simp only [prov, provs_eq, Bool.and_eq_true, List.all_eq_true] at hp ⊢
    first
      | exact ⟨⟨⟨hp.1.1.1, (envMap_prov hp.1.2 hp.2).1⟩, (envMap_prov hp.1.2 hp.2).2⟩, hh⟩
      | exact ⟨⟨⟨hp.1.1.1, (envMap_cons_prov hp.1.1.2 hp.1.2 hp.2).1⟩, (envMap_cons_prov hp.1.1.2 hp.1.2 hp.2).2⟩, hh⟩
      | exact ⟨⟨⟨hp.1.1.1, (envMap_cons_prov rfl hp.1.2 hp.2).1⟩, (envMap_cons_prov rfl hp.1.2 hp.2).2⟩, hh⟩

end Verification.TolerantFrames.ReadOnly
