import Verification.Programs.TolerantFramesStepLinkSound

/-! # Tolerant frames: an edge's store and transfer

What an edge carries from a node's exit to its target (`SinglePass.lean`
1807, 1981): the edge's store (`SinglePass.edgeStoreOf`: a handler's
heap-free entry facts, an observed result's or a promoted Boolean's facts
added, else the step's store) and the target's state (`SinglePass.edgeTransfer`:
the mapped names, the store without the names the edge drops, the fresh names
and implications it keeps). The state's meaning is existential in the name
valuation, so the dropped names keep their values: every operation of the
edge keeps the facts holding at the exit's valuation (`drop_ok`,
`edgeStore_observed`, `edgeStore_promote`, `edgeTransfer_ok`).

Named hypothesis: the mapped names (`SinglePass.mapNames`) name each target
slot by the name of the source slot the mapping reads (`MapNamesSound`).
`mapNames` reads the mapping's ordered suffix by `orderedSuffix`, a `while`
loop, which no proof unfolds. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates

section Edge
variable {ι : Type}

/-! ## Lists the pass keeps the first of -/

theorem keepFirst_foldl {α : Type} [BEq α] [Hashable α] (P : α → Prop) :
    ∀ (l : List α) (acc : Std.HashSet α × Array α), (∀ y ∈ acc.2.toList, P y) → (∀ y ∈ l, P y) →
      ∀ y ∈ (l.foldl (fun (sk : Std.HashSet α × Array α) a =>
        if sk.1.contains a then (sk.1, sk.2) else (sk.1.insert a, sk.2.push a)) acc).2.toList, P y
  | [], _, h, _ => h
  | a :: l, acc, h, hl => by
    rw [List.foldl_cons]
    refine keepFirst_foldl P l _ ?_ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    intro y hy
    split at hy
    · exact h y hy
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact h y hy
      · exact hl _ (List.mem_cons_self ..)

theorem keepFirst_mem {α : Type} [BEq α] [Hashable α] {l : List α} {s : Std.HashSet α} {x : α}
    (hx : x ∈ (keepFirst s l).2.toList) : x ∈ l :=
  keepFirst_foldl (· ∈ l) l (s, #[]) (fun _ h => by simp at h) (fun _ h => h) x hx

/-! ## Dropping names -/

theorem storeOk_bind {η : Env} {h : Heap} {m : Id Store} {k : Store → Id Store} (hm : StoreOk m η h)
    (hk : ∀ a, StoreOk a η h → StoreOk (k a) η h) : StoreOk (m >>= k) η h := hk m hm

theorem storeOk_forIn {α : Type} {η : Env} {h : Heap} (l : List α) (init : Store)
    (f : α → Store → Id (ForInStep Store)) (h0 : StoreOk init η h)
    (hf : ∀ a ∈ l, ∀ b, StoreOk b η h → StoreOk (f a b).value η h) : StoreOk (forIn l init f) η h :=
  forIn_inv l init f (fun b => StoreOk b η h) h0 hf

/-- A separation fact with fewer partners holds where the fact does. -/
theorem sep_partners {f : HeapSeparation.Fact} {η : Env} {h : Heap} (hf : AtomHolds (.sep f) η h)
    (P : Nat × List PropKey → Bool) : AtomHolds (.sep { f with partners := f.partners.filter P }) η h :=
  fun p hp g hg => hf p (List.mem_filter.mp hp).1 g hg

/-- The alias table `Store.drop` builds sends a name to one its alias links
make equal to it. -/
theorem keptAlias_ok {links : List HeapLinks.Link} {η : Env} {h : Heap} (hl : HeapLinks.Holds links η h)
    (dset : Std.HashSet Nat) :
    ∀ x y, (links.foldl (fun (acc : Std.HashMap Nat Nat) g =>
      if !g.alias then acc
      else if dset.contains g.cell && !dset.contains g.value && !acc.contains g.cell then acc.insert g.cell g.value
      else if dset.contains g.value && !dset.contains g.cell && !acc.contains g.value then acc.insert g.value g.cell
      else acc) {}).get? x = some y → η y = η x := by
  suffices ∀ (l : List HeapLinks.Link) (acc : Std.HashMap Nat Nat), (∀ g ∈ l, g ∈ links) →
      (∀ x y, acc.get? x = some y → η y = η x) →
      ∀ x y, (l.foldl (fun (acc : Std.HashMap Nat Nat) g =>
        if !g.alias then acc
        else if dset.contains g.cell && !dset.contains g.value && !acc.contains g.cell then acc.insert g.cell g.value
        else if dset.contains g.value && !dset.contains g.cell && !acc.contains g.value then acc.insert g.value g.cell
        else acc) acc).get? x = some y → η y = η x from
    this links {} (fun _ h => h) (fun x y h => by simp at h)
  intro l
  induction l with
  | nil => intro _ _ h; exact h
  | cons g l ih =>
    intro acc hsub hacc
    rw [List.foldl_cons]
    refine ih _ (fun g' h' => hsub g' (List.mem_cons_of_mem _ h')) ?_
    have hg : g.alias = true → η g.cell = η g.value := fun ha => by
      have := hl g (hsub g (List.mem_cons_self ..)); simpa [ha] using this
    have ins : ∀ a b, η b = η a → ∀ x y, (acc.insert a b).get? x = some y → η y = η x := by
      intro a b hab x y hxy
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hxy
      split at hxy
      · rename_i he; simp only [beq_iff_eq] at he; cases hxy; subst he; exact hab
      · exact hacc x y (by rw [Std.HashMap.get?_eq_getElem?]; exact hxy)
    split
    · exact hacc
    · rename_i hna
      have ha : g.alias = true := by simpa using hna
      split
      · exact ins _ _ (hg ha).symm
      · split
        · exact ins _ _ (hg ha)
        · exact hacc

theorem index_filterMap_holds {xs : List Atom} {η : Env} {h : Heap} (ha : ∀ a ∈ xs, AtomHolds a η h) :
    HeapKnowledge.IndexHolds (xs.filterMap fun a => match a with | .index x => some x | _ => none) η h := by
  intro y hy
  obtain ⟨a, haa, hay⟩ := List.mem_filterMap.mp hy
  split at hay
  · cases hay; exact ha _ haa y (List.mem_singleton_self _)
  · cases hay

theorem link_filterMap_holds {xs : List Atom} {η : Env} {h : Heap} (ha : ∀ a ∈ xs, AtomHolds a η h) :
    HeapLinks.Holds (xs.filterMap fun a => match a with | .link g => some g | _ => none) η h := by
  intro g hg
  obtain ⟨a, haa, hag⟩ := List.mem_filterMap.mp hg
  split at hag
  · cases hag; exact ha _ haa g (List.mem_singleton_self _)
  · cases hag

theorem getD_self_ok {m : Std.HashMap Nat Nat} {η : Env} (hm : ∀ x y, m.get? x = some y → η y = η x) (x : Nat) :
    η (m.getD x x) = η x := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases hx : m[x]? with
  | none => rfl
  | some y => exact hm x y (by rw [Std.HashMap.get?_eq_getElem?]; exact hx)

/-- **Dropping names keeps the store holding** at the same valuation: the
removed facts leave, and each fact added (a separation with fewer partners,
a fact restated through an alias link, a derived linear fact) holds where
the store's facts do. -/
theorem drop_ok {s : Store} {D : List Nat} {η : Env} {h : Heap} (hs : StoreOk s η h) :
    StoreOk (s.drop D) η h := by
  unfold Store.drop
  simp only [Id.run, timedKind]
  split
  · exact hs
  split
  · exact hs
  -- Every fact `Store.drop` reads is a stored fact.
  have hat : ∀ a ∈ (keepFirst ∅ (D.flatMap s.about)).2.toList, AtomHolds a η h := fun a ha => by
    obtain ⟨n, -, hn⟩ := List.mem_flatMap.mp (keepFirst_mem ha)
    exact hs a (about_storeAll hn)
  have hread : ∀ a ∈ (keepFirst ∅ (D.flatMap s.about)).2.toList ++ ((keepFirst ∅
      ((keepFirst ∅ (((keepFirst ∅ (D.flatMap s.about)).2.toList.flatMap Atom.names).filter
        (!(D.foldl (·.insert ·) ({} : Std.HashSet Nat)).contains ·))).2.toList.flatMap s.about)).2.toList.filter fun a =>
          match a with
          | .index x => match x.fact with | .linear _ => true | _ => false
          | .link _ => true
          | _ => false), AtomHolds a η h := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hat a ha
    · obtain ⟨n, -, hn⟩ := List.mem_flatMap.mp (keepFirst_mem (List.mem_filter.mp ha).1)
      exact hs a (about_storeAll hn)
  refine storeOk_bind (storeOk_forIn _ _ _ (foldl_remove_ok _ _ hs) ?_) ?_
  · intro a ha b hb
    split
    · rename_i f
      split
      · split
        · exact add_ok hb (sep_partners (hat _ ha) _)
        · exact hb
      · exact hb
    · exact hb
  · intro b hb
    split
    · refine storeOk_bind (storeOk_forIn _ _ _ hb ?_) fun c hc => storeOk_bind (storeOk_forIn _ _ _ hc ?_) fun d hd => hd
      · intro a ha c hc
        split
        · rename_i b hr
          split
          · refine add_ok hc (atomHolds_rename (η := η) (fun x i hx => ?_) hr (hat a ha))
            simp only [Option.some.injEq] at hx
            subst hx
            exact getD_self_ok (keptAlias_ok (link_filterMap_holds hread) (D.foldl (·.insert ·) {})) x
          · exact hc
        · exact hc
      · intro x hx c hc
        split
        · refine add_ok hc fun y hy => ?_
          simp only [List.mem_singleton] at hy
          subst hy
          refine HeapKnowledge.eliminateIndices_holds (fun a ha => ?_) y (List.mem_of_mem_drop hx)
          rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_append.mp ha with ha | ha
            · exact index_filterMap_holds hread a ha
            · exact HeapKnowledge.restateReads_holds (link_filterMap_holds hread) (index_filterMap_holds hread) a ha
          · exact HeapKnowledge.restateStores_holds (link_filterMap_holds hread) (index_filterMap_holds hread) a ha
        · exact hc
    · refine storeOk_bind (storeOk_forIn _ _ _ hb ?_) fun d hd => hd
      intro x hx c hc
      split
      · refine add_ok hc fun y hy => ?_
        simp only [List.mem_singleton] at hy
        subst hy
        refine HeapKnowledge.eliminateIndices_holds (fun a ha => ?_) y (List.mem_of_mem_drop hx)
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · exact index_filterMap_holds hread a ha
          · exact HeapKnowledge.restateReads_holds (link_filterMap_holds hread) (index_filterMap_holds hread) a ha
        · exact HeapKnowledge.restateStores_holds (link_filterMap_holds hread) (index_filterMap_holds hread) a ha
      · exact hc

/-! ## The edge's store -/

/-- The renaming an edge's observation reads back (`SinglePass.lean` 941,
946): a slot the table's inverse gives its name, else the slot's name. -/
theorem edgeBack_ok {names : List Nat} {want : Std.HashSet Nat} {whole : Bool} {ρ η : Env}
    (hs : SlotsNamed names ρ η) :
    ∀ i x, ((Std.HashMap.fold (fun acc nm s => acc.insert s nm) ({} : Std.HashMap Nat Nat)
      (SinglePass.slotTable names want whole)).get? i).orElse (fun _ => names[i]?) = some x → η x = ρ i := by
  intro i x hb
  cases hi : (Std.HashMap.fold (fun acc nm s => acc.insert s nm) ({} : Std.HashMap Nat Nat)
      (SinglePass.slotTable names want whole)).get? i with
  | none => rw [hi] at hb; exact (hs i x (by simpa using hb)).symm
  | some y =>
    rw [hi] at hb
    simp only [Option.orElse_some, Option.some.injEq] at hb; subst hb
    exact (hs i _ (slotTable_get (inverse_get hi))).symm

/-- A state's meaning does not read its fresh names' absence. -/
theorem stateHolds_noFresh {G : NormalGraph ι} {N : List Nat} {S : Store} {F : List Nat}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨N, S, F⟩ I start E ρ m s) : StateHolds G ⟨N, S, []⟩ I start E ρ m s := by
  obtain ⟨η, hn, hst, hI, -, hs⟩ := hS
  exact ⟨η, hn, hst, hI, (fun _ h => absurd h (List.not_mem_nil)), hs⟩

/-- **An observed edge's store holds**: the observation's facts at slot 0
(`HeapKnowledge.observeTyped`, an alternative it contradicts released,
`withElements`) added to the store by the delta. -/
theorem edgeStore_observed [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {N : List Nat} {S : Store}
    {F : List Nat} {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat}
    {s : IndexedHeap} {o : BranchRefinement.Observation} (d : Nat)
    (hS : StateHolds G ⟨N, S, F⟩ I start E ρ m s) (he : EnvOk G Γ ρ s.n s.W) (ho : o.holds (ρ 0)) :
    StateHolds G ⟨N, applyDelta S (materialize ⟨N, S, []⟩ d [0] false).2.1
      (HeapKnowledge.withElements (HeapKnowledge.observeTyped G Γ (materialize ⟨N, S, []⟩ d [0] false).1 0 o)) false
      (fun i => ((Std.HashMap.fold (fun acc nm s => acc.insert s nm) ({} : Std.HashMap Nat Nat)
        (materialize ⟨N, S, []⟩ d [0] false).2.2).get? i).orElse fun _ => N[i]?), F⟩ I start E ρ m s := by
  have hk := stateHolds_materialize (stateHolds_noFresh hS) d [0] true
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  obtain ⟨want, hT⟩ := materialize_table ⟨N, S, []⟩ d [0] false
  refine ⟨η, hn, ?_, hI, hF, hs⟩
  rw [hT]
  exact applyDelta_ok (deltaRemove_ok hst)
    (HeapKnowledge.withElements_holds (HeapKnowledge.observeTyped_holds he hk ho)) (edgeBack_ok hn)

/-- **A promoted Boolean's store holds**: a branch's answer `q` promotes the
facts guarded by the truthiness of slot 0 (`HeapKnowledge.promoteTruthy`). -/
theorem edgeStore_promote {G : NormalGraph ι} {N : List Nat} {S : Store} {F : List Nat}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap}
    {q : Bool} (d : Nat)
    (hS : StateHolds G ⟨N, S, F⟩ I start E ρ m s) (hq : tagHolds .truthy (ρ 0) = q) :
    StateHolds G ⟨N, applyDelta S (materialize ⟨N, S, []⟩ d [0] false).2.1
      (HeapKnowledge.withElements (HeapKnowledge.promoteTruthy (materialize ⟨N, S, []⟩ d [0] false).1 0 q)) false
      (fun i => ((Std.HashMap.fold (fun acc nm s => acc.insert s nm) ({} : Std.HashMap Nat Nat)
        (materialize ⟨N, S, []⟩ d [0] false).2.2).get? i).orElse fun _ => N[i]?), F⟩ I start E ρ m s := by
  have hk := stateHolds_materialize (stateHolds_noFresh hS) d [0] true
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  obtain ⟨want, hT⟩ := materialize_table ⟨N, S, []⟩ d [0] false
  refine ⟨η, hn, ?_, hI, hF, hs⟩
  rw [hT]
  exact applyDelta_ok (deltaRemove_ok hst)
    (HeapKnowledge.withElements_holds (HeapKnowledge.promoteTruthy_holds hk hq)) (edgeBack_ok hn)

/-- A state at the pushed environment holds, without its first slot, at the
node's environment. -/
theorem stateHolds_tail {G : NormalGraph ι} {r : Nat} {N : List Nat} {S : Store} {F : List Nat}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {v : Tm} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨r :: N, S, F⟩ I start E (push v ρ) m s) : StateHolds G ⟨N, S, F⟩ I start E ρ m s := by
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  exact ⟨η, fun i x hx => by simpa [push] using hn (i + 1) x (by simpa using hx), hst, hI, hF, hs⟩

/-- **A handler edge's state**: the thrown value at a new name `e` pushed on
the entry's heap-free state. -/
theorem stateHolds_handler {G : NormalGraph ι} {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap} {x : Nat} {v : Tm}
    (hS : StateHolds G st I start E ρ m s) (hb : NamesBelow st I start x) :
    StateHolds G ⟨x :: st.names, st.store, st.fresh⟩ I start E (push v ρ) m s := by
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  obtain ⟨-, g2, -⟩ := set_agree (v := v) (η := η) (.inl hb)
  exact stateHolds_pushed hn hI hF hs (Admissible.refl s) (.inl hb)
    fun a ha => (atomHolds_congr fun y hy => (g2 a ha y hy).symm).mp (hst a ha)

/-! ## The edge's transfer -/

/-- **(Hypothesis) The mapped names name each target slot by the source
slot the mapping reads.** `mapNames` reads the mapping's ordered suffix by
`orderedSuffix`, a `while` loop no proof unfolds; the identity mapping is
proved (`mapNamesSound_none`). -/
def MapNamesSound (names : List Nat) (m : PointClaims.Mapping) : Prop :=
  ∀ j x, (mapNames names m)[j]? = some x → names[PointClaims.slot m j]? = some x

theorem mapNamesSound_none (names : List Nat) : MapNamesSound names none :=
  fun _ _ h => by simpa [mapNames, PointClaims.slot] using h

/-- **The edge's transfer keeps the state holding** at the target's
environment: each target slot named by its source slot's name; the store
without the dropped names (`drop_ok`), whatever names they are; the fresh
names it keeps, the result among them where it holds a fresh store; the
implications naming no dropped name. -/
theorem edgeTransfer_ok [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {names : List Nat} {m : PointClaims.Mapping}
    {pushed isHandler outFresh : Bool} {entry : SinglePass.State} {result : Nat} {edgeStore : Store}
    {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E ρ : Env} {mk : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨names, edgeStore, entry.fresh⟩ I start E ρ mk s) (hmap : MapNamesSound names m)
    (hfo : pushed = true → isHandler = false → outFresh = true → result ∉ entry.fresh →
      names[0]? = some result ∧ FreshAt mk (ρ 0)) :
    StateHolds G (edgeTransfer names m pushed isHandler outFresh entry result edgeStore I).1
      (edgeTransfer names m pushed isHandler outFresh entry result edgeStore I).2 start E
      (PointClaims.mapEnv m ρ) mk s := by
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  simp only [edgeTransfer, timedKind]
  refine ⟨η, fun j x hx => (hn _ x (hmap j x hx)), drop_ok hst, ?_, ?_, hs⟩
  · intro y hy ht
    have hy' := keepFirst_mem hy
    exact hI y (List.mem_filter.mp hy').1 ht
  · intro x hx
    have hx' := (List.mem_filter.mp hx).1
    split at hx'
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hc
      obtain ⟨⟨⟨hp, hh⟩, ho⟩, hnf⟩ := hc
      rcases List.mem_cons.mp hx' with rfl | hx'
      · obtain ⟨h0, hfr⟩ := hfo hp hh ho hnf
        rw [← hn 0 x h0]; exact hfr
      · exact hF x hx'
    · exact hF x hx'

/-! ## The edges of a node -/

theorem namesBelow_mono {st : SinglePass.State} {I : List (PromiseCalls.Implication ι)} {start : List Nat}
    {x y : Nat} (hle : x ≤ y) (h : NamesBelow st I start x) : NamesBelow st I start y := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun z hz => Nat.lt_of_lt_of_le (h1 z hz) hle, fun a ha z hz => Nat.lt_of_lt_of_le (h2 a ha z hz) hle,
    fun z hz => Nat.lt_of_lt_of_le (h3 z hz) hle, fun z hz => Nat.lt_of_lt_of_le (h4 z hz) hle,
    fun w hw => ⟨Nat.lt_of_lt_of_le (h5 w hw).1 hle, Nat.lt_of_lt_of_le (h5 w hw).2 hle⟩⟩

theorem namesBelow_dropHeap {N : List Nat} {S : Store} {F : List Nat} {I : List (PromiseCalls.Implication ι)}
    {start : List Nat} {x : Nat} (w : StoreWF S) (keep : Atom → Bool) (h : NamesBelow ⟨N, S, F⟩ I start x) :
    NamesBelow ⟨N, S.dropHeap keep, F⟩ I start x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, fun a ha => h2 a ((dropHeap_cover w keep).2 a ha).1, h3, h4, h5⟩

/-- What a normal exit observes of its value `v` (`Exit.observed`,
`Exit.promote`): a branch-binding's observation, a branch's answer. -/
def ObservedOk (observed : Option BranchRefinement.Observation) (promote : Option Bool) (v : Tm) : Prop :=
  match observed, promote with
  | some o, _ => o.holds v
  | none, some q => tagHolds .truthy v = q
  | none, none => True

/-- **A normal edge from a step's exit**: from the state after the step at
the pushed environment (`checkedStep_sound`) and what the edge observes of
the value, the target's state (`edgeTransfer` of `edgeStoreOf`) holds at the
target's environment under the edge's mapping, its names as the pass names
them (`SinglePass.lean` 1804–1807, 1981). An observation is read of a pushed
edge, a promotion of an unpushed one (`Exit.ofNode`). -/
theorem edge_normal_sound [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {entry : SinglePass.State} {store : Store} {result width : Nat} {v : Tm} {ρ : Env}
    {pushed outFresh : Bool} {observed : Option BranchRefinement.Observation} {promote : Option Bool}
    {θ : PointClaims.Mapping} {I : List (PromiseCalls.Implication ι)} {start : List Nat} {E : Env} {m : Nat}
    {s : IndexedHeap}
    (hS : StateHolds G ⟨result :: entry.names, store, entry.fresh⟩ I start E (push v ρ) m s)
    (hobs : ObservedOk observed promote v)
    (hpo : observed.isSome = true → pushed = true) (hpp : promote.isSome = true → pushed = false)
    (he : observed.isSome = true → EnvOk G Γ (push v ρ) s.n s.W)
    (hmap : MapNamesSound (if pushed then result :: entry.names else entry.names) θ)
    (hfo : pushed = true → outFresh = true → result ∉ entry.fresh → FreshAt m v) :
    StateHolds G (edgeTransfer (if pushed then result :: entry.names else entry.names) θ pushed false outFresh entry
        result (edgeStoreOf G Γ entry.store store (if pushed then result :: entry.names else entry.names)
          (result :: entry.names) width pushed false observed promote) I).1
      (edgeTransfer (if pushed then result :: entry.names else entry.names) θ pushed false outFresh entry
        result (edgeStoreOf G Γ entry.store store (if pushed then result :: entry.names else entry.names)
          (result :: entry.names) width pushed false observed promote) I).2
      start E (PointClaims.mapEnv θ (if pushed then push v ρ else ρ)) m s := by
  have hfo' : ∀ ρx : Env, ρx 0 = v → pushed = true → false = false → outFresh = true → result ∉ entry.fresh →
      (if pushed then result :: entry.names else entry.names)[0]? = some result ∧ FreshAt m (ρx 0) :=
    fun ρx h0 hp _ ho hn => by simp only [hp, if_true, List.getElem?_cons_zero]; exact ⟨trivial, h0 ▸ hfo hp ho hn⟩
  cases pushed with
  | true =>
    simp only [if_true] at hmap ⊢
    refine edgeTransfer_ok ?_ hmap (hfo' _ rfl)
    simp only [edgeStoreOf, Bool.false_eq_true, if_false]
    cases observed with
    | some o => exact edgeStore_observed _ hS (he rfl) hobs
    | none =>
      cases promote with
      | some q => cases hpp rfl
      | none => exact hS
  | false =>
    simp only [Bool.false_eq_true, if_false] at hmap ⊢
    refine edgeTransfer_ok ?_ hmap (fun h => by cases h)
    simp only [edgeStoreOf, Bool.false_eq_true, if_false]
    cases observed with
    | some o => cases hpo rfl
    | none =>
      cases promote with
      | some q => exact stateHolds_tail (edgeStore_promote _ hS hobs)
      | none => exact stateHolds_tail hS

/-- **A handler edge**: from the step's throw state (`checkedStep_sound`:
the entry's heap-free facts at the node's environment), the thrown value at
the fresh name `x` (`thrown`, above every name), the target's state holds at
the handler's environment under its mapping. -/
theorem edge_handler_sound [DecidableEq ι] [Hashable ι] {G : NormalGraph ι} {Γ : List (Ty ι)}
    {entry : SinglePass.State} {store : Store} {result width x : Nat} {e : Tm} {ρ : Env}
    {outFresh : Bool} {θ : PointClaims.Mapping} {I : List (PromiseCalls.Implication ι)} {start : List Nat}
    {E : Env} {m : Nat} {s : IndexedHeap}
    (hS : StateHolds G ⟨entry.names, entry.store.dropHeap (fun _ => false), entry.fresh⟩ I start E ρ m s)
    (w : StoreWF entry.store) (hb : NamesBelow entry I start x) (hmap : MapNamesSound (x :: entry.names) θ) :
    StateHolds G (edgeTransfer (x :: entry.names) θ true true outFresh entry result
        (edgeStoreOf G Γ entry.store store (x :: entry.names) (result :: entry.names) width true true none none) I).1
      (edgeTransfer (x :: entry.names) θ true true outFresh entry result
        (edgeStoreOf G Γ entry.store store (x :: entry.names) (result :: entry.names) width true true none none) I).2
      start E (PointClaims.mapEnv θ (push e ρ)) m s :=
  edgeTransfer_ok (stateHolds_handler (v := e) hS (namesBelow_dropHeap w _ hb)) hmap (fun _ h => by cases h)

/-! ## The implications an edge adds -/

/-- Implications holding at every valuation naming the slots join the state. -/
theorem stateHolds_addImplies {G : NormalGraph ι} {st : SinglePass.State} {I J : List (PromiseCalls.Implication ι)}
    {start : List Nat} {E ρ : Env} {m : Nat} {s : IndexedHeap} (hS : StateHolds G st I start E ρ m s)
    (hJ : ∀ η, SlotsNamed st.names ρ η → PromiseCalls.ImpliesOk G J η s.n s.W) :
    StateHolds G st (I ++ J) start E ρ m s := by
  obtain ⟨η, hn, hst, hI, hF, hs⟩ := hS
  refine ⟨η, hn, hst, fun y hy => ?_, hF, hs⟩
  rcases List.mem_append.mp hy with hy | hy
  · exact hI y hy
  · exact hJ η hn y hy

/-- **The implications a pushed edge states of its result** (`freshImpl`,
`SinglePass.lean` 1917–1919): where the step's yields hold of its value
(`PromiseCalls.YieldsOk`), each conditional yield's implication holds at
every valuation naming the pushed slots. -/
theorem freshImpl_ok [DecidableEq ι] {G : NormalGraph ι} {ys : List (PromiseCalls.Yield ι)} {result : Nat}
    {names : List Nat} {v : Tm} {ρ η : Env} {n : Nat} {W : WorldT n}
    (hy : PromiseCalls.YieldsOk G ys ρ n W v) (hn : SlotsNamed (result :: names) (push v ρ) η) :
    PromiseCalls.ImpliesOk G (ys.filterMap fun y => if y.conditional && !y.onFalse then
      (names[y.target]?).map fun tgt => (⟨result, tgt, y.type⟩ : PromiseCalls.Implication ι) else none) η n W := by
  intro x hx ht
  obtain ⟨y, hym, hyx⟩ := List.mem_filterMap.mp hx
  split at hyx
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨t, ht', rfl⟩ := Option.map_eq_some_iff.mp hyx
    have h0 : η result = v := by simpa [push] using (hn 0 result rfl).symm
    have hv : v = .tru := h0 ▸ ht
    have htg : η t = ρ y.target := by simpa [push] using (hn (y.target + 1) t (by simpa using ht')).symm
    simp only
    rw [htg]
    exact hy y hym (fun _ => hv) (fun h => by rw [hc.2] at h; cases h)
  · cases hyx

/-! ## Interface between the head entry and the edge check -/

/-- **The head query is sound** (`SinglePass.lean` 1949–1952): where the
edge's facts `k` hold at the source environment, typed by the edge's context
`Γ`, and the target's types hold at the mapped environment, the given facts
`checkIn` accepts hold there (the `facts` field of `HeadEstablishes` at the
head's environment `mapEnv θ ρ`), with the target's types. -/
theorem head_query_sound [DecidableEq ι] {G : NormalGraph ι} {Γ Δ : List (Ty ι)} {req k : HeapKnowledge.Knowledge}
    {θ : PointClaims.Mapping} {ρ : Env} {n : Nat} {W : WorldT (n + 1)} {h : Heap}
    (hq : KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G Δ)
      (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req θ k)) req θ = true)
    (hk : HeapKnowledge.Holds k ρ h) (he : EnvOk G Γ ρ (n + 1) W) (hh : HeapOk (n + 1) W h)
    (htc : EnvOk G Δ (PointClaims.mapEnv θ ρ) (n + 1) W) :
    HeapKnowledge.Holds req (PointClaims.mapEnv θ ρ) h ∧ EnvOk G Δ (PointClaims.mapEnv θ ρ) (n + 1) W :=
  ⟨KnowledgeExpand.checkIn_sound hq (KnowledgeExpand.ctxOf_ok htc)
    (HeapKnowledge.withTypedLinks_holds he (withTypedCells_holds (fun _ => HeapExpressionRules.typedCells_holds he hh)
      (fun _ _ hr => HeapExpressionRules.typeValues_sound hr he) hk)), htc⟩

end Edge

end Verification.TolerantFrames
