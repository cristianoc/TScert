import Verification.Programs.TolerantFramesMergeBelow

/-! # Tolerant frames: the merge's guarded join is sound

The guarded facts a merge keeps (`mergeGuarded`) hold at the slot
environment on the path through any predecessor (`guardedHolds_of_path`),
which discharges the merge theorem's premise `GuardedHolds`. Each fact the
join keeps is checked against every predecessor's view materialized at the
seed slots (`HeapKnowledge.indicesCheckWith`): the joined facts
(`CertificateProducer.joinGuarded`) against the view with its guards also
lowered through its read links (`HeapKnowledge.lowerGuards`), the tagged
facts against the view itself. On the path through `p`, `p`'s view holds at
the merge's valuation, so its materialization holds at the slots
(`materializeFrom_holds`); lowering a guard through a read link keeps it
holding (`lowerGuards_holds`); and `indicesCheckWith_sound` gives the fact. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations HeapKnowledge
open Verification.SinglePass (Atom Store State)
open ProgramTyping PositiveGraphs

/-! ## A guard lowered through a read link -/

/-- **A read link bridges a path**: where the links hold and `c` reads `f`
into `v`, a path `f :: q` read from `c` reads what `q` reads from `v`. -/
theorem guardReads_path {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {c v : Nat} {f : String} (hm : (c, f, v) ∈ guardReads ls) {q : List String} {w : Val}
    (hr : readPath h (ρ c) (f :: q) = some w) : readPath h (ρ v) q = some w := by
  obtain ⟨g, hg, hgm⟩ := List.mem_filterMap.mp hm
  split at hgm
  · cases hgm
  · rename_i ha
    split at hgm
    · rename_i f' hf'
      simp only [Option.some.injEq, Prod.mk.injEq] at hgm
      obtain ⟨rfl, rfl, rfl⟩ := hgm
      have hlg := hl g hg
      have ha' : g.alias = false := by simpa using ha
      simp only [ha', Bool.false_eq_true, ite_false] at hlg
      cases ho : g.optional
      · simp only [ho, Bool.false_eq_true, ite_false] at hlg
        obtain ⟨flds, cd, oid, l, he, hlk, hv⟩ := hlg
        rw [hf'] at hlk
        rw [he, readPath_cons hlk hv] at hr
        exact hr
      · simp only [ho, ite_true] at hlg
        obtain ⟨flds, cd, oid, he, hrg⟩ := hlg
        rw [he] at hr
        unfold HeapFacts.ReadGave at hrg
        rw [hf'] at hrg
        cases hlk : flds.lookup (.str f') with
        | some l =>
          rw [hlk] at hrg
          rw [readPath_cons hlk hrg] at hr
          exact hr
        | none => simp [readPath, hlk] at hr
    · cases hgm

/-- **Lowering a fact through a read link keeps it holding**
(`IndexFact.lowerRead`): a term rooted at `c` whose path starts with `f`
denotes what the term rooted at `v` with the rest of the path denotes, and a
guard's path alike. -/
theorem lowerRead_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap} (hl : HeapLinks.Holds ls ρ h)
    {c v : Nat} {f : String} (hm : (c, f, v) ∈ guardReads ls) :
    ∀ (B : IndexFact), B.HoldsAt ε ρ h → (B.lowerRead c f v).HoldsAt ε ρ h := by
  intro B
  induction B with
  | linear F =>
    intro ⟨hd, hF⟩
    let g' : Term → Term := fun t => match t.path with
      | g :: q => if t.slot == c && g == f && !t.atEntry then (HeapKnowledge.Term.now t.kind v q) else t
      | [] => t
    have heq : ∀ t ∈ F.vars, termValue ε ρ h (g' t) = termValue ε ρ h t := by
      intro t ht
      obtain ⟨kind, s, path, a⟩ := t
      cases a
      case true => cases path <;> simp [g']
      obtain ⟨w, n, hw, hk, hn⟩ := termValue_isSome (hd _ ht) rfl
      rw [hn]
      simp only at hw hk
      cases path with
      | nil => exact hn
      | cons g q =>
        show termValue ε ρ h (if s == c && g == f && !false then (HeapKnowledge.Term.now kind v q) else (HeapKnowledge.Term.now kind s (g :: q))) = some n
        split
        · rename_i hc
          simp only [Bool.not_false, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [termValue, termAt, Bool.false_eq_true, ite_false, guardReads_path hl hm hw, Option.bind_some, hk]
        · exact hn
    obtain ⟨F', hF'⟩ := Linear.Fact.mapVars_some g' F
    show (IndexFact.linear ((F.mapVars fun t => some (g' t)).getD F)).HoldsAt ε ρ h
    have hF'' : (F.mapVars fun t => some (g' t)) = some F' := hF'
    rw [hF'', Option.getD_some]
    refine ⟨fun t' ht' => ?_, ?_⟩
    · obtain ⟨t, ht, hte⟩ := Linear.Fact.mapVars_vars hF'' t' ht'
      cases hte
      rw [heq t ht]; exact hd t ht
    · refine (Linear.Fact.holds_mapVars hF'' fun t ht y hy => ?_).mpr hF
      cases hy
      simp only [termValuation, heq t ht]
  | guarded s p t B ih =>
    intro ⟨w, hw, hB⟩
    have hB' : t.holds w ∨ (B.lowerRead c f v).HoldsAt ε ρ h := hB.imp id (ih ·)
    cases p with
    | nil => exact ⟨w, hw, hB'⟩
    | cons g q =>
      show (if s == c && g == f then IndexFact.guarded v q t (B.lowerRead c f v)
        else .guarded s (g :: q) t (B.lowerRead c f v)).HoldsAt ε ρ h
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨w, by rw [← guardReads_read hl hm q]; exact hw, hB'⟩
      · exact ⟨w, hw, hB'⟩
  | index | length | bound | int | pastSafe | either | element | fieldRead | every | atIndex | apart | spineApart | elemSpineApart | same =>
    intro hB; exact hB

/-- **The lowered guards hold** where the atoms and the links do. -/
theorem lowerGuards_holds {ls : HeapLinks.Links} {as : List IndexAtom} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (ha : IndexHolds ε as ρ h) : IndexHolds ε (lowerGuards ls as) ρ h := by
  intro b hb hcond
  obtain ⟨a, haa, hb⟩ := List.mem_flatMap.mp hb
  split at hb
  · rename_i s f q t B hf
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha _ haa hcond
    · obtain ⟨⟨c, g, v⟩, hr, hrb⟩ := List.mem_filterMap.mp hb
      cases hcg : (c == s && g == f)
      · simp [hcg] at hrb
      · simp only [hcg, ite_true, Option.some.injEq] at hrb
        subst hrb
        simp only [Bool.and_eq_true, beq_iff_eq] at hcg
        obtain ⟨rfl, rfl⟩ := hcg
        exact lowerRead_holds hl hr _ (ha a haa hcond)
  · rcases List.mem_singleton.mp hb with rfl
    exact ha _ haa hcond
  · cases hb

/-- A knowledge's lowered form (as the merge's join reads it) holds where
the knowledge does. -/
theorem lowered_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    let pSet : Std.HashSet IndexAtom := Std.HashSet.ofList k.indices
    Holds { k with indices := k.indices ++ ((lowerGuards k.links k.indices).filter (!pSet.contains ·)) } ε ρ h := by
  intro pSet
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk
  refine ⟨h1, h2, h3, h4, h5, fun a ha hc => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact h6 a ha hc
  · exact lowerGuards_holds h3 h6 a (List.mem_filter.mp ha).1 hc

/-- Filtering out disjunctions from a knowledge's indices keeps it holding. -/
theorem filter_holds {k : Knowledge} {ρ : Env} {h : Heap} {pred : IndexAtom → Bool} (hk : Holds k ε ρ h) :
    Holds { k with indices := k.indices.filter pred } ε ρ h :=
  ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, fun a ha hc => hk.2.2.2.2.2 a (List.mem_filter.mp ha).1 hc⟩

/-- **A check against a holding knowledge is sound**: a fact
`indicesCheckWith` accepts over a knowledge that holds, with its guard tags
and alias classes, holds. -/
theorem check_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) {a : IndexAtom}
    (hc : indicesCheckWith (guardTags k) (HeapLinks.aliases k.links) k.links k.indices [a] none = true) :
    IndexHolds ε [a] ρ h :=
  indicesCheckWith_sound (m := none) (guardTags_sound hk) (fun _ _ hy => HeapLinks.aliases_eq hk.2.2.1 hy)
    hk.2.2.1 hc hk.2.2.2.2.2

/-! ## The guarded join on one path -/

theorem mem_ite_nil {α : Type} {c : Prop} [Decidable c] {l : List α} {x : α}
    (h : x ∈ (if c then [] else l)) : x ∈ l := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; cases h
  · rwa [ite_eq_right hc] at h

section Path
variable {preds : List State} {width fresh0 p : Nat} {ρ η : Env} {h : Heap}

/-- **`p`'s view materialized at any slots holds at the slots** on the path
through `p`. -/
theorem OnPath.projection_holds (P : OnPath preds width fresh0 p ε ρ η h) {v : State}
    (hv : StoreOk ε v.store (mVal preds width fresh0 ρ η) h)
    (hn : v.names = (mNames preds width fresh0).toList) (d : Nat) (slots : List Nat) :
    Holds (SinglePass.materialize v d slots false).1 ε ρ h := by
  rw [materialize_eq]
  refine materializeFrom_holds (η := mVal preds width fresh0 ρ η) (hn ▸ P.slotsNamed) fun a ha => ?_
  obtain ⟨n, hn⟩ := selectedFromIndex v slots true false a ha
  exact hv a (about_storeAll hn)

theorem mem_of_hashSet_ofList {as : List IndexAtom} {a : IndexAtom}
    (h : (Std.HashSet.ofList as).contains a = true) : a ∈ as :=
  List.contains_iff_mem.mp (Std.HashSet.mem_ofList.mp (Std.HashSet.contains_iff_mem.mp h))

theorem fieldReadLinkSet_holds {ls : HeapLinks.Links} {ρ : Env} {h : Heap}
    (hl : HeapLinks.Holds ls ρ h) (rep : Std.HashMap Nat Nat)
    (hrep : ∀ x, ρ (HeapLinks.repOf rep x) = ρ x)
    {c v : Nat} {f : String}
    (hm : (CertificateProducer.fieldReadLinkSet rep ls).contains
      (HeapLinks.repOf rep c, f, HeapLinks.repOf rep v) = true) :
    (HeapKnowledge.IndexFact.fieldRead v c f).HoldsAt ε ρ h := by
  have key : ∀ (xs : HeapLinks.Links) (acc : Std.HashSet (Nat × String × Nat)),
      (∀ l ∈ xs, l ∈ ls) →
      (∀ {c' f' v'}, acc.contains (c', f', v') = true →
        ∃ l ∈ ls, !l.alias = true ∧ !l.optional = true ∧ l.field = .str f' ∧
          HeapLinks.repOf rep l.cell = c' ∧ HeapLinks.repOf rep l.value = v') →
      ∀ {c' f' v'}, (xs.foldl (init := acc) fun acc l =>
        if !l.alias && !l.optional then match l.field with
          | .str fn => acc.insert (HeapLinks.repOf rep l.cell, fn, HeapLinks.repOf rep l.value)
          | .sym _ => acc
        else acc).contains (c', f', v') = true →
        ∃ l ∈ ls, !l.alias = true ∧ !l.optional = true ∧ l.field = .str f' ∧
          HeapLinks.repOf rep l.cell = c' ∧ HeapLinks.repOf rep l.value = v' := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc c' f' v' hc; exact hacc hc
    | cons l rest ih =>
      intro acc hsub hacc c' f' v' hc
      refine ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) ?_ hc
      intro c0 f0 v0 h0
      dsimp only at h0
      split at h0
      · rename_i hna
        cases hf : l.field with
        | sym _ => rw [hf] at h0; exact hacc h0
        | str fn =>
          rw [hf] at h0
          rw [Std.HashSet.contains_insert, Bool.or_eq_true] at h0
          rcases h0 with heq | hprev
          · simp only [beq_iff_eq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [Bool.and_eq_true] at hna
            exact ⟨l, hsub l (List.mem_cons_self ..), hna.1, hna.2, hf, rfl, rfl⟩
          · exact hacc hprev
      · exact hacc h0
  obtain ⟨l, hlmem, hna, hno, hfld, hrc, hrv⟩ := key ls {} (fun _ h => h) (by simp) hm
  have hlink := hl l hlmem
  cases hal : l.alias <;> cases hop : l.optional <;>
    simp only [hal, hop, Bool.false_eq_true, ↓reduceIte] at hna hno hlink
  · rw [hfld] at hlink
    rcases hlink with ⟨flds, cl, oid, loc, hcell, hlookup, hval⟩
    have hρc : ρ c = ρ l.cell := by rw [← hrep c, ← hrc, hrep]
    have hρv : ρ v = ρ l.value := by rw [← hrep v, ← hrv, hrep]
    simp only [HeapKnowledge.IndexFact.HoldsAt, hρc, hρv, HeapKnowledge.readPath, hcell, hlookup, hval]
  · cases hno
  · cases hna
  · cases hna

theorem factTrivialIn_holds {p : Knowledge} {ρ : Env} {h : Heap} (hk : Holds p ε ρ h)
    {tags : Option HeapKnowledge.GuardTagTable}
    (htags : ∀ tg, tags = some tg → tg = HeapKnowledge.GuardTagTable.ofKnowledge p)
    {links : Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))}
    (hlinks : ∀ rep lset, links = some (rep, lset) →
      rep = HeapLinks.repMap (HeapLinks.classes p.links) ∧ lset = CertificateProducer.fieldReadLinkSet rep p.links) :
    ∀ {F : HeapKnowledge.IndexFact},
      CertificateProducer.factTrivialIn (Std.HashSet.ofList p.indices) tags links F = true →
      F.HoldsAt ε ρ h := by
  intro F
  induction F with
  | either A B ihA ihB =>
    intro hf
    unfold CertificateProducer.factTrivialIn at hf
    simp only [Bool.or_eq_true] at hf
    rcases hf with ((hA | hB) | hA) | hB
    · exact Or.inl (hk.2.2.2.2.2 _ (mem_of_hashSet_ofList hA) (fun _ hc => by cases hc))
    · exact Or.inr (hk.2.2.2.2.2 _ (mem_of_hashSet_ofList hB) (fun _ hc => by cases hc))
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | guarded s q t B ihB =>
    intro hf
    unfold CertificateProducer.factTrivialIn at hf
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hf
    rcases hf with htg | ⟨hq, hB⟩
    · cases hts : tags with
      | none => rw [hts] at htg; cases htg
      | some tg =>
        rw [hts] at htg
        have heq := htags tg hts
        subst heq
        obtain ⟨v, hv, ht⟩ := HeapKnowledge.GuardTagTable.check_sound hk s q t htg
        exact ⟨v, hv, Or.inl ht⟩
    · cases q with
      | nil => exact ⟨ρ s, rfl, Or.inr (ihB hB)⟩
      | cons _ _ => cases hq
  | fieldRead v c f =>
    intro hf
    unfold CertificateProducer.factTrivialIn at hf
    simp only [Bool.or_eq_true] at hf
    rcases hf with hmem | hlk
    · exact hk.2.2.2.2.2 _ (mem_of_hashSet_ofList hmem) (fun _ hc => by cases hc)
    · cases hlq : links with
      | none => rw [hlq] at hlk; cases hlk
      | some rl =>
        obtain ⟨rep, lset⟩ := rl
        rw [hlq] at hlk
        obtain ⟨rfl, rfl⟩ := hlinks rep lset hlq
        exact fieldReadLinkSet_holds hk.2.2.1 _ (HeapLinks.repOf_eq (HeapLinks.classes_one hk.2.2.1)) hlk
  | _ =>
    intro hf
    unfold CertificateProducer.factTrivialIn at hf
    exact hk.2.2.2.2.2 _ (mem_of_hashSet_ofList hf) (fun _ hc => by cases hc)

theorem atomTrivialIn_holds {p : Knowledge} {ρ : Env} {h : Heap} (hk : Holds p ε ρ h)
    {tags : Option HeapKnowledge.GuardTagTable}
    (htags : ∀ tg, tags = some tg → tg = HeapKnowledge.GuardTagTable.ofKnowledge p)
    {links : Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))}
    (hlinks : ∀ rep lset, links = some (rep, lset) →
      rep = HeapLinks.repMap (HeapLinks.classes p.links) ∧ lset = CertificateProducer.fieldReadLinkSet rep p.links)
    {a : IndexAtom} (ha : CertificateProducer.atomTrivialIn (Std.HashSet.ofList p.indices) tags links a = true) :
    IndexHolds ε [a] ρ h := by
  intro x hx hcond
  have hxa : x = a := List.mem_singleton.mp hx
  subst hxa
  unfold CertificateProducer.atomTrivialIn at ha
  simp only [Bool.or_eq_true, Bool.and_eq_true] at ha
  rcases ha with hmem | ⟨_, htriv⟩
  · exact hk.2.2.2.2.2 x (mem_of_hashSet_ofList hmem) hcond
  · exact factTrivialIn_holds hk htags hlinks htriv

/-- Well-formedness of a prepared projection tuple `(p, pSet, tg, lk)`. -/
def PreparedOk (entry : Knowledge × Std.HashSet IndexAtom ×
    Option HeapKnowledge.GuardTagTable ×
    Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))) : Prop :=
  let (p, pSet, tg, lk) := entry
  pSet = Std.HashSet.ofList p.indices ∧
  (∀ t, tg = some t → t = HeapKnowledge.GuardTagTable.ofKnowledge p) ∧
  (∀ r lset, lk = some (r, lset) →
    r = HeapLinks.repMap (HeapLinks.classes p.links) ∧ lset = CertificateProducer.fieldReadLinkSet r p.links)

theorem mem_insertByDesc {α : Type} {x y : Nat × α} {ys : List (Nat × α)} :
    y ∈ CertificateProducer.insertByDesc x ys ↔ y = x ∨ y ∈ ys := by
  induction ys with
  | nil => simp [CertificateProducer.insertByDesc]
  | cons z zs ih =>
    unfold CertificateProducer.insertByDesc
    split <;> simp [ih, or_left_comm]

theorem mem_sortByDesc {α : Type} {y : Nat × α} {xs : List (Nat × α)} :
    y ∈ CertificateProducer.sortByDesc xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp [CertificateProducer.sortByDesc]
  | cons x xs ih => simp [CertificateProducer.sortByDesc, mem_insertByDesc, ih]

theorem narrowKnowledge_holds {p : Knowledge} {rep? : Option (Std.HashMap Nat Nat)}
    {slow : List IndexAtom} {ρ : Env} {h : Heap} (hk : Holds p ε ρ h) :
    Holds (CertificateProducer.narrowKnowledge p rep? slow) ε ρ h := by
  unfold CertificateProducer.narrowKnowledge
  dsimp only
  split
  · exact hk
  · split
    · exact filter_holds hk
    · split
      · exact hk
      · exact filter_holds hk

theorem filterOnePrepared_sub {useCases : Bool} {cur : List IndexAtom}
    {entry : Knowledge × Std.HashSet IndexAtom × Option HeapKnowledge.GuardTagTable ×
      Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))}
    {x : IndexAtom} (hx : x ∈ CertificateProducer.filterOnePrepared useCases cur entry) : x ∈ cur := by
  unfold CertificateProducer.filterOnePrepared at hx
  split at hx
  · cases hx
  · dsimp only at hx
    split at hx
    · exact (List.mem_filter.mp (by simpa [List.partition_eq_filter_filter] using hx)).1
    · rcases List.mem_append.mp hx with hf | hs
      · exact (List.mem_filter.mp (by simpa [List.partition_eq_filter_filter] using hf)).1
      · have hs' := HeapKnowledge.indicesFilter_sub hs
        simp only [List.partition_eq_filter_filter, List.mem_filter] at hs'
        exact hs'.1

theorem filterOnePrepared_holds {useCases : Bool} {cur : List IndexAtom}
    {entry : Knowledge × Std.HashSet IndexAtom × Option HeapKnowledge.GuardTagTable ×
      Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))}
    {ρ : Env} {h : Heap} (hok : PreparedOk entry) (hk : Holds entry.1 ε ρ h) :
    IndexHolds ε (CertificateProducer.filterOnePrepared useCases cur entry) ρ h := by
  intro x hx hcond
  obtain ⟨p, pSet, tg, lk⟩ := entry
  obtain ⟨rfl, htg, hlk⟩ := hok
  unfold CertificateProducer.filterOnePrepared at hx
  split at hx
  · cases hx
  · dsimp only at hx
    split at hx
    · have hf : x ∈ cur.filter (CertificateProducer.atomTrivialIn (Std.HashSet.ofList p.indices) tg lk) := by
        simpa [List.partition_eq_filter_filter] using hx
      exact atomTrivialIn_holds hk htg hlk (List.mem_filter.mp hf).2 x (List.mem_singleton.mpr rfl) hcond
    · rcases List.mem_append.mp hx with hf | hs
      · have hf' : x ∈ cur.filter (CertificateProducer.atomTrivialIn (Std.HashSet.ofList p.indices) tg lk) := by
          simpa [List.partition_eq_filter_filter] using hf
        exact atomTrivialIn_holds hk htg hlk (List.mem_filter.mp hf').2 x (List.mem_singleton.mpr rfl) hcond
      · exact HeapKnowledge.indicesFilter_holds (narrowKnowledge_holds hk) x hs hcond

theorem foldl_filterOnePrepared_sub (useCases : Bool) :
    ∀ (es : List (Knowledge × Std.HashSet IndexAtom × Option HeapKnowledge.GuardTagTable ×
        Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))))
      (cur : List IndexAtom) (x : IndexAtom),
      x ∈ es.foldl (CertificateProducer.filterOnePrepared useCases) cur → x ∈ cur
  | [], _, _, hx => hx
  | _ :: es, _, x, hx => filterOnePrepared_sub (foldl_filterOnePrepared_sub useCases es _ x hx)

theorem foldl_filterOnePrepared_holds {ρ : Env} {h : Heap} (useCases : Bool) :
    ∀ (es : List (Knowledge × Std.HashSet IndexAtom × Option HeapKnowledge.GuardTagTable ×
        Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat))))
      (cur : List IndexAtom) {e},
      e ∈ es → PreparedOk e → Holds e.1 ε ρ h →
      IndexHolds ε (es.foldl (CertificateProducer.filterOnePrepared useCases) cur) ρ h
  | [], _, _, he, _, _ => by cases he
  | q :: es, cur, e, he, hok, hk => by
    rcases List.mem_cons.mp he with rfl | he
    · intro x hx hcond
      exact filterOnePrepared_holds hok hk x (foldl_filterOnePrepared_sub useCases es _ x hx) hcond
    · exact foldl_filterOnePrepared_holds useCases es (CertificateProducer.filterOnePrepared useCases cur q) he hok hk

theorem filterPreparedAll_holds {useCases : Bool}
    {es : List (Knowledge × Std.HashSet IndexAtom × Option HeapKnowledge.GuardTagTable ×
      Option (Std.HashMap Nat Nat × Std.HashSet (Nat × String × Nat)))}
    {cs : List IndexAtom} {e} {ρ : Env} {h : Heap}
    (he : e ∈ es) (hok : PreparedOk e) (hk : Holds e.1 ε ρ h) :
    IndexHolds ε (CertificateProducer.filterPreparedAll useCases es cs) ρ h := by
  intro x hx hcond
  unfold CertificateProducer.filterPreparedAll at hx
  split at hx
  · cases hx
  · cases es with
    | nil => cases he
    | cons e0 rest =>
      cases rest with
      | nil =>
        have hEq : e = e0 := List.mem_singleton.mp he
        subst hEq
        exact filterOnePrepared_holds hok hk x hx hcond
      | cons e1 rest' =>
        dsimp only at hx
        split at hx
        · have hf : x ∈ cs.filter fun a => (e0 :: e1 :: rest').all fun (_, pSet, tg, links) =>
              CertificateProducer.atomTrivialIn pSet tg links a := by
            simpa [List.partition_eq_filter_filter] using hx
          have hall := List.all_eq_true.mp (List.mem_filter.mp hf).2 e he
          obtain ⟨p, pSet, tg, lk⟩ := e
          obtain ⟨rfl, htg, hlk⟩ := hok
          exact atomTrivialIn_holds hk htg hlk hall x (List.mem_singleton.mpr rfl) hcond
        · rcases List.mem_append.mp hx with hf | hr
          · have hf' : x ∈ cs.filter fun a => (e0 :: e1 :: rest').all fun (_, pSet, tg, links) =>
                CertificateProducer.atomTrivialIn pSet tg links a := by
              simpa [List.partition_eq_filter_filter] using hf
            have hall := List.all_eq_true.mp (List.mem_filter.mp hf').2 e he
            obtain ⟨p, pSet, tg, lk⟩ := e
            obtain ⟨rfl, htg, hlk⟩ := hok
            exact atomTrivialIn_holds hk htg hlk hall x (List.mem_singleton.mpr rfl) hcond
          · have he' : e ∈ (CertificateProducer.sortByDesc ((e0 :: e1 :: rest').map fun entry =>
                ((cs.partition fun a => (e0 :: e1 :: rest').all fun (_, pSet, tg, links) =>
                  CertificateProducer.atomTrivialIn pSet tg links a).2.foldl
                  (fun n a => if CertificateProducer.atomTrivialIn entry.2.1 entry.2.2.1 entry.2.2.2 a then n else n + 1) 0,
                  entry))).map Prod.snd :=
              List.mem_map.mpr ⟨_, mem_sortByDesc.mpr (List.mem_map.mpr ⟨e, he, rfl⟩), rfl⟩
            exact foldl_filterOnePrepared_holds useCases _ _ he' hok hk x hr hcond

theorem filterAllFast_holds {ρ : Env} {h : Heap} (useCases : Bool := true)
    (ps : List Knowledge) (cs : List IndexAtom) {p : Knowledge}
    (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε (CertificateProducer.filterAllFast ps cs useCases) ρ h := by
  unfold CertificateProducer.filterAllFast
  split
  · intro x hx; cases hx
  · refine filterPreparedAll_holds (List.mem_map.mpr ⟨p, hp, rfl⟩) ?_ hk
    refine ⟨rfl, ?_, ?_⟩
    · intro t ht
      split at ht
      · cases ht
      · injection ht with ht; exact ht.symm
    · intro r lset hl
      split at hl
      · cases hl
      · rename_i hnl
        injection hl with hl
        simp only [Prod.mk.injEq] at hl
        obtain ⟨hrep, hlset⟩ := hl
        subst hrep
        have hnl' : (cs.any fun a => a.cond.isNone && CertificateProducer.hasFieldRead a.fact) = true := by
          simpa using hnl
        refine ⟨?_, hlset.symm⟩
        generalize (cs.any fun a => a.cond.isNone && match a.fact with | .guarded .. => true | _ => false) = b
        cases b
        · simp [hnl']
        · rfl

theorem filterTaggedFast_holds {ρ : Env} {h : Heap} (useCases : Bool := true)
    (ps : List Knowledge) (cs : List IndexAtom) {p : Knowledge}
    (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε (CertificateProducer.filterTaggedFast ps (ps.map HeapKnowledge.GuardTagTable.ofKnowledge) cs useCases) ρ h := by
  unfold CertificateProducer.filterTaggedFast
  split
  · intro x hx; cases hx
  · have hmem : (p, HeapKnowledge.GuardTagTable.ofKnowledge p) ∈ ps.zip (ps.map HeapKnowledge.GuardTagTable.ofKnowledge) := by
      clear hk
      induction ps with
      | nil => cases hp
      | cons q qs ih =>
        rcases List.mem_cons.mp hp with rfl | hp
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hp)
    refine filterPreparedAll_holds (List.mem_map.mpr ⟨_, hmem, rfl⟩) ?_ hk
    refine ⟨rfl, fun t ht => by injection ht with ht; exact ht.symm, ?_⟩
    intro r lset hl
    split at hl
    · cases hl
    · injection hl with hl
      simp only [Prod.mk.injEq] at hl
      obtain ⟨hrep, hlset⟩ := hl
      subst hrep
      exact ⟨rfl, hlset.symm⟩

theorem joinGuarded_holds {ρ : Env} {h : Heap} {ps : List Knowledge} {k : Knowledge} {p : Knowledge} {x : IndexAtom}
    (hx : x ∈ CertificateProducer.joinGuarded ps k) (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε [x] ρ h := by
  intro y hy
  rw [List.mem_singleton.mp hy]
  unfold CertificateProducer.joinGuarded at hx
  exact filterTaggedFast_holds true ps _ hp hk x hx

theorem mem_filterAllFast_holds {ρ : Env} {h : Heap} {useCases : Bool} {ps : List Knowledge} {cs : List IndexAtom} {p : Knowledge} {x : IndexAtom}
    (hx : x ∈ CertificateProducer.filterAllFast ps cs useCases) (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε [x] ρ h := by
  intro y hy
  rw [List.mem_singleton.mp hy]
  exact filterAllFast_holds useCases ps cs hp hk x hx

theorem mem_filterTaggedFast_holds {ρ : Env} {h : Heap} {useCases : Bool} {ps : List Knowledge} {cs : List IndexAtom} {p : Knowledge} {x : IndexAtom}
    (hx : x ∈ CertificateProducer.filterTaggedFast ps (ps.map HeapKnowledge.GuardTagTable.ofKnowledge) cs useCases)
    (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε [x] ρ h := by
  intro y hy
  rw [List.mem_singleton.mp hy]
  exact filterTaggedFast_holds useCases ps cs hp hk x hx

theorem loweredCond_holds {k : Knowledge} {ρ : Env} {h : Heap} (hk : Holds k ε ρ h) :
    Holds (if k.indices.any (fun a => match a.fact with | .guarded _ (_ :: _) _ _ => true | _ => false) then
      let pSet : Std.HashSet IndexAtom := Std.HashSet.ofList k.indices
      { k with indices := k.indices ++ ((lowerGuards k.links k.indices).filter (!pSet.contains ·)) }
    else k) ε ρ h := by
  split
  · exact lowered_holds hk
  · exact hk

theorem mem_ite_append_filterTagged {ps : List Knowledge} {cs1 cs2 cs3 : List IndexAtom} {cond : Bool} {x : IndexAtom}
    {p : Knowledge} (hp : p ∈ ps) (hk : Holds p ε ρ h)
    (hx : x ∈ (if cond then CertificateProducer.filterTaggedFast ps (ps.map HeapKnowledge.GuardTagTable.ofKnowledge) cs1 false
      else CertificateProducer.filterTaggedFast ps (ps.map HeapKnowledge.GuardTagTable.ofKnowledge) cs2 false ++
        CertificateProducer.filterTaggedFast ps (ps.map HeapKnowledge.GuardTagTable.ofKnowledge) cs3 false)) :
    IndexHolds ε [x] ρ h := by
  split at hx
  · exact mem_filterTaggedFast_holds hx hp hk
  · rcases List.mem_append.mp hx with hx | hx
    · exact mem_filterTaggedFast_holds hx hp hk
    · exact mem_filterTaggedFast_holds hx hp hk

theorem viewsK_holds {vs : List State} {v : State} (hv : v ∈ vs)
    {width : Nat} {seedSlots slots : List Nat}
    (h1 : Holds (SinglePass.materialize v width seedSlots false).1 ε ρ h)
    (h2 : Holds (SinglePass.materialize v width slots false).1 ε ρ h) :
    ∃ vk ∈ (if (!seedSlots.isEmpty && slots.all seedSlots.contains) = true then
        (if seedSlots.isEmpty = true then [] else vs.map fun ps => (SinglePass.materialize ps width seedSlots false).1)
      else vs.map fun ps => (SinglePass.materialize ps width slots false).1),
      Holds vk ε ρ h := by
  cases hse : seedSlots.isEmpty
  · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ⟨_, List.mem_map.mpr ⟨v, hv, rfl⟩, h1⟩
    · exact ⟨_, List.mem_map.mpr ⟨v, hv, rfl⟩, h2⟩
  · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, List.mem_map.mpr ⟨v, hv, rfl⟩, h2⟩

theorem mem_ite_nil_of {α : Type} {c : Bool} {l : List α} {x : α}
    (h : x ∈ (if c then [] else l)) : c = false ∧ x ∈ l := by
  cases c
  · exact ⟨rfl, h⟩
  · cases h

theorem mem_filterAllFast_viewsK_holds {vs : List State} {v : State} (hv : v ∈ vs)
    {width : Nat} {seedSlots slots : List Nat} {f : Knowledge → Knowledge}
    (hf : ∀ k, Holds k ε ρ h → Holds (f k) ε ρ h)
    {cs : List IndexAtom} {useCases : Bool} {x : IndexAtom}
    (h1 : Holds (SinglePass.materialize v width seedSlots false).1 ε ρ h)
    (h2 : Holds (SinglePass.materialize v width slots false).1 ε ρ h)
    (hx : x ∈ CertificateProducer.filterAllFast
      ((if (!seedSlots.isEmpty && slots.all seedSlots.contains) = true then
          (if seedSlots.isEmpty = true then [] else vs.map fun ps => (SinglePass.materialize ps width seedSlots false).1)
        else vs.map fun ps => (SinglePass.materialize ps width slots false).1).map f) cs useCases) :
    IndexHolds ε [x] ρ h := by
  obtain ⟨vk, hvkMem, hvkHolds⟩ := viewsK_holds hv h1 h2
  exact mem_filterAllFast_holds hx (List.mem_map.mpr ⟨vk, hvkMem, rfl⟩) (hf vk hvkHolds)

theorem mem_filterTaggedFast_if_holds {ps : List Knowledge} {cond : Bool} (hc : cond = false)
    {cs1 cs2 cs3 : List IndexAtom} {want : Bool} {x : IndexAtom}
    {p : Knowledge} (hp : p ∈ ps) (hk : Holds p ε ρ h)
    (hx : x ∈ (if want then
        CertificateProducer.filterTaggedFast ((if cond then [] else ps).map fun p => { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true })
          (((if cond then [] else ps).map fun p => { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true }).map HeapKnowledge.GuardTagTable.ofKnowledge) cs1 false
      else
        CertificateProducer.filterTaggedFast ((if cond then [] else ps).map fun p => { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true })
          (((if cond then [] else ps).map fun p => { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true }).map HeapKnowledge.GuardTagTable.ofKnowledge) cs2 false ++
        CertificateProducer.filterTaggedFast ((if cond then [] else ps).map fun p => { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true })
          (((if cond then [] else ps).map fun p => { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true }).map HeapKnowledge.GuardTagTable.ofKnowledge) cs3 false)) :
    IndexHolds ε [x] ρ h := by
  subst hc
  exact mem_ite_append_filterTagged (List.mem_map.mpr ⟨p, hp, rfl⟩) (filter_holds hk) hx

/-- **(Guarded join) The guarded facts the merge keeps hold** at the slot
environment on the path through any predecessor `p`: `GuardedHolds`. -/
theorem guardedHolds_of_path (P : OnPath preds width fresh0 p ε ρ η h) : GuardedHolds preds width fresh0 ε ρ h := by
  obtain ⟨v, hvm, hv, -⟩ := P.view_ok
  have hvn : v.names = (mNames preds width fresh0).toList := by
    unfold mergeViews at hvm
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hvm
    rfl
  intro x hx
  unfold mergeGuarded at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨hse, hx⟩ := mem_ite_nil_of hx
    rcases List.mem_append.mp hx with hx | hx
    · -- the joined facts: each checked against every lowered flat projection
      simp only [SinglePass.timedKind, hse, Bool.false_eq_true, ↓reduceIte] at hx
      exact joinGuarded_holds hx
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨v, hvm, rfl⟩, rfl⟩, rfl⟩)
        (loweredCond_holds (filter_holds (P.projection_holds hv hvn _ _)))
    · -- the tagged facts: each checked against every flat projection
      simp only [SinglePass.timedKind] at hx
      replace hx := mem_ite_nil hx
      exact mem_filterTaggedFast_if_holds hse (List.mem_map.mpr ⟨v, hvm, rfl⟩)
        (P.projection_holds hv hvn _ _) hx
  · -- the disjoined facts: batched `filterAllFast` over filtered views
    simp only [SinglePass.timedKind] at hx
    replace hx := mem_ite_nil hx
    replace hx := mem_ite_nil hx
    rcases List.mem_append.mp hx with hx | hx
    · replace hx := mem_ite_nil hx
      exact mem_filterAllFast_viewsK_holds hvm (fun _ hk => filter_holds hk)
        (P.projection_holds hv hvn _ _) (P.projection_holds hv hvn _ _) hx
    · replace hx := mem_ite_nil hx
      exact mem_filterAllFast_viewsK_holds hvm (fun _ hk => filter_holds hk)
        (P.projection_holds hv hvn _ _) (P.projection_holds hv hvn _ _) hx

end Path

end Verification.TolerantFrames
