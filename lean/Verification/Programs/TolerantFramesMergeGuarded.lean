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
  | index | length | bound | int | pastSafe | either | element | fieldRead | every | atIndex | apart | spineApart | same =>
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
    Holds { k with indices := k.indices ++ ((lowerGuards k.links k.indices).filter (!k.indices.contains ·)) } ε ρ h := by
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
  obtain ⟨n, hn⟩ := selectedFromIndex v slots true a ha
  exact hv a (about_storeAll hn)

theorem foldl_indicesFilter_sub : ∀ (ps : List Knowledge) (cs : List IndexAtom) (x : IndexAtom),
    x ∈ ps.foldl (fun cs p => HeapKnowledge.indicesFilter p cs) cs → x ∈ cs
  | [], _, _, hx => hx
  | _ :: ps, _, x, hx => HeapKnowledge.indicesFilter_sub (foldl_indicesFilter_sub ps _ x hx)

theorem foldl_indicesFilter_holds {ρ : Env} {h : Heap} :
    ∀ (ps : List Knowledge) (cs : List IndexAtom) {p : Knowledge},
      p ∈ ps → Holds p ε ρ h → IndexHolds ε (ps.foldl (fun cs q => HeapKnowledge.indicesFilter q cs) cs) ρ h
  | [], _, _, hp, _ => by cases hp
  | q :: ps, cs, p, hp, hk => by
    rcases List.mem_cons.mp hp with rfl | hp
    · intro x hx hcond
      exact HeapKnowledge.indicesFilter_holds hk x (foldl_indicesFilter_sub ps _ x hx) hcond
    · exact foldl_indicesFilter_holds ps (HeapKnowledge.indicesFilter q cs) hp hk

theorem joinGuarded_holds {ρ : Env} {h : Heap} {ps : List Knowledge} {k : Knowledge} {p : Knowledge} {x : IndexAtom}
    (hx : x ∈ CertificateProducer.joinGuarded ps k) (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε [x] ρ h := by
  intro y hy
  rw [List.mem_singleton.mp hy]
  unfold CertificateProducer.joinGuarded at hx
  exact foldl_indicesFilter_holds ps _ hp hk x hx

theorem mem_foldl_indicesFilter_holds {ρ : Env} {h : Heap} {ps : List Knowledge} {cs : List IndexAtom} {p : Knowledge} {x : IndexAtom}
    (hx : x ∈ ps.foldl (fun cs q => HeapKnowledge.indicesFilter q cs) cs) (hp : p ∈ ps) (hk : Holds p ε ρ h) :
    IndexHolds ε [x] ρ h := by
  intro y hy
  rw [List.mem_singleton.mp hy]
  exact foldl_indicesFilter_holds ps cs hp hk x hx

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
  · replace hx := mem_ite_nil hx
    rcases List.mem_append.mp hx with hx | hx
    · -- the joined facts: each checked against every lowered flat projection
      simp only [SinglePass.timedKind] at hx
      exact joinGuarded_holds hx
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨v, hvm, rfl⟩, rfl⟩, rfl⟩)
        (lowered_holds (filter_holds (P.projection_holds hv hvn _ _)))
    · -- the tagged facts: each checked against every flat projection
      simp only [SinglePass.timedKind] at hx
      replace hx := mem_ite_nil hx
      exact mem_foldl_indicesFilter_holds hx
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨v, hvm, rfl⟩, rfl⟩)
        (filter_holds (P.projection_holds hv hvn _ _))
  · -- the disjoined facts: each checked against every filtered view at its own slots
    simp only [SinglePass.timedKind] at hx
    replace hx := mem_ite_nil hx
    have hc := List.all_eq_true.mp (List.mem_filter.mp hx).2 _ hvm
    exact check_holds (filter_holds (P.projection_holds hv hvn _ _)) hc

end Path

end Verification.TolerantFrames
