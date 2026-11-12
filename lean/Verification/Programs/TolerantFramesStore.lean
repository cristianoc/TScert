import Verification.Programs.TolerantFramesDelta

/-! # Tolerant frames: the store's well-formedness and its removals

The pass's store (`SinglePass.Store`) is a set of live facts and an index by
name. Its well-formedness (`StoreWF`): live facts canonical, each fact the
index lists under a name live, mentioning that name, and listed there once.
This module proves that every insertion and removal keeps it, from the lemmas
of `Std.HashSet` and `Std.HashMap`, and that a fact `Store.remove` removes
leaves the store; so the removal loop of a step's delta removes each handed
fact the output lost (`removedLeave`), and a writing step's delta keeps every
fact holding (`applyDelta_writing`). -/
namespace Verification.TolerantFrames
open Verification
open Verification.SinglePass (Atom Store State)

/-! ## Facts in canonical form, names once -/

theorem canon_canon (a : Atom) : a.canon.canon = a.canon := by
  cases a with
  | index x => rcases x with ⟨f, c, neg⟩; cases c <;> cases neg <;> rfl
  | elem e => rcases e with ⟨sl, p, c, neg⟩; cases c <;> cases neg <;> simp [Atom.canon]
  | cell _ | value _ | link _ | sep _ => rfl

theorem nodup_eraseDups : ∀ (l : List Nat), l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, nodup_eraseDups _⟩
    have := List.mem_eraseDups.mp h
    simp at this
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- **An index updated at distinct names**: each of them holds `g` of its
list, every other name its list. -/
theorem getD_foldl_insert (g : List Atom → List Atom) :
    ∀ (ns : List Nat) (m : Std.HashMap Nat (List Atom)) (k : Nat), ns.Nodup →
      (ns.foldl (fun m n => m.insert n (g (m.getD n []))) m).getD k [] =
        if k ∈ ns then g (m.getD k []) else m.getD k []
  | [], m, k, _ => by simp
  | n :: ns, m, k, hnd => by
    obtain ⟨hn, hnd⟩ := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    rw [getD_foldl_insert g ns _ k hnd]
    simp only [Std.HashMap.getD_insert]
    by_cases hk : k = n
    · subst hk; simp [hn]
    · have : (n == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
      simp [this, hk]

theorem contains_foldl_insert {x : Atom} :
    ∀ (l : List Atom) (m : Std.HashSet Atom), (l.foldl (·.insert ·) m).contains x = true → x ∈ l ∨ m.contains x = true
  | [], _, h => .inr h
  | a :: l, m, h => by
    rcases contains_foldl_insert l _ h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · rw [Std.HashSet.contains_insert] at h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact .inl (beq_iff_eq.mp h ▸ List.mem_cons_self ..)
      · exact .inr h

/-! ## Each operation keeps the store well-formed -/

theorem storeAll_live {s : Store} (w : StoreWF s) {a : Atom} (ha : a ∈ storeAll s) : a ∈ s.live := by
  rcases List.mem_append.mp ha with ha | ha
  · exact mem_keysOf.mp ha
  · obtain ⟨n, hn⟩ := mem_valsOf.mp ha
    exact w.indexed n a hn

theorem storeAll_canon {s : Store} (w : StoreWF s) {a : Atom} (ha : a ∈ storeAll s) : a.canon = a :=
  w.canonical a (storeAll_live w ha)

/-- **A fact added raw keeps the store well-formed.** -/
theorem addRaw_wf {s : Store} (w : StoreWF s) (a : Atom) : StoreWF (s.addRaw a) := by
  unfold Store.addRaw
  dsimp only
  split
  · exact w
  · rename_i hc
    have hnot : a.canon ∉ s.live := fun h => hc (Std.HashSet.contains_iff_mem.mpr h)
    have hg := fun k => getD_foldl_insert (a.canon :: ·) a.canon.names.eraseDups s.byName k (nodup_eraseDups _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Std.HashSet.mem_insert.mp hx with h | h
      · rw [← beq_iff_eq.mp h]; exact canon_canon a
      · exact w.canonical x h
    · intro n x hx
      dsimp only at hx
      rw [hg n] at hx
      refine Std.HashSet.mem_insert.mpr ?_
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl (beq_self_eq_true _)
        · exact .inr (w.indexed n x hx)
      · exact .inr (w.indexed n x hx)
    · intro n x hx
      dsimp only at hx
      rw [hg n] at hx
      split at hx
      · rename_i hn
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_eraseDups.mp hn
        · exact w.named n x hx
      · exact w.named n x hx
    · intro n
      dsimp only
      rw [hg n]
      split
      · exact List.nodup_cons.mpr ⟨fun h => hnot (w.indexed n _ h), w.nodup n⟩
      · exact w.nodup n

/-- **A fact removed keeps the store well-formed.** -/
theorem remove_wf {s : Store} (w : StoreWF s) (a : Atom) : StoreWF (s.remove a) := by
  unfold Store.remove
  dsimp only
  split
  · have hg := fun k => getD_foldl_insert (·.erase a.canon) a.canon.names.eraseDups s.byName k (nodup_eraseDups _)
    refine ⟨fun x hx => w.canonical x (Std.HashSet.mem_erase.mp hx).2, ?_, ?_, ?_⟩
    · intro n x hx
      dsimp only at hx
      rw [hg n] at hx
      split at hx
      · have hne : a.canon ≠ x := fun h => by subst h; exact (w.nodup n).not_mem_erase hx
        exact Std.HashSet.mem_erase.mpr ⟨beq_eq_false_iff_ne.mpr hne, w.indexed n x (List.mem_of_mem_erase hx)⟩
      · rename_i hn
        have hne : a.canon ≠ x := fun h => by subst h; exact hn (List.mem_eraseDups.mpr (w.named n _ hx))
        exact Std.HashSet.mem_erase.mpr ⟨beq_eq_false_iff_ne.mpr hne, w.indexed n x hx⟩
    · intro n x hx
      dsimp only at hx
      rw [hg n] at hx
      split at hx
      · exact w.named n x (List.mem_of_mem_erase hx)
      · exact w.named n x hx
    · intro n
      dsimp only
      rw [hg n]
      split
      · exact (w.nodup n).erase _
      · exact w.nodup n
  · exact w

theorem foldl_remove_wf : ∀ (as : List Atom) (s : Store), StoreWF s → StoreWF (as.foldl Store.remove s)
  | [], _, w => w
  | _ :: as, _, w => foldl_remove_wf as _ (remove_wf w _)

/-- **A bound added keeps the store well-formed.** -/
theorem addBound_wf {s : Store} (w : StoreWF s) (a : Atom) : StoreWF (s.addBound a) := by
  unfold Store.addBound
  dsimp only
  split
  · exact w
  · split
    · split
      · exact w
      · exact addRaw_wf (foldl_remove_wf _ _ w) _
    · exact addRaw_wf w _

theorem foldl_addBound_wf {c : Option Nat} {neg : Bool} :
    ∀ (Fs : List (Linear.Fact HeapKnowledge.Term)) (s : Store), StoreWF s →
      StoreWF (Fs.foldl (fun (s : Store) F => s.addBound (.index ⟨.linear F, c, neg⟩)) s)
  | [], _, w => w
  | _ :: Fs, _, w => foldl_addBound_wf Fs _ (addBound_wf w _)

/-- **A fact added (`Store.add`) keeps the store well-formed.** -/
theorem add_wf {s : Store} (w : StoreWF s) (a : Atom) : StoreWF (s.add a) := by
  unfold Store.add
  dsimp only
  split
  · exact w
  · refine addBound_wf ?_ _
    split
    · exact foldl_addBound_wf _ _ w
    · exact w

/-! ## A removed fact leaves the store -/

/-- A removal keeps only facts the store held. -/
theorem remove_sub {s : Store} {a x : Atom} (hx : x ∈ storeAll (s.remove a)) : x ∈ storeAll s := by
  unfold Store.remove at hx
  dsimp only at hx
  split at hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (keys_erase _ _ _ hx)
    · refine vals_foldl (fun x => x ∈ storeAll s) _ (fun m n hm y hy => ?_) _ _
        (fun y hy => List.mem_append_right _ hy) x hx
      rcases vals_insert _ _ _ _ hy with hy | hy
      · exact hm y (findD_vals _ _ _ (List.mem_of_mem_erase hy))
      · exact hm y hy
  · exact hx

/-- **A fact `Store.remove` removes leaves the store**: it is erased from the
live set and from each of its names' lists, which hold it once, and no other
list holds it. -/
theorem remove_absent {s : Store} (w : StoreWF s) (a : Atom) : a ∉ storeAll (s.remove a) := by
  intro h
  have hs := remove_sub h
  have hc := storeAll_canon w hs
  have hl : s.live.contains a.canon = true := by rw [hc]; exact Std.HashSet.contains_iff_mem.mpr (storeAll_live w hs)
  unfold Store.remove at h
  dsimp only at h
  rw [if_pos hl] at h
  rcases List.mem_append.mp h with h | h
  · have := (Std.HashSet.mem_erase.mp (mem_keysOf.mp h)).1
    rw [hc] at this
    simp at this
  · obtain ⟨n, hn⟩ := mem_valsOf.mp h
    rw [getD_foldl_insert (·.erase a.canon) _ _ n (nodup_eraseDups _)] at hn
    split at hn
    · rw [hc] at hn; exact (w.nodup n).not_mem_erase hn
    · rename_i hnn
      rw [hc] at hnn
      exact hnn (List.mem_eraseDups.mpr (w.named n a hn))

/-- **The removal loop removes each handed fact whose image the output
lost, and keeps the store well-formed.** -/
theorem deltaRemove_wf {s : Store} (w : StoreWF s) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge)
    (shift : Bool) : StoreWF (deltaRemove s pairs out shift) ∧ RemovedLeave s pairs out shift := by
  let P : Nat → Store → Prop := fun k t => StoreWF t ∧ (∀ x ∈ storeAll t, x ∈ storeAll s) ∧
    ∀ i < k, ∀ ab, pairs[i]? = some ab → deltaImage shift ab.2 ∉ SinglePass.atomsOf out → ab.1 ∉ storeAll t
  have hend : ∀ t, P pairs.length t → StoreWF t ∧ ∀ x ∈ storeAll t,
      x ∈ storeAll s ∧ ∀ ab ∈ pairs, deltaImage shift ab.2 ∉ SinglePass.atomsOf out → x ≠ ab.1 := by
    intro t ⟨wt, hsub, hgone⟩
    refine ⟨wt, fun x hx => ⟨hsub x hx, fun ab hab himg he => ?_⟩⟩
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hab
    exact hgone i (List.getElem?_eq_some_iff.mp hi).1 ab hi himg (he ▸ hx)
  unfold RemovedLeave
  unfold deltaRemove
  simp only [Id.run]
  refine forIn_idx_bind (R := fun t => StoreWF t ∧ ∀ x ∈ storeAll t,
      x ∈ storeAll s ∧ ∀ ab ∈ pairs, deltaImage shift ab.2 ∉ SinglePass.atomsOf out → x ≠ ab.1)
    (Q := fun t => StoreWF t ∧ ∀ x ∈ storeAll t,
      x ∈ storeAll s ∧ ∀ ab ∈ pairs, deltaImage shift ab.2 ∉ SinglePass.atomsOf out → x ≠ ab.1)
    pairs s _ P _ ⟨w, fun _ h => h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩ ?_ ?_ hend (fun _ h => h)
  · intro k ab t t' hk ⟨wt, hsub, hgone⟩ hf
    split at hf
    · rename_i hnc
      cases hf
      refine ⟨remove_wf wt _, fun x hx => hsub x (remove_sub hx), fun i hi ab' hab' himg => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact fun hx => hgone i hi ab' hab' himg (remove_sub hx)
      · rw [hk] at hab'; cases hab'
        exact remove_absent wt _
    · rename_i hc
      cases hf
      refine ⟨wt, hsub, fun i hi ab' hab' himg => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hgone i hi ab' hab' himg
      · rw [hk] at hab'; cases hab'
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
        rcases contains_foldl_insert _ _ hc with h | h
        · exact absurd h himg
        · simp at h
  · intro k ab t t' _ _ hf
    split at hf <;> cases hf

/-- **A fact the removal loop removes leaves the store**, for a well-formed
store. -/
theorem removedLeave {s : Store} (w : StoreWF s) (pairs : List (Atom × Atom)) (out : HeapKnowledge.Knowledge)
    (shift : Bool) : RemovedLeave s pairs out shift :=
  (deltaRemove_wf w pairs out shift).2

/-- **(Writing) A step's delta keeps the store's facts holding** where every
stored fact either holds after the step (the facts its effect keeps) or is
handed to the rule (a pair), and the removal loop removes the handed facts
whose image the output lost (`removedLeave`, for a well-formed store): a kept
handed fact holds by the output, read back through the pushed slots and the
table. -/
theorem applyDelta_writing {s : Store} {pairs : List (Atom × Atom)}
    {out : HeapKnowledge.Knowledge} {back f : Nat → Option Nat} {η ρ : Env} {v : Tm} {h : Heap}
    (w : StoreWF s)
    (hcov : ∀ x ∈ storeAll s, AtomHolds x η h ∨ ∃ b, (x, b) ∈ pairs ∧ x.rename f = some b)
    (hf : ∀ x i, f x = some i → ρ i = η x) (hout : HeapKnowledge.Holds out (push v ρ) h)
    (hback : ∀ i x, back i = some x → η x = push v ρ i) :
    StoreOk (SinglePass.applyDelta s pairs out true back) η h := by
  refine applyDelta_ok (fun x hx => ?_) hout hback
  obtain ⟨hxs, hne⟩ := removedLeave w pairs out true x hx
  rcases hcov x hxs with hh | ⟨b, hp, hr⟩
  · exact hh
  · have himg : deltaImage true b ∈ SinglePass.atomsOf out :=
      Classical.byContradiction fun hn => hne (x, b) hp hn rfl
    obtain ⟨c, hc⟩ := rename_succ_total b
    have hci : deltaImage true b = c := by simp [deltaImage, hc]
    have hcb : AtomHolds c (push v ρ) h := hci ▸ atomsOf_holds hout _ himg
    have hb : AtomHolds b ρ h := atomHolds_rename_rev (f := fun i => some (i + 1))
      (fun x i hx => by simp only [Option.some.injEq] at hx; subst hx; rfl) hc hcb
    exact atomHolds_rename_rev hf hr hb

end Verification.TolerantFrames
