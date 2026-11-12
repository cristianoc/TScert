import Verification.Programs.TolerantFramesMergeMeet

/-! # Tolerant frames: a merge's joins

Beyond the met store, the merge keeps a linear bound every predecessor states
of one form at the weakest of their bounds (`mergeBounds`), a linear fact one
predecessor states that every predecessor's view holds or entails
(`mergeEntailed`), and the guarded facts its join keeps (`mergeAddGuarded`).
Each is stated here as a property of stores closed under adding the facts it
adds (`mergeBounds_inv`, `mergeEntailed_inv`, `mergeAddGuarded_inv`), and on
the path through one predecessor the facts it adds hold at the merge's
valuation. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open Verification.SinglePass (Atom Store State)

/-! ## Linear forms in normal form -/

theorem insertTerm_vars {x : HeapKnowledge.Term} {c : Int} :
    ∀ (f : Linear.Form HeapKnowledge.Term), ∀ y ∈ (Linear.insertTerm x c f).map (·.1), y = x ∨ y ∈ f.map (·.1)
  | [], y, hy => by
    simp only [Linear.insertTerm] at hy
    split at hy
    · simp at hy
    · simp at hy; exact .inl hy
  | (z, d) :: t, y, hy => by
    simp only [Linear.insertTerm] at hy
    split at hy
    · split at hy
      · exact .inr hy
      · simp only [List.map_cons, List.mem_cons] at hy
        rcases hy with hy | hy
        · exact .inl hy
        · exact .inr (by simpa using hy)
    · split at hy
      · split at hy
        · exact .inr (by simp only [List.map_cons, List.mem_cons]; exact .inr hy)
        · simp only [List.map_cons, List.mem_cons] at hy
          exact .inr (by simp only [List.map_cons, List.mem_cons]; exact hy)
      · simp only [List.map_cons, List.mem_cons] at hy
        rcases hy with hy | hy
        · exact .inr (by simp [hy])
        · rcases insertTerm_vars t y hy with hy | hy
          · exact .inl hy
          · exact .inr (by simp only [List.map_cons, List.mem_cons]; exact .inr hy)

/-- **A form's normal form names only its variables.** -/
theorem normalize_vars : ∀ (f : Linear.Form HeapKnowledge.Term), ∀ y ∈ (Linear.normalize f).map (·.1), y ∈ f.map (·.1)
  | [], y, hy => by simp [Linear.normalize] at hy
  | (x, c) :: f, y, hy => by
    simp only [Linear.normalize, List.foldr_cons] at hy
    rcases insertTerm_vars _ y hy with rfl | hy
    · simp
    · exact List.mem_cons_of_mem _ (normalize_vars f y hy)

/-- **A bound in normal form, weakened, holds** where the bound does. -/
theorem linear_weaken {F : Linear.Form HeapKnowledge.Term} {k w : Int} {c : Option Nat} {neg : Bool}
    {η : Env} {h : Heap} (ha : AtomHolds (.index ⟨.linear (.le F k), c, neg⟩) η h) (hkw : k ≤ w) :
    AtomHolds (.index ⟨.linear (.le (Linear.normalize F) w), c, neg⟩) η h := by
  intro y hy hcond
  simp only [List.mem_singleton] at hy; subst hy
  obtain ⟨hd, hv⟩ := ha _ (List.mem_singleton_self _) hcond
  refine ⟨fun t ht => hd t (normalize_vars F t ht), ?_⟩
  have hv' : Linear.Form.eval (HeapKnowledge.termValuation η h) F ≤ k := hv
  show Linear.Form.eval (HeapKnowledge.termValuation η h) (Linear.normalize F) ≤ w
  rw [Linear.eval_normalize]; omega

/-! ## The weakest bounds -/

/-- **Each bound of a predecessor's map is one of its facts**, in normal
form. -/
theorem boundsOf_get {d : List Atom} {key : Linear.Form HeapKnowledge.Term × Option Nat × Bool} {k : Int}
    (hk : (boundsOf d)[key]? = some k) :
    ∃ F0, Atom.index ⟨.linear (.le F0 k), key.2.1, key.2.2⟩ ∈ d ∧ Linear.normalize F0 = key.1 := by
  unfold boundsOf at hk
  revert hk
  refine foldl_inv (fun (acc : Std.HashMap (Linear.Form HeapKnowledge.Term × Option Nat × Bool) Int) =>
    ∀ key k, acc[key]? = some k → ∃ F0, Atom.index ⟨.linear (.le F0 k), key.2.1, key.2.2⟩ ∈ d ∧
      Linear.normalize F0 = key.1) _ _ _ ?_ ?_ key k
  · intro _ _ h; simp at h
  intro a ha acc hacc key k hk
  split at hk
  · rename_i F d0 c neg
    rw [Std.HashMap.getElem?_insert] at hk
    split at hk
    · rename_i he
      simp only [beq_iff_eq] at he
      subst he
      cases hk
      have hnew : ∃ F0, Atom.index ⟨.linear (.le F0 d0), c, neg⟩ ∈ d ∧ Linear.normalize F0 = Linear.normalize F :=
        ⟨F, ha, rfl⟩
      split
      · rename_i d' hd'
        rcases Int.le_total d0 d' with hle | hle
        · rw [Int.min_eq_left hle]; exact hnew
        · rw [Int.min_eq_right hle]; exact hacc _ _ hd'
      · exact hnew
    · exact hacc key k hk
  · exact hacc key k hk

/-- **The weakest bound one form takes**: `weakestStep` adds nothing, or the
form's bound at a `w` at least `d` and at least each map's bound, every map
having one. -/
theorem weakestStep_cases (bs : List (Std.HashMap (Linear.Form HeapKnowledge.Term × Option Nat × Bool) Int))
    (acc : Store) (key : Linear.Form HeapKnowledge.Term × Option Nat × Bool) (d : Int) :
    weakestStep bs acc key d = acc ∨ ∃ w, weakestStep bs acc key d =
      acc.add (.index ⟨.linear (.le key.1 w), key.2.1, key.2.2⟩) ∧ d ≤ w ∧
      ∀ b ∈ bs, ∃ d', b[key]? = some d' ∧ d' ≤ w := by
  unfold weakestStep
  simp only [Id.run]
  refine forIn_idx_bind bs (none, d) _
    (fun k (r : Option Store × Int) => r.1 = none ∧ d ≤ r.2 ∧ ∀ j (hj : j < bs.length), j < k →
      ∃ d', bs[j][key]? = some d' ∧ d' ≤ r.2)
    (fun (r : Option Store × Int) => r.1 = some acc ∨ (r.1 = none ∧ d ≤ r.2 ∧
      ∀ b ∈ bs, ∃ d', b[key]? = some d' ∧ d' ≤ r.2)) _
    (fun s => s = acc ∨ ∃ w, s = acc.add (.index ⟨.linear (.le key.1 w), key.2.1, key.2.2⟩) ∧ d ≤ w ∧
      ∀ b ∈ bs, ∃ d', b[key]? = some d' ∧ d' ≤ w)
    ⟨rfl, Int.le_refl _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_ ?_ ?_
  · intro k b r r' hk ⟨h1, h2, h3⟩ hf
    split at hf
    · rename_i d' hd'
      cases hf
      rw [Std.HashMap.get?_eq_getElem?] at hd'
      refine ⟨rfl, by simp only; omega, fun j hj hjk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | rfl
      · obtain ⟨d'', h, hle⟩ := h3 j hj hjk; exact ⟨d'', h, by simp only; omega⟩
      · have : bs[j] = b := Option.some.inj (by rw [← List.getElem?_eq_getElem hj]; exact hk)
        rw [this]; exact ⟨d', hd', by simp only; omega⟩
    · cases hf
  · intro k b r r' _ _ hf
    split at hf
    · cases hf
    · cases hf; exact .inl rfl
  · intro r ⟨h1, h2, h3⟩
    refine .inr ⟨h1, h2, fun b hb => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    exact h3 j hj hj
  · intro r hr
    rcases hr with h1 | ⟨h1, h2, h3⟩
    · simp only [h1]; exact .inl rfl
    · simp only [h1]; exact .inr ⟨r.2, rfl, h2, h3⟩

/-- **The weakest bounds keep a property of stores** closed under adding a
form's bound at a `w` at least each predecessor's bound of the form. -/
theorem mergeBounds_inv (Pr : Store → Prop) (Q : Atom → Prop) (hadd : ∀ s a, Pr s → Q a → Pr (s.add a))
    {diffs : List (List Atom)}
    (hQ : ∀ (key : Linear.Form HeapKnowledge.Term × Option Nat × Bool) (w : Int), (∀ b ∈ diffs.map boundsOf, ∃ d', b[key]? = some d' ∧ d' ≤ w) →
      Q (.index ⟨.linear (.le key.1 w), key.2.1, key.2.2⟩))
    {met : Store} (h0 : Pr met) : Pr (mergeBounds diffs met) := by
  unfold mergeBounds
  split
  · rename_i b0 bs hbs
    rw [Std.HashMap.fold_eq_foldl_toList]
    refine foldl_inv Pr _ _ _ h0 fun ⟨key, d⟩ hkd acc hacc => ?_
    have hb0 : b0[key]? = some d := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkd
    rcases weakestStep_cases bs acc key d with he | ⟨w, he, hdw, hall⟩
    · simp only [he]; exact hacc
    · simp only [he]
      refine hadd _ _ hacc (hQ key w fun b hb => ?_)
      rw [hbs] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨d, hb0, hdw⟩
      · exact hall b hb
  · exact h0

/-! ## The entailed bounds -/

theorem linearKey_some {a : Atom} {key : Linear.Form HeapKnowledge.Term × Option Nat × Bool} {d : Int}
    (h : a.linearKey = some (key, d)) :
    ∃ F, a = .index ⟨.linear (.le F d), key.2.1, key.2.2⟩ ∧ Linear.normalize F = key.1 := by
  unfold Atom.linearKey at h
  split at h
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

/-- An unconditional fact holds where its fact does. -/
theorem index_none_holds {f : HeapKnowledge.IndexFact} {neg : Bool} {η : Env} {h : Heap} (hf : f.HoldsAt η h) :
    AtomHolds (.index ⟨f, none, neg⟩) η h := by
  intro y hy _
  simp only [List.mem_singleton] at hy; subst hy
  exact hf

/-- **`Store.holds` is sound for an unconditional linear fact whose terms are
defined**: the store holds it as it is, or a bound of its normal form at
least as strong. -/
theorem holds_sound {s : Store} {F : Linear.Fact HeapKnowledge.Term} {neg : Bool} {η : Env} {h : Heap}
    (hs : StoreOk s η h) (hh : s.holds (.index ⟨.linear F, none, neg⟩) = true)
    (hd : ∀ t ∈ F.vars, (HeapKnowledge.termValue η h t).isSome) :
    AtomHolds (.index ⟨.linear F, none, neg⟩) η h := by
  have hc : (Atom.index ⟨.linear F, none, neg⟩).canon = .index ⟨.linear F, none, false⟩ := by
    cases neg <;> rfl
  unfold Store.holds at hh
  simp only [hc] at hh
  rcases Bool.or_eq_true_iff.mp hh with hl | hk
  · have := hs _ (live_storeAll (Std.HashSet.contains_iff_mem.mp hl))
    rw [← hc, atomHolds_canon] at this; exact this
  · refine index_none_holds ⟨hd, ?_⟩
    split at hk
    · rename_i key d hkey
      obtain ⟨F', he, hn⟩ := linearKey_some hkey
      simp only [Atom.index.injEq, HeapKnowledge.IndexAtom.mk.injEq] at he
      obtain ⟨hF, hc1, -⟩ := he
      cases hF
      obtain ⟨b, hb, hbk⟩ := List.any_eq_true.mp hk
      split at hbk
      · rename_i key' d' hkey'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbk
        obtain ⟨hkk, hle⟩ := hbk
        subst hkk
        obtain ⟨F'', rfl, hn'⟩ := linearKey_some hkey'
        have hbh := hs _ (about_storeAll hb) _ (List.mem_singleton_self _) (fun _ h => by
          simp only at h; rw [← hc1] at h; cases h)
        have hv : Linear.Form.eval (HeapKnowledge.termValuation η h) F'' ≤ d' := hbh.2
        show Linear.Form.eval (HeapKnowledge.termValuation η h) F' ≤ d
        rw [← Linear.eval_normalize, hn, ← hn', Linear.eval_normalize]; omega
      · cases hbk
    · cases hk

/-- `SinglePass.Store.linearNear` lists facts of its store: a named
hypothesis. Its search is a `while` loop, which Lean does not unfold; read
from the code, each fact it lists is an `index` fact some `about` list of the
store holds. -/
def LinearNearSound : Prop :=
  ∀ (s : Store) (names : List Nat) (limit : Nat), ∀ x ∈ s.linearNear names limit, Atom.index x ∈ storeAll s

/-- **The entailed bounds keep a property of stores** closed under adding a
linear fact of the differences that every view holds or entails and whose
terms every view defines (`SinglePass.entailDefinedCheck`). -/
theorem mergeEntailed_inv (Pr : Store → Prop) (Q : Atom → Prop) (hadd : ∀ s a, Pr s → Q a → Pr (s.add a))
    {live : Std.HashSet Nat} {diffs : List (List Atom)} {views : List State}
    (hQ : ∀ d ∈ diffs, ∀ F neg, Atom.index ⟨.linear F, none, neg⟩ ∈ d →
      (views.all fun (qs : State) => qs.store.holds (.index ⟨.linear F, none, neg⟩) ||
        HeapKnowledge.entailsKnown (qs.store.linearNear (Atom.index ⟨.linear F, none, neg⟩).names) F) = true →
      (views.all fun (qs : State) => SinglePass.entailDefinedCheck qs (.index ⟨.linear F, none, neg⟩) F) = true →
      Q (.index ⟨.linear F, none, neg⟩))
    {met : Store} (h0 : Pr met) : Pr (mergeEntailed live diffs views met) := by
  unfold mergeEntailed SinglePass.timedKind
  simp only [Id.run]
  refine id_bind_inv _ _ (fun r : Store × Std.HashSet Atom => Pr r.1) _
    (forIn_inv (P := fun r : Store × Std.HashSet Atom => Pr r.1) _ _ _ h0 ?_) (fun r hr => hr)
  intro d hd r hr
  refine forIn_inv (P := fun r : Store × Std.HashSet Atom => Pr r.1) _ _ _ hr ?_
  intro a ha r' hr'
  split
  · rename_i F neg
    split
    · split
      · rename_i hall
        split
        · rename_i hdef
          exact hadd _ _ hr' (hQ d hd F neg ha hall hdef)
        · exact hr'
      · exact hr'
    · exact hr'
  · exact hr'

/-! ## The guarded facts and the fresh names -/

/-- **The guarded facts, renamed to the merge's names, keep a property of
stores** closed under adding their renamings. -/
theorem mergeAddGuarded_inv (Pr : Store → Prop) (Q : Atom → Prop) (hadd : ∀ s a, Pr s → Q a → Pr (s.add a))
    {names : List Nat} {guarded : List HeapKnowledge.IndexAtom}
    (hQ : ∀ x ∈ guarded, ∀ a, (Atom.index x).rename (names[·]?) = some a → Q a)
    {met : Store} (h0 : Pr met) : Pr (mergeAddGuarded names guarded met) := by
  unfold mergeAddGuarded
  refine foldl_inv Pr _ _ _ h0 fun x hx acc hacc => ?_
  split
  · rename_i a ha; exact hadd _ _ hacc (hQ x hx a ha)
  · exact hacc

end Verification.TolerantFrames
