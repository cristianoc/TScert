import Verification.Semantics.FootprintStability
import Verification.Semantics.FootprintRebase
import Verification.Semantics.IndexFacts

/-! # Supports of index facts

The supports of the pass's index facts (FOOTPRINTS.md, "Supports of index
facts"): what each reads of the current heap, each read with the change it
tolerates, in a context of certified evidence (`ReadContext`). A path's read
keeps every field location it passes, but a first field the context states
stable; a length keeps its store, or tolerates growth where a larger length
keeps the fact; a typed array's length keeps its length location, but where
the context keeps it; an entry term reads no current heap. -/
namespace Verification.Footprints
open HeapKnowledge

/-- The certified evidence a support may rely on besides its regions: the
first fields of slots' objects whose contents a transition keeps (`stable`,
`FirstKept`), and the first fields holding typed arrays whose length it keeps
(`views`, `ViewsKept`). -/
structure ReadContext where
  stable : Nat → String → Bool := fun _ _ => false
  views : Nat → String → Bool := fun _ _ => false

def ReadContext.Holds (c : ReadContext) (ρ : Env) (h h' : Heap) : Prop :=
  FirstKept c.stable ρ h h' ∧ ViewsKept c.views ρ h h'

/-- The location of the key `k` of the object the path `p` reads from slot
`x`, at the change `δ`, where the context does not keep it: a first field the
context states stable (`p` empty) needs no region. -/
def keyRead (c : ReadContext) (x : Nat) (p : List String) (k : String) (r : Region) (δ : Change) : Footprint :=
  if p.isEmpty && c.stable x k then [] else [(r, δ)]

/-- The field locations a path's read passes, after the prefix `pre`: each
at `keep` (`keyRead`). -/
def pathReads (c : ReadContext) (x : Nat) : List String → List String → Footprint
  | _, [] => []
  | pre, f :: q => keyRead c x pre f (.path x pre (.str f)) .keep ++ pathReads c x (pre ++ [f]) q

private theorem supported_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') : Supported S ρ h h' :=
  fun e he => hs e (List.mem_append_left _ he)

private theorem supported_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') : Supported T ρ h h' :=
  fun e he => hs e (List.mem_append_right _ he)

theorem supported_sub {S T : Footprint} {ρ h h'} (hs : Supported T ρ h h') (hst : ∀ e ∈ S, e ∈ T) :
    Supported S ρ h h' := fun e he => hs e (hst e he)

/-- A location read at a key the support keeps, or the context keeps, holds
its contents. -/
private theorem keyRead_kept {c : ReadContext} {x : Nat} {pre : List String} {k : String} {r : Region}
    {ρ : Env} {h h' : Heap} {v : Val} {fs : List (PropKey × Nat)} {cd : CallCode} {o l : Nat} {u : Val}
    (hc : c.Holds ρ h h') (hs : Supported (keyRead c x pre k r .keep) ρ h h')
    (hv : readPath h (ρ x) pre = some v) (hobj : v = .objAt fs cd o) (hl : fs.lookup (.str k) = some l)
    (hu : h[l]? = some u) (hm : r.mem ρ h l = true) : h'[l]? = some u := by
  unfold keyRead at hs
  split at hs
  · rename_i hst
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hst
    obtain ⟨rfl, hst⟩ := hst
    simp only [readPath, Option.some.injEq] at hv
    exact hc.1 x k fs cd o l u hst (hv.trans hobj) hl hu
  · obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) l u hm hu
    simp only [Change.Holds] at hk
    rw [← hk]; exact hv'

/-- **A path's read is kept** where its support (`pathReads`) is, in its
context. -/
theorem pathReads_sound {c : ReadContext} {x : Nat} {ρ : Env} {h h' : Heap} (hc : c.Holds ρ h h') :
    ∀ (q pre : List String) {v w : Val}, Supported (pathReads c x pre q) ρ h h' →
      readPath h (ρ x) pre = some v → readPath h' (ρ x) pre = some v →
      readPath h v q = some w → readPath h' v q = some w := by
  intro q
  induction q with
  | nil => intro pre v w _ _ _ hw; exact hw
  | cons f q ih =>
    intro pre v w hs hv hv' hw
    cases v with
    | objAt fs cd o =>
      simp only [readPath] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          have hm : (Region.path x pre (.str f)).mem ρ h l = true := by
            simp [Region.mem, hv, fieldsOf, hl]
          have hu' := keyRead_kept hc (supported_left hs) hv rfl hl hu hm
          simp only [hu']
          have happ : ∀ (h : Heap), readPath h (ρ x) pre = some (.objAt fs cd o) → h[l]? = some u →
              readPath h (ρ x) (pre ++ [f]) = some u := by
            intro h hp hlu
            rw [readPath_append, hp]
            simp [readPath, hl, hlu]
          exact ih (pre ++ [f]) (supported_right hs) (happ h hv hu) (happ h' hv' hu') hw
        · cases hw
      · cases hw
    | _ => simp [readPath] at hw

/-- **A guard's read is kept** where its path's read is: an absent key
reads `undefined` by the object alone. -/
theorem guardReads_sound {c : ReadContext} {x : Nat} {ρ : Env} {h h' : Heap} (hc : c.Holds ρ h h') :
    ∀ (q pre : List String) {v w : Val}, Supported (pathReads c x pre q) ρ h h' →
      readPath h (ρ x) pre = some v → readPath h' (ρ x) pre = some v →
      readGuard h v q = some w → readGuard h' v q = some w := by
  intro q
  induction q with
  | nil => intro pre v w _ _ _ hw; exact hw
  | cons f q ih =>
    intro pre v w hs hv hv' hw
    cases v with
    | objAt fs cd o =>
      simp only [readGuard] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          have hm : (Region.path x pre (.str f)).mem ρ h l = true := by
            simp [Region.mem, hv, fieldsOf, hl]
          have hu' := keyRead_kept hc (supported_left hs) hv rfl hl hu hm
          simp only [hu']
          have happ : ∀ (h : Heap), readPath h (ρ x) pre = some (.objAt fs cd o) → h[l]? = some u →
              readPath h (ρ x) (pre ++ [f]) = some u := by
            intro h hp hlu
            rw [readPath_append, hp]
            simp [readPath, hl, hlu]
          exact ih (pre ++ [f]) (supported_right hs) (happ h hv hu) (happ h' hv' hu') hw
        · cases hw
      · split at hw
        · rename_i hp
          simp only [hp, ite_true]
          cases q with
          | nil => exact hw
          | cons g q => simp [readGuard] at hw
        · cases hw
    | _ => cases q <;> simp_all [readGuard]

/-! ## Terms -/

/-- The store of the array the path `p` reads from slot `x`, at `δ`, where
the context does not keep it (`keyRead`); the region is its location where it
holds a store. -/
def storeRead (c : ReadContext) (x : Nat) (p : List String) (δ : Change) : Footprint :=
  keyRead c x p "[]" (.inCls (.path x p arrayStoreKey) .store) δ

/-- A one-field path whose typed array's length the context keeps. -/
def viewKept (c : ReadContext) (x : Nat) : List String → Bool
  | [g] => c.views x g
  | _ => false

/-- A typed array's length location at the path `p` from slot `x`, where
the context does not keep it: a one-field path whose view the context frames
(`views`), or a first field stated stable (`keyRead`). -/
def viewRead (c : ReadContext) (x : Nat) (p : List String) : Footprint :=
  if viewKept c x p then [] else
    keyRead c x p "[[viewLength]]" (.path x p viewLengthKey) .keep

/-- **A term's support** at the change `δ` its store tolerates: nothing for
an entry term; else its path's reads, and what its kind reads of the value
the path ends at: a length its store (`storeRead`), a typed array's length
its length location (`viewRead`), a value or a string's length nothing more. -/
def _root_.Verification.HeapKnowledge.Term.support (c : ReadContext) (δ : Change) (t : Term) : Footprint :=
  if t.atEntry then [] else
  pathReads c t.slot [] t.path ++ match t.kind with
    | .value | .strLength => []
    | .length => storeRead c t.slot t.path δ
    | .view => viewRead c t.slot t.path

/-- What a supported store read keeps: the store, grown at most where `δ` is
`grow`. -/
theorem storeRead_sound {c : ReadContext} {x : Nat} {p : List String} {δ : Change} {ρ : Env} {h h' : Heap}
    {w : Val} {s : Nat} {ls : List (Option Nat)} (hc : c.Holds ρ h h') (hδ : δ = .keep ∨ δ = .grow)
    (hs : Supported (storeRead c x p δ) ρ h h') (hw : readPath h (ρ x) p = some w)
    (hst : storeOf w = some s) (hls : h[s]? = some (.arr ls)) :
    ∃ ls', h'[s]? = some (.arr ls') ∧ LengthGrows ls ls' ∧ (δ = .keep → ls' = ls) := by
  unfold storeRead keyRead at hs
  split at hs
  · rename_i hk
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
    obtain ⟨rfl, hk⟩ := hk
    simp only [readPath, Option.some.injEq] at hw
    subst hw
    cases hρ : ρ x with
    | objAt fs cd o =>
      rw [hρ] at hst
      have hl : fs.lookup (.str "[]") = some s := by simpa [storeOf, fieldsOf, arrayStoreKey] using hst
      exact ⟨ls, hc.1 x "[]" fs cd o s _ hk hρ hl hls, LengthGrows.refl ls, fun _ => rfl⟩
    | _ => rw [hρ] at hst; simp [storeOf, fieldsOf] at hst
  · have hm : (Region.inCls (.path x p arrayStoreKey) .store).mem ρ h s = true := by
      simp only [Region.mem, hw, hls, Bool.and_eq_true]
      refine ⟨?_, rfl⟩
      simpa [storeOf] using hst
    obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) s _ hm hls
    rcases hδ with rfl | rfl
    · simp only [Change.Holds] at hk
      subst hk
      exact ⟨ls, hv', LengthGrows.refl ls, fun _ => rfl⟩
    · rcases hk with rfl | ⟨ls₁, ls', h₁, rfl, -, -, hg⟩ | hsc
      · exact ⟨ls, hv', LengthGrows.refl ls, fun _ => rfl⟩
      · cases h₁; exact ⟨ls', hv', hg, fun h => by cases h⟩
      · exact absurd hsc.2.1 (by simp [isArr])

theorem viewLengthOf_congr {h h' : Heap} {w : Val}
    (hl : ∀ l, (fieldsOf w).lookup viewLengthKey = some l → h'[l]? = h[l]?) :
    viewLengthOf h' w = viewLengthOf h w := by
  cases w with
  | objAt fs cd o =>
    simp only [viewLengthOf]
    split
    · cases hk : fs.lookup viewLengthKey with
      | none => rfl
      | some l => simp only [hl l (by simpa [fieldsOf] using hk)]
    · rfl
  | _ => rfl

/-- **A term keeps what it denotes** where its support at `keep` is kept,
and a length at `grow` denotes at least as much. -/
theorem Term.support_sound {c : ReadContext} {δ : Change} {t : Term} {ρ : Env} {h h' : Heap} {n : Int}
    (hc : c.Holds ρ h h') (hδ : δ = .keep ∨ δ = .grow) (hs : Supported (t.support c δ) ρ h h')
    (ht : termValue ε ρ h t = some n) :
    ∃ n', termValue ε ρ h' t = some n' ∧ n ≤ n' ∧ (δ = .keep → n' = n) := by
  obtain ⟨kind, x, p, a⟩ := t
  cases a
  case true => exact ⟨n, termValue_entry_some rfl ht, Int.le_refl n, fun _ => rfl⟩
  simp only [Term.support, Bool.false_eq_true, if_false] at hs
  simp only [termValue, termAt, Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hk⟩ := ht
  have hw' : readPath h' (ρ x) p = some w :=
    pathReads_sound hc p [] (supported_left hs) rfl rfl hw
  have hkind := supported_right hs
  refine (fun (e : ∃ n', kindValue h' kind w = some n' ∧ n ≤ n' ∧ (δ = .keep → n' = n)) => ?_) ?_
  · obtain ⟨n', h1, h2, h3⟩ := e; exact ⟨n', ⟨w, hw', h1⟩, h2, h3⟩
  cases kind with
  | value => exact ⟨n, hk, Int.le_refl n, fun _ => rfl⟩
  | strLength => exact ⟨n, hk, Int.le_refl n, fun _ => rfl⟩
  | length =>
    simp only [kindValue] at hk ⊢
    obtain ⟨s, ls, hst, hls, rfl, hmax⟩ := lengthOf_store hk
    obtain ⟨ls', hls', hg, hkeep⟩ := storeRead_sound hc hδ hkind hw hst hls
    refine ⟨ls'.length, lengthOf_of_store hst hls' (hg.2 hmax), by exact_mod_cast hg.1, fun h => ?_⟩
    rw [hkeep h]
  | view =>
    simp only [kindValue] at hk ⊢
    refine ⟨n, ?_, Int.le_refl n, fun _ => rfl⟩
    obtain ⟨fs, cd, o, l, b, rfl, -, hl, hb, -, -⟩ := viewLengthOf_inv hk
    by_cases hv : viewKept c x p = true
    · match p, hv with
      | [g], hv =>
        simp only [viewKept] at hv
        cases hρ : ρ x with
        | objAt fs0 cd0 o0 =>
          rw [hρ] at hw
          simp only [readPath] at hw
          split at hw
          · rename_i l0 hl0
            split at hw
            · rename_i u hu
              simp only [Option.some.injEq] at hw
              subst hw
              rw [hc.2 x g fs0 cd0 o0 l0 _ hv hρ hl0 hu]; exact hk
            · cases hw
          · cases hw
        | _ => rw [hρ] at hw; simp [readPath] at hw
    · simp only [viewRead, hv, if_false, Bool.false_eq_true] at hkind
      rw [viewLengthOf_congr ?_]; exact hk
      intro l' hl'
      simp only [fieldsOf] at hl'
      rw [hl] at hl'; cases hl'
      by_cases hst : (p.isEmpty && c.stable x "[[viewLength]]") = true
      · simp only [Bool.and_eq_true, List.isEmpty_iff] at hst
        obtain ⟨rfl, hst⟩ := hst
        simp only [readPath, Option.some.injEq] at hw
        rw [hc.1 x "[[viewLength]]" fs cd o l _ hst hw (by simpa [viewLengthKey] using hl) hb, hb]
      · simp only [keyRead, hst, if_false, Bool.false_eq_true] at hkind
        have hm : (Region.path x p viewLengthKey).mem ρ h l = true := by
          simp [Region.mem, hw, fieldsOf, hl]
        obtain ⟨v', hv', hkk⟩ := hkind _ (List.mem_singleton_self _) l _ hm hb
        simp only [Change.Holds] at hkk
        rw [hv', hkk, hb]

/-! ## Facts -/

/-- **A linear fact's support**: each term's (`Term.support`), in `F ≤ d`
at `grow` for a term of coefficient at most `0`, which a larger value keeps,
and otherwise at `keep`. -/
def linearSupport (c : ReadContext) : Linear.Fact Term → Footprint
  | .le G _ => G.flatMap fun p => p.1.support c (if p.2 ≤ 0 then .grow else .keep)
  | .ne G _ => G.flatMap fun p => p.1.support c .keep

/-- **A linear fact's support supports it** in its context. -/
theorem linearSupport_supports (c : ReadContext) (F : Linear.Fact Term) :
    Supports c.Holds (fun ρ h => (IndexFact.linear F).HoldsAt ε ρ h) (linearSupport c F) := by
  intro ρ h h' hc hF hs
  let S := linearSupport c F
  let kept : Term → Bool := fun t => (t.support c .keep).all S.contains
  let grown : Term → Bool := fun t => (t.support c .grow).all S.contains
  have sub : ∀ (δ : Change) (t : Term), (t.support c δ).all S.contains = true → Supported (t.support c δ) ρ h h' :=
    fun δ t ha => supported_sub hs fun e he => by
      have := List.all_eq_true.mp ha e he
      simpa using this
  have hk : ∀ t n, kept t = true → termValue ε ρ h t = some n → termValue ε ρ h' t = some n := by
    intro t n ht hn
    obtain ⟨n', h1, -, h3⟩ := Term.support_sound hc (.inl rfl) (sub .keep t ht) hn
    rw [h3 rfl] at h1; exact h1
  have hg : ∀ t n, grown t = true → termValue ε ρ h t = some n → ∃ n', termValue ε ρ h' t = some n' ∧ n ≤ n' := by
    intro t n ht hn
    obtain ⟨n', h1, h2, -⟩ := Term.support_sound hc (.inr rfl) (sub .grow t ht) hn
    exact ⟨n', h1, h2⟩
  have hall : ∀ (δ : Change) (G : Linear.Form Term) (f : Term × Int → Change), ∀ q ∈ G,
      f q = δ → (G.flatMap fun p => p.1.support c (f p)) = S → (q.1.support c δ).all S.contains = true := by
    intro δ G f q hq hf hS
    refine List.all_eq_true.mpr fun e he => ?_
    rw [← hS]
    simp only [List.contains_iff_mem, List.mem_flatMap]
    exact ⟨q, hq, by rw [hf]; exact he⟩
  refine factAt_monotone (kept := kept) (grown := grown) hk hg ?_ hF
  cases F with
  | le G d =>
    simp only [factMonotone, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro q hq
    by_cases ha : q.2 ≤ 0
    · exact .inr ⟨ha, hall .grow G (fun p => if p.2 ≤ 0 then .grow else .keep) q hq (by simp [ha]) rfl⟩
    · exact .inl (hall .keep G (fun p => if p.2 ≤ 0 then .grow else .keep) q hq (by simp [ha]) rfl)
  | ne G d =>
    simp only [factMonotone, List.all_eq_true]
    intro q hq
    exact hall .keep G (fun _ => .keep) q hq rfl rfl

/-- **The support of an index fact**, where one is produced: nothing for a
fact of slots' values alone; a length its store at `keep`, a bound its store
at `grow`; a linear fact `linearSupport`; a disjunction both sides'; a
guarded fact its guard's path reads and its body's; a store separation its
two paths' reads. An element fact, a quantified fact and a region fact get
none here: no support is produced, and nothing is kept by it. -/
def _root_.Verification.HeapKnowledge.IndexFact.support? (c : ReadContext) : IndexFact → Option Footprint
  | .index _ | .int _ | .pastSafe _ => some []
  | .length x _ => some (storeRead c x [] .keep)
  | .bound x _ _ => some (storeRead c x [] .grow)
  | .linear F => some (linearSupport c F)
  | .either A B => do pure ((← A.support? c) ++ (← B.support? c))
  | .guarded s p _ B => do pure (pathReads c s [] p ++ (← B.support? c))
  | .storeApart a p b q => some (pathReads c a [] p ++ pathReads c b [] q)
  | .element _ _ _ | .every _ _ _ _ | .apart _ _ => none

/-- **Every produced support supports its fact** in its context. -/
theorem IndexFact.support?_supports (c : ReadContext) :
    ∀ (F : IndexFact) {S : Footprint}, F.support? c = some S → Supports c.Holds (F.HoldsAt ε) S := by
  intro F
  induction F with
  | index k | int k | pastSafe k =>
    intro S hS; simp only [IndexFact.support?, Option.some.injEq] at hS; subst hS
    exact Supports.of_invariant fun _ _ _ _ hF => hF
  | length x n =>
    intro S hS; simp only [IndexFact.support?, Option.some.injEq] at hS; subst hS
    intro ρ h h' hc hF hs
    obtain ⟨s, ls, hst, hls, hn, hmax⟩ := hF
    obtain ⟨ls', hls', -, hk⟩ := storeRead_sound hc (.inl rfl) hs (w := ρ x) rfl hst hls
    rw [hk rfl] at hls'
    exact ⟨s, ls, hst, hls', hn, hmax⟩
  | bound x k st =>
    intro S hS; simp only [IndexFact.support?, Option.some.injEq] at hS; subst hS
    intro ρ h h' hc hF hs
    obtain ⟨s, ls, b, i, hst, hls, hb, hi, hle⟩ := hF
    obtain ⟨ls', hls', hg, -⟩ := storeRead_sound hc (.inr rfl) hs (w := ρ x) rfl hst hls
    exact ⟨s, ls', b, i, hst, hls', hb, hi, by have := hg.1; omega⟩
  | linear F =>
    intro S hS; simp only [IndexFact.support?, Option.some.injEq] at hS; subst hS
    exact linearSupport_supports c F
  | either A B ihA ihB =>
    intro S hS
    simp only [IndexFact.support?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hS
    obtain ⟨SA, hA, SB, hB, rfl⟩ := hS
    exact Supports.or (ihA hA) (ihB hB)
  | guarded s p tag B ih =>
    intro S hS
    simp only [IndexFact.support?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hS
    obtain ⟨SB, hB, rfl⟩ := hS
    intro ρ h h' hc hF hs
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, guardReads_sound hc p [] (supported_left hs) rfl rfl hv,
      hor.imp id fun hb => ih hB ρ h h' hc hb (supported_right hs)⟩
  | storeApart a p b q =>
    intro S hS; simp only [IndexFact.support?, Option.some.injEq] at hS; subst hS
    intro ρ h h' hc hF hs
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    exact ⟨u, w, pathReads_sound hc p [] (supported_left hs) rfl rfl hu,
      pathReads_sound hc q [] (supported_right hs) rfl rfl hw, hne⟩
  | element _ _ _ => intro S hS; simp [IndexFact.support?] at hS
  | every _ _ _ _ => intro S hS; simp [IndexFact.support?] at hS
  | apart _ _ => intro S hS; simp [IndexFact.support?] at hS

/-- **The survival check**: a produced support of the fact that the effect
respects under the query. -/
def _root_.Verification.HeapKnowledge.IndexFact.keeps (q : SepQuery) (c : ReadContext) (Φ : Footprint) (F : IndexFact) : Bool :=
  match F.support? c with
  | some S => respects q S Φ
  | none => false

/-- **The survival check is sound**: a fact the check keeps holds after
every transition within the effect meeting the context, from a prestate
where the query is sound (`keeps_sound`). -/
theorem IndexFact.keeps_sound {q : SepQuery} {c : ReadContext} {Φ : Footprint} {F : IndexFact}
    {ρ : Env} {h h' : Heap} (hk : F.keeps q c Φ = true) (hq : q.Sound ρ h) (hp : Post Φ ρ h h')
    (hc : c.Holds ρ h h') (hF : F.HoldsAt ε ρ h) : F.HoldsAt ε ρ h' := by
  unfold IndexFact.keeps at hk
  split at hk
  · rename_i S hS
    exact Footprints.keeps_sound (IndexFact.support?_supports c F hS) hk hq hp hc hF
  · cases hk

end Verification.Footprints
