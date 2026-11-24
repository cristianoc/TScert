import Verification.Semantics.FootprintStability
import Verification.Semantics.FootprintRebase
import Verification.Semantics.IndexFacts

/-! # Supports of index facts

The supports of the pass's index facts (FOOTPRINTS.md, "Supports of index
facts"): what each reads of the current heap, each read with the change it
tolerates, in a context of certified evidence (`ReadContext`). A path's read
keeps every field location it passes, but a first field the context states
stable; a length keeps its spine, or tolerates growth where a larger length
keeps the fact; a typed array's length keeps its length location, but where
the context keeps it; an entry term reads no current heap. -/
namespace Verification.Footprints
open HeapKnowledge

/-- The certified evidence a support may rely on besides its regions: the
keys of slots' objects whose contents a transition keeps (`stable`). `Holds`
is the condition `C` of a support under a condition (the note, §5,
Definition "Support", and "Supports of the atoms": a field a condition says
keeps its contents is left out of the reads, `fieldRead`), and the support is
then under it. -/
structure ReadContext where
  stable : Nat → PropKey → Bool := fun _ _ => false

/-- **A transition keeps the context's keys**: the location of each key the
context states of a slot's object holds its contents. -/
def ReadContext.Holds (c : ReadContext) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ x k fs cd o l v, c.stable x k = true → ρ x = .objAt fs cd o → fs.lookup k = some l →
    h[l]? = some v → h'[l]? = some v

/-- The context keeping the first fields `first` states, string keys. -/
def ReadContext.ofFirst (first : Nat → String → Bool) : ReadContext where
  stable x k := match k with
    | .str g => first x g
    | .sym _ => false

theorem ReadContext.ofFirst_holds {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    (hf : FirstKept first ρ h h') : (ReadContext.ofFirst first).Holds ρ h h' := by
  intro x k fs cd o l v hs hx hl hv
  cases k with
  | str g => exact hf x g fs cd o l v hs hx hl hv
  | sym _ => cases hs

/-- **The read of the key `k` of slot `x`'s object, at the change `δ`**:
the region `r` holding its location, left out where the context keeps the
key. -/
def fieldRead (c : ReadContext) (x : Nat) (k : PropKey) (r : Region) (δ : Change) : Footprint :=
  if c.stable x k then [] else [(r, δ)]

/-- The location of the key `k` of the object the path `p` reads from slot
`x`, at the change `δ`, where the context does not keep it: a first field the
context states stable (`p` empty) needs no region (`fieldRead`). -/
def keyRead (c : ReadContext) (x : Nat) (p : List String) (k : String) (r : Region) (δ : Change) : Footprint :=
  if p.isEmpty then fieldRead c x (.str k) r δ else [(r, δ)]

/-- A field read the context keeps, or whose region is supported, changes
the field's location of slot `x`'s object within `δ`. -/
theorem fieldRead_supported {c : ReadContext} {x : Nat} {k : PropKey} {δ : Change} {ρ : Env} {h h' : Heap}
    (hc : c.Holds ρ h h') (hs : Supported (fieldRead c x k (.field x k) δ) ρ h h') :
    Supported [(.field x k, δ)] ρ h h' := by
  unfold fieldRead at hs
  split at hs
  · rename_i hk
    intro e he l v hm hv
    simp only [List.mem_singleton] at he
    subst he
    refine ⟨v, ?_, Change.Holds.refl _ _ _⟩
    simp only [Region.mem, beq_iff_eq] at hm
    cases hx : ρ x with
    | objAt fs cd o => rw [hx] at hm; exact hc x k fs cd o l v hk hx (by simpa [fieldsOf] using hm) hv
    | _ => rw [hx] at hm; simp [fieldsOf] at hm
  · exact hs

/-- **A fact kind's support in a context** (the note, §5, "Supports of the
atoms"): its kind's support (`FactKind.support`), each field of a slot's
object the context keeps left out (`fieldRead`). -/
def _root_.Verification.Footprints.FactKind.supportIn (c : ReadContext) (F : FactKind) : Footprint :=
  F.support.flatMap fun e => match e.1 with
    | .field x k => fieldRead c x k e.1 e.2
    | _ => [e]

/-- **A fact kind's support in a context supports it** under the context's
condition (`FactKind.support_sound`, `fieldRead_supported`). -/
theorem FactKind.supportsIn (c : ReadContext) (F : FactKind) : Supports c.Holds F.Holds (F.supportIn c) := by
  refine Supports.intro fun ρ h h' hc hF hs => FactKind.support_sound hF ?_
  rintro ⟨r, δ⟩ he l v hm hv
  cases r
  case field x k =>
    have hsub : Supported (fieldRead c x k (.field x k) δ) ρ h h' := fun e' he' =>
      hs e' (List.mem_flatMap.mpr ⟨_, he, by simpa using he'⟩)
    exact fieldRead_supported hc hsub _ (List.mem_singleton_self _) l v hm hv
  all_goals exact hs _ (List.mem_flatMap.mpr ⟨_, he, by simp⟩) l v hm hv

/-- The field locations a path's read passes, after the prefix `pre`: each
location the read passes on from holds an object, at `grow`, which keeps an
object; the last at `last`, which keeps the value the read ends at (`keyRead`). -/
def pathReads (c : ReadContext) (x : Nat) (last : Change) : List String → List String → Footprint
  | _, [] => []
  | pre, f :: q => keyRead c x pre f (.path x pre (.str f))
      (if q.isEmpty then last else .grow) ++ pathReads c x last (pre ++ [f]) q

private theorem supported_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') : Supported S ρ h h' :=
  fun e he => hs e (List.mem_append_left _ he)

private theorem supported_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') : Supported T ρ h h' :=
  fun e he => hs e (List.mem_append_right _ he)

theorem supported_sub {S T : Footprint} {ρ h h'} (hs : Supported T ρ h h') (hst : ∀ e ∈ S, e ∈ T) :
    Supported S ρ h h' := fun e he => hs e (hst e he)

/-- A change keeps the contents `u` where every step of it from `u` is none. -/
def Keeps (δ : Change) (u : Val) : Prop := ∀ b u', δ.Holds b u u' → u' = u

theorem keeps_keep (u : Val) : Keeps .keep u := fun _ _ h => h

theorem keeps_obj {δ : Change} (hδ : δ ≠ .any) {u : Val} (ho : isObj u = true) : Keeps δ u :=
  fun _ _ h => h.object_kept hδ ho

theorem keeps_defined {δ : Change} (hδ : δ.le .init = true) {u : Val} (hn : nullish u = false) : Keeps δ u :=
  fun _ _ h => h.defined_kept hδ hn

/-- A location read at a key the support keeps at a change keeping its
contents, or the context keeps, holds its contents. -/
private theorem keyRead_kept {c : ReadContext} {x : Nat} {pre : List String} {k : String} {r : Region}
    {δ : Change} {ρ : Env} {h h' : Heap} {v : Val} {fs : List (PropKey × Nat)} {cd : CallCode} {o l : Nat}
    {u : Val} (hc : c.Holds ρ h h') (hs : Supported (keyRead c x pre k r δ) ρ h h') (hδ : Keeps δ u)
    (hv : readPath h (ρ x) pre = some v) (hobj : v = .objAt fs cd o) (hl : fs.lookup (.str k) = some l)
    (hu : h[l]? = some u) (hm : r.mem ρ h l = true) : h'[l]? = some u := by
  unfold keyRead fieldRead at hs
  split at hs
  · rename_i hp
    simp only [List.isEmpty_iff] at hp
    subst hp
    split at hs
    · rename_i hst
      simp only [readPath, Option.some.injEq] at hv
      exact hc x _ fs cd o l u hst (hv.trans hobj) hl hu
    · obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) l u hm hu
      rw [← hδ _ _ hk]; exact hv'
  · obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) l u hm hu
    rw [← hδ _ _ hk]; exact hv'

private theorem readPath_obj {h : Heap} {u w : Val} {g : String} {q : List String}
    (hw : readPath h u (g :: q) = some w) : isObj u = true := by
  cases u <;> simp_all [readPath, isObj]

private theorem readGuard_obj {h : Heap} {u w : Val} {g : String} {q : List String}
    (hw : readGuard h u (g :: q) = some w) : isObj u = true := by
  cases u <;> simp_all [readGuard, isObj]

/-- **A path's read is kept** where its support (`pathReads`) is, in its
context, its last change keeping the value it reads. -/
theorem pathReads_sound {c : ReadContext} {x : Nat} {last : Change} {ρ : Env} {h h' : Heap}
    (hc : c.Holds ρ h h') :
    ∀ (q pre : List String) {v w : Val}, Supported (pathReads c x last pre q) ρ h h' → Keeps last w →
      readPath h (ρ x) pre = some v → readPath h' (ρ x) pre = some v →
      readPath h v q = some w → readPath h' v q = some w := by
  intro q
  induction q with
  | nil => intro pre v w _ _ _ _ hw; exact hw
  | cons f q ih =>
    intro pre v w hs hlast hv hv' hw
    cases v with
    | objAt fs cd o =>
      simp only [readPath] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          have hδ : Keeps (if q.isEmpty then last else .grow) u := by
            cases q with
            | nil => simp only [readPath, Option.some.injEq] at hw; subst hw; simpa using hlast
            | cons g q => exact by simpa using keeps_obj (by decide) (readPath_obj hw)
          have hm : (Region.path x pre (.str f)).mem ρ h l = true := by
            simp only [Region.mem, hv]
            simp [fieldsOf, hl]
          have hu' := keyRead_kept hc (supported_left hs) hδ hv rfl hl hu hm
          simp only [hu']
          have happ : ∀ (h : Heap), readPath h (ρ x) pre = some (.objAt fs cd o) → h[l]? = some u →
              readPath h (ρ x) (pre ++ [f]) = some u := by
            intro h hp hlu
            rw [readPath_append, hp]
            simp [readPath, hl, hlu]
          exact ih (pre ++ [f]) (supported_right hs) hlast (happ h hv hu) (happ h' hv' hu') hw
        · cases hw
      · cases hw
    | _ => simp [readPath] at hw

/-- **A guard's read is kept** where its path's read is at `keep` last: an
absent key reads `undefined` by the object alone. -/
theorem guardReads_sound {c : ReadContext} {x : Nat} {ρ : Env} {h h' : Heap} (hc : c.Holds ρ h h') :
    ∀ (q pre : List String) {v w : Val}, Supported (pathReads c x .keep pre q) ρ h h' →
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
          have hδ : Keeps (if q.isEmpty then .keep else .grow) u := by
            cases q with
            | nil => simpa using keeps_keep u
            | cons g q => exact by simpa using keeps_obj (by decide) (readGuard_obj hw)
          have hm : (Region.path x pre (.str f)).mem ρ h l = true := by
            simp only [Region.mem, hv]
            simp [fieldsOf, hl]
          have hu' := keyRead_kept hc (supported_left hs) hδ hv rfl hl hu hm
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

/-- The spine of the array the path `p` reads from slot `x`, at `δ`, where
the context does not keep it (`keyRead`). -/
def spineRead (c : ReadContext) (x : Nat) (p : List String) (δ : Change) : Footprint :=
  keyRead c x p "[]" (.path x p arraySpineKey) δ

/-- The change the last location a term's path reads tolerates: a number
or a string is kept by `init`, an object by `grow`. -/
def lastChange : Term.Kind → Change
  | .value | .strLength => .init
  | .length | .view => .grow

/-- **A term's support** at the change `δ` its spine tolerates: nothing for
an entry term; else its path's reads, and what its kind reads of the value
the path ends at: a length its spine (`spineRead`); a typed array's length,
which its descriptor holds, a value or a string's length nothing more. -/
def _root_.Verification.HeapKnowledge.Term.support (c : ReadContext) (δ : Change) (t : Term) : Footprint :=
  if t.atEntry then [] else
  pathReads c t.slot (lastChange t.kind) [] t.path ++ match t.kind with
    | .value | .strLength | .view => []
    | .length => spineRead c t.slot t.path δ

/-- What a supported spine read keeps: the spine, grown at most where `δ` is
`grow`. -/
theorem spineRead_sound {c : ReadContext} {x : Nat} {p : List String} {δ : Change} {ρ : Env} {h h' : Heap}
    {w : Val} {s : Nat} {ls : List (Option Nat)} (hc : c.Holds ρ h h') (hδ : δ = .keep ∨ δ = .grow)
    (hs : Supported (spineRead c x p δ) ρ h h') (hw : readPath h (ρ x) p = some w)
    (hst : spineOf w = some s) (hls : h[s]? = some (.arr ls)) :
    ∃ ls', h'[s]? = some (.arr ls') ∧ LengthGrows ls ls' ∧ (δ = .keep → ls' = ls) := by
  unfold spineRead keyRead fieldRead at hs
  by_cases hk : p.isEmpty = true ∧ c.stable x (.str "[]") = true
  · obtain ⟨hp, hk⟩ := hk
    simp only [List.isEmpty_iff] at hp
    subst hp
    simp only [readPath, Option.some.injEq] at hw
    subst hw
    cases hρ : ρ x with
    | objAt fs cd o =>
      rw [hρ] at hst
      have hl : fs.lookup (.str "[]") = some s := by simpa [fieldsOf, arraySpineKey] using spineOf_lookup hst
      exact ⟨ls, hc x "[]" fs cd o s _ hk hρ hl hls, LengthGrows.refl ls, fun _ => rfl⟩
    | _ => rw [hρ] at hst; simp [spineOf, fieldsOf] at hst
  · have hs : Supported [(.path x p arraySpineKey, δ)] ρ h h' := by
      split at hs
      · rename_i hp
        split at hs
        · rename_i hst'
          exact absurd ⟨hp, hst'⟩ hk
        · exact hs
      · exact hs
    have hm : (Region.path x p arraySpineKey).mem ρ h s = true := by
      simp only [Region.mem, hw]
      simpa using spineOf_lookup hst
    obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) s _ hm hls
    rcases hδ with rfl | rfl
    · simp only [Change.Holds] at hk
      subst hk
      exact ⟨ls, hv', LengthGrows.refl ls, fun _ => rfl⟩
    · rcases hk with rfl | ⟨ls₁, ls', h₁, rfl, -, -, hg⟩ | hsc | ⟨_, _, _, he, -⟩
      · exact ⟨ls, hv', LengthGrows.refl ls, fun _ => rfl⟩
      · cases h₁; exact ⟨ls', hv', hg, fun h => by cases h⟩
      · exact absurd hsc.2.1 (by simp [isArr])
      · cases he

/-- **A term keeps what it denotes** where its support at `keep` is kept,
and a length at `grow` denotes at least as much. -/
theorem Term.support_sound {c : ReadContext} {δ : Change} {t : Term} {ρ : Env} {h h' : Heap} {n : Int}
    (hc : c.Holds ρ h h') (hδ : δ = .keep ∨ δ = .grow) (hs : Supported (t.support c δ) ρ h h')
    (ht : termValue ε ρ h t = some n) :
    ∃ n', termValue ε ρ h' t = some n' ∧ n ≤ n' ∧ (δ = .keep → n' = n) := by
  obtain ⟨kind, x, p, a⟩ := t
  cases a
  case true => exact ⟨n, termValue_entry_some rfl ht, Int.le_refl n, fun _ => rfl⟩
  simp only [Term.support, Bool.false_eq_true, ite_false] at hs
  simp only [termValue, termAt, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hk⟩ := ht
  have hlast : Keeps (lastChange kind) w := by
    cases kind with
    | value =>
      obtain ⟨b, rfl, -⟩ := intValue_safe hk
      exact keeps_defined (by decide) rfl
    | strLength =>
      cases w <;> simp [kindValue, strLengthOf] at hk
      exact keeps_defined (by decide) rfl
    | length =>
      obtain ⟨s, -, hst, -⟩ := lengthOf_spine hk
      cases w <;> simp [spineOf, fieldsOf] at hst
      exact keeps_obj (by decide) rfl
    | view =>
      obtain ⟨fs, o, st, f, N, rfl, -⟩ := viewLengthOf_inv hk
      exact keeps_obj (by decide) rfl
  have hw' : readPath h' (ρ x) p = some w :=
    pathReads_sound hc p [] (supported_left hs) hlast rfl rfl hw
  have hkind := supported_right hs
  refine (fun (e : ∃ n', kindValue h' kind w = some n' ∧ n ≤ n' ∧ (δ = .keep → n' = n)) => ?_) ?_
  · obtain ⟨n', h1, h2, h3⟩ := e; exact ⟨n', ⟨w, hw', h1⟩, h2, h3⟩
  cases kind with
  | value => exact ⟨n, hk, Int.le_refl n, fun _ => rfl⟩
  | strLength => exact ⟨n, hk, Int.le_refl n, fun _ => rfl⟩
  | length =>
    simp only [kindValue] at hk ⊢
    obtain ⟨s, ls, hst, hls, rfl, hmax⟩ := lengthOf_spine hk
    obtain ⟨ls', hls', hg, hkeep⟩ := spineRead_sound hc hδ hkind hw hst hls
    refine ⟨ls'.length, lengthOf_of_spine hst hls' (hg.2 hmax), by exact_mod_cast hg.1, fun h => ?_⟩
    rw [hkeep h]
  | view => exact ⟨n, hk, Int.le_refl n, fun _ => rfl⟩

/-! ## Facts -/

/-- **A term's value has its support at `keep`** (the note, §5, Definition
"Supports of the atoms", the rows of terms): where the support is kept, the
term denotes what it denoted (`Term.support_sound`). -/
theorem Term.supports_keep (c : ReadContext) (t : Term) (n : Int) :
    Supports c.Holds (fun ρ h => termValue ε ρ h t = some n) (t.support c .keep) :=
  Supports.intro fun _ _ _ hc ht hs => by
    obtain ⟨n', h1, -, h3⟩ := Term.support_sound hc (.inl rfl) hs ht
    rw [h3 rfl] at h1; exact h1

/-- **A term's lower bound has its support at `grow`**: where the support is
kept, a length denotes at least as much (`Term.support_sound`). -/
theorem Term.supports_grow (c : ReadContext) (t : Term) (n : Int) :
    Supports c.Holds (fun ρ h => ∃ m, termValue ε ρ h t = some m ∧ n ≤ m) (t.support c .grow) :=
  Supports.intro fun _ _ _ hc ⟨m, ht, hnm⟩ hs => by
    obtain ⟨m', h1, h2, -⟩ := Term.support_sound hc (.inr rfl) hs ht
    exact ⟨m', h1, Int.le_trans hnm h2⟩

/-- **A linear fact's support**: each term's (`Term.support`), in `F ≤ d`
at `grow` for a term of coefficient at most `0`, which a larger value keeps,
and otherwise at `keep`. -/
def linearSupport (c : ReadContext) : Linear.Fact Term → Footprint
  | .le G _ => G.flatMap fun p => p.1.support c (if p.2 ≤ 0 then .grow else .keep)
  | .ne G _ => G.flatMap fun p => p.1.support c .keep

/-- **A linear fact's support supports it** in its context. -/
theorem linearSupport_supports (c : ReadContext) (F : Linear.Fact Term) :
    Supports c.Holds (fun ρ h => (IndexFact.linear F).HoldsAt ε ρ h) (linearSupport c F) := by
  refine Supports.intro fun ρ h h' hc hF hs => ?_
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

/-- A value's region (`RegionOf`) is kept where its spine location keeps its
contents. -/
theorem regionOf_supported {x : Nat} {ρ : Env} {h h' : Heap} {st : Option Nat} {cells : List (Option Nat)}
    (hs : Supported [(.field x arraySpineKey, .keep)] ρ h h') (hr : RegionOf h (ρ x) st cells) :
    RegionOf h' (ρ x) st cells := by
  rcases hr with hr | ⟨l, rfl, hst, hl⟩
  · exact .inl hr
  · have hm : (Region.field x arraySpineKey).mem ρ h l = true := by
      simpa [Region.mem] using spineOf_lookup hst
    obtain ⟨v', hv', hk⟩ := hs _ (List.mem_singleton_self _) l _ hm hl
    simp only [Change.Holds] at hk
    exact .inr ⟨l, rfl, hst, by rw [hv', hk]⟩

/-- Whether a quantified body's variables read the heap only through the
element cells and terms: no projection through an element. -/
def Bound.scalar : Bound → Bool
  | .project _ _ => false
  | _ => true

/-- The supports of a quantified body's terms, at `keep`. -/
def bodySupport (c : ReadContext) (body : List (LinearClause Bound)) : Footprint :=
  body.flatMap fun F => F.vars.flatMap fun b => match b with
    | .free t => t.support c .keep
    | _ => []

/-- The locations a quantified fact over the array the path `p` reads from
slot `s` reads besides its path: the spine of its elements, an array's
under `[]` or a typed array's view spine (`Region.spine`), and the element
cells, which hold numbers where an element is read, at `init`. -/
def everyCells (s : Nat) (p : List String) : Footprint :=
  [(.path s p arraySpineKey, .keep), (.spine s p, .keep), (.cls .values, .init)]

/-- The support of a region fact `apart(a, b)`: its two spine locations at
`keep`. -/
def apartSupport (a b : Nat) : Footprint :=
  [(.field a arraySpineKey, .keep), (.field b arraySpineKey, .keep)]

/-- The support of an element fact $`z[t] \doteq v`$ over the array a slot
holds (the note, §5, Definition "Supports of the atoms", the row of
$`z[t] \doteq v`$: $`\mathrm{reads}_{\mathsf{grow}}(z) \cup \{z[\ast]{:}\,\mathsf{keep}\} \cup
\mathrm{supp}(t)`$): its spine location, an array's or a typed array's view
spine, at `keep`, and the element cells it lists at `keep`; the slot's path
is empty and its index a slot's value, which read no location. -/
def elementSupport (x : Nat) : Footprint :=
  [(.spine x [], .keep), (.cells x, .keep)]

/-- The support of a quantified fact whose body reads no element's fields:
its array's path, spine and element cells (`everyCells`), its bound's and
its body's terms. -/
def everySupport (c : ReadContext) (s : Nat) (p : List String) (stop : Term) (body : List (LinearClause Bound)) :
    Footprint :=
  pathReads c s .grow [] p ++ everyCells s p ++ stop.support c .keep ++ bodySupport c body

/-- **Finite evidence of an index fact's support**: the form of the fact
the support is computed for, and, for a disjunction and a guarded fact, the
supports of the parts with their evidence. -/
inductive FactSupport where
  /-- A fact of slots' values alone, by the empty support. -/
  | slots
  | length
  | bound
  | linear
  | either (left : Footprint) (l : FactSupport) (right : Footprint) (r : FactSupport)
  | guarded (body : Footprint) (b : FactSupport)
  | spineApart
  | apart
  | element
  | every
  deriving Repr

/-- **The check of an index fact's support by evidence**: the footprint is
the one the evidence's form gives the fact, the parts' checked by theirs; a
quantified fact's body reads no element's fields. -/
def FactSupport.check (c : ReadContext) : IndexFact → Footprint → FactSupport → Bool
  | .index _, S, .slots | .int _, S, .slots | .pastSafe _, S, .slots => S.isEmpty
  | .length x _, S, .length => S == spineRead c x [] .keep
  | .bound x _ _, S, .bound => S == spineRead c x [] .grow
  | .linear F, S, .linear => S == linearSupport c F
  | .either A B, S, .either SA a SB b => S == SA ++ SB && check c A SA a && check c B SB b
  | .guarded s p _ B, S, .guarded SB b => S == pathReads c s .keep [] p ++ SB && check c B SB b
  | .spineApart a p b q, S, .spineApart => S == pathReads c a .keep [] p ++ pathReads c b .keep [] q
  | .apart a b, S, .apart => S == apartSupport a b
  | .element _ x _, S, .element => S == elementSupport x
  | .every s p stop body, S, .every =>
    body.all (fun F => F.vars.all Bound.scalar) && S == everySupport c s p stop body
  | _, _, _ => false

/-- **A checked support supports its fact** in its context. -/
theorem FactSupport.check_sound (c : ReadContext) :
    ∀ (F : IndexFact) {S : Footprint} {ev : FactSupport}, ev.check c F S = true →
      Supports c.Holds (F.HoldsAt ε) S := by
  intro F
  induction F with
  | index k | int k | pastSafe k =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, List.isEmpty_iff, Bool.false_eq_true] at hS
    subst hS
    exact SupportDomain.Supports.of_invariant fun _ _ _ _ _ _ hF => hF
  | length x n =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, beq_iff_eq, Bool.false_eq_true] at hS
    subst hS
    refine Supports.intro fun ρ h h' hc hF hs => ?_
    obtain ⟨s, ls, hst, hls, hn, hmax⟩ := hF
    obtain ⟨ls', hls', -, hk⟩ := spineRead_sound hc (.inl rfl) hs (w := ρ x) rfl hst hls
    rw [hk rfl] at hls'
    exact ⟨s, ls, hst, hls', hn, hmax⟩
  | bound x k st =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, beq_iff_eq, Bool.false_eq_true] at hS
    subst hS
    refine Supports.intro fun ρ h h' hc hF hs => ?_
    obtain ⟨s, ls, b, i, hst, hls, hb, hi, hle⟩ := hF
    obtain ⟨ls', hls', hg, -⟩ := spineRead_sound hc (.inr rfl) hs (w := ρ x) rfl hst hls
    exact ⟨s, ls', b, i, hst, hls', hb, hi, by have := hg.1; omega⟩
  | linear F =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, beq_iff_eq, Bool.false_eq_true] at hS
    subst hS
    exact linearSupport_supports c F
  | either A B ihA ihB =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hS
    obtain ⟨⟨rfl, hA⟩, hB⟩ := hS
    exact SupportDomain.Supports.or (ihA hA) (ihB hB)
  | guarded s p tag B ih =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hS
    obtain ⟨rfl, hB⟩ := hS
    refine Supports.intro fun ρ h h' hc hF hs => ?_
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, guardReads_sound hc p [] (supported_left hs) rfl rfl hv,
      hor.imp id fun hb => (ih hB).apply hc hb (supported_right hs)⟩
  | spineApart a p b q =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, beq_iff_eq, Bool.false_eq_true] at hS
    subst hS
    refine Supports.intro fun ρ h h' hc hF hs => ?_
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    exact ⟨u, w, pathReads_sound hc p [] (supported_left hs) (keeps_keep u) rfl rfl hu,
      pathReads_sound hc q [] (supported_right hs) (keeps_keep w) rfl rfl hw, hne⟩
  | element v x k =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, beq_iff_eq, Bool.false_eq_true] at hS
    subst hS
    refine Supports.intro fun ρ h h' _ hF hs => ?_
    obtain ⟨s, ls, b, i, hx, hls, hb, hi, hlt, hcell, hnone⟩ := hF
    obtain ⟨u, hu, hue⟩ := Option.bind_eq_some_iff.mp hls
    have hm : (Region.spine x []).mem ρ h s = true := by
      simp [Region.mem, readPath, hx]
    obtain ⟨u', hu', hk⟩ := hs (.spine x [], .keep) (by simp [elementSupport]) s _ hm hu
    simp only [Change.Holds] at hk
    subst hk
    refine ⟨s, ls, b, i, hx, by rw [hu']; exact hue, hb, hi, hlt, fun l hl => ?_, hnone⟩
    have hv := hcell l hl
    have hmem : (Region.cells x).mem ρ h l = true := by
      have ho : some l ∈ entriesAt h (some s) := by
        simp only [entriesAt, hls, Option.getD_some]
        exact List.mem_of_getElem? hl
      simpa [Region.mem, List.contains_iff_mem] using elementsOf_entries_sub hx ho
    obtain ⟨v', hv', hk'⟩ := hs (.cells x, .keep) (by simp [elementSupport]) l _ hmem hv
    simp only [Change.Holds] at hk'
    rw [hv', hk']
  | apart a b =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, beq_iff_eq, Bool.false_eq_true] at hS
    subst hS
    refine Supports.intro fun ρ h h' _ hF hs => ?_
    obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := hF
    exact ⟨sa, xs, sb, ys, regionOf_supported (supported_sub hs (by simp [apartSupport])) hx,
      regionOf_supported (supported_sub hs (by simp [apartSupport])) hy, hab⟩
  | every s p stop body =>
    intro S ev hS
    cases ev <;> simp only [FactSupport.check, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hS
    obtain ⟨hsc, rfl⟩ := hS
    refine Supports.intro fun ρ h h' hc hF hs => ?_
    have hpath := supported_left (supported_left (supported_left hs))
    have hcells := supported_right (supported_left (supported_left hs))
    have hstop := supported_right (supported_left hs)
    have hbody := supported_right hs
    have hw_obj : ∀ w st, readPath h (ρ s) p = some w → elementsOf w = some st → isObj w = true := by
      intro w st _ he; cases w <;> simp_all [elementsOf, isObj]
    refine IndexFact.every_frame hF (fun w hw => ?_) (fun w st ls hw he hls => ?_) (fun z hz => ?_)
      (fun w st ls hw he hls F hF i b hb z hz => ?_)
    · obtain ⟨w0, st0, -, -, hw0, he0, -⟩ := hF
      have hww : w0 = w := by rw [hw0] at hw; exact Option.some.inj hw
      subst hww
      have ho := hw_obj _ st0 hw0 he0
      exact pathReads_sound hc p [] hpath (keeps_obj (by decide) ho) rfl rfl hw0
    · -- the spine of elements, an array's or a view spine, holds a spine
      obtain ⟨u, hu, hue⟩ := Option.bind_eq_some_iff.mp hls
      have hm : (Region.spine s p).mem ρ h st = true := by
        simp [Region.mem, hw, he]
      obtain ⟨v', hv', hk⟩ := hcells (.spine s p, .keep)
        (by simp [everyCells]) st _ hm hu
      simp only [Change.Holds] at hk; rw [hv', hk]; exact hue
    · obtain ⟨n', h1, -, h3⟩ := Term.support_sound hc (.inl rfl) hstop hz
      rw [h3 rfl] at h1; exact h1
    · have hcell : ∀ j z, elementInt h ls j = some z → elementInt h' ls j = some z := by
        intro j z hj
        simp only [elementInt] at hj ⊢
        split at hj
        · rename_i l hl
          simp only [Option.bind_eq_some_iff] at hj ⊢
          obtain ⟨v, hv, hz⟩ := hj
          obtain ⟨bv, rfl, -⟩ := intValue_safe hz
          have hm : (Region.cls .values).mem ρ h l = true := by simp [Region.mem, hv, isArr]
          obtain ⟨v', hv', hk⟩ := hcells (.cls .values, .init) (by simp [everyCells]) l _ hm hv
          exact ⟨_, hv', by rw [(show Change.init.Holds _ _ _ from hk).defined_kept (by decide) rfl]; exact hz⟩
        · cases hj
      cases b with
      | index => exact hz
      | elem => exact hcell i z hz
      | offset d => exact hcell (i + d) z hz
      | project k q =>
        have := List.all_eq_true.mp (List.all_eq_true.mp hsc F hF) _ hb
        simp [Bound.scalar] at this
      | free t =>
        have hsub : Supported (t.support c .keep) ρ h h' := supported_sub hbody fun e he => by
          simp only [bodySupport, List.mem_flatMap]
          exact ⟨F, hF, .free t, hb, he⟩
        obtain ⟨n', h1, -, h3⟩ := Term.support_sound hc (.inl rfl) hsub hz
        rw [h3 rfl] at h1; exact h1

/-- **The support of an index fact, with its evidence**, where one is
produced: nothing for a fact of slots' values alone; a length its spine at
`keep`, a bound its spine at `grow`; a linear fact `linearSupport`; a
disjunction both sides'; a guarded fact its guard's path reads and its
body's; a spine separation its two paths' reads; a region fact its two
spines at `keep`; a quantified fact whose body reads no element's fields its
array's path, spine and element cells (`everyCells`), its bound's and its
body's terms; an element fact its spine and element cells at `keep`
(`elementSupport`). A quantified fact projecting through elements gets none:
the note gives a term $`z[t].\vec f`$ no support. -/
def _root_.Verification.HeapKnowledge.IndexFact.produceSupport (c : ReadContext) :
    IndexFact → Option (Footprint × FactSupport)
  | .index _ | .int _ | .pastSafe _ => some ([], .slots)
  | .length x _ => some (spineRead c x [] .keep, .length)
  | .bound x _ _ => some (spineRead c x [] .grow, .bound)
  | .linear F => some (linearSupport c F, .linear)
  | .either A B => do
    let (SA, a) ← A.produceSupport c
    let (SB, b) ← B.produceSupport c
    pure (SA ++ SB, .either SA a SB b)
  | .guarded s p _ B => do
    let (SB, b) ← B.produceSupport c
    pure (pathReads c s .keep [] p ++ SB, .guarded SB b)
  | .spineApart a p b q => some (pathReads c a .keep [] p ++ pathReads c b .keep [] q, .spineApart)
  | .apart a b => some (apartSupport a b, .apart)
  | .every s p stop body =>
    if body.all (fun F => F.vars.all Bound.scalar) then some (everySupport c s p stop body, .every) else none
  | .element _ x _ => some (elementSupport x, .element)

/-- **The support of an index fact**, where one is produced: the footprint
of the produced support (`produceSupport`). -/
def _root_.Verification.HeapKnowledge.IndexFact.support? (c : ReadContext) (F : IndexFact) : Option Footprint :=
  (F.produceSupport c).map Prod.fst

/-- **A produced support checks with its evidence.** -/
theorem IndexFact.produceSupport_check (c : ReadContext) :
    ∀ (F : IndexFact) {S : Footprint} {ev : FactSupport}, F.produceSupport c = some (S, ev) →
      ev.check c F S = true := by
  intro F
  induction F with
  | either A B ihA ihB =>
    intro S ev h
    simp only [IndexFact.produceSupport, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨SA, a⟩, hA, ⟨SB, b⟩, hB, h⟩ := h
    cases h
    simp [FactSupport.check, ihA hA, ihB hB]
  | guarded s p tag B ih =>
    intro S ev h
    simp only [IndexFact.produceSupport, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨SB, b⟩, hB, h⟩ := h
    cases h
    simp [FactSupport.check, ih hB]
  | every s p stop body =>
    intro S ev h
    simp only [IndexFact.produceSupport] at h
    split at h
    · rename_i hsc
      cases h
      simp [FactSupport.check, hsc]
    · cases h
  | _ => intro S ev h; cases h; simp [FactSupport.check]

/-- **Every produced support supports its fact** in its context
(`produceSupport_check`, `FactSupport.check_sound`). -/
theorem IndexFact.support?_supports (c : ReadContext) (F : IndexFact) {S : Footprint}
    (hS : F.support? c = some S) : Supports c.Holds (F.HoldsAt ε) S := by
  simp only [IndexFact.support?, Option.map_eq_some_iff] at hS
  obtain ⟨⟨S', ev⟩, h, rfl⟩ := hS
  exact FactSupport.check_sound c F (IndexFact.produceSupport_check c F h)

/-- **The index facts as an assertion language** over arbitrary heaps: the
condition of a read context, and supports by `FactSupport` evidence. -/
def indexFacts (ε : HeapKnowledge.EntryState) : SupportLanguage heaps where
  Formula := IndexFact
  sat F := fun ρ _ h => F.HoldsAt ε ρ h
  Context := ReadContext
  condition c := fun ρ _ h h' => c.Holds ρ h h'
  Evidence := FactSupport
  check c F S ev := ev.check c F S
  check_sound c F _ _ h := FactSupport.check_sound c F h

/-- **The survival check**: a produced support of the fact that the effect
respects under the query. -/
def _root_.Verification.HeapKnowledge.IndexFact.keeps (q : SepQuery) (c : ReadContext) (Φ : Footprint) (F : IndexFact) : Bool :=
  match F.support? c with
  | some S => respects q S Φ
  | none => false

/-- **The survival check is sound**: a fact the check keeps holds after
every transition within the effect meeting the context, from a prestate
where the query is sound (`frame_step`). -/
theorem IndexFact.keeps_sound {q : SepQuery} {c : ReadContext} {Φ : Footprint} {F : IndexFact}
    {ρ : Env} {h h' : Heap} (hk : F.keeps q c Φ = true) (hq : q.Sound ρ h) (hp : Post Φ ρ h h')
    (hc : c.Holds ρ h h') (hF : F.HoldsAt ε ρ h) : F.HoldsAt ε ρ h' := by
  unfold IndexFact.keeps at hk
  split at hk
  · rename_i S hS
    exact frame_step (D := heaps) (m := 0) (IndexFact.support?_supports c F hS) hk hq hp trivial hc hF
  · cases hk

end Verification.Footprints
