import Verification.Semantics.HeapLinks

/-! # Separation facts

Heap knowledge's separation (heap-freshness draft, §2): a depth `d` and
facts addressed by **level**, level `ℓ < d` naming slot `d - 1 - ℓ`, so a
push renames every slot and no level. A fact separates its subject's fields
(`none`: every own location of the object) from each partner's listed
fields: different locations, whatever either holds. The meaning names no
heap, so it survives every heap change. A slot at or past the depth has no
level, and no fact names it. -/
namespace Verification.HeapSeparation
open ProgramTyping

/-- A separation fact: the subject's level, its fields (`none`: every own
location), and its partners, each a level and the fields of it. -/
structure Fact where
  slot : Nat
  fields : Option (List PropKey) := none
  partners : List (Nat × List PropKey)
  deriving DecidableEq, Hashable, Repr

/-- A depth and the facts its levels address. `{}` states nothing. -/
structure Separation where
  depth : Nat := 0
  facts : List Fact := []
  deriving DecidableEq, Hashable, Repr

/-- `l` is a location of the fields `F` of `v` (every own location where `F`
is `none`); a value that is no object has none. -/
def At (F : Option (List PropKey)) (v : Tm) (l : Nat) : Prop :=
  match v with
  | .objAt flds _ _ => match F with
    | none => l ∈ flds.map Prod.snd
    | some fs => ∃ f ∈ fs, flds.lookup f = some l
  | _ => False

/-- The fields `F` of slot `i`'s object and field `g` of slot `j`'s are
different locations. -/
def Apart (ρ : Env) (i : Nat) (F : Option (List PropKey)) (j : Nat) (g : PropKey) : Prop :=
  ∀ l l', At F (ρ i) l → At (some [g]) (ρ j) l' → l ≠ l'

def Fact.Holds (d : Nat) (ρ : Env) (a : Fact) : Prop :=
  a.slot < d ∧ ∀ p ∈ a.partners, p.1 < d ∧ ∀ g ∈ p.2, Apart ρ (d - 1 - a.slot) a.fields (d - 1 - p.1) g

def Holds (S : Separation) (ρ : Env) : Prop := ∀ a ∈ S.facts, a.Holds S.depth ρ

theorem empty_holds (ρ : Env) : Holds {} ρ := by simp [Holds]

/-! ## Locations -/

/-- `f` is among the fields `F` (every key where `F` is `none`). -/
def covers : Option (List PropKey) → PropKey → Bool
  | none, _ => true
  | some fs, f => fs.contains f

theorem lookup_mem_snd : ∀ {flds : List (PropKey × Nat)} {f : PropKey} {l : Nat},
    flds.lookup f = some l → l ∈ flds.map Prod.snd
  | [], _, _, h => by simp at h
  | (k, v) :: rest, f, l, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem_snd h)

theorem at_lookup {flds : List (PropKey × Nat)} {c oid f l} (h : flds.lookup f = some l) :
    At (some [f]) (.objAt flds c oid) l := ⟨f, by simp, h⟩

theorem at_of_single {F : Option (List PropKey)} {v f l}
    (hc : covers F f = true) (h : At (some [f]) v l) : At F v l := by
  unfold At at h ⊢
  split at h
  · rename_i flds _ _
    obtain ⟨f', hf', hl⟩ := h
    simp only [List.mem_singleton] at hf'
    subst hf'
    cases F with
    | none => exact lookup_mem_snd hl
    | some fs => exact ⟨f', by simpa [covers] using hc, hl⟩
  · exact h.elim

/-- A separation of fields `F` is one of every field in them. -/
theorem Apart.single {ρ i F j g f} (h : Apart ρ i F j g)
    (hc : covers F f = true) : Apart ρ i (some [f]) j g :=
  fun l l' hl hl' => h l l' (at_of_single hc hl) hl'

theorem Apart.symm {ρ i j f g} (h : Apart ρ i (some [f]) j g) : Apart ρ j (some [g]) i f :=
  fun l l' hl hl' heq => h l' l hl' hl heq.symm

theorem Apart.ofSingles {ρ i fs j g} (h : ∀ f ∈ fs, Apart ρ i (some [f]) j g) : Apart ρ i (some fs) j g := by
  intro l l' hl hl'
  unfold At at hl
  split at hl
  · obtain ⟨f, hf, hlk⟩ := hl
    rename_i flds c oid heq
    exact h f hf l l' (by rw [heq]; exact at_lookup hlk) hl'
  · exact hl.elim

theorem Apart.congr {ρ ρ' i i' F j j' g} (h : Apart ρ i F j g) (hi : ρ' i' = ρ i) (hj : ρ' j' = ρ j) :
    Apart ρ' i' F j' g := by
  unfold Apart; rw [hi, hj]; exact h

/-! ## Canonical form and renaming -/

/-- Facts without partners say nothing; no fact left is the empty
separation, whatever the depth. -/
def norm (d : Nat) (fs : List Fact) : Separation :=
  let fs := fs.filter (fun a => !a.partners.isEmpty)
  if fs.isEmpty then {} else ⟨d, fs⟩

theorem norm_holds {d fs ρ} (h : ∀ a ∈ fs, a.Holds d ρ) : Holds (norm d fs) ρ := by
  unfold norm
  dsimp only
  split
  · exact empty_holds ρ
  · intro a ha
    exact h a (List.mem_filter.mp ha).1

/-- A fact holds where a holding fact names the same values at its subject
and at each of its partners, with at least its partner fields. -/
theorem Fact.rename {d d' : Nat} {ρ ρ' : Env} {a a' : Fact} (ha : a.Holds d ρ) (hs : a'.slot < d')
    (hss : ρ' (d' - 1 - a'.slot) = ρ (d - 1 - a.slot)) (hf : a'.fields = a.fields)
    (hp : ∀ p' ∈ a'.partners, p'.1 < d' ∧ ∀ g ∈ p'.2, ∃ p ∈ a.partners,
      ρ' (d' - 1 - p'.1) = ρ (d - 1 - p.1) ∧ g ∈ p.2) :
    a'.Holds d' ρ' := by
  refine ⟨hs, fun p' hp' => ⟨(hp p' hp').1, fun g hg => ?_⟩⟩
  obtain ⟨p, hpm, hpe, hgp⟩ := (hp p' hp').2 g hg
  rw [hf]
  exact ((ha.2 p hpm).2 g hgp).congr hss hpe

/-- The same facts one push deeper. -/
theorem Fact.pushed {d ρ v} {a : Fact} (ha : a.Holds d ρ) : a.Holds (d + 1) (push v ρ) := by
  have e : ∀ ℓ, ℓ < d → push v ρ (d + 1 - 1 - ℓ) = ρ (d - 1 - ℓ) := by
    intro ℓ hl
    have : d + 1 - 1 - ℓ = (d - 1 - ℓ) + 1 := by omega
    rw [this]; rfl
  exact Fact.rename ha (by have := ha.1; omega) (e _ ha.1) rfl
    (fun p hp => ⟨by have := (ha.2 p hp).1; omega, fun g hg => ⟨p, hp, e _ (ha.2 p hp).1, hg⟩⟩)

/-! ## Push, drop, rebase, copy -/

def shift (S : Separation) : Separation := norm (S.depth + 1) S.facts

theorem shift_holds {S ρ v} (h : Holds S ρ) : Holds (shift S) (push v ρ) :=
  norm_holds fun a ha => Fact.pushed (h a ha)

/-- Pop slot 0, level `depth - 1`: its facts and partners go. -/
def drop (S : Separation) : Separation :=
  let top := S.depth - 1
  norm top (S.facts.filterMap fun a =>
    if a.slot == top then none else some { a with partners := a.partners.filter (·.1 != top) })

theorem drop_holds {S ρ v} (h : Holds S (push v ρ)) : Holds (drop S) ρ := by
  have e : ∀ ℓ, ℓ < S.depth - 1 → ρ (S.depth - 1 - 1 - ℓ) = push v ρ (S.depth - 1 - ℓ) := by
    intro ℓ hl
    have : S.depth - 1 - ℓ = (S.depth - 1 - 1 - ℓ) + 1 := by omega
    rw [this]; rfl
  apply norm_holds
  intro a' ha'
  obtain ⟨a, ha, hsel⟩ := List.mem_filterMap.mp ha'
  split at hsel
  · cases hsel
  · rename_i hne
    cases hsel
    have hh := h a ha
    have hne : a.slot ≠ S.depth - 1 := by simpa using hne
    have hsl : a.slot < S.depth - 1 := by have := hh.1; omega
    refine Fact.rename hh hsl (e _ hsl) rfl ?_
    intro p hp
    have hp := List.mem_filter.mp hp
    have hpd := (hh.2 p hp.1).1
    have hpt : p.1 ≠ S.depth - 1 := by simpa using hp.2
    exact ⟨by omega, fun g hg => ⟨p, hp.1, e _ (by omega), hg⟩⟩

/-- Each fact and partner on slot `x` also stated on slot `y`, which holds
the same value. -/
def restate (S : Separation) (x y : Nat) : Separation :=
  if x < S.depth ∧ y < S.depth then
    let lx := S.depth - 1 - x
    let ly := S.depth - 1 - y
    ⟨S.depth, S.facts.flatMap fun a =>
      let a' : Fact := { a with partners := a.partners ++ (a.partners.filter (·.1 == lx)).map fun p => (ly, p.2) }
      if a.slot == lx then [a', { a' with slot := ly }] else [a']⟩
  else S

theorem restate_holds {S ρ x y} (hxy : ρ y = ρ x) (h : Holds S ρ) : Holds (restate S x y) ρ := by
  unfold restate
  split
  · rename_i hd
    intro a' ha'
    obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp ha'
    have hh := h a ha
    have hy : S.depth - 1 - (S.depth - 1 - y) = y := by omega
    have hx : S.depth - 1 - (S.depth - 1 - x) = x := by omega
    have hps : ∀ p' ∈ a.partners ++ (a.partners.filter (·.1 == S.depth - 1 - x)).map
        (fun p => (S.depth - 1 - y, p.2)), p'.1 < S.depth ∧ ∀ g ∈ p'.2, ∃ p ∈ a.partners,
          ρ (S.depth - 1 - p'.1) = ρ (S.depth - 1 - p.1) ∧ g ∈ p.2 := by
      intro p' hp'
      rcases List.mem_append.mp hp' with hp' | hp'
      · exact ⟨(hh.2 p' hp').1, fun g hg => ⟨p', hp', rfl, hg⟩⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
        have hp := List.mem_filter.mp hp
        have hpl : p.1 = S.depth - 1 - x := by simpa using hp.2
        refine ⟨by omega, fun g hg => ⟨p, hp.1, ?_, hg⟩⟩
        simp only [hpl, hy, hx, hxy]
    split at hm
    · rename_i hs
      have hs : a.slot = S.depth - 1 - x := by simpa using hs
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Fact.rename hh hh.1 rfl rfl hps
      · simp only [List.mem_singleton] at hm
        subst hm
        exact Fact.rename hh (by simp; omega) (by simp only [hs, hy, hx, hxy]) rfl hps
    · simp only [List.mem_singleton] at hm
      subst hm
      exact Fact.rename hh hh.1 rfl rfl hps
  · exact h

/-- The same slots at a depth `D` at least the separation's. -/
def rebase (S : Separation) (D : Nat) : Separation :=
  if S.depth ≤ D then
    norm D (S.facts.map fun a => (⟨a.slot + (D - S.depth), a.fields,
      a.partners.map fun p => (p.1 + (D - S.depth), p.2)⟩ : Fact))
  else S

theorem rebase_holds {S ρ D} (h : Holds S ρ) : Holds (rebase S D) ρ := by
  unfold rebase
  split
  · rename_i hle
    have e : ∀ ℓ, ℓ < S.depth → ρ (D - 1 - (ℓ + (D - S.depth))) = ρ (S.depth - 1 - ℓ) := by
      intro ℓ hl; congr 1; omega
    apply norm_holds
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    have hh := h a ha
    refine Fact.rename hh (by have := hh.1; simp; omega) (e _ hh.1) rfl ?_
    intro p' hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    have hpd := (hh.2 p hp).1
    exact ⟨by simp; omega, fun g hg => ⟨p, hp, e _ hpd, hg⟩⟩
  · exact h

/-- Each partner at level `li` gains a twin at level `t`. -/
def twin (li t : Nat) (a : Fact) : Fact :=
  { a with partners := a.partners ++ (a.partners.filter (·.1 == li)).map fun p => (t, p.2) }

/-- Push a copy of slot `i`: level `depth` of the result holds slot `i`'s
value, so it takes slot `i`'s facts in both roles. A slot without a level
is pushed. -/
def copy (S : Separation) (i : Nat) : Separation :=
  if i < S.depth then
    let li := S.depth - 1 - i
    let plus := S.facts.map (twin li S.depth)
    norm (S.depth + 1) (plus ++ (plus.filter (·.slot == li)).map fun a => { a with slot := S.depth })
  else shift S

theorem copy_holds {S ρ i} (h : Holds S ρ) : Holds (copy S i) (push (ρ i) ρ) := by
  unfold copy
  split
  · rename_i hi
    have e : ∀ ℓ, ℓ < S.depth → push (ρ i) ρ (S.depth + 1 - 1 - ℓ) = ρ (S.depth - 1 - ℓ) := by
      intro ℓ hl
      have : S.depth + 1 - 1 - ℓ = (S.depth - 1 - ℓ) + 1 := by omega
      rw [this]; rfl
    -- Level `depth`, the copy, holds what level `li` holds.
    have e0 : push (ρ i) ρ (S.depth + 1 - 1 - S.depth) = ρ (S.depth - 1 - (S.depth - 1 - i)) := by
      have h0 : S.depth + 1 - 1 - S.depth = 0 := by omega
      have h1 : S.depth - 1 - (S.depth - 1 - i) = i := by omega
      rw [h0, h1]; rfl
    have hpart : ∀ a ∈ S.facts, ∀ p' ∈ (twin (S.depth - 1 - i) S.depth a).partners,
        p'.1 < S.depth + 1 ∧ ∀ g ∈ p'.2, ∃ p ∈ a.partners,
          push (ρ i) ρ (S.depth + 1 - 1 - p'.1) = ρ (S.depth - 1 - p.1) ∧ g ∈ p.2 := by
      intro a ha p' hp'
      have hh := h a ha
      rcases List.mem_append.mp hp' with hp' | hp'
      · have hpd := (hh.2 p' hp').1
        exact ⟨by omega, fun g hg => ⟨p', hp', e _ hpd, hg⟩⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
        have hp := List.mem_filter.mp hp
        have hpe : p.1 = S.depth - 1 - i := by simpa using hp.2
        exact ⟨by omega, fun g hg => ⟨p, hp.1, by rw [hpe]; exact e0, hg⟩⟩
    apply norm_holds
    intro a' ha'
    rcases List.mem_append.mp ha' with ha' | ha'
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      have hh := h a ha
      exact Fact.rename hh (by simp only [twin]; have := hh.1; omega) (e _ hh.1) rfl (hpart a ha)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha'
      have hb := List.mem_filter.mp hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb.1
      have hh := h a ha
      have hsl : a.slot = S.depth - 1 - i := by simpa [twin] using hb.2
      exact Fact.rename hh (by simp) (by rw [hsl]; exact e0) rfl (hpart a ha)
  · exact shift_holds h

/-! ## Allocation -/

/-- The partners of an allocation at depth `D`: each slot below `D` that
`fields` names, with its fields, at its level. -/
def partnersOf (fields : List (Nat × PropKey)) (D : Nat) : List (Nat × List PropKey) :=
  (fields.map (·.1)).eraseDups.filterMap fun s =>
    if s < D then some (D - 1 - s, (fields.filter (·.1 == s)).map (·.2)) else none

/-- The fresh object's fact at depth `D`. -/
def freshFact (fields : List (Nat × PropKey)) (D : Nat) : Fact := ⟨D, none, partnersOf fields D⟩

/-- Push a fresh object, separated from the fields `fields` (slot and key)
of the context's `n` slots. -/
def allocate (S : Separation) (n : Nat) (fields : List (Nat × PropKey)) : Separation :=
  norm (max S.depth n + 1) ((rebase S (max S.depth n)).facts ++ [freshFact fields (max S.depth n)])

theorem allocate_holds {S ρ n fields o} (h : Holds S ρ)
    (hfresh : ∀ s g, (s, g) ∈ fields → Apart (push o ρ) 0 none (s + 1) g) :
    Holds (allocate S n fields) (push o ρ) := by
  unfold allocate
  have hr := rebase_holds (D := max S.depth n) h
  -- The rebased separation is at depth `max S.depth n`, or states nothing.
  have hdepth : (rebase S (max S.depth n)).facts = [] ∨ (rebase S (max S.depth n)).depth = max S.depth n := by
    unfold rebase norm
    split
    · dsimp only; split
      · exact .inl rfl
      · exact .inr rfl
    · omega
  apply norm_holds
  intro a' ha'
  rcases List.mem_append.mp ha' with ha' | ha'
  · rcases hdepth with he | he
    · rw [he] at ha'; simp at ha'
    · have hh := hr a' ha'
      rw [he] at hh
      exact Fact.pushed hh
  · simp only [List.mem_singleton] at ha'
    subst ha'
    refine ⟨by simp [freshFact], fun p hp => ?_⟩
    obtain ⟨s, _, hsel⟩ := List.mem_filterMap.mp hp
    split at hsel
    · rename_i hs
      cases hsel
      refine ⟨by omega, fun g hg => ?_⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      have hq := List.mem_filter.mp hq
      have hqs : q.1 = s := by simpa using hq.2
      have := hfresh q.1 q.2 hq.1
      rw [hqs] at this
      have h0 : max S.depth n + 1 - 1 - max S.depth n = 0 := by omega
      have h1 : max S.depth n + 1 - 1 - (max S.depth n - 1 - s) = s + 1 := by omega
      simpa only [freshFact, h0, h1] using this
    · cases hsel


/-! ## The query -/

def keyed (ps : List (Nat × List PropKey)) (y : Nat) (g : PropKey) : Bool :=
  ps.any fun p => p.1 == y && p.2.contains g

/-- Field `f` of slot `i` and field `g` of slot `s` are separated: a fact
states it, in either orientation. -/
def apart (S : Separation) (i : Nat) (f : PropKey) (s : Nat) (g : PropKey) : Bool :=
  i < S.depth && s < S.depth &&
    S.facts.any fun a =>
      (a.slot == S.depth - 1 - i && covers a.fields f && keyed a.partners (S.depth - 1 - s) g) ||
      (a.slot == S.depth - 1 - s && covers a.fields g && keyed a.partners (S.depth - 1 - i) f)

theorem keyed_sound {d ρ y g} {a : Fact} (ha : a.Holds d ρ) (hk : keyed a.partners y g = true) :
    y < d ∧ Apart ρ (d - 1 - a.slot) a.fields (d - 1 - y) g := by
  obtain ⟨p, hp, hpk⟩ := List.any_eq_true.mp hk
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hpk
  obtain ⟨rfl, hg⟩ := hpk
  exact ⟨(ha.2 p hp).1, (ha.2 p hp).2 g hg⟩

theorem apart_sound {S ρ i f s g} (ha : apart S i f s g = true) (h : Holds S ρ)
    {flds c oid l flds' c' oid' l'} (hi : ρ i = .objAt flds c oid) (hl : flds.lookup f = some l)
    (hs : ρ s = .objAt flds' c' oid') (hl' : flds'.lookup g = some l') : l ≠ l' := by
  simp only [apart, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at ha
  obtain ⟨⟨hid, hsd⟩, a, ham, hcase⟩ := ha
  have hh := h a ham
  rcases hcase with ⟨⟨hsl, hc⟩, hk⟩ | ⟨⟨hsl, hc⟩, hk⟩
  · obtain ⟨_, hap⟩ := keyed_sound hh hk
    have hi' : S.depth - 1 - a.slot = i := by omega
    have hs' : S.depth - 1 - (S.depth - 1 - s) = s := by omega
    rw [hi', hs'] at hap
    exact (hap.single hc) l l' (by rw [hi]; exact at_lookup hl) (by rw [hs]; exact at_lookup hl')
  · obtain ⟨_, hap⟩ := keyed_sound hh hk
    have hs' : S.depth - 1 - a.slot = s := by omega
    have hi' : S.depth - 1 - (S.depth - 1 - i) = i := by omega
    rw [hs', hi'] at hap
    exact ((hap.single hc).symm) l l' (by rw [hi]; exact at_lookup hl) (by rw [hs]; exact at_lookup hl')

/-- Every own location of slot `i` and field `g` of slot `s` are separated: a
fact about all of `i`'s own locations states it. -/
def apartAll (S : Separation) (i : Nat) (s : Nat) (g : PropKey) : Bool :=
  i < S.depth && s < S.depth &&
    S.facts.any fun a => a.slot == S.depth - 1 - i && a.fields == none && keyed a.partners (S.depth - 1 - s) g

theorem apartAll_sound {S ρ i s g} (ha : apartAll S i s g = true) (h : Holds S ρ)
    {l : Nat} (hl : At none (ρ i) l) {flds c oid l'} (hs : ρ s = .objAt flds c oid)
    (hl' : flds.lookup g = some l') : l ≠ l' := by
  simp only [apartAll, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at ha
  obtain ⟨⟨hid, hsd⟩, a, ham, ⟨hsl, hf⟩, hk⟩ := ha
  obtain ⟨_, hap⟩ := keyed_sound (h a ham) hk
  have hi' : S.depth - 1 - a.slot = i := by omega
  have hs' : S.depth - 1 - (S.depth - 1 - s) = s := by omega
  rw [hi', hs', hf] at hap
  exact hap l l' hl (by rw [hs]; exact at_lookup hl')

/-! ## Edges -/

/-- A separation as its pairs: subject level, subject field (`none`: every
own location), partner level, partner field. -/
abbrev Pair := Nat × Option PropKey × Nat × PropKey

def pairs (S : Separation) : List Pair :=
  S.facts.flatMap fun a => a.partners.flatMap fun p => p.2.flatMap fun g =>
    match a.fields with
    | none => [(a.slot, none, p.1, g)]
    | some fs => fs.map fun f => (a.slot, some f, p.1, g)

theorem pairs_sound {S ρ q} (h : Holds S ρ) (hq : q ∈ pairs S) :
    q.1 < S.depth ∧ q.2.2.1 < S.depth ∧
      Apart ρ (S.depth - 1 - q.1) (q.2.1.map ([·])) (S.depth - 1 - q.2.2.1) q.2.2.2 := by
  obtain ⟨a, ha, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨g, hg, hq⟩ := List.mem_flatMap.mp hq
  have hh := h a ha
  have hap := (hh.2 p hp).2 g hg
  cases hF : a.fields with
  | none =>
    rw [hF] at hq hap
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨hh.1, (hh.2 p hp).1, hap⟩
  | some fs =>
    rw [hF] at hq hap
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
    exact ⟨hh.1, (hh.2 p hp).1, hap.single (by simpa [covers] using hf)⟩

/-- A target level's source level under the mapping, where both exist. -/
def level (a b : Separation) (m : PointClaims.Mapping) (ℓ : Nat) : Option Nat :=
  if ℓ < b.depth then
    let j := PointClaims.slot m (b.depth - 1 - ℓ)
    if j < a.depth then some (a.depth - 1 - j) else none
  else none

theorem level_some {a b m ℓ x} (h : level a b m ℓ = some x) :
    ℓ < b.depth ∧ x < a.depth ∧ a.depth - 1 - x = PointClaims.slot m (b.depth - 1 - ℓ) := by
  unfold level at h
  split at h
  · dsimp only at h
    split at h
    · cases h; refine ⟨by assumption, by omega, by omega⟩
    · cases h
  · cases h

/-- One target pair, justified by a source pair in either orientation. -/
def justified (P : Std.HashSet Pair) (x : Nat) (F : Option (List PropKey)) (y : Nat) (g : PropKey) : Bool :=
  match F with
  | none => P.contains (x, none, y, g)
  | some fs => fs.all fun f => P.contains (x, none, y, g) || P.contains (x, some f, y, g) ||
      P.contains (y, none, x, f) || P.contains (y, some g, x, f)

/-- Every target fact's levels exist under the mapping and each of its pairs
is a source pair, in either orientation. The source's pairs are hashed
once. -/
def check (a b : Separation) (m : PointClaims.Mapping) : Bool :=
  let P : Std.HashSet Pair := Std.HashSet.ofList (pairs a)
  b.facts.all fun t => match level a b m t.slot with
    | none => false
    | some x => t.partners.all fun p => match level a b m p.1 with
      | none => false
      | some y => p.2.all fun g => justified P x t.fields y g

theorem check_sound {a b m ρ} (hc : check a b m = true) (h : Holds a ρ) :
    Holds b (PointClaims.mapEnv m ρ) := by
  have mem : ∀ q, (Std.HashSet.ofList (pairs a) : Std.HashSet Pair).contains q = true → q ∈ pairs a := by
    intro q hq
    simpa only [Std.HashSet.contains_ofList, List.contains_iff_mem] using hq
  intro t ht
  have hct := List.all_eq_true.mp hc t ht
  split at hct
  · cases hct
  · rename_i x hx
    obtain ⟨htd, hxd, hxs⟩ := level_some hx
    refine ⟨htd, fun p hp => ?_⟩
    have hcp := List.all_eq_true.mp hct p hp
    split at hcp
    · cases hcp
    · rename_i y hy
      obtain ⟨hpd, hyd, hys⟩ := level_some hy
      refine ⟨hpd, fun g hg => ?_⟩
      have hj := List.all_eq_true.mp hcp g hg
      -- The target's slots hold the source's values at `x` and `y`.
      have ex : PointClaims.mapEnv m ρ (b.depth - 1 - t.slot) = ρ (a.depth - 1 - x) := by
        simp [PointClaims.mapEnv, hxs]
      have ey : PointClaims.mapEnv m ρ (b.depth - 1 - p.1) = ρ (a.depth - 1 - y) := by
        simp [PointClaims.mapEnv, hys]
      have src := fun q (hq : (Std.HashSet.ofList (pairs a) : Std.HashSet Pair).contains q = true) =>
        pairs_sound h (mem q hq)
      unfold justified at hj
      cases hF : t.fields with
      | none =>
        rw [hF] at hj
        exact (src _ hj).2.2.congr ex ey
      | some fs =>
        rw [hF] at hj
        refine Apart.ofSingles fun f hf => ?_
        have hjf := List.all_eq_true.mp hj f hf
        simp only [Bool.or_eq_true] at hjf
        rcases hjf with ((h1 | h2) | h3) | h4
        · exact ((src _ h1).2.2.single (f := f) rfl).congr ex ey
        · exact (src _ h2).2.2.congr ex ey
        · exact (((src _ h3).2.2.single (f := g) rfl).symm).congr ex ey
        · exact ((src _ h4).2.2.symm).congr ex ey

/-- The source's pairs, their levels renamed by `rn`, hashed. -/
@[noinline] def renamedPairs (rn : Nat → Nat) (a : Separation) : Std.HashSet Pair :=
  Std.HashSet.ofList ((pairs a).map fun q => (rn q.1, q.2.1, rn q.2.2.1, q.2.2.2))

/-- Every target pair is one of the hashed source pairs `P`. -/
@[noinline] def checkAgainst (P : Std.HashSet Pair) (rn : Nat → Nat) (a b : Separation)
    (m : PointClaims.Mapping) : Bool :=
  b.facts.all fun t => match level a b m t.slot with
    | none => false
    | some x => t.partners.all fun p => match level a b m p.1 with
      | none => false
      | some y => p.2.all fun g => justified P (rn x) t.fields (rn y) g

/-- `check`, with the source's levels read through `rn` on both sides:
each source pair and each target endpoint at the level `rn` gives, a level
whose slot holds the same value. -/
def checkBy (rn : Nat → Nat) (a b : Separation) (m : PointClaims.Mapping) : Bool :=
  b.facts.isEmpty || (m.isNone && decide (a = b)) || checkAgainst (renamedPairs rn a) rn a b m

/-- `checkBy`, each level's representative read from the table `t`. -/
@[noinline] def checkWithTable (t : Array Nat) (a b : Separation) (m : PointClaims.Mapping) : Bool :=
  checkBy (fun ℓ => t.getD ℓ ℓ) a b m

theorem checkBy_sound {rn : Nat → Nat} {a b m ρ}
    (hrn : ∀ ℓ, ℓ < a.depth → rn ℓ < a.depth ∧ ρ (a.depth - 1 - rn ℓ) = ρ (a.depth - 1 - ℓ))
    (hc : checkBy rn a b m = true) (h : Holds a ρ) : Holds b (PointClaims.mapEnv m ρ) := by
  -- A hashed pair, read back: a source pair at the renamed levels, apart.
  unfold checkBy at hc
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · rcases Bool.or_eq_true_iff.mp hc with he | he
    · intro t ht; simp [List.isEmpty_iff.mp he] at ht
    · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact h
  unfold checkAgainst at hc
  have src : ∀ q, (renamedPairs rn a).contains q = true →
      Apart ρ (a.depth - 1 - q.1) (q.2.1.map ([·])) (a.depth - 1 - q.2.2.1) q.2.2.2 := by
    intro q hq
    simp only [renamedPairs, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨h1, h2, hap⟩ := pairs_sound h hq'
    exact hap.congr (hrn _ h1).2 (hrn _ h2).2
  intro t ht
  have hct := List.all_eq_true.mp hc t ht
  split at hct
  · cases hct
  · rename_i x hx
    obtain ⟨htd, hxd, hxs⟩ := level_some hx
    refine ⟨htd, fun p hp => ?_⟩
    have hcp := List.all_eq_true.mp hct p hp
    split at hcp
    · cases hcp
    · rename_i y hy
      obtain ⟨hpd, hyd, hys⟩ := level_some hy
      refine ⟨hpd, fun g hg => ?_⟩
      have hj := List.all_eq_true.mp hcp g hg
      have ex : PointClaims.mapEnv m ρ (b.depth - 1 - t.slot) = ρ (a.depth - 1 - rn x) := by
        simp [PointClaims.mapEnv, hxs, (hrn x hxd).2]
      have ey : PointClaims.mapEnv m ρ (b.depth - 1 - p.1) = ρ (a.depth - 1 - rn y) := by
        simp [PointClaims.mapEnv, hys, (hrn y hyd).2]
      unfold justified at hj
      cases hF : t.fields with
      | none =>
        rw [hF] at hj
        exact (src _ hj).congr ex ey
      | some fs =>
        rw [hF] at hj
        refine Apart.ofSingles fun f hf => ?_
        have hjf := List.all_eq_true.mp hj f hf
        simp only [Bool.or_eq_true] at hjf
        rcases hjf with ((h1 | h2) | h3) | h4
        · exact ((src _ h1).single (f := f) rfl).congr ex ey
        · exact (src _ h2).congr ex ey
        · exact (((src _ h3).single (f := g) rfl).symm).congr ex ey
        · exact ((src _ h4).symm).congr ex ey

/-- `apart`, asked of every pair of slots `M` gives as holding the two
slots' values. -/
def apartBy (M : Nat → List Nat) (S : Separation) (i : Nat) (f : PropKey) (s : Nat) (g : PropKey) : Bool :=
  (M i).any fun i' => (M s).any fun s' => apart S i' f s' g

theorem apartBy_sound {M : Nat → List Nat} {S ρ i f s g} (hM : ∀ x, ∀ y ∈ M x, ρ y = ρ x)
    (ha : apartBy M S i f s g = true) (h : Holds S ρ)
    {flds c oid l flds' c' oid' l'} (hi : ρ i = .objAt flds c oid) (hl : flds.lookup f = some l)
    (hs : ρ s = .objAt flds' c' oid') (hl' : flds'.lookup g = some l') : l ≠ l' := by
  obtain ⟨i', hi', ha⟩ := List.any_eq_true.mp ha
  obtain ⟨s', hs', ha⟩ := List.any_eq_true.mp ha
  exact apart_sound ha h (by rw [hM i i' hi', hi]) hl (by rw [hM s s' hs', hs]) hl'

/-! ## The residual representation -/

/-- Pairs of slots' fields, each one explicit fact at depth `d`. -/
def ofPairs (d : Nat) (ps : List (Nat × PropKey × Nat × PropKey)) : Separation :=
  ⟨d, ps.map fun q => (⟨d - 1 - q.1, some [q.2.1], [(d - 1 - q.2.2.1, [q.2.2.2])]⟩ : Fact)⟩

/-- Any set of distinct links, each a pair of slots below `d`, has a
separation of the same meaning. -/
theorem ofPairs_iff {d ps ρ} (hd : ∀ q ∈ ps, q.1 < d ∧ q.2.2.1 < d) :
    Holds (ofPairs d ps) ρ ↔ ∀ q ∈ ps, Apart ρ q.1 (some [q.2.1]) q.2.2.1 q.2.2.2 := by
  show (∀ a ∈ _, Fact.Holds d ρ a) ↔ _
  constructor
  · intro h q hq
    have hh := h _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    have hp := (hh.2 _ (List.mem_singleton_self _)).2 q.2.2.2 (List.mem_singleton_self _)
    have h1 : d - 1 - (d - 1 - q.1) = q.1 := by have := (hd q hq).1; omega
    have h2 : d - 1 - (d - 1 - q.2.2.1) = q.2.2.1 := by have := (hd q hq).2; omega
    simpa only [h1, h2] using hp
  · intro h a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    refine ⟨by show d - 1 - q.1 < d; have := (hd q hq).1; omega, fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp
    subst hp
    refine ⟨by have := (hd q hq).2; omega, fun g hg => ?_⟩
    simp only [List.mem_singleton] at hg
    subst hg
    have h1 : d - 1 - (d - 1 - q.1) = q.1 := by have := (hd q hq).1; omega
    have h2 : d - 1 - (d - 1 - q.2.2.1) = q.2.2.1 := by have := (hd q hq).2; omega
    simpa only [h1, h2] using h q hq

/-- Completeness of allocation against the pairwise rule: the query answers
for every field of the fresh object and every listed field of a slot below
`n`. -/
theorem allocate_apart {S n fields s g f} (hm : (s, g) ∈ fields) (hs : s < n) :
    apart (allocate S n fields) 0 f (s + 1) g = true := by
  have hp : (max S.depth n - 1 - s, (fields.filter (·.1 == s)).map (·.2)) ∈ partnersOf fields (max S.depth n) :=
    List.mem_filterMap.mpr ⟨s, List.mem_eraseDups.mpr (List.mem_map.mpr ⟨_, hm, rfl⟩), by rw [if_pos (by omega)]⟩
  have hnew : freshFact fields (max S.depth n) ∈
      ((rebase S (max S.depth n)).facts ++ [freshFact fields (max S.depth n)]).filter (fun a => !a.partners.isEmpty) := by
    refine List.mem_filter.mpr ⟨by simp, ?_⟩
    cases hq : partnersOf fields (max S.depth n) with
    | nil => rw [hq] at hp; simp at hp
    | cons _ _ => simp [freshFact, hq]
  have hne : (((rebase S (max S.depth n)).facts ++ [freshFact fields (max S.depth n)]).filter
      (fun a => !a.partners.isEmpty)).isEmpty = false := by
    cases hl : (((rebase S (max S.depth n)).facts ++ [freshFact fields (max S.depth n)]).filter
      (fun a => !a.partners.isEmpty)) with
    | nil => rw [hl] at hnew; simp at hnew
    | cons _ _ => rfl
  unfold allocate norm
  simp only [hne, Bool.false_eq_true, if_false]
  simp only [apart, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨by omega, by omega⟩, _, hnew, .inl ⟨⟨by simp [freshFact], rfl⟩, ?_⟩⟩
  refine List.any_eq_true.mpr ⟨_, hp, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
  exact ⟨by omega, List.mem_map.mpr ⟨(s, g), List.mem_filter.mpr ⟨hm, by simp⟩, rfl⟩⟩

/-! ## The producer's projection and join (untrusted: every edge is checked) -/

/-- Each fact at every target slot the mapping takes from its subject's slot,
each partner at every target slot taken from its slot, at depth `count`. -/
def project (M : Nat → List Nat) (S : Separation) (m : PointClaims.Mapping) (count : Nat) : Separation :=
  let preimages : Std.HashMap Nat (List Nat) := (List.range count).foldr
    (fun j acc => acc.alter (PointClaims.slot m j) fun js => some (j :: js.getD [])) ∅
  let levels := fun (ℓ : Nat) => if ℓ < S.depth then
      ((M (S.depth - 1 - ℓ)).flatMap fun x => preimages.getD x []).eraseDups.map fun j => count - 1 - j else []
  norm count (S.facts.flatMap fun a => (levels a.slot).map fun x =>
    (⟨x, a.fields, a.partners.flatMap fun p => (levels p.1).map fun y => (y, p.2)⟩ : Fact))

/-- What every state establishes: the pairs of the first state every other
state justifies, in either orientation. A fact of every own location keeps
the partner fields every state justifies for it whole; for a pair another
state justifies only for some of the subject's fields, it keeps those fields
as residual facts, one per field. An explicit fact keeps each of its fields'
justified pairs. States at different depths share nothing. -/
def meet : List Separation → Separation
  | [] => {}
  | s :: ss =>
    if ss.all (·.depth == s.depth) then
      let others := ss.map fun o => (Std.HashSet.ofList (pairs o) : Std.HashSet Pair)
      let every := fun (x : Nat) (F : Option (List PropKey)) (y : Nat) (g : PropKey) =>
        others.all fun P => justified P x F y g
      -- The fields the other states name of each level: the candidates of a
      -- whole-object fact's residual.
      let named : Std.HashMap Nat (List PropKey) := ss.foldl (fun acc o => (pairs o).foldl (fun acc q =>
          let acc := match q.2.1 with
            | some f => acc.alter q.1 fun l => some (f :: l.getD [])
            | none => acc
          acc.alter q.2.2.1 fun l => some (q.2.2.2 :: l.getD [])) acc) ∅
      let keep := fun (a : Fact) (F : Option (List PropKey)) (apartWhole : Option (Option (List PropKey))) =>
        (⟨a.slot, F, a.partners.map fun p => (p.1, p.2.filter fun g =>
          (apartWhole.all fun U => !every a.slot U p.1 g) && every a.slot F p.1 g)⟩ : Fact)
      norm s.depth ((s.facts.flatMap fun a => match a.fields with
        | none => keep a none none :: ((named.getD a.slot []).eraseDups.map fun f => keep a (some [f]) (some none))
        | some fs => fs.map fun f => keep a (some [f]) none).map fun a =>
          { a with partners := a.partners.filter (!·.2.isEmpty) })
    else {}

/-- Both separations' facts, where both are at one depth or one is empty;
the second otherwise. -/
def union (S T : Separation) : Separation :=
  if S.facts.isEmpty then T
  else if T.facts.isEmpty then S
  else if S.depth == T.depth then norm S.depth (S.facts ++ T.facts.filter (!S.facts.contains ·))
  else T

end Verification.HeapSeparation
