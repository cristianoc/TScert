import Verification.Semantics.HeapSeparation
import Verification.Semantics.ValueSets

/-! The normal form of separation (heap-knowledge draft, §5): the atomic
statements a separation makes, between slots renamed to their alias classes'
representatives, a pair of fields stored once and in one orientation, a pair
of fields a whole-object pair implies dropped, sorted. -/
namespace Verification.SeparationNormal
open ProgramTyping HeapSeparation CanonicalLists

/-- An atomic separation: every own location of `i`'s object (`whole`), or
its field `f`, differs from field `g` of `j`'s. -/
inductive SepAtom where
  | whole (i j : Nat) (g : PropKey)
  | field (i : Nat) (f : PropKey) (j : Nat) (g : PropKey)
  deriving DecidableEq

def SepAtom.Holds (ρ : Env) : SepAtom → Prop
  | .whole i j g => Apart ρ i none j g
  | .field i f j g => Apart ρ i (some [f]) j g

def SepAtom.key : SepAtom → List Nat
  | .whole i j g => 0 :: i :: j :: ValueSets.propKey g
  | .field i f j g => 1 :: i :: j :: (ValueSets.propKey f).length :: (ValueSets.propKey f ++ ValueSets.propKey g)

theorem SepAtom.key_inj {a b : SepAtom} (h : a.key = b.key) : a = b := by
  cases a with
  | whole i j g =>
    cases b with
    | whole i' j' g' =>
      simp only [SepAtom.key, List.cons.injEq] at h
      obtain ⟨-, rfl, rfl, hg⟩ := h
      rw [ValueSets.propKey_inj hg]
    | field => simp [SepAtom.key] at h
  | field i f j g =>
    cases b with
    | whole => simp [SepAtom.key] at h
    | field i' f' j' g' =>
      simp only [SepAtom.key, List.cons.injEq] at h
      obtain ⟨-, rfl, rfl, hlen, h⟩ := h
      obtain ⟨hf, hg⟩ := List.append_inj h hlen
      rw [ValueSets.propKey_inj hf, ValueSets.propKey_inj hg]

instance : LT SepAtom := ⟨fun a b => a.key < b.key⟩
instance : DecidableLT SepAtom := fun a b => inferInstanceAs (Decidable (a.key < b.key))

instance : StrictTotal SepAtom where
  irrefl a := StrictTotal.irrefl a.key
  trans h₁ h₂ := StrictTotal.trans (α := List Nat) h₁ h₂
  total h := StrictTotal.total (α := List Nat) fun e => h (SepAtom.key_inj e)

/-- The atomic statements of a separation, about slots. -/
def atoms (S : Separation) : List SepAtom :=
  S.facts.flatMap fun a => a.partners.flatMap fun p => p.2.flatMap fun g =>
    let i := S.depth - 1 - a.slot
    let j := S.depth - 1 - p.1
    match a.fields with
    | none => [.whole i j g]
    | some fs => fs.map fun f => .field i f j g

/-- A separation whose levels name slots. -/
def WellFormed (S : Separation) : Prop :=
  ∀ a ∈ S.facts, a.slot < S.depth ∧ ∀ p ∈ a.partners, p.1 < S.depth

theorem atoms_holds {S : Separation} {ρ : Env} :
    WellFormed S → (Holds S ρ ↔ ∀ x ∈ atoms S, x.Holds ρ) := by
  intro wf
  constructor
  · intro hS x hx
    simp only [atoms, List.mem_flatMap] at hx
    obtain ⟨a, ha, p, hp, g, hg, hx⟩ := hx
    have := (hS a ha).2 p hp
    have hap := this.2 g hg
    cases hf : a.fields with
    | none => rw [hf] at hx hap; simp at hx; subst hx; exact hap
    | some fs =>
      rw [hf] at hx hap
      obtain ⟨f, hf', rfl⟩ := List.mem_map.mp hx
      exact hap.single (by simp [covers, hf'])
  · intro hx a ha
    obtain ⟨hs, hps⟩ := wf a ha
    refine ⟨hs, fun p hp => ⟨hps p hp, fun g hg => ?_⟩⟩
    have mem : ∀ y, y ∈ (match a.fields with
        | none => [SepAtom.whole (S.depth - 1 - a.slot) (S.depth - 1 - p.1) g]
        | some fs => fs.map fun f => SepAtom.field (S.depth - 1 - a.slot) f (S.depth - 1 - p.1) g) →
        y ∈ atoms S := fun y hy => by
      simp only [atoms, List.mem_flatMap]
      exact ⟨a, ha, p, hp, g, hg, hy⟩
    cases hf : a.fields with
    | none =>
      have := hx _ (mem (.whole (S.depth - 1 - a.slot) (S.depth - 1 - p.1) g) (by rw [hf]; simp))
      simpa [SepAtom.Holds] using this
    | some fs =>
      apply Apart.ofSingles
      intro f hfs
      have := hx _ (mem (.field (S.depth - 1 - a.slot) f (S.depth - 1 - p.1) g) (by rw [hf]; simp [hfs]))
      simpa [SepAtom.Holds] using this

/-- An endpoint's key, for orienting a pair of fields. -/
def endKey (i : Nat) (f : PropKey) : List Nat := i :: ValueSets.propKey f

/-- Rename slots by `r`, and orient a pair of fields by its endpoints' keys. -/
def rename (r : Nat → Nat) : SepAtom → SepAtom
  | .whole i j g => .whole (r i) (r j) g
  | .field i f j g =>
    if endKey (r j) g < endKey (r i) f then .field (r j) g (r i) f else .field (r i) f (r j) g

/-- A pair of fields a whole-object pair among `xs` implies. -/
def absorbed (xs : List SepAtom) : SepAtom → Bool
  | .whole .. => false
  | .field i f j g => xs.contains (.whole i j g) || xs.contains (.whole j i f)

def normAtoms (r : Nat → Nat) (S : Separation) : List SepAtom :=
  let xs := (atoms S).map (rename r)
  canon (xs.filter fun x => !absorbed xs x)

def encode (d : Nat) : SepAtom → Fact
  | .whole i j g => ⟨d - 1 - i, none, [(d - 1 - j, [g])]⟩
  | .field i f j g => ⟨d - 1 - i, some [f], [(d - 1 - j, [g])]⟩

/-- The normal form of a separation, its slots renamed by `r`. -/
def norm (r : Nat → Nat) (S : Separation) : Separation :=
  let xs := normAtoms r S
  if xs.isEmpty then {} else ⟨S.depth, xs.map (encode S.depth)⟩

section
variable {r : Nat → Nat} {ρ : Env}

theorem rename_holds (hr : ∀ x, ρ (r x) = ρ x) (x : SepAtom) : (rename r x).Holds ρ ↔ x.Holds ρ := by
  cases x with
  | whole i j g =>
    simp only [rename, SepAtom.Holds]
    exact ⟨fun h => h.congr (hr i).symm (hr j).symm, fun h => h.congr (hr i) (hr j)⟩
  | field i f j g =>
    simp only [rename]
    split
    · simp only [SepAtom.Holds]
      exact ⟨fun h => (h.congr (hr j).symm (hr i).symm).symm, fun h => (h.symm).congr (hr j) (hr i)⟩
    · simp only [SepAtom.Holds]
      exact ⟨fun h => h.congr (hr i).symm (hr j).symm, fun h => h.congr (hr i) (hr j)⟩

/-- A whole-object pair implies its fields' pairs, in either orientation. -/
theorem absorbed_holds {xs : List SepAtom} (hx : ∀ i j g, SepAtom.whole i j g ∈ xs → (SepAtom.whole i j g).Holds ρ)
    {x : SepAtom} (ha : absorbed xs x = true) : x.Holds ρ := by
  cases x with
  | whole => simp [absorbed] at ha
  | field i f j g =>
    simp only [absorbed, Bool.or_eq_true, List.contains_iff_mem] at ha
    rcases ha with ha | ha
    · exact (hx _ _ _ ha : Apart ρ i none j g).single (by simp [covers])
    · exact ((hx _ _ _ ha : Apart ρ j none i f).single (f := g) (by simp [covers])).symm

theorem encode_holds {d : Nat} {x : SepAtom} (h : match x with | .whole i j _ | .field i _ j _ => i < d ∧ j < d) :
    (encode d x).Holds d ρ ↔ x.Holds ρ := by
  cases x with
  | whole i j g =>
    obtain ⟨hi, hj⟩ := h
    have e₁ : d - 1 - (d - 1 - i) = i := by omega
    have e₂ : d - 1 - (d - 1 - j) = j := by omega
    simp only [encode, Fact.Holds, List.mem_singleton, forall_eq, List.mem_singleton, e₁, e₂, SepAtom.Holds]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨by omega, by omega, h⟩
  | field i f j g =>
    obtain ⟨hi, hj⟩ := h
    have e₁ : d - 1 - (d - 1 - i) = i := by omega
    have e₂ : d - 1 - (d - 1 - j) = j := by omega
    simp only [encode, Fact.Holds, List.mem_singleton, forall_eq, e₁, e₂, SepAtom.Holds]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨by omega, by omega, h⟩

end

section
variable {r : Nat → Nat} {ρ : Env} {S : Separation}

abbrev Within (d : Nat) : SepAtom → Prop
  | .whole i j _ | .field i _ j _ => i < d ∧ j < d

theorem atoms_within (wf : WellFormed S) : ∀ x ∈ atoms S, Within S.depth x := by
  intro x hx
  simp only [atoms, List.mem_flatMap] at hx
  obtain ⟨a, ha, p, hp, g, _, hx⟩ := hx
  have h₁ := (wf a ha).1
  have h₂ := (wf a ha).2 p hp
  cases hf : a.fields with
  | none => rw [hf] at hx; simp at hx; subst hx; exact ⟨by omega, by omega⟩
  | some fs =>
    rw [hf] at hx
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨by omega, by omega⟩

theorem rename_within (hle : ∀ x, r x ≤ x) {d : Nat} {x : SepAtom} (h : Within d x) : Within d (rename r x) := by
  cases x with
  | whole i j g => obtain ⟨hi, hj⟩ := h; exact ⟨by have := hle i; omega, by have := hle j; omega⟩
  | field i f j g =>
    obtain ⟨hi, hj⟩ := h
    simp only [rename]
    split
    · exact ⟨by have := hle j; omega, by have := hle i; omega⟩
    · exact ⟨by have := hle i; omega, by have := hle j; omega⟩

theorem normAtoms_within (wf : WellFormed S) (hle : ∀ x, r x ≤ x) :
    ∀ y ∈ normAtoms r S, Within S.depth y := by
  intro y hy
  obtain ⟨hy, _⟩ := List.mem_filter.mp (mem_canon.mp hy)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact rename_within hle (atoms_within wf x hx)

theorem norm_holds_iff_atoms (wf : WellFormed S) (hle : ∀ x, r x ≤ x) :
    Holds (norm r S) ρ ↔ ∀ y ∈ normAtoms r S, y.Holds ρ := by
  unfold norm
  dsimp only
  split
  · rename_i he
    simp only [List.isEmpty_iff] at he
    rw [he]
    exact ⟨fun _ _ h => by simp at h, fun _ => empty_holds ρ⟩
  · constructor
    · intro h y hy
      exact (encode_holds (normAtoms_within wf hle y hy)).mp (h _ (List.mem_map.mpr ⟨y, hy, rfl⟩))
    · intro h a ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact (encode_holds (normAtoms_within wf hle y hy)).mpr (h y hy)

/-- **The normal form of a separation holds exactly where it does.** -/
theorem norm_holds (wf : WellFormed S) (hle : ∀ x, r x ≤ x) (hr : ∀ x, ρ (r x) = ρ x) :
    Holds (norm r S) ρ ↔ Holds S ρ := by
  rw [norm_holds_iff_atoms wf hle, atoms_holds wf]
  constructor
  · intro h x hx
    apply (rename_holds hr x).mp
    have hmem : rename r x ∈ (atoms S).map (rename r) := List.mem_map.mpr ⟨x, hx, rfl⟩
    -- Kept, it is in the normal form; absorbed, a kept whole pair implies it.
    have kept : ∀ y ∈ (atoms S).map (rename r), absorbed ((atoms S).map (rename r)) y = false → y.Holds ρ :=
      fun y hy hn => h y (mem_canon.mpr (List.mem_filter.mpr ⟨hy, by simp [hn]⟩))
    cases ha : absorbed ((atoms S).map (rename r)) (rename r x)
    · exact kept _ hmem ha
    · exact absorbed_holds (fun i j g hw => kept _ hw rfl) ha
  · intro h y hy
    obtain ⟨hy, _⟩ := List.mem_filter.mp (mem_canon.mp hy)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (rename_holds hr x).mpr (h x hx)

end

section idem
variable {r : Nat → Nat} {S : Separation}

theorem atoms_encode {d : Nat} {xs : List SepAtom} (hw : ∀ x ∈ xs, Within d x) :
    atoms ⟨d, xs.map (encode d)⟩ = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ih := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    simp only [atoms, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    have hx := hw x (List.mem_cons_self ..)
    cases x with
    | whole i j g =>
      obtain ⟨hi, hj⟩ := hx
      simp only [encode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
      congr 2 <;> omega
    | field i f j g =>
      obtain ⟨hi, hj⟩ := hx
      simp only [encode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      congr 2 <;> omega

theorem rename_rename (hrr : ∀ x, r (r x) = r x) (x : SepAtom) : rename r (rename r x) = rename r x := by
  cases x with
  | whole i j g => simp [rename, hrr]
  | field i f j g =>
    by_cases h : endKey (r j) g < endKey (r i) f
    · simp only [rename, if_pos h, hrr]
      rw [if_neg (fun h' => StrictTotal.irrefl _ (StrictTotal.trans h h'))]
    · simp only [rename, if_neg h, hrr]

theorem absorbed_mono {xs ys : List SepAtom} (h : ∀ z ∈ xs, z ∈ ys) {x : SepAtom}
    (ha : absorbed xs x = true) : absorbed ys x = true := by
  cases x with
  | whole => simp [absorbed] at ha
  | field i f j g =>
    simp only [absorbed, Bool.or_eq_true, List.contains_iff_mem] at ha ⊢
    exact ha.imp (h _) (h _)

theorem norm_idem (wf : WellFormed S) (hle : ∀ x, r x ≤ x) (hrr : ∀ x, r (r x) = r x) :
    norm r (norm r S) = norm r S := by
  have hw := normAtoms_within (r := r) wf hle
  -- The normal form's atoms are its own, each renamed and kept.
  have hkeep : normAtoms r (norm r S) = normAtoms r S := by
    unfold norm
    dsimp only
    split
    · rename_i he
      simp only [List.isEmpty_iff] at he
      rw [he]; simp [normAtoms, atoms]
    · rw [show normAtoms r ⟨S.depth, (normAtoms r S).map (encode S.depth)⟩ =
          canon (((atoms ⟨S.depth, (normAtoms r S).map (encode S.depth)⟩).map (rename r)).filter fun x =>
            !absorbed ((atoms ⟨S.depth, (normAtoms r S).map (encode S.depth)⟩).map (rename r)) x) from rfl,
        atoms_encode hw]
      have hmap : (normAtoms r S).map (rename r) = normAtoms r S := by
        conv => rhs; rw [← List.map_id (normAtoms r S)]
        apply List.map_congr_left
        intro y hy
        obtain ⟨hy, _⟩ := List.mem_filter.mp (mem_canon.mp hy)
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
        exact rename_rename hrr x
      rw [hmap]
      have hfil : (normAtoms r S).filter (fun x => !absorbed (normAtoms r S) x) = normAtoms r S := by
        apply List.filter_eq_self.mpr
        intro y hy
        obtain ⟨_, hn⟩ := List.mem_filter.mp (mem_canon.mp hy)
        cases ha : absorbed (normAtoms r S) y
        · rfl
        · have := absorbed_mono (fun z hz => (List.mem_filter.mp (mem_canon.mp hz)).1) ha
          rw [this] at hn; cases hn
      rw [hfil]
      exact canon_of_pairwise (pairwise_canon _)
  have hd : ¬ (normAtoms r S).isEmpty = true → (norm r S).depth = S.depth := fun h => by
    simp [norm, h]
  show (if (normAtoms r (norm r S)).isEmpty then {} else
    (⟨(norm r S).depth, (normAtoms r (norm r S)).map (encode (norm r S).depth)⟩ : Separation)) = norm r S
  rw [hkeep]
  by_cases he : (normAtoms r S).isEmpty = true
  · rw [if_pos he]; simp only [norm, he, if_true]
  · rw [if_neg he, hd he]; simp [norm, he]

end idem

/-- **Unique**: separations of one depth whose renamed atomic statements are
the same have one normal form. -/
theorem norm_congr {r : Nat → Nat} {S₁ S₂ : Separation} (hd : S₁.depth = S₂.depth)
    (h : ∀ x, x ∈ (atoms S₁).map (rename r) ↔ x ∈ (atoms S₂).map (rename r)) : norm r S₁ = norm r S₂ := by
  have hab : ∀ x, absorbed ((atoms S₁).map (rename r)) x = absorbed ((atoms S₂).map (rename r)) x := by
    intro x
    cases ha : absorbed ((atoms S₁).map (rename r)) x
    · cases hb : absorbed ((atoms S₂).map (rename r)) x
      · rfl
      · rw [absorbed_mono (fun z hz => (h z).mpr hz) hb] at ha; cases ha
    · exact (absorbed_mono (fun z hz => (h z).mp hz) ha).symm
  have hn : normAtoms r S₁ = normAtoms r S₂ := by
    unfold normAtoms
    exact canon_eq fun x => by simp only [List.mem_filter, hab, h x]
  simp only [norm, hn, hd]

/-- A separation that holds names slots at every level. -/
theorem wellFormed_of_holds {S : Separation} {ρ : Env} (h : Holds S ρ) : WellFormed S :=
  fun a ha => ⟨(h a ha).1, fun p hp => ((h a ha).2 p hp).1⟩

end Verification.SeparationNormal
