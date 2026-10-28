import Verification.Semantics.HeapSeparation
import Verification.Semantics.ValueSets

/-! Separation's stored form (heap-knowledge draft, §5): levels read through
their slots' alias-class representatives, one fact per subject and fields,
its partners merged by level, levels and fields in order and each once. It
states exactly what the separation states (`compact_holds`), is its own
compacted form (`compact_idem`) and has at most the separation's facts
(`compact_size`). The atomic statements a separation makes (`atoms`) are its
reference reading, which `KnowledgeExpand.expand` restates on every alias. -/
namespace Verification.SeparationNormal
open ProgramTyping HeapSeparation CanonicalLists

/-- An atomic separation: every own location of `i`'s object (`whole`), or
its field `f`, differs from field `g` of `j`'s. -/
inductive SepAtom where
  | whole (i j : Nat) (g : PropKey)
  | field (i : Nat) (f : PropKey) (j : Nat) (g : PropKey)
  deriving DecidableEq, Hashable

def SepAtom.Holds (ρ : Env) : SepAtom → Prop
  | .whole i j g => Apart ρ i none j g
  | .field i f j g => Apart ρ i (some [f]) j g

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

/-- An atom as a fact at depth `d`. -/
def encode (d : Nat) : SepAtom → Fact
  | .whole i j g => ⟨d - 1 - i, none, [(d - 1 - j, [g])]⟩
  | .field i f j g => ⟨d - 1 - i, some [f], [(d - 1 - j, [g])]⟩

section
variable {ρ : Env}

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

/-- A separation that holds names slots at every level. -/
theorem wellFormed_of_holds {S : Separation} {ρ : Env} (h : Holds S ρ) : WellFormed S :=
  fun a ha => ⟨(h a ha).1, fun p hp => ((h a ha).2 p hp).1⟩

/-! ## Compaction -/

/-- A level read through its slot's representative `r`. -/
def levelRep (r : Nat → Nat) (d ℓ : Nat) : Nat := if ℓ < d then d - 1 - r (d - 1 - ℓ) else ℓ

/-- `levelRep r d` at each level below `d`, computed once. -/
@[noinline] def levelTable (r : Nat → Nat) (d : Nat) : Array Nat := (Array.range d).map (levelRep r d)

theorem levelTable_eq (r : Nat → Nat) (d ℓ : Nat) : (levelTable r d).getD ℓ ℓ = levelRep r d ℓ := by
  simp only [levelTable, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases h : ℓ < d
  · simp [h]
  · simp [h, levelRep]

/-! ### Property keys in order -/

/-- Property keys in order: strings by the string order, before symbols by
their numbers. -/
def PropKey.lt : PropKey → PropKey → Prop
  | .str a, .str b => a < b
  | .str _, .sym _ => True
  | .sym _, .str _ => False
  | .sym m, .sym n => m < n

instance : LT PropKey := ⟨PropKey.lt⟩
instance : DecidableLT PropKey := fun a b => match a, b with
  | .str a, .str b => inferInstanceAs (Decidable (a < b))
  | .str _, .sym _ => inferInstanceAs (Decidable True)
  | .sym _, .str _ => inferInstanceAs (Decidable False)
  | .sym m, .sym n => inferInstanceAs (Decidable (m < n))

instance : StrictTotal PropKey where
  irrefl a h := by
    cases a with
    | str x => exact StrictTotal.irrefl x h
    | sym n => exact StrictTotal.irrefl n h
  trans {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;> simp only [LT.lt, PropKey.lt] at h₁ h₂ ⊢
    all_goals first | trivial | exact StrictTotal.trans (α := String) h₁ h₂ | exact Nat.lt_trans h₁ h₂
  total {a b} h := by
    cases a with
    | str x => cases b with
      | str y => exact StrictTotal.total (α := String) fun e => h (e ▸ rfl)
      | sym _ => exact Or.inl trivial
    | sym m => cases b with
      | str _ => exact Or.inr trivial
      | sym n => exact StrictTotal.total (α := Nat) fun e => h (e ▸ rfl)

/-- A list of fields in order, each once. -/
def fieldsCanon (fs : List PropKey) : List PropKey := canon fs

/-! ### The compacted form -/

/-- The first occurrence of each element, in order. -/
def firsts {κ : Type} [DecidableEq κ] : List κ → List κ
  | [] => []
  | x :: xs => x :: (firsts xs).filter (· ≠ x)

/-- Partners of one level merged: the levels in order, each with its fields
in order, each once. -/
def mergePartners (ps : List (Nat × List PropKey)) : List (Nat × List PropKey) :=
  (canon (ps.map (·.1))).map fun l => (l, fieldsCanon ((ps.filter (·.1 = l)).flatMap (·.2)))

/-- A fact's subject and partner levels read through `rn`, its fields in order. -/
def renameFact (rn : Nat → Nat) (a : Fact) : Fact :=
  ⟨rn a.slot, a.fields.map fieldsCanon, a.partners.map fun p => (rn p.1, p.2)⟩

/-- What facts of one group share: the subject's level and its fields. -/
def factKey (a : Fact) : Nat × Option (List PropKey) := (a.slot, a.fields)

/-- A separation compacted, its levels read through `rn`: one fact per
subject and fields, its partners merged by level, each field once, facts
without partners dropped. -/
def compactBy (rn : Nat → Nat) (S : Separation) : Separation :=
  let fs := S.facts.map (renameFact rn)
  HeapSeparation.norm S.depth ((firsts (fs.map factKey)).map fun key =>
    ⟨key.1, key.2, mergePartners ((fs.filter (factKey · = key)).flatMap (·.partners))⟩)

/-- `compactBy`, each level's representative read from the table `t`. -/
@[noinline] def compactWith (t : Array Nat) (S : Separation) : Separation :=
  compactBy (fun ℓ => t.getD ℓ ℓ) S

/-- A separation compacted, levels read through their slots' representatives `r`. -/
def compact (r : Nat → Nat) (S : Separation) : Separation := compactWith (levelTable r S.depth) S

theorem compact_eq (r : Nat → Nat) (S : Separation) : compact r S = compactBy (levelRep r S.depth) S := by
  simp only [compact, compactWith]
  congr 1
  funext ℓ
  exact levelTable_eq r S.depth ℓ

/-! ### Lists -/

section lists
variable {κ : Type} [DecidableEq κ]

theorem mem_firsts : ∀ {l : List κ} {x : κ}, x ∈ firsts l ↔ x ∈ l
  | [], _ => by simp [firsts]
  | y :: ys, x => by
    simp only [firsts, List.mem_cons, List.mem_filter, mem_firsts, decide_eq_true_eq]
    by_cases h : x = y <;> simp [h]

theorem nodup_firsts : ∀ (l : List κ), (firsts l).Nodup
  | [] => List.nodup_nil
  | y :: ys => by
    simp only [firsts, List.nodup_cons, List.mem_filter, decide_eq_true_eq, ne_eq, not_true_eq_false,
      and_false, not_false_eq_true, true_and]
    exact (nodup_firsts ys).filter _

theorem firsts_of_nodup : ∀ {l : List κ}, l.Nodup → firsts l = l
  | [], _ => rfl
  | y :: ys, h => by
    rw [List.nodup_cons] at h
    simp only [firsts, firsts_of_nodup h.2, List.cons.injEq, true_and]
    exact List.filter_eq_self.mpr fun x hx => by
      simp only [ne_eq, decide_eq_true_eq]; exact fun e => h.1 (e ▸ hx)

theorem length_firsts : ∀ (l : List κ), (firsts l).length ≤ l.length
  | [] => Nat.le_refl _
  | y :: ys => by
    simp only [firsts, List.length_cons]
    exact Nat.succ_le_succ (Nat.le_trans (List.length_filter_le _ _) (length_firsts ys))

/-- In a list whose keys are distinct, one element has its key. -/
theorem filter_key_one {α : Type} (k : α → κ) : ∀ {l : List α} {x : α}, (l.map k).Nodup → x ∈ l →
    l.filter (fun y => decide (k y = k x)) = [x]
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: ys, x, hnd, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hk : k y = k x
    · have hyx : y = x := by
        rcases List.mem_cons.mp hx with h | h
        · exact h.symm
        · exact absurd (hk ▸ List.mem_map_of_mem h) hnd.1
      subst hyx
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      exact List.filter_eq_nil_iff.mpr fun z hz => by
        simp only [decide_eq_true_eq]; exact fun e => hnd.1 (e ▸ List.mem_map_of_mem hz)
    · rw [List.filter_cons_of_neg (by simpa using hk)]
      have hx' : x ∈ ys := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd (h ▸ rfl) hk
        · exact h
      exact filter_key_one k hnd.2 hx'

end lists

theorem mem_fieldsCanon {fs : List PropKey} {g : PropKey} : g ∈ fieldsCanon fs ↔ g ∈ fs := mem_canon

theorem fieldsCanon_fieldsCanon (fs : List PropKey) : fieldsCanon (fieldsCanon fs) = fieldsCanon fs :=
  canon_canon fs

/-- A merged partner's fields are the fields of the partners at its level. -/
theorem mem_mergePartners {ps : List (Nat × List PropKey)} {q : Nat × List PropKey} (hq : q ∈ mergePartners ps) :
    (∃ p ∈ ps, p.1 = q.1) ∧ ∀ g, g ∈ q.2 ↔ ∃ p ∈ ps, p.1 = q.1 ∧ g ∈ p.2 := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
  obtain ⟨p, hp, hpl⟩ := List.mem_map.mp (mem_canon.mp hl)
  refine ⟨⟨p, hp, hpl⟩, fun g => ?_⟩
  simp only [mem_fieldsCanon, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨p, ⟨hp, he⟩, hg⟩ => ⟨p, hp, he, hg⟩, fun ⟨p, hp, he, hg⟩ => ⟨p, ⟨hp, he⟩, hg⟩⟩

/-- Every partner's fields are among the merged partner's at its level. -/
theorem mergePartners_covers {ps : List (Nat × List PropKey)} {p : Nat × List PropKey} (hp : p ∈ ps) :
    ∃ q ∈ mergePartners ps, q.1 = p.1 ∧ ∀ g ∈ p.2, g ∈ q.2 := by
  refine ⟨(p.1, fieldsCanon ((ps.filter (·.1 = p.1)).flatMap (·.2))),
    List.mem_map.mpr ⟨p.1, mem_canon.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩), rfl⟩, rfl, fun g hg => ?_⟩
  simp only [mem_fieldsCanon, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  exact ⟨p, ⟨hp, rfl⟩, hg⟩

theorem mergePartners_ne_nil {ps : List (Nat × List PropKey)} (h : ps ≠ []) : mergePartners ps ≠ [] := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ps h
  obtain ⟨q, hq, -⟩ := mergePartners_covers hp
  exact List.ne_nil_of_mem hq

theorem mergePartners_def (ps : List (Nat × List PropKey)) : mergePartners ps =
    (canon (ps.map (·.1))).map fun l => (l, fieldsCanon ((ps.filter (·.1 = l)).flatMap (·.2))) := rfl

theorem mergePartners_fst (ps : List (Nat × List PropKey)) :
    (mergePartners ps).map (·.1) = canon (ps.map (·.1)) := by
  rw [mergePartners_def, List.map_map]; exact List.map_id' _

theorem mergePartners_snd {ps : List (Nat × List PropKey)} {q} (hq : q ∈ mergePartners ps) :
    q.2.Pairwise (· < ·) := by
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hq
  exact pairwise_canon _

/-- Merged partners merge to themselves. -/
theorem mergePartners_mergePartners (ps : List (Nat × List PropKey)) :
    mergePartners (mergePartners ps) = mergePartners ps := by
  have hfst : (mergePartners ps).map (·.1) = canon (ps.map (·.1)) := by
    rw [mergePartners_def, List.map_map]; exact List.map_id' _
  have hnd : ((mergePartners ps).map (·.1)).Nodup := by
    rw [hfst]
    exact (pairwise_canon _).imp fun h e => by subst e; exact StrictTotal.irrefl _ h
  rw [mergePartners_def (mergePartners ps), hfst, canon_canon]
  conv => rhs; rw [mergePartners_def ps]
  apply List.map_congr_left
  intro l hl
  have hq : (l, fieldsCanon ((ps.filter (·.1 = l)).flatMap (·.2))) ∈ mergePartners ps :=
    List.mem_map.mpr ⟨l, hl, rfl⟩
  have hone := filter_key_one (·.1) hnd hq
  simp only at hone
  rw [hone]
  simp [fieldsCanon_fieldsCanon]

/-! ### Meaning -/

theorem at_fieldsCanon {F : Option (List PropKey)} {v : Tm} {l : Nat} :
    At (F.map fieldsCanon) v l ↔ At F v l := by
  cases F with
  | none => rfl
  | some fs =>
    simp only [Option.map_some, At]
    split
    · simp only [mem_fieldsCanon]
    · exact Iff.rfl

theorem apart_fieldsCanon {ρ : Env} {i j : Nat} {F : Option (List PropKey)} {g : PropKey} :
    Apart ρ i (F.map fieldsCanon) j g ↔ Apart ρ i F j g := by
  simp only [Apart, at_fieldsCanon]

theorem holds_norm {d : Nat} {fs : List Fact} {ρ : Env} :
    Holds (HeapSeparation.norm d fs) ρ ↔ ∀ a ∈ fs, a.partners ≠ [] → a.Holds d ρ := by
  unfold HeapSeparation.norm
  dsimp only
  split
  · rename_i he
    refine ⟨fun _ a ha hp => ?_, fun _ => empty_holds ρ⟩
    have : a ∈ fs.filter (fun a => !a.partners.isEmpty) := List.mem_filter.mpr ⟨ha, by simpa using hp⟩
    simp [List.isEmpty_iff.mp he] at this
  · constructor
    · intro h a ha hp
      exact h a (List.mem_filter.mpr ⟨ha, by simpa using hp⟩)
    · intro h a ha
      have ha := List.mem_filter.mp ha
      exact h a ha.1 (by simpa using ha.2)

section meaning
variable {rn : Nat → Nat} {S : Separation} {ρ : Env}

/-- The compacted form's facts before the empty ones are dropped. -/
def grouped (rn : Nat → Nat) (S : Separation) : List Fact :=
  let fs := S.facts.map (renameFact rn)
  (firsts (fs.map factKey)).map fun key =>
    ⟨key.1, key.2, mergePartners ((fs.filter (factKey · = key)).flatMap (·.partners))⟩

theorem compactBy_eq : compactBy rn S = HeapSeparation.norm S.depth (grouped rn S) := rfl

/-- A grouped fact's partner and field come from a fact of its group. -/
theorem grouped_source {t : Fact} (ht : t ∈ grouped rn S) :
    (∃ a ∈ S.facts, rn a.slot = t.slot ∧ a.fields.map fieldsCanon = t.fields) ∧
    (∀ q ∈ t.partners, ∃ a ∈ S.facts, ∃ p ∈ a.partners, rn p.1 = q.1) ∧
    ∀ q ∈ t.partners, ∀ g ∈ q.2, ∃ a ∈ S.facts, rn a.slot = t.slot ∧ a.fields.map fieldsCanon = t.fields ∧
      ∃ p ∈ a.partners, rn p.1 = q.1 ∧ g ∈ p.2 := by
  obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp ht
  obtain ⟨a', ha', hk⟩ := List.mem_map.mp (mem_firsts.mp hkey)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  refine ⟨⟨a, ha, by simp [← hk, factKey, renameFact], by simp [← hk, factKey, renameFact]⟩, fun q hq => ?_,
    fun q hq g hg => ?_⟩
  · obtain ⟨⟨p', hp', hpq⟩, -⟩ := mem_mergePartners hq
    obtain ⟨b', hb', hp'b⟩ := List.mem_flatMap.mp hp'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb').1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'b
    exact ⟨b, hb, p, hp, hpq⟩
  obtain ⟨p', hp', hpq, hgp⟩ := ((mem_mergePartners hq).2 g).mp hg
  obtain ⟨b', hb', hp'b⟩ := List.mem_flatMap.mp hp'
  obtain ⟨hb'm, hbk⟩ := List.mem_filter.mp hb'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'm
  have hbk : factKey (renameFact rn b) = key := by simpa using hbk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'b
  exact ⟨b, hb, by simp [← hbk, factKey, renameFact], by simp [← hbk, factKey, renameFact], p, hp, hpq, hgp⟩

/-- Every fact's partners' fields are stated by its group's fact. -/
theorem grouped_covers {a : Fact} (ha : a ∈ S.facts) {p} (hp : p ∈ a.partners) :
    ∃ t ∈ grouped rn S, t.slot = rn a.slot ∧ t.fields = a.fields.map fieldsCanon ∧
      ∃ q ∈ t.partners, q.1 = rn p.1 ∧ ∀ g ∈ p.2, g ∈ q.2 := by
  let key := factKey (renameFact rn a)
  have hmem : renameFact rn a ∈ (S.facts.map (renameFact rn)).filter (factKey · = key) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨a, ha, rfl⟩, by simp [key]⟩
  have hp' : (rn p.1, p.2) ∈ ((S.facts.map (renameFact rn)).filter (factKey · = key)).flatMap (·.partners) :=
    List.mem_flatMap.mpr ⟨_, hmem, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  obtain ⟨q, hq, hq1, hq2⟩ := mergePartners_covers hp'
  exact ⟨_, List.mem_map.mpr ⟨key, mem_firsts.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩), rfl⟩,
    rfl, rfl, q, hq, hq1, hq2⟩

/-- **Compaction states what the separation states**, where each renamed
level names a slot holding the same value. -/
theorem compactBy_holds (wf : WellFormed S)
    (hrn : ∀ ℓ, ℓ < S.depth → rn ℓ < S.depth ∧ ρ (S.depth - 1 - rn ℓ) = ρ (S.depth - 1 - ℓ)) :
    Holds (compactBy rn S) ρ ↔ Holds S ρ := by
  rw [compactBy_eq, holds_norm]
  constructor
  · intro h a ha
    refine ⟨(wf a ha).1, fun p hp => ⟨(wf a ha).2 p hp, fun g hg => ?_⟩⟩
    obtain ⟨t, ht, hts, htf, q, hq, hq1, hq2⟩ := grouped_covers (rn := rn) ha hp
    have hth := h t ht (List.ne_nil_of_mem hq)
    have hap := (hth.2 q hq).2 g (hq2 g hg)
    rw [hts, htf, hq1, apart_fieldsCanon] at hap
    exact hap.congr (hrn _ (wf a ha).1).2.symm (hrn _ ((wf a ha).2 p hp)).2.symm
  · intro h t ht _
    obtain ⟨⟨a, ha, has, -⟩, hlev, hsrc⟩ := grouped_source ht
    refine ⟨by rw [← has]; exact (hrn _ (wf a ha).1).1, fun q hq => ⟨?_, fun g hg => ?_⟩⟩
    · obtain ⟨c, hc, p', hp', hpq⟩ := hlev q hq
      rw [← hpq]; exact (hrn _ ((wf c hc).2 p' hp')).1
    · obtain ⟨b, hb, hbs, hbf, p, hp, hpq, hgp⟩ := hsrc q hq g hg
      have hap := ((h b hb).2 p hp).2 g hgp
      rw [← apart_fieldsCanon, hbf] at hap
      rw [← hbs, ← hpq]
      exact hap.congr (hrn _ (wf b hb).1).2 (hrn _ ((wf b hb).2 p hp)).2

end meaning

/-! ### Idempotence and size -/

section idem
variable {rn : Nat → Nat} {S : Separation}

theorem grouped_keys_nodup : ((grouped rn S).map factKey).Nodup := by
  simp only [grouped, List.map_map]
  have : (factKey ∘ fun key : Nat × Option (List PropKey) =>
      (⟨key.1, key.2, mergePartners (((S.facts.map (renameFact rn)).filter (factKey · = key)).flatMap (·.partners))⟩ : Fact)) = id := by
    funext key; rfl
  rw [this, List.map_id]
  exact nodup_firsts _

/-- A grouped fact's levels are fixed by `rn` and its fields in order. -/
theorem renameFact_grouped (wf : WellFormed S) (hrr : ∀ ℓ, ℓ < S.depth → rn (rn ℓ) = rn ℓ)
    {t : Fact} (ht : t ∈ grouped rn S) : renameFact rn t = t := by
  obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp ht
  obtain ⟨a', ha', hk⟩ := List.mem_map.mp (mem_firsts.mp hkey)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  subst hk
  simp only [renameFact, factKey, Fact.mk.injEq]
  refine ⟨hrr _ (wf a ha).1, ?_, ?_⟩
  · simp only [Option.map_map]
    congr 1
    funext fs
    exact fieldsCanon_fieldsCanon fs
  · conv => rhs; rw [← List.map_id (mergePartners _)]
    apply List.map_congr_left
    intro q hq
    obtain ⟨⟨p, hp, hpq⟩, -⟩ := mem_mergePartners hq
    obtain ⟨b, hb, hbp⟩ := List.mem_flatMap.mp hp
    obtain ⟨hbm, -⟩ := List.mem_filter.mp hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbm
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hbp
    show (rn q.1, q.2) = q
    have e : q.1 = rn p'.1 := hpq.symm
    rw [e, hrr _ ((wf c hc).2 p' hp'), ← e]

theorem norm_norm (d : Nat) (fs : List Fact) :
    HeapSeparation.norm (HeapSeparation.norm d fs).depth (HeapSeparation.norm d fs).facts = HeapSeparation.norm d fs := by
  unfold HeapSeparation.norm
  by_cases h : (fs.filter fun a => !a.partners.isEmpty).isEmpty
  · simp [h]
  · simp [h, List.filter_filter]

/-- The compacted form compacts to itself. -/
theorem compactBy_idem (wf : WellFormed S) (hrr : ∀ ℓ, ℓ < S.depth → rn (rn ℓ) = rn ℓ) :
    compactBy rn (compactBy rn S) = compactBy rn S := by
  have hg : grouped rn (HeapSeparation.norm S.depth (grouped rn S)) =
      (HeapSeparation.norm S.depth (grouped rn S)).facts := by
    unfold HeapSeparation.norm
    dsimp only
    split
    · simp [grouped, firsts]
    · let fs := (grouped rn S).filter fun a => !a.partners.isEmpty
      have hsub : ∀ t ∈ fs, t ∈ grouped rn S := fun t ht => (List.mem_filter.mp ht).1
      have hren : fs.map (renameFact rn) = fs := by
        conv => rhs; rw [← List.map_id fs]
        exact List.map_congr_left fun t ht => renameFact_grouped wf hrr (hsub t ht)
      have hnd : (fs.map factKey).Nodup :=
        List.Nodup.sublist (List.Sublist.map factKey List.filter_sublist) grouped_keys_nodup
      show (firsts ((fs.map (renameFact rn)).map factKey)).map (fun key =>
          (⟨key.1, key.2, mergePartners (((fs.map (renameFact rn)).filter (factKey · = key)).flatMap (·.partners))⟩ : Fact)) = fs
      rw [hren, firsts_of_nodup hnd, List.map_map]
      conv => rhs; rw [← List.map_id fs]
      apply List.map_congr_left
      intro t ht
      have hone : fs.filter (factKey · = factKey t) = [t] := filter_key_one factKey hnd ht
      simp only [Function.comp, hone, List.flatMap_cons, List.flatMap_nil, List.append_nil, id]
      obtain ⟨key, -, rfl⟩ := List.mem_map.mp (hsub t ht)
      simp only [factKey, mergePartners_mergePartners]
  have e : compactBy rn S = HeapSeparation.norm S.depth (grouped rn S) := rfl
  rw [e, compactBy_eq, hg, norm_norm]

/-- The compacted form has at most the separation's facts, and each fact's
partner levels and each partner's fields are in order, each once. -/
theorem compactBy_size :
    (compactBy rn S).facts.length ≤ S.facts.length ∧
    ∀ t ∈ (compactBy rn S).facts, (t.partners.map (·.1)).Pairwise (· < ·) ∧
      ∀ q ∈ t.partners, q.2.Pairwise (· < ·) := by
  have hmem : ∀ t ∈ (compactBy rn S).facts, t ∈ grouped rn S := by
    intro t ht
    rw [compactBy_eq] at ht
    unfold HeapSeparation.norm at ht
    dsimp only at ht
    split at ht
    · simp at ht
    · exact (List.mem_filter.mp ht).1
  refine ⟨?_, fun t ht => ?_⟩
  · rw [compactBy_eq]
    unfold HeapSeparation.norm
    dsimp only
    split
    · simp
    · simp only [grouped]
      refine Nat.le_trans (List.length_filter_le _ _) ?_
      rw [List.length_map]
      have := length_firsts (((S.facts.map (renameFact rn)).map factKey))
      simpa using this
  · obtain ⟨key, -, rfl⟩ := List.mem_map.mp (hmem t ht)
    exact ⟨mergePartners_fst _ ▸ pairwise_canon _, fun q hq => mergePartners_snd hq⟩

theorem compactBy_empty (rn : Nat → Nat) : compactBy rn {} = {} := rfl

theorem compactBy_cases (rn : Nat → Nat) (S : Separation) :
    compactBy rn S = {} ∨ (compactBy rn S).depth = S.depth := by
  rw [compactBy_eq]
  unfold HeapSeparation.norm
  dsimp only
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end idem

/-! ### Through representatives -/

section reps
variable {r : Nat → Nat} {S : Separation} {ρ : Env}

theorem levelRep_lt {d ℓ : Nat} (h : ℓ < d) : levelRep r d ℓ < d := by
  simp only [levelRep, h, if_true]; omega

theorem levelRep_eq (hle : ∀ x, r x ≤ x) (hr : ∀ x, ρ (r x) = ρ x) {d ℓ : Nat} (h : ℓ < d) :
    ρ (d - 1 - levelRep r d ℓ) = ρ (d - 1 - ℓ) := by
  simp only [levelRep, h, if_true]
  have := hle (d - 1 - ℓ)
  rw [show d - 1 - (d - 1 - r (d - 1 - ℓ)) = r (d - 1 - ℓ) by omega]
  exact hr _

theorem levelRep_levelRep (hle : ∀ x, r x ≤ x) (hrr : ∀ x, r (r x) = r x) {d ℓ : Nat} (h : ℓ < d) :
    levelRep r d (levelRep r d ℓ) = levelRep r d ℓ := by
  have hl := levelRep_lt (r := r) h
  have := hle (d - 1 - ℓ)
  conv => lhs; rw [levelRep, if_pos hl]
  simp only [levelRep, h, if_true]
  rw [show d - 1 - (d - 1 - r (d - 1 - ℓ)) = r (d - 1 - ℓ) by omega, hrr]

/-- **The compacted separation holds exactly where the separation does**,
where each slot's representative holds its value. -/
theorem compact_holds (wf : WellFormed S) (hle : ∀ x, r x ≤ x) (hr : ∀ x, ρ (r x) = ρ x) :
    Holds (compact r S) ρ ↔ Holds S ρ := by
  rw [compact_eq]
  exact compactBy_holds wf fun ℓ h => ⟨levelRep_lt h, levelRep_eq hle hr h⟩

/-- **The compacted separation is its own compacted form.** -/
theorem compact_idem (wf : WellFormed S) (hle : ∀ x, r x ≤ x) (hrr : ∀ x, r (r x) = r x) :
    compact r (compact r S) = compact r S := by
  rw [compact_eq r S]
  rcases compactBy_cases (levelRep r S.depth) S with h | h
  · rw [h]; rfl
  · rw [compact_eq, h]
    exact compactBy_idem wf fun ℓ hl => levelRep_levelRep hle hrr hl

/-- The compacted separation has at most the separation's facts, each with
its partner levels and each partner's fields in order, each once. -/
theorem compact_size :
    (compact r S).facts.length ≤ S.facts.length ∧
    ∀ t ∈ (compact r S).facts, (t.partners.map (·.1)).Pairwise (· < ·) ∧
      ∀ q ∈ t.partners, q.2.Pairwise (· < ·) := by
  rw [compact_eq]; exact compactBy_size

end reps

end Verification.SeparationNormal
