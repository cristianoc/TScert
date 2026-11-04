import Verification.Semantics.HeapLinks
import Verification.Semantics.Partitions
import Verification.Semantics.ValueSets
import Std.Data.HashMap.Lemmas

/-! The alias classes of links (heap-knowledge draft, §3): the slots alias
links relate, closed under the law that two reads of one field from one
object give one value. Computed by merging classes until no rule applies,
and proved to relate exactly the slots the rules generate. -/
namespace Verification.LinkClasses
open ProgramTyping HeapFacts HeapLinks Partitions CanonicalLists

/-- The slots the rules relate: alias links, and the destinations of two
reads of one field from related receivers. -/
inductive Gen (ls : Links) : Nat → Nat → Prop where
  | refl (a : Nat) : Gen ls a a
  | symm {a b : Nat} : Gen ls a b → Gen ls b a
  | trans {a b c : Nat} : Gen ls a b → Gen ls b c → Gen ls a c
  | alias {g : Link} : g ∈ ls → g.alias = true → Gen ls g.cell g.value
  | read {g g' : Link} : g ∈ ls → g' ∈ ls → g.alias = false → g'.alias = false → g.field = g'.field →
      Gen ls g.cell g'.cell → Gen ls g.value g'.value

/-- What a read link states, as a `ReadGave`. -/
theorem readGave_of_link {g : Link} {ρ : Env} {h : Heap} (hg : g.alias = false)
    (hh : HeapLinks.Holds [g] ρ h) :
    ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value) := by
  have := hh g (List.mem_singleton_self g)
  simp only [hg, Bool.false_eq_true, ite_false] at this
  cases ho : g.optional
  · simp only [ho, Bool.false_eq_true, ite_false] at this
    obtain ⟨flds, c, oid, l, he, hl, hv⟩ := this
    exact ⟨flds, c, oid, he, ReadGave.present hl hv⟩
  · simpa [ho] using this

/-- The rules hold of every environment the links hold of. -/
theorem gen_sound {ls : Links} {ρ : Env} {h : Heap} (hh : HeapLinks.Holds ls ρ h) {a b : Nat}
    (hg : Gen ls a b) : ρ a = ρ b := by
  induction hg with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | alias hg ha => simpa [ha] using hh _ hg
  | @read g g' hg hg' ha ha' hf _ ih =>
    obtain ⟨flds, c, oid, he, hr⟩ := readGave_of_link ha fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hh g hg
    obtain ⟨flds', c', oid', he', hr'⟩ := readGave_of_link ha' fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hh g' hg'
    rw [ih, he'] at he
    cases he
    rw [hf] at hr
    exact ReadGave.unique hr hr'

/-- The slots the links name, once each. -/
def slots (ls : Links) : List Nat := canon (ls.flatMap fun g => [g.cell, g.value])

theorem mem_slots {ls : Links} {g : Link} (hg : g ∈ ls) : g.cell ∈ slots ls ∧ g.value ∈ slots ls := by
  simp only [slots, mem_canon, List.mem_flatMap]
  exact ⟨⟨g, hg, by simp⟩, ⟨g, hg, by simp⟩⟩

def init (ls : Links) : Partition := (slots ls).map ([·])

theorem init_ok (ls : Links) : Ok (slots ls) (init ls) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · simp only [init, List.mem_map]
    constructor
    · intro hx; exact ⟨[x], ⟨x, hx, rfl⟩, List.mem_singleton_self x⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩; rw [List.mem_singleton.mp hx]; exact ha
  · intro k hk k' hk' x hx hx'
    simp only [init, List.mem_map] at hk hk'
    obtain ⟨a, _, rfl⟩ := hk
    obtain ⟨b, _, rfl⟩ := hk'
    simp at hx hx'
    rw [← hx, ← hx']
  · intro k hk
    simp only [init, List.mem_map] at hk
    obtain ⟨a, _, rfl⟩ := hk
    simp

/-- One merge per rule instance. -/
def step (cs : Partition) (r : Link × Link) : Partition :=
  if r.1.alias then merge cs r.1.cell r.1.value
  else if !r.2.alias && r.1.field == r.2.field && same cs r.1.cell r.2.cell then merge cs r.1.value r.2.value
  else cs

/-- A read's key: its receiver's class and its field. Two reads of one key
give one value. -/
def key (cs : Partition) (g : Link) : List Nat × PropKey := (cls cs g.cell, g.field)

/-- The first read of each key, by hash. -/
def table (cs : Partition) (ls : Links) : Std.HashMap (List Nat × PropKey) Link :=
  (ls.filter (!·.alias)).foldl (fun m g => m.insertIfNew (key cs g) g) ∅

/-- The first read of a read's key: one link per key. -/
def anchor (cs : Partition) (t : Std.HashMap (List Nat × PropKey) Link) (g : Link) : Link :=
  (t[key cs g]?).getD g

/-- The rule instances a pass applies: each alias link with itself, and each
read with its key's first read. -/
def rules (ls : Links) (cs : Partition) : List (Link × Link) :=
  let t := table cs ls
  ls.map fun g => if g.alias then (g, g) else (anchor cs t g, g)

/-- One merge per alias link and per read, against the first read of its key:
linear in the links, where every pair of reads would be quadratic. -/
def pass (ls : Links) (cs : Partition) : Partition :=
  (rules ls cs).foldl step cs

def iter (ls : Links) : Nat → Partition → Partition
  | 0, cs => cs
  | n + 1, cs => let cs' := pass ls cs; if cs' = cs then cs else iter ls n cs'

/-- The alias classes: merge passes until none changes the partition. -/
def closure (ls : Links) : Partition := iter ls ((slots ls).length + 1) (init ls)

/-- The rule instances of the links. -/
abbrev pairs (ls : Links) : List (Link × Link) := ls.flatMap fun g => ls.map fun g' => (g, g')

theorem mem_pairs {ls : Links} {r : Link × Link} (hr : r ∈ pairs ls) : r.1 ∈ ls ∧ r.2 ∈ ls := by
  simp only [pairs, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨g, hg, g', hg', rfl⟩ := hr
  exact ⟨hg, hg'⟩

section steps
variable {ls : Links}

theorem table_fold {cs : Partition} : ∀ (l : Links) (m : Std.HashMap (List Nat × PropKey) Link),
    (∀ g ∈ l, g ∈ ls ∧ g.alias = false) →
    (∀ k a, m[k]? = some a → a ∈ ls ∧ a.alias = false ∧ key cs a = k) →
    (∀ k a, (l.foldl (fun m g => m.insertIfNew (key cs g) g) m)[k]? = some a →
      a ∈ ls ∧ a.alias = false ∧ key cs a = k) ∧
    (∀ g ∈ l, (l.foldl (fun m g => m.insertIfNew (key cs g) g) m).contains (key cs g) = true) ∧
    (∀ k, m.contains k = true → (l.foldl (fun m g => m.insertIfNew (key cs g) g) m).contains k = true)
  | [], m, _, hm => ⟨hm, by simp, fun _ h => h⟩
  | g :: l, m, hl, hm => by
    have hm' : ∀ k a, (m.insertIfNew (key cs g) g)[k]? = some a → a ∈ ls ∧ a.alias = false ∧ key cs a = k := by
      intro k a h
      rw [Std.HashMap.getElem?_insertIfNew] at h
      split at h
      · rename_i hc
        cases h
        exact ⟨(hl g (List.mem_cons_self ..)).1, (hl g (List.mem_cons_self ..)).2, eq_of_beq hc.1⟩
      · exact hm k a h
    obtain ⟨h₁, h₂, h₃⟩ := table_fold l _ (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) hm'
    refine ⟨h₁, fun g' hg' => ?_, fun k hk => h₃ k (by rw [Std.HashMap.contains_insertIfNew, hk]; simp)⟩
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact h₃ _ (by rw [Std.HashMap.contains_insertIfNew]; simp)
    · exact h₂ g' hg'

theorem table_props {cs : Partition} :
    (∀ k a, (table cs ls)[k]? = some a → a ∈ ls ∧ a.alias = false ∧ key cs a = k) ∧
    (∀ g ∈ ls, g.alias = false → (table cs ls).contains (key cs g) = true) := by
  obtain ⟨h₁, h₂, -⟩ := table_fold (cs := cs) (ls := ls) (ls.filter (!·.alias)) ∅
    (fun g hg => by
      obtain ⟨hg, ha⟩ := List.mem_filter.mp hg
      exact ⟨hg, by simpa using ha⟩)
    (fun k a h => by simp at h)
  exact ⟨h₁, fun g hg ha => h₂ g (List.mem_filter.mpr ⟨hg, by simp [ha]⟩)⟩

/-- A read's key's first read: a read of the links, of that key. -/
theorem anchor_spec {cs : Partition} {g : Link} (hg : g ∈ ls) (ha : g.alias = false) :
    anchor cs (table cs ls) g ∈ ls ∧ (anchor cs (table cs ls) g).alias = false ∧
      key cs (anchor cs (table cs ls) g) = key cs g := by
  unfold anchor
  have hc := (table_props (cs := cs) (ls := ls)).2 g hg ha
  cases hf : (table cs ls)[key cs g]? with
  | none =>
    have hs : ((table cs ls)[key cs g]?).isSome = true := by
      rw [Std.HashMap.isSome_getElem?_iff_mem]; exact Std.HashMap.contains_iff_mem.mp hc
    rw [hf] at hs
    cases hs
  | some e =>
    simpa using (table_props (cs := cs) (ls := ls)).1 _ _ hf

/-- Two reads of one key have one first read. -/
theorem anchor_key {cs : Partition} {g g' : Link} (h : key cs g = key cs g') :
    anchor cs (table cs ls) g = anchor cs (table cs ls) g' ∨
      ((table cs ls)[key cs g]?).isNone := by
  unfold anchor
  rw [h]
  cases (table cs ls)[key cs g']? <;> simp

theorem rules_pairs {cs : Partition} {r : Link × Link} (hr : r ∈ rules ls cs) : r ∈ pairs ls := by
  simp only [rules, List.mem_map] at hr
  obtain ⟨g, hg, rfl⟩ := hr
  apply List.mem_flatMap.mpr
  split
  · exact ⟨g, hg, List.mem_map.mpr ⟨g, hg, rfl⟩⟩
  · rename_i ha
    exact ⟨_, (anchor_spec hg (by simpa using ha)).1, List.mem_map.mpr ⟨g, hg, rfl⟩⟩

theorem step_ok {cs : Partition} (h : Ok (slots ls) cs) {r : Link × Link} (hr : r ∈ pairs ls) :
    Ok (slots ls) (step cs r) := by
  obtain ⟨h₁, h₂⟩ := mem_pairs hr
  unfold step
  split
  · exact merge_ok h (mem_slots h₁).1 (mem_slots h₁).2
  · split
    · exact merge_ok h (mem_slots h₁).2 (mem_slots h₂).2
    · exact h

theorem step_shrink {cs : Partition} (h : Ok (slots ls) cs) {r : Link × Link} (hr : r ∈ pairs ls) :
    step cs r = cs ∨ (step cs r).length < cs.length := by
  obtain ⟨h₁, h₂⟩ := mem_pairs hr
  have m : ∀ {a b}, a ∈ slots ls → b ∈ slots ls → merge cs a b = cs ∨ (merge cs a b).length < cs.length :=
    fun {a b} ha hb => by
      cases hs : same cs a b
      · exact Or.inr (merge_length h ha hb hs)
      · exact Or.inl (by simp [merge, hs])
  unfold step
  split
  · exact m (mem_slots h₁).1 (mem_slots h₁).2
  · split
    · exact m (mem_slots h₁).2 (mem_slots h₂).2
    · exact Or.inl rfl

/-- A step relates only slots the rules relate. -/
theorem step_gen {cs : Partition} (h : Ok (slots ls) cs) (hg : ∀ x y, same cs x y = true → Gen ls x y)
    {r : Link × Link} (hr : r ∈ pairs ls) : ∀ x y, same (step cs r) x y = true → Gen ls x y := by
  obtain ⟨h₁, h₂⟩ := mem_pairs hr
  have m : ∀ {a b}, a ∈ slots ls → b ∈ slots ls → Gen ls a b →
      ∀ x y, same (merge cs a b) x y = true → Gen ls x y := fun {a b} ha hb hab x y e => by
    rcases (same_merge h ha hb x y).mp e with e | ⟨hx, hy⟩
    · exact hg x y e
    · have gx : Gen ls x a := hx.elim (hg x a) fun e => .trans (hg x b e) (.symm hab)
      have gy : Gen ls y a := hy.elim (hg y a) fun e => .trans (hg y b e) (.symm hab)
      exact .trans gx (.symm gy)
  unfold step
  split
  · rename_i ha; exact m (mem_slots h₁).1 (mem_slots h₁).2 (.alias h₁ ha)
  · rename_i ha
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      simp only [Bool.not_eq_true] at ha
      exact m (mem_slots h₁).2 (mem_slots h₂).2 (.read h₁ h₂ ha hc.1.1 hc.1.2 (hg _ _ hc.2))
    · exact hg

/-- A fold of steps, each the identity or shrinking the partition, keeps a
partition, relates only what the rules relate, and is the identity only where
every step is. -/
theorem fold_props {rs : List (Link × Link)} (hrs : ∀ r ∈ rs, r ∈ pairs ls) {cs : Partition}
    (h : Ok (slots ls) cs) (hg : ∀ x y, same cs x y = true → Gen ls x y) :
    Ok (slots ls) (rs.foldl step cs) ∧ (∀ x y, same (rs.foldl step cs) x y = true → Gen ls x y) ∧
    (rs.foldl step cs = cs ∨ (rs.foldl step cs).length < cs.length) ∧
    (rs.foldl step cs = cs → ∀ r ∈ rs, step cs r = cs) := by
  induction rs generalizing cs with
  | nil => simp_all
  | cons r rs ih =>
    have hr := hrs r (List.mem_cons_self ..)
    have hok := step_ok h hr
    obtain ⟨o, g, sh, fix⟩ := ih (fun r' h' => hrs r' (List.mem_cons_of_mem _ h')) hok (step_gen h hg hr)
    simp only [List.foldl_cons]
    have hlen : (rs.foldl step (step cs r)).length ≤ (step cs r).length := by
      rcases sh with e | e
      · rw [e]; exact Nat.le_refl _
      · omega
    refine ⟨o, g, ?_, ?_⟩
    · rcases step_shrink h hr with e | e
      · rw [e] at sh ⊢; exact sh
      · exact Or.inr (by omega)
    · intro e r' hr'
      -- An identity overall is an identity at every step: lengths only shrink.
      have hstep : step cs r = cs := by
        rcases step_shrink h hr with e' | e'
        · exact e'
        · rw [e] at hlen; omega
      rw [hstep] at e fix
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact hstep
      · exact fix e r' hr'

end steps

section closure
variable {ls : Links}

/-- At a fixpoint of the pass, every rule holds of the partition. -/
theorem closed {cs : Partition} (h : Ok (slots ls) cs) (hg : ∀ x y, same cs x y = true → Gen ls x y)
    (hfix : pass ls cs = cs) :
    (∀ g ∈ ls, g.alias = true → same cs g.cell g.value = true) ∧
    (∀ g ∈ ls, ∀ g' ∈ ls, g.alias = false → g'.alias = false → g.field = g'.field →
      same cs g.cell g'.cell = true → same cs g.value g'.value = true) := by
  have hall := (fold_props (rs := rules ls cs) (fun _ h => rules_pairs h) h hg).2.2.2 hfix
  -- A merge that is the identity merged one class.
  have stays : ∀ {a b}, a ∈ slots ls → b ∈ slots ls → merge cs a b = cs → same cs a b = true :=
    fun {a b} ha hb e => by
      cases hs : same cs a b
      · have := merge_length h ha hb hs; rw [e] at this; omega
      · rfl
  -- A read and its key's first read hold one value.
  have toAnchor : ∀ g ∈ ls, g.alias = false →
      same cs (anchor cs (table cs ls) g).value g.value = true := by
    intro g hg ha
    obtain ⟨hm, haa, hk⟩ := anchor_spec (cs := cs) hg ha
    have hr : (anchor cs (table cs ls) g, g) ∈ rules ls cs := by
      simp only [rules, List.mem_map]
      exact ⟨g, hg, by simp [ha]⟩
    have := hall _ hr
    simp only [key, Prod.mk.injEq] at hk
    have hsame : same cs (anchor cs (table cs ls) g).cell g.cell = true := (same_iff h).mpr hk.1
    simp only [step, haa, ha, hk.2, hsame, Bool.false_eq_true, if_false, Bool.not_false, beq_self_eq_true,
      Bool.and_self, if_true] at this
    exact stays (mem_slots hm).2 (mem_slots hg).2 this
  constructor
  · intro g hg ha
    have hr : (g, g) ∈ rules ls cs := by
      simp only [rules, List.mem_map]
      exact ⟨g, hg, by simp [ha]⟩
    have := hall _ hr
    simp only [step, ha, if_true] at this
    exact stays (mem_slots hg).1 (mem_slots hg).2 this
  · intro g hg g' hg' ha ha' hf hs
    have hk : key cs g = key cs g' := by simp only [key, (same_iff h).mp hs, hf]
    have he : anchor cs (table cs ls) g = anchor cs (table cs ls) g' := by
      rcases anchor_key (ls := ls) hk with e | e
      · exact e
      · exfalso
        have hc := (table_props (cs := cs) (ls := ls)).2 g hg ha
        have hs : ((table cs ls)[key cs g]?).isSome = true := by
          rw [Std.HashMap.isSome_getElem?_iff_mem]; exact Std.HashMap.contains_iff_mem.mp hc
        rw [Option.isNone_iff_eq_none] at e
        rw [e] at hs
        cases hs
    have e₁ := toAnchor g hg ha
    have e₂ := toAnchor g' hg' ha'
    rw [he] at e₁
    exact same_trans h (same_symm h e₁) e₂

theorem iter_props : ∀ (n : Nat) {cs : Partition}, Ok (slots ls) cs → (∀ x y, same cs x y = true → Gen ls x y) →
    cs.length < n →
    Ok (slots ls) (iter ls n cs) ∧ (∀ x y, same (iter ls n cs) x y = true → Gen ls x y) ∧
      pass ls (iter ls n cs) = iter ls n cs
  | 0, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, cs, h, hg, hn => by
    simp only [iter]
    split
    · rename_i e; exact ⟨h, hg, e⟩
    · rename_i e
      obtain ⟨o, g, sh, _⟩ := fold_props (rs := rules ls cs) (fun _ h => rules_pairs h) h hg
      have : (pass ls cs).length < cs.length := sh.resolve_left e
      exact iter_props n o g (by omega)

theorem closure_props : Ok (slots ls) (closure ls) ∧ (∀ x y, same (closure ls) x y = true → Gen ls x y) ∧
    pass ls (closure ls) = closure ls := by
  apply iter_props _ (init_ok ls) _ (by simp [init])
  intro x y e
  -- Initially every class is one slot.
  have ok := init_ok ls
  by_cases hx : x ∈ slots ls
  · have : cls (init ls) x = [x] := cls_of_mem ok (List.mem_map.mpr ⟨x, hx, rfl⟩) (List.mem_singleton_self x)
    simp only [same, this, List.contains_iff_mem, List.mem_singleton] at e
    subst e; exact .refl _
  · simp only [same, cls_not_mem ok hx, List.contains_iff_mem, List.mem_singleton] at e
    subst e; exact .refl _

/-- **The closure relates exactly the slots the rules relate.** -/
theorem same_closure_iff {x y : Nat} : same (closure ls) x y = true ↔ Gen ls x y := by
  obtain ⟨ok, sound, fix⟩ := closure_props (ls := ls)
  obtain ⟨cl₁, cl₂⟩ := closed ok sound fix
  refine ⟨sound x y, fun hg => ?_⟩
  induction hg with
  | refl a => exact same_refl _ a
  | symm _ ih => exact same_symm ok ih
  | trans _ _ ih₁ ih₂ => exact same_trans ok ih₁ ih₂
  | alias hg ha => exact cl₁ _ hg ha
  | read hg hg' ha ha' hf _ ih => exact cl₂ _ hg _ hg' ha ha' hf ih

end closure

/-! ## The normal form -/

/-- The least of `d` and a list. -/
def least (d : Nat) (l : List Nat) : Nat := l.foldl min d

theorem least_le {d : Nat} {l : List Nat} : least d l ≤ d ∧ ∀ z ∈ l, least d l ≤ z := by
  induction l generalizing d with
  | nil => simp [least]
  | cons a l ih =>
    simp only [least, List.foldl_cons] at ih ⊢
    obtain ⟨h₁, h₂⟩ := ih (d := min d a)
    refine ⟨by omega, fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · exact h₂ z hz

theorem least_mem {d : Nat} {l : List Nat} : least d l = d ∨ least d l ∈ l := by
  induction l generalizing d with
  | nil => simp [least]
  | cons a l ih =>
    simp only [least, List.foldl_cons] at ih ⊢
    rcases ih (d := min d a) with e | e
    · rw [e]; by_cases h : d ≤ a
      · left; omega
      · right; simp; omega
    · right; exact List.mem_cons_of_mem _ e

/-- The least of two lists with the same members, each holding its start, is one. -/
theorem least_congr {d d' : Nat} {l l' : List Nat} (hd : d ∈ l) (hd' : d' ∈ l') (h : ∀ z, z ∈ l ↔ z ∈ l') :
    least d l = least d' l' := by
  have m₁ : least d l ∈ l := (least_mem (l := l)).elim (fun e => e ▸ hd) id
  have m₂ : least d' l' ∈ l' := (least_mem (l := l')).elim (fun e => e ▸ hd') id
  have a := (least_le (d := d) (l := l)).2 _ ((h _).mpr m₂)
  have b := (least_le (d := d') (l := l')).2 _ ((h _).mp m₁)
  omega

variable (ls : Links)

/-- A slot's representative: the least slot of its class. -/
def rep (x : Nat) : Nat := least x (cls (closure ls) x)

theorem rep_gen (x : Nat) : Gen ls x (rep ls x) := by
  apply same_closure_iff.mp
  simp only [same, List.contains_iff_mem, rep]
  exact (least_mem (l := cls (closure ls) x)).elim (fun e => e ▸ mem_cls_self x) id

theorem rep_eq_of_gen {x y : Nat} (h : Gen ls x y) : rep ls x = rep ls y := by
  have ok := (closure_props (ls := ls)).1
  have e := (same_iff ok).mp (same_closure_iff.mpr h)
  simp only [rep, e]
  exact least_congr (e ▸ mem_cls_self x) (mem_cls_self y) (fun _ => Iff.rfl)

/-- Whether every read of `g`'s field from `g`'s class may find no field. -/
def mayMiss (g : Link) : Bool :=
  ls.all fun g' => g'.alias || g'.field != g.field || !same (closure ls) g'.cell g.cell || g'.optional

/-- Each non-representative slot linked to its representative, and each read
between representatives, with whether it may find no field. -/
def links : Links :=
  (slots ls).filterMap (fun x => if rep ls x = x then none else some ⟨rep ls x, x, true, valueField, false⟩) ++
  ls.filterMap fun g => if g.alias then none else some ⟨rep ls g.cell, rep ls g.value, false, g.field, mayMiss ls g⟩

variable {ls}

theorem mayMiss_required {g : Link} (hg : g ∈ ls) (ha : g.alias = false) (ho : g.optional = false) :
    mayMiss ls g = false := by
  apply Bool.eq_false_iff.mpr
  intro hm
  have := List.all_eq_true.mp hm g hg
  simp [ha, same_refl, ho] at this

theorem mayMiss_witness {g : Link} (hm : mayMiss ls g = false) :
    ∃ g' ∈ ls, g'.alias = false ∧ g'.field = g.field ∧ Gen ls g'.cell g.cell ∧ g'.optional = false := by
  simp only [mayMiss, List.all_eq_false] at hm
  obtain ⟨g', hg', hn⟩ := hm
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, Bool.not_eq_true,
    Decidable.not_not] at hn
  exact ⟨g', hg', hn.1.1.1, hn.1.1.2, same_closure_iff.mp (by simpa using hn.1.2), hn.2⟩

/-- A required read gives what an optional one states. -/
theorem holds_optional {g : Link} {ρ : Env} {h : Heap} (ha : g.alias = false)
    (hh : HeapLinks.Holds [g] ρ h) : HeapLinks.Holds [{ g with optional := true }] ρ h := by
  intro x hx
  rw [List.mem_singleton.mp hx]
  obtain ⟨flds, c, oid, he, hr⟩ := readGave_of_link ha hh
  simp only [ha, Bool.false_eq_true, ite_false, ite_true]
  exact ⟨flds, c, oid, he, hr⟩

theorem links_holds {ρ : Env} {h : Heap} (hh : HeapLinks.Holds ls ρ h) : HeapLinks.Holds (links ls) ρ h := by
  have hrep : ∀ x, ρ (rep ls x) = ρ x := fun x => (gen_sound hh (rep_gen ls x)).symm
  intro L hL
  simp only [links, List.mem_append, List.mem_filterMap] at hL
  rcases hL with ⟨x, _, hx⟩ | ⟨g, hg, hx⟩
  · split at hx
    · cases hx
    · cases hx; simp [hrep]
  · split at hx
    · cases hx
    · rename_i ha
      cases hx
      simp only [Bool.not_eq_true] at ha
      simp only [Bool.false_eq_true, ite_false, hrep]
      cases hm : mayMiss ls g
      · obtain ⟨g', hg', ha', hf, hc, ho⟩ := mayMiss_witness hm
        have h' := hh g' hg'
        simp only [ha', ho, Bool.false_eq_true, ite_false] at h' ⊢
        rw [← gen_sound hh hc, ← gen_sound hh (.read hg' hg ha' ha hf hc), ← hf]
        exact h'
      · obtain ⟨flds, c, oid, he, hr⟩ := readGave_of_link ha fun x hx => by
          rw [List.mem_singleton.mp hx]; exact hh g hg
        simp only [ite_true]
        exact ⟨flds, c, oid, he, hr⟩

theorem holds_links {ρ : Env} {h : Heap} (hh : HeapLinks.Holds (links ls) ρ h) : HeapLinks.Holds ls ρ h := by
  have hrep : ∀ x, ρ (rep ls x) = ρ x := by
    intro x
    by_cases e : rep ls x = x
    · rw [e]
    · have hx : x ∈ slots ls := Classical.byContradiction fun hx => by
        have := cls_not_mem (closure_props (ls := ls)).1 hx
        simp [rep, this, least] at e
      have := hh ⟨rep ls x, x, true, valueField, false⟩ (by
        simp only [links, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨x, hx, by simp [e]⟩)
      simpa using this
  intro g hg
  cases ha : g.alias
  · have hL := hh ⟨rep ls g.cell, rep ls g.value, false, g.field, mayMiss ls g⟩ (by
      simp only [links, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨g, hg, by simp [ha]⟩)
    simp only [Bool.false_eq_true, ite_false, hrep] at hL ⊢
    cases ho : g.optional
    · rw [mayMiss_required hg ha ho] at hL
      simpa using hL
    · simp only [ite_true]
      cases hm : mayMiss ls g
      · simp only [hm, Bool.false_eq_true, ite_false] at hL
        obtain ⟨flds, c, oid, l, he, hl, hv⟩ := hL
        exact ⟨flds, c, oid, he, ReadGave.present hl hv⟩
      · simpa [hm] using hL
  · have e := rep_eq_of_gen ls (.alias hg ha)
    simp only [ite_true]
    rw [← hrep g.cell, ← hrep g.value, e]

/-! ## Canonical order, and the four obligations -/

def linkKey (g : Link) : List Nat :=
  g.cell :: g.value :: (if g.alias then 1 else 0) :: (if g.optional then 1 else 0) :: ValueSets.propKey g.field

instance : LT Link := ⟨fun a b => linkKey a < linkKey b⟩
instance : DecidableLT Link := fun a b => inferInstanceAs (Decidable (linkKey a < linkKey b))

theorem linkKey_inj {a b : Link} (h : linkKey a = linkKey b) : a = b := by
  obtain ⟨c, v, al, f, o⟩ := a
  obtain ⟨c', v', al', f', o'⟩ := b
  simp only [linkKey, List.cons.injEq] at h
  obtain ⟨rfl, rfl, ha, ho, hf⟩ := h
  rw [ValueSets.propKey_inj hf]
  congr
  · cases al <;> cases al' <;> simp_all
  · cases o <;> cases o' <;> simp_all

instance : StrictTotal Link where
  irrefl a := StrictTotal.irrefl (linkKey a)
  trans h₁ h₂ := StrictTotal.trans (α := List Nat) h₁ h₂
  total h := StrictTotal.total (α := List Nat) fun e => h (linkKey_inj e)

/-- The normal form of links. -/
def norm (ls : Links) : Links := canon (links ls)

theorem norm_holds {ρ : Env} {h : Heap} : HeapLinks.Holds (norm ls) ρ h ↔ HeapLinks.Holds ls ρ h := by
  constructor
  · intro hh; exact holds_links fun g hg => hh g (mem_canon.mpr hg)
  · intro hh g hg; exact links_holds hh g (mem_canon.mp hg)

/-- The rules depend on the links' members alone. -/
theorem gen_congr {l₁ l₂ : Links} (h : ∀ g, g ∈ l₁ ↔ g ∈ l₂) {x y : Nat} (hg : Gen l₁ x y) : Gen l₂ x y := by
  induction hg with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | alias hg ha => exact .alias ((h _).mp hg) ha
  | read hg hg' ha ha' hf _ ih => exact .read ((h _).mp hg) ((h _).mp hg') ha ha' hf ih

theorem rep_rep (x : Nat) : rep ls (rep ls x) = rep ls x := (rep_eq_of_gen ls (rep_gen ls x)).symm

theorem rep_mem_slots {x : Nat} (hx : rep ls x ≠ x) : x ∈ slots ls := Classical.byContradiction fun hn => by
  have := cls_not_mem (closure_props (ls := ls)).1 hn
  simp [rep, this, least] at hx

/-- A slot's class, as the slots the rules relate it to. -/
theorem mem_cls_closure {x z : Nat} : z ∈ cls (closure ls) x ↔ Gen ls x z := by
  rw [← same_closure_iff]; simp [same]

/-- Links with the same rule relation have the same representatives. -/
theorem rep_congr {l₁ l₂ : Links} (h : ∀ x y, Gen l₁ x y ↔ Gen l₂ x y) (x : Nat) : rep l₁ x = rep l₂ x :=
  least_congr (mem_cls_self x) (mem_cls_self x) fun z => by rw [mem_cls_closure, mem_cls_closure, h]

theorem gen_links_iff {x y : Nat} : Gen (links ls) x y ↔ Gen ls x y := by
  have toRep : ∀ z, Gen (links ls) z (rep ls z) := fun z => by
    by_cases e : rep ls z = z
    · rw [e]; exact .refl _
    · exact .symm (.alias (g := ⟨rep ls z, z, true, valueField, false⟩) (by
        simp only [links, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨z, rep_mem_slots e, by simp [e]⟩) rfl)
  constructor
  · intro hg
    induction hg with
    | refl => exact .refl _
    | symm _ ih => exact .symm ih
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | @alias g hg ha =>
      simp only [links, List.mem_append, List.mem_filterMap] at hg
      rcases hg with ⟨z, _, hz⟩ | ⟨r, _, hr⟩
      · split at hz
        · cases hz
        · cases hz; exact .symm (rep_gen ls z)
      · split at hr
        · cases hr
        · cases hr; simp at ha
    | @read g g' hg hg' ha ha' hf _ ih =>
      simp only [links, List.mem_append, List.mem_filterMap] at hg hg'
      rcases hg with ⟨z, _, hz⟩ | ⟨r, hr, e⟩
      · split at hz <;> cases hz; simp at ha
      rcases hg' with ⟨z, _, hz⟩ | ⟨r', hr', e'⟩
      · split at hz <;> cases hz; simp at ha'
      have hra : r.alias = false := by cases h : r.alias <;> simp_all
      have hra' : r'.alias = false := by cases h : r'.alias <;> simp_all
      simp only [hra, hra', Bool.false_eq_true, ite_false, Option.some.injEq] at e e'
      subst e e'
      have hc : Gen ls r.cell r'.cell := .trans (rep_gen ls _) (.trans ih (.symm (rep_gen ls _)))
      exact .trans (.symm (rep_gen ls _)) (.trans (.read hr hr' hra hra' hf hc) (rep_gen ls _))
  · intro hg
    induction hg with
    | refl => exact .refl _
    | symm _ ih => exact .symm ih
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | @alias g hg ha =>
      have e := rep_eq_of_gen ls (.alias hg ha)
      exact .trans (toRep _) (e ▸ .symm (toRep _))
    | @read g g' hg hg' ha ha' hf _ ih =>
      have mem : ∀ r ∈ ls, r.alias = false →
          (⟨rep ls r.cell, rep ls r.value, false, r.field, mayMiss ls r⟩ : Link) ∈ links ls := fun r hr hra => by
        simp only [links, List.mem_append, List.mem_filterMap]
        exact Or.inr ⟨r, hr, by simp [hra]⟩
      have hc : Gen (links ls) (rep ls g.cell) (rep ls g'.cell) := .trans (.symm (toRep _)) (.trans ih (toRep _))
      have := Gen.read (mem g hg ha) (mem g' hg' ha') rfl rfl hf hc
      exact .trans (toRep _) (.trans this (.symm (toRep _)))

theorem gen_norm_iff {x y : Nat} : Gen (norm ls) x y ↔ Gen ls x y :=
  ⟨fun h => gen_links_iff.mp (gen_congr (fun _ => mem_canon) h),
   fun h => gen_congr (fun _ => mem_canon.symm) (gen_links_iff.mpr h)⟩

theorem mem_links {L : Link} : L ∈ links ls ↔
    (∃ x, rep ls x ≠ x ∧ L = ⟨rep ls x, x, true, valueField, false⟩) ∨
    (∃ g ∈ ls, g.alias = false ∧ L = ⟨rep ls g.cell, rep ls g.value, false, g.field, mayMiss ls g⟩) := by
  simp only [links, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨x, _, hx⟩ | ⟨g, hg, hx⟩)
    · split at hx
      · cases hx
      · rename_i e; cases hx; exact Or.inl ⟨x, e, rfl⟩
    · split at hx
      · cases hx
      · rename_i e; cases hx; exact Or.inr ⟨g, hg, by simpa using e, rfl⟩
  · rintro (⟨x, e, rfl⟩ | ⟨g, hg, ha, rfl⟩)
    · exact Or.inl ⟨x, rep_mem_slots e, by simp [e]⟩
    · exact Or.inr ⟨g, hg, by simp [ha]⟩

/-- **Unique**: links generating one relation, with the same reads between
representatives, have one normal form. -/
theorem norm_congr {l₁ l₂ : Links} (hG : ∀ x y, Gen l₁ x y ↔ Gen l₂ x y)
    (hR : ∀ L : Link, (∃ g ∈ l₁, g.alias = false ∧ L = ⟨rep l₁ g.cell, rep l₁ g.value, false, g.field, mayMiss l₁ g⟩) ↔
      (∃ g ∈ l₂, g.alias = false ∧ L = ⟨rep l₂ g.cell, rep l₂ g.value, false, g.field, mayMiss l₂ g⟩)) :
    norm l₁ = norm l₂ := by
  apply canon_eq
  intro L
  rw [mem_links, mem_links, hR L]
  simp only [rep_congr hG]

theorem mayMiss_key {g g' : Link} (hf : g.field = g'.field) (hc : Gen ls g.cell g'.cell) :
    mayMiss ls g = mayMiss ls g' := by
  have ok := (closure_props (ls := ls)).1
  have hs := same_closure_iff.mpr hc
  have : ∀ x, same (closure ls) x g.cell = same (closure ls) x g'.cell := fun x => by
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun e => same_trans ok e hs, fun e => same_trans ok e (same_symm ok hs)⟩
  simp only [mayMiss, hf, this]

/-- In the normal form, the reads of a key all carry the key's answer. -/
theorem mayMiss_norm {r : Link} (hr : r ∈ ls) (hra : r.alias = false) :
    mayMiss (norm ls) ⟨rep ls r.cell, rep ls r.value, false, r.field, mayMiss ls r⟩ = mayMiss ls r := by
  have hsame : ∀ x y, same (closure (norm ls)) x y = same (closure ls) x y := fun x y =>
    Bool.eq_iff_iff.mpr (by rw [same_closure_iff, same_closure_iff, gen_norm_iff])
  have hmem : (⟨rep ls r.cell, rep ls r.value, false, r.field, mayMiss ls r⟩ : Link) ∈ norm ls :=
    mem_canon.mpr (mem_links.mpr (Or.inr ⟨r, hr, hra, rfl⟩))
  cases hm : mayMiss ls r
  · apply Bool.eq_false_iff.mpr
    intro hall
    have := List.all_eq_true.mp hall _ hmem
    simp [hsame, same_refl, hm] at this
  · apply List.all_eq_true.mpr
    intro g' hg'
    rcases mem_links.mp (mem_canon.mp hg') with ⟨x, _, rfl⟩ | ⟨r', hr', hra', rfl⟩
    · rfl
    · simp only [hsame, Bool.false_or, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
      by_cases hf : r'.field = r.field
      · by_cases hs : same (closure ls) (rep ls r'.cell) (rep ls r.cell) = true
        · right
          have hc : Gen ls r'.cell r.cell :=
            .trans (rep_gen ls _) (.trans (same_closure_iff.mp hs) (.symm (rep_gen ls _)))
          rw [mayMiss_key hf hc, hm]
        · left; right; simpa using hs
      · left; left; exact hf

/-- **Stored**: the normal form is its own normal form. -/
theorem norm_idem : norm (norm ls) = norm ls := by
  have hG : ∀ x y, Gen (norm ls) x y ↔ Gen ls x y := fun _ _ => gen_norm_iff
  have hrep := rep_congr hG
  show canon (links (norm ls)) = canon (links ls)
  apply canon_eq
  intro L
  rw [mem_links, mem_links]
  simp only [hrep]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨g, hg, ha, rfl⟩
    rcases mem_links.mp (mem_canon.mp hg) with ⟨x, _, rfl⟩ | ⟨r, hr, hra, rfl⟩
    · simp at ha
    · refine ⟨r, hr, hra, ?_⟩
      simp only [rep_rep, mayMiss_norm hr hra]
  · rintro ⟨r, hr, hra, rfl⟩
    have hg : (⟨rep ls r.cell, rep ls r.value, false, r.field, mayMiss ls r⟩ : Link) ∈ norm ls :=
      mem_canon.mpr (mem_links.mpr (Or.inr ⟨r, hr, hra, rfl⟩))
    refine ⟨_, hg, rfl, ?_⟩
    simp only [rep_rep, mayMiss_norm hr hra]

/-! ## Computing with one closure

The definitions above recompute the closure at every representative; these
take it once, and are the same functions. -/

/-- `rep` at a computed partition. -/
def repIn (cs : Partition) (x : Nat) : Nat := least x (cls cs x)

def mayMissIn (ls : Links) (cs : Partition) (g : Link) : Bool :=
  ls.all fun g' => g'.alias || g'.field != g.field || !same cs g'.cell g.cell || g'.optional

def linksIn (ls : Links) (cs : Partition) : Links :=
  (slots ls).filterMap (fun x => if repIn cs x = x then none else some ⟨repIn cs x, x, true, valueField, false⟩) ++
  ls.filterMap fun g => if g.alias then none else some ⟨repIn cs g.cell, repIn cs g.value, false, g.field, mayMissIn ls cs g⟩

end Verification.LinkClasses
