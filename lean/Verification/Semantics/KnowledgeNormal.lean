import Verification.Semantics.HeapKnowledge
import Verification.Semantics.LinkClasses
import Verification.Semantics.SeparationNormal

/-! The normal form of heap facts (heap-knowledge draft, §4): one value fact
per alias class, the meet of every value fact on its slots and of every cell
fact a read link makes its value, at the class's context and absent where it
states no more than the context; one cell fact per class and field no read
link answers; the links in their normal form (`LinkClasses.norm`). -/
namespace Verification.KnowledgeNormal
open ProgramTyping HeapFacts HeapKnowledge ValueSets CanonicalLists

/-- A slot's context: the values its type admits, where a value set states
them. -/
abbrev Ctx := Nat → Option ValueSet

def CtxOk (ctx : Ctx) (ρ : Env) : Prop := ∀ i C, ctx i = some C → C.mem (ρ i) = true

/-- Without a context, the normal form holds of exactly the values the set
does. -/
theorem normIn_top_mem (V : ValueSet) (v : Tm) : (ValueSet.top.normIn V).mem v = V.mem v := by
  cases hv : isVal v
  · have h₁ : (ValueSet.top.normIn V).mem v = false := by
      cases e : (ValueSet.top.normIn V).mem v
      · rfl
      · rw [ValueSet.mem_isVal e] at hv; cases hv
    have h₂ : V.mem v = false := by
      cases e : V.mem v
      · rfl
      · rw [ValueSet.mem_isVal e] at hv; cases hv
    rw [h₁, h₂]
  · exact ValueSet.normIn_mem (ValueSet.mem_top hv)

/-- A meet, the first set itself where the two are one: a repeated fact
costs a comparison. -/
def meetStep (V W : ValueSet) : ValueSet := if V = W then V else V.meet W

theorem mem_meetStep (V W : ValueSet) (v : Tm) : (meetStep V W).mem v = (V.mem v && W.mem v) := by
  unfold meetStep
  split
  · rename_i e; subst e; simp
  · exact ValueSet.mem_meet V W v

/-- The meet of a list of value sets, from `init`. -/
def meetAll (init : ValueSet) (l : List ValueSet) : ValueSet := l.foldl meetStep init

theorem mem_meetAll {init : ValueSet} {l : List ValueSet} {v : Tm} :
    (meetAll init l).mem v = true ↔ init.mem v = true ∧ ∀ x ∈ l, x.mem v = true := by
  induction l generalizing init with
  | nil => simp [meetAll]
  | cons a l ih =>
    simp only [meetAll, List.foldl_cons] at ih ⊢
    rw [ih, mem_meetStep]
    simp only [Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- A class and a field, the key of a cell fact. -/
structure CellKey where
  slot : Nat
  field : PropKey
  deriving DecidableEq

def CellKey.key (c : CellKey) : List Nat := c.slot :: ValueSets.propKey c.field

instance : LT CellKey := ⟨fun a b => a.key < b.key⟩
instance : DecidableLT CellKey := fun a b => inferInstanceAs (Decidable (a.key < b.key))

instance : StrictTotal CellKey where
  irrefl a := StrictTotal.irrefl a.key
  trans h₁ h₂ := StrictTotal.trans (α := List Nat) h₁ h₂
  total {a b} h := StrictTotal.total (α := List Nat) fun e => h (by
    cases a; cases b
    simp only [CellKey.key, List.cons.injEq] at e
    rw [e.1, ValueSets.propKey_inj e.2])

section
variable (ctx : Ctx) (k : Knowledge)

def rep (x : Nat) : Nat := LinkClasses.rep k.links x

/-- The class a read link from class `r` through `f` gives its value to. -/
def readDest (r : Nat) (f : PropKey) : Option Nat :=
  ((LinkClasses.norm k.links).find? fun g => !g.alias && g.cell == r && g.field == f).map (·.value)

/-- What is known of class `r`'s value: its slots' value facts, and the cell
facts whose read links give it. -/
def valueParts (r : Nat) : List ValueSet :=
  (k.values.filter fun f => rep k f.slot == r).map (·.contents) ++
  (k.cells.filter fun f => readDest k (rep k f.slot) f.field == some r).map (·.contents)

/-- The context of class `r`: the meet of its slots' contexts, where any has one. -/
def classCtx (r : Nat) : Option ValueSet :=
  match (canon (Partitions.cls (LinkClasses.closure k.links) r)).filterMap ctx with
  | [] => none
  | C :: Cs => some (meetAll C Cs)

def classes : List Nat :=
  canon ((k.values.map fun f => rep k f.slot) ++ k.cells.filterMap fun f => readDest k (rep k f.slot) f.field)

def valueFact (r : Nat) : Option Fact :=
  let C := (classCtx ctx k r).getD ValueSet.top
  let V := C.normIn (meetAll ValueSet.top (valueParts k r))
  if (classCtx ctx k r).isSome && V == C.normIn ValueSet.top then none else some ⟨r, V, valueField⟩

def cellKeys : List CellKey :=
  canon (k.cells.filterMap fun f =>
    if readDest k (rep k f.slot) f.field = none then some ⟨rep k f.slot, f.field⟩ else none)

def cellParts (c : CellKey) : List ValueSet :=
  (k.cells.filter fun f => rep k f.slot == c.slot && f.field == c.field).map (·.contents)

/-- The normal form of the facts, links and separation. -/
def norm : Knowledge :=
  ⟨(cellKeys k).map (fun c => ⟨c.slot, ValueSet.top.normIn (meetAll ValueSet.top (cellParts k c)), c.field⟩),
   (classes k).filterMap (valueFact ctx k), LinkClasses.norm k.links,
   SeparationNormal.compact (rep k) k.separation, k.elems⟩

end

section sound
variable {ctx : Ctx} {k : Knowledge} {ρ : Env} {h : Heap}

theorem rep_eq' (hl : HeapLinks.Holds k.links ρ h) (x : Nat) : ρ (rep k x) = ρ x :=
  (LinkClasses.gen_sound hl (LinkClasses.rep_gen k.links x)).symm

theorem rep_eq (hk : HeapKnowledge.Holds k ρ h) (x : Nat) : ρ (rep k x) = ρ x := rep_eq' hk.2.2.1 x

theorem rep_le (x : Nat) : rep k x ≤ x := LinkClasses.least_le.1

theorem readDest_link {r d : Nat} {f : PropKey} (hd : readDest k r f = some d) :
    ∃ g ∈ LinkClasses.norm k.links, g.alias = false ∧ g.cell = r ∧ g.field = f ∧ g.value = d := by
  simp only [readDest, Option.map_eq_some_iff] at hd
  obtain ⟨g, hf, rfl⟩ := hd
  have hg := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
  exact ⟨g, hg, hp.1.1, hp.1.2, hp.2, rfl⟩

/-- A cell fact a read link answers states the link's destination. -/
theorem cell_dest (hk : HeapKnowledge.Holds k ρ h) {f : Fact} (hf : f ∈ k.cells) {d : Nat}
    (hd : readDest k (rep k f.slot) f.field = some d) : f.contents.mem (ρ d) = true := by
  obtain ⟨g, hg, ha, hc, hfl, hv⟩ := readDest_link hd
  have hl := (LinkClasses.norm_holds (ls := k.links)).mpr hk.2.2.1
  obtain ⟨flds, c, oid, he, hr⟩ := LinkClasses.readGave_of_link ha fun x hx => by
    rw [List.mem_singleton.mp hx]; exact hl g hg
  obtain ⟨flds', c', oid', u, he', hr', hm⟩ := hk.1 f hf
  rw [hc, rep_eq hk, he'] at he
  cases he
  rw [hfl] at hr
  rw [← hv, ← ReadGave.unique hr' hr]
  exact hm

theorem classCtx_mem (hc : CtxOk ctx ρ) (hl : HeapLinks.Holds k.links ρ h) {r : Nat} {C : ValueSet}
    (h : classCtx ctx k r = some C) : C.mem (ρ r) = true := by
  have each : ∀ D ∈ (canon (Partitions.cls (LinkClasses.closure k.links) r)).filterMap ctx, D.mem (ρ r) = true := by
    intro D hD
    obtain ⟨m, hm, hmD⟩ := List.mem_filterMap.mp hD
    have hg : LinkClasses.Gen k.links r m := LinkClasses.mem_cls_closure.mp (mem_canon.mp hm)
    rw [LinkClasses.gen_sound hl hg]
    exact hc m D hmD
  unfold classCtx at h
  split at h
  · cases h
  · rename_i C' Cs e
    cases h
    rw [e] at each
    exact mem_meetAll.mpr ⟨each C' (List.mem_cons_self ..), fun x hx => each x (List.mem_cons_of_mem _ hx)⟩

/-- **The normal form holds wherever the knowledge does.** -/
theorem norm_holds (hc : CtxOk ctx ρ) (hk : HeapKnowledge.Holds k ρ h) :
    HeapKnowledge.Holds (norm ctx k) ρ h := by
  refine ⟨?_, ?_, (LinkClasses.norm_holds (ls := k.links)).mpr hk.2.2.1,
    (SeparationNormal.compact_holds (SeparationNormal.wellFormed_of_holds hk.2.2.2.1) rep_le (rep_eq hk)).mpr hk.2.2.2.1,
    hk.2.2.2.2⟩
  · -- A cell fact per key: every fact on its slots reads one object's field.
    intro F hF
    simp only [norm, List.mem_map] at hF
    obtain ⟨key, hkey, rfl⟩ := hF
    obtain ⟨f, hf, hfk⟩ := List.mem_filterMap.mp (mem_canon.mp hkey)
    split at hfk
    · cases hfk
      obtain ⟨flds, c, oid, u, he, hr, hm⟩ := hk.1 f hf
      refine ⟨flds, c, oid, u, by rw [rep_eq hk, he], hr, ?_⟩
      rw [normIn_top_mem, mem_meetAll]
      refine ⟨ValueSet.mem_top (ValueSet.mem_isVal hm), fun x hx => ?_⟩
      simp only [cellParts, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨g, ⟨hg, hgs, hgf⟩, rfl⟩ := hx
      obtain ⟨flds', c', oid', u', he', hr', hm'⟩ := hk.1 g hg
      rw [← rep_eq hk g.slot, hgs, rep_eq hk, he] at he'
      cases he'
      rw [hgf] at hr'
      rw [ReadGave.unique hr hr']
      exact hm'
    · cases hfk
  · -- A value fact per class: the meet of what its slots and links state.
    intro F hF
    obtain ⟨r, hr, hFr⟩ := List.mem_filterMap.mp (hF)
    simp only [valueFact] at hFr
    split at hFr
    · cases hFr
    · cases hFr
      -- Every part holds of the class's value.
      have parts : ∀ x ∈ valueParts k r, x.mem (ρ r) = true := by
        intro x hx
        simp only [valueParts, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hx
        rcases hx with ⟨f, ⟨hf, hfr⟩, rfl⟩ | ⟨f, ⟨hf, hfr⟩, rfl⟩
        · rw [← hfr, rep_eq hk]; exact hk.2.1 f hf
        · exact cell_dest hk hf (by simpa using hfr)
      -- The class is named by a fact, so one part exists.
      have hone : ∃ x ∈ valueParts k r, True := by
        simp only [classes, mem_canon, List.mem_append, List.mem_map, List.mem_filterMap] at hr
        rcases hr with ⟨f, hf, rfl⟩ | ⟨f, hf, hd⟩
        · refine ⟨f.contents, ?_, trivial⟩
          simp only [valueParts, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
          exact Or.inl ⟨f, ⟨hf, rfl⟩, rfl⟩
        · refine ⟨f.contents, ?_, trivial⟩
          simp only [valueParts, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
          exact Or.inr ⟨f, ⟨hf, by simp [hd]⟩, rfl⟩
      obtain ⟨x, hx, -⟩ := hone
      have hval := ValueSet.mem_isVal (parts x hx)
      have hmeet : (meetAll ValueSet.top (valueParts k r)).mem (ρ r) = true :=
        mem_meetAll.mpr ⟨ValueSet.mem_top hval, parts⟩
      show ((classCtx ctx k r).getD ValueSet.top |>.normIn _).mem (ρ r) = true
      cases hC : classCtx ctx k r with
      | none => simp only [Option.getD_none]; rw [normIn_top_mem]; exact hmeet
      | some C => simp only [Option.getD_some]; rw [ValueSet.normIn_mem (classCtx_mem hc hk.2.2.1 hC)]; exact hmeet

end sound

section complete
variable {ctx : Ctx} {k : Knowledge} {ρ : Env} {h : Heap}

/-- From the normal form, every part of a class's value holds of it. -/
theorem parts_of_norm (hc : CtxOk ctx ρ) (hn : HeapKnowledge.Holds (norm ctx k) ρ h) {r : Nat}
    (hr : r ∈ classes k) : ∀ x ∈ valueParts k r, x.mem (ρ r) = true := by
  have hl : HeapLinks.Holds k.links ρ h := (LinkClasses.norm_holds (ls := k.links)).mp hn.2.2.1
  have hmeet : (meetAll ValueSet.top (valueParts k r)).mem (ρ r) = true := by
    cases hv : valueFact ctx k r with
    | some F =>
      have hF : F ∈ (norm ctx k).values := List.mem_filterMap.mpr ⟨r, hr, hv⟩
      have := hn.2.1 F hF
      simp only [valueFact] at hv
      split at hv
      · cases hv
      · cases hv
        simp only at this
        cases hC : classCtx ctx k r with
        | none => rw [hC, Option.getD_none, normIn_top_mem] at this; exact this
        | some C =>
          rw [hC, Option.getD_some, ValueSet.normIn_mem (classCtx_mem hc hl hC)] at this; exact this
    | none =>
      simp only [valueFact] at hv
      split at hv
      · rename_i e
        simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at e
        obtain ⟨⟨C, hC⟩, he⟩ := e
        rw [hC, Option.getD_some] at he
        have hCm := classCtx_mem hc hl hC
        have := congrArg (fun V => V.mem (ρ r)) he
        rw [ValueSet.normIn_mem hCm, ValueSet.normIn_mem hCm, ValueSet.mem_top (ValueSet.mem_isVal hCm)] at this
        exact this
      · cases hv
  exact (mem_meetAll.mp hmeet).2

/-- **The knowledge holds wherever its normal form does**: no fact is lost. -/
theorem holds_of_norm (hc : CtxOk ctx ρ) (wf : SeparationNormal.WellFormed k.separation)
    (hn : HeapKnowledge.Holds (norm ctx k) ρ h) : HeapKnowledge.Holds k ρ h := by
  have hl : HeapLinks.Holds k.links ρ h := (LinkClasses.norm_holds (ls := k.links)).mp hn.2.2.1
  refine ⟨?_, ?_, hl, (SeparationNormal.compact_holds wf rep_le (rep_eq' hl)).mp hn.2.2.2.1, hn.2.2.2.2⟩
  · intro f hf
    cases hd : readDest k (rep k f.slot) f.field with
    | some d =>
      -- The link from the receiver gives the destination, which the class's value states.
      have hdc : d ∈ classes k := by
        simp only [classes, mem_canon, List.mem_append, List.mem_filterMap]
        exact Or.inr ⟨f, hf, hd⟩
      have hpart : f.contents.mem (ρ d) = true := parts_of_norm hc hn hdc f.contents (by
        simp only [valueParts, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
        exact Or.inr ⟨f, ⟨hf, by simp [hd]⟩, rfl⟩)
      obtain ⟨g, hg, ha, hgc, hgf, hgv⟩ := readDest_link hd
      obtain ⟨flds, c, oid, he, hr⟩ := LinkClasses.readGave_of_link ha fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hn.2.2.1 g hg
      rw [hgc, rep_eq' hl] at he
      rw [hgf, hgv] at hr
      exact ⟨flds, c, oid, ρ d, he, hr, hpart⟩
    | none =>
      -- The key's cell fact holds, and meets this one.
      have hkey : (⟨rep k f.slot, f.field⟩ : CellKey) ∈ cellKeys k := by
        simp only [cellKeys, mem_canon, List.mem_filterMap]
        exact ⟨f, hf, by simp [hd]⟩
      have := hn.1 _ (List.mem_map.mpr ⟨_, hkey, rfl⟩)
      obtain ⟨flds, c, oid, u, he, hr, hm⟩ := this
      simp only at he hr hm
      rw [rep_eq' hl] at he
      rw [normIn_top_mem, mem_meetAll] at hm
      refine ⟨flds, c, oid, u, he, hr, hm.2 _ ?_⟩
      simp only [cellParts, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
      exact ⟨f, ⟨hf, rfl, rfl⟩, rfl⟩
  · intro f hf
    have hr : rep k f.slot ∈ classes k := by
      simp only [classes, mem_canon, List.mem_append, List.mem_map]
      exact Or.inl ⟨f, hf, rfl⟩
    have := parts_of_norm hc hn hr f.contents (by
      simp only [valueParts, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
      exact Or.inl ⟨f, ⟨hf, rfl⟩, rfl⟩)
    rwa [rep_eq' hl] at this

end complete

section idem
variable {ctx : Ctx} {k : Knowledge}

theorem rep_norm (x : Nat) : rep (norm ctx k) x = rep k x :=
  LinkClasses.rep_congr (fun _ _ => LinkClasses.gen_norm_iff) x

theorem readDest_norm (r : Nat) (f : PropKey) : readDest (norm ctx k) r f = readDest k r f := by
  simp only [readDest, norm, LinkClasses.norm_idem]

theorem classCtx_norm (r : Nat) : classCtx ctx (norm ctx k) r = classCtx ctx k r := by
  have : canon (Partitions.cls (LinkClasses.closure (norm ctx k).links) r) =
      canon (Partitions.cls (LinkClasses.closure k.links) r) :=
    canon_eq fun z => by
      rw [LinkClasses.mem_cls_closure, LinkClasses.mem_cls_closure]
      exact LinkClasses.gen_norm_iff
  simp only [classCtx, this]

/-- A class is named by its representative. -/
theorem rep_classes {r : Nat} (hr : r ∈ classes k) : rep k r = r := by
  simp only [classes, mem_canon, List.mem_append, List.mem_map, List.mem_filterMap] at hr
  rcases hr with ⟨f, _, rfl⟩ | ⟨f, _, hd⟩
  · exact LinkClasses.rep_rep _
  · obtain ⟨g, hg, ha, _, _, rfl⟩ := readDest_link hd
    rcases LinkClasses.mem_links.mp (mem_canon.mp hg) with ⟨x, _, rfl⟩ | ⟨r', _, _, rfl⟩
    · simp at ha
    · exact LinkClasses.rep_rep _

/-- The normal form's cell facts are no link's. -/
theorem norm_cells {F : Fact} (hF : F ∈ (norm ctx k).cells) :
    readDest k F.slot F.field = none ∧ rep k F.slot = F.slot := by
  simp only [norm, List.mem_map] at hF
  obtain ⟨key, hkey, rfl⟩ := hF
  obtain ⟨f, _, hfk⟩ := List.mem_filterMap.mp (mem_canon.mp hkey)
  split at hfk
  · rename_i hd; cases hfk; exact ⟨hd, LinkClasses.rep_rep _⟩
  · cases hfk

theorem normIn_top_meet (C V : ValueSet) : C.normIn (ValueSet.top.meet V) = C.normIn V := by
  apply ValueSet.normIn_congr
  · intro v _
    rw [ValueSet.mem_meet]
    cases hv : V.mem v
    · simp
    · simp [ValueSet.mem_top (ValueSet.mem_isVal hv)]
  · right
    cases hn : V.num with
    | these p => left; exact ⟨p.filter fun _ => true, p, by simp [ValueSet.meet, ValueSet.top, Lit.all, Lit.meet, hn], rfl⟩
    | allBut a => right; exact ⟨a, a, by simp [ValueSet.meet, ValueSet.top, Lit.all, Lit.meet, hn], rfl⟩
  · right
    cases ho : V.obj with
    | none => simp [ValueSet.meet, ValueSet.top, Obj.meet, ho]
    | some l =>
      have hl : l.filter (fun _ => true) = l := List.filter_eq_self.mpr fun _ _ => rfl
      simp [ValueSet.meet, ValueSet.top, Obj.meet, ho, hl]


theorem normIn_meetAll_single (C V : ValueSet) : C.normIn (meetAll ValueSet.top [V]) = C.normIn V := by
  simp only [meetAll, List.foldl_cons, List.foldl_nil, meetStep]
  split
  · rename_i e; rw [← e]
  · exact normIn_top_meet C V
end idem

theorem nodup_of_pairwise {α : Type} [LT α] [DecidableLT α] [StrictTotal α] {l : List α}
    (h : l.Pairwise (· < ·)) : l.Nodup :=
  h.imp fun hab e => by subst e; exact StrictTotal.irrefl _ hab

theorem filter_single {α : Type} {l : List α} (hn : l.Nodup) {p : α → Bool} {x : α} (hx : x ∈ l)
    (hp : ∀ y ∈ l, p y = true ↔ y = x) : l.filter p = [x] := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    simp only [List.filter_cons]
    by_cases e : a = x
    · subst e
      rw [if_pos ((hp a (List.mem_cons_self ..)).mpr rfl)]
      congr
      apply List.filter_eq_nil_iff.mpr
      intro y hy hpy
      exact ha ((hp y (List.mem_cons_of_mem _ hy)).mp hpy ▸ hy)
    · rw [if_neg (fun h => e ((hp a (List.mem_cons_self ..)).mp h))]
      rcases List.mem_cons.mp hx with h | h
      · exact absurd h.symm e
      · exact ih ht h fun y hy => hp y (List.mem_cons_of_mem _ hy)

theorem filterMap_single {α β : Type} [DecidableEq α] {l : List α} (hn : l.Nodup) {g : α → Option β} {r : α} {x : β}
    (hr : r ∈ l) (hg : ∀ a ∈ l, g a = if a = r then some x else none) : l.filterMap g = [x] := by
  induction l with
  | nil => simp at hr
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    simp only [List.filterMap_cons]
    rw [hg a (List.mem_cons_self ..)]
    by_cases e : a = r
    · subst e
      simp only [if_true]
      congr
      rw [List.filterMap_eq_nil_iff]
      intro b hb
      rw [hg b (List.mem_cons_of_mem _ hb), if_neg (fun (h : b = a) => ha (h ▸ hb))]
    · simp only [e, if_false]
      rcases List.mem_cons.mp hr with h | h
      · exact absurd h.symm e
      · exact ih ht h fun b hb => hg b (List.mem_cons_of_mem _ hb)

theorem valueFact_slot {ctx : Ctx} {k : Knowledge} {r : Nat} {F : Fact} (h : valueFact ctx k r = some F) :
    F.slot = r := by
  simp only [valueFact] at h
  split at h
  · cases h
  · cases h; rfl

section idem2
variable {ctx : Ctx} {k : Knowledge}

/-- A stored value fact is its class's normal form. -/
theorem valueFact_norm {r : Nat} {F : Fact} (hr : r ∈ classes k) (hF : valueFact ctx k r = some F) :
    valueFact ctx (norm ctx k) r = some F := by
  have hparts : valueParts (norm ctx k) r = [F.contents] := by
    have hcells : (norm ctx k).cells.filter (fun f => readDest (norm ctx k) (rep (norm ctx k) f.slot) f.field == some r) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro f hf
      obtain ⟨hd, hrep⟩ := norm_cells hf
      simp [rep_norm, readDest_norm, hrep, hd]
    have hvals : (norm ctx k).values.filter (fun f => rep (norm ctx k) f.slot == r) = [F] := by
      show ((classes k).filterMap (valueFact ctx k)).filter _ = [F]
      rw [List.filter_filterMap]
      apply filterMap_single (nodup_of_pairwise (pairwise_canon _)) hr
      intro a ha
      by_cases e : a = r
      · subst e
        rw [if_pos rfl, hF]
        have hs := valueFact_slot hF
        simp only [Option.filter_some, rep_norm, hs, rep_classes ha, beq_self_eq_true, ite_true]
      · rw [if_neg e]
        cases hv : valueFact ctx k a with
        | none => rfl
        | some G =>
          simp only [Option.filter_some, rep_norm, valueFact_slot hv, rep_classes ha, beq_iff_eq, e,
            ite_false]
    simp only [valueParts, hvals, hcells, List.map_cons, List.map_nil, List.append_nil]
  have hF' := hF
  simp only [valueFact] at hF' ⊢
  rw [hparts, classCtx_norm]
  split at hF'
  · cases hF'
  · cases hF'
    rename_i hn
    rw [normIn_meetAll_single, ValueSet.normIn_idem, if_neg hn]

end idem2

theorem filterMap_congr {α β : Type} {f g : α → Option β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr fun b hb => h b (List.mem_cons_of_mem _ hb)]

section idem3
variable {ctx : Ctx} {k : Knowledge}

def cellFact (k : Knowledge) (c : CellKey) : Fact :=
  ⟨c.slot, ValueSet.top.normIn (meetAll ValueSet.top (cellParts k c)), c.field⟩

theorem cellKeys_rep {c : CellKey} (hc : c ∈ cellKeys k) : rep k c.slot = c.slot := by
  obtain ⟨f, _, hfk⟩ := List.mem_filterMap.mp (mem_canon.mp hc)
  split at hfk
  · cases hfk; exact LinkClasses.rep_rep _
  · cases hfk

theorem cellFact_norm {c : CellKey} (hc : c ∈ cellKeys k) : cellFact (norm ctx k) c = cellFact k c := by
  have hparts : cellParts (norm ctx k) c = [(cellFact k c).contents] := by
    show (((cellKeys k).map (cellFact k)).filter _).map _ = _
    rw [List.filter_map]
    have : (cellKeys k).filter ((fun f => rep (norm ctx k) f.slot == c.slot && f.field == c.field) ∘ cellFact k) = [c] := by
      apply filter_single (nodup_of_pairwise (pairwise_canon _)) hc
      intro c' hc'
      simp only [Function.comp, cellFact, rep_norm, cellKeys_rep hc', Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h₁, h₂⟩; cases c'; cases c; simp_all
      · rintro rfl; exact ⟨rfl, rfl⟩
    rw [this]; rfl
  simp only [cellFact, hparts]
  rw [normIn_meetAll_single, ValueSet.normIn_idem]

theorem cellKeys_norm : cellKeys (norm ctx k) = cellKeys k := by
  show canon (((cellKeys k).map (cellFact k)).filterMap _) = cellKeys k
  rw [List.filterMap_map]
  have : (cellKeys k).filterMap ((fun f : Fact =>
      if readDest (norm ctx k) (rep (norm ctx k) f.slot) f.field = none then
        some (⟨rep (norm ctx k) f.slot, f.field⟩ : CellKey) else none) ∘ cellFact k) = cellKeys k := by
    conv => rhs; rw [← List.filterMap_some (l := cellKeys k)]
    apply filterMap_congr
    intro c hc
    have hn := norm_cells (ctx := ctx) (k := k) (F := cellFact k c) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hs : (cellFact k c).slot = c.slot := rfl
    have hf : (cellFact k c).field = c.field := rfl
    rw [hs, hf] at hn
    simp only [Function.comp, rep_norm, readDest_norm, hs, hf, hn.2, hn.1, if_true]
  rw [this]
  exact canon_canon _

end idem3

theorem map_filterMap_self {α β : Type} {f : α → Option β} {g : β → α} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b, f a = some b → g b = a) →
      (l.filterMap f).map g = l.filter fun a => (f a).isSome
  | [], _ => rfl
  | a :: l, h => by
    have ih := map_filterMap_self (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.filterMap_cons, List.filter_cons]
    cases e : f a with
    | none => simp [ih]
    | some b => simp [ih, h a (List.mem_cons_self ..) b e]

theorem filterMap_filter_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (l.filter fun a => (f a).isSome).filterMap f = l.filterMap f
  | [] => rfl
  | a :: l => by
    have ih := filterMap_filter_isSome (f := f) (l := l)
    rw [List.filter_cons]
    cases e : f a
    · simp [e, ih]
    · simp [e, ih]

section idem4
variable {ctx : Ctx} {k : Knowledge}

theorem classes_norm : classes (norm ctx k) = (classes k).filter fun r => (valueFact ctx k r).isSome := by
  have hcells : (norm ctx k).cells.filterMap (fun f => readDest (norm ctx k) (rep (norm ctx k) f.slot) f.field) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro f hf
    obtain ⟨hd, hrep⟩ := norm_cells hf
    simp [rep_norm, readDest_norm, hrep, hd]
  have hvals : (norm ctx k).values.map (fun f => rep (norm ctx k) f.slot) =
      (classes k).filter fun r => (valueFact ctx k r).isSome := by
    show ((classes k).filterMap (valueFact ctx k)).map _ = _
    apply map_filterMap_self
    intro a ha F hF
    simp [rep_norm, valueFact_slot hF, rep_classes ha]
  simp only [classes, hcells, List.append_nil, hvals]
  exact canon_of_pairwise ((pairwise_canon _).sublist List.filter_sublist)

/-- **Stored**: the normal form is its own normal form. -/
theorem norm_idem (wf : SeparationNormal.WellFormed k.separation) : norm ctx (norm ctx k) = norm ctx k := by
  have hcells : (cellKeys (norm ctx k)).map (cellFact (norm ctx k)) = (cellKeys k).map (cellFact k) := by
    rw [cellKeys_norm]; exact List.map_congr_left fun c hc => cellFact_norm hc
  have hvalues : (classes (norm ctx k)).filterMap (valueFact ctx (norm ctx k)) =
      (classes k).filterMap (valueFact ctx k) := by
    rw [classes_norm]
    rw [filterMap_congr (g := valueFact ctx k), filterMap_filter_isSome]
    intro a ha
    obtain ⟨ha, hs⟩ := List.mem_filter.mp ha
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp hs
    rw [valueFact_norm ha hF, hF]
  have hsep : SeparationNormal.compact (rep (norm ctx k)) (SeparationNormal.compact (rep k) k.separation) =
      SeparationNormal.compact (rep k) k.separation := by
    rw [show rep (norm ctx k) = rep k from funext rep_norm]
    exact SeparationNormal.compact_idem wf rep_le fun x => LinkClasses.rep_rep _
  show Knowledge.mk ((cellKeys (norm ctx k)).map (cellFact (norm ctx k)))
      ((classes (norm ctx k)).filterMap (valueFact ctx (norm ctx k)))
      (LinkClasses.norm (LinkClasses.norm k.links))
      (SeparationNormal.compact (rep (norm ctx k)) (SeparationNormal.compact (rep k) k.separation)) k.elems =
    Knowledge.mk ((cellKeys k).map (cellFact k)) ((classes k).filterMap (valueFact ctx k))
      (LinkClasses.norm k.links) (SeparationNormal.compact (rep k) k.separation) k.elems
  rw [hcells, hvalues, LinkClasses.norm_idem, hsep]

end idem4

section unique
variable {ctx : Ctx} {k₁ k₂ : Knowledge}

/-- The side conditions of `ValueSet.normIn_congr`: numbers under a finite
context or in one form, and objects with one clause normal form. -/
def Forms (C V W : ValueSet) : Prop :=
  ((∃ f, C.num = .these f) ∨ (∃ p q, V.num = .these p ∧ W.num = .these q) ∨
    (∃ a b, V.num = .allBut a ∧ W.num = .allBut b)) ∧
  (C.obj = none ∨ objNorm V.obj = objNorm W.obj)

theorem gen_congr_of_norm (hL : LinkClasses.norm k₁.links = LinkClasses.norm k₂.links) (x y : Nat) :
    LinkClasses.Gen k₁.links x y ↔ LinkClasses.Gen k₂.links x y := by
  rw [← LinkClasses.gen_norm_iff (ls := k₁.links), hL, LinkClasses.gen_norm_iff]

/-- **Unique**: knowledge whose links have one normal form, naming the same
classes and cell keys, whose classes' facts admit the same values at their
context and whose keys' facts the same values, has one normal form. -/
theorem norm_congr (hL : LinkClasses.norm k₁.links = LinkClasses.norm k₂.links)
    (hcls : ∀ r, r ∈ classes k₁ ↔ r ∈ classes k₂)
    (hV : ∀ r ∈ classes k₁, ∀ v, (∀ C, classCtx ctx k₁ r = some C → C.mem v = true) →
      (meetAll ValueSet.top (valueParts k₁ r)).mem v = (meetAll ValueSet.top (valueParts k₂ r)).mem v)
    (hVf : ∀ r ∈ classes k₁, Forms ((classCtx ctx k₁ r).getD ValueSet.top)
      (meetAll ValueSet.top (valueParts k₁ r)) (meetAll ValueSet.top (valueParts k₂ r)))
    (hkeys : ∀ c, c ∈ cellKeys k₁ ↔ c ∈ cellKeys k₂)
    (hW : ∀ c ∈ cellKeys k₁, ∀ v, (meetAll ValueSet.top (cellParts k₁ c)).mem v =
      (meetAll ValueSet.top (cellParts k₂ c)).mem v)
    (hWf : ∀ c ∈ cellKeys k₁, Forms ValueSet.top (meetAll ValueSet.top (cellParts k₁ c))
      (meetAll ValueSet.top (cellParts k₂ c)))
    (hS : k₁.separation = k₂.separation) (hE : k₁.elems = k₂.elems) :
    norm ctx k₁ = norm ctx k₂ := by
  have hG := gen_congr_of_norm hL
  have hctx : ∀ r, classCtx ctx k₁ r = classCtx ctx k₂ r := fun r => by
    have : canon (Partitions.cls (LinkClasses.closure k₁.links) r) =
        canon (Partitions.cls (LinkClasses.closure k₂.links) r) :=
      canon_eq fun z => by rw [LinkClasses.mem_cls_closure, LinkClasses.mem_cls_closure, hG]
    simp only [classCtx, this]
  have hclasses : classes k₁ = classes k₂ := by
    have := canon_eq (l₁ := classes k₁) (l₂ := classes k₂) hcls
    simpa only [classes, canon_canon] using this
  have hck : cellKeys k₁ = cellKeys k₂ := by
    have := canon_eq (l₁ := cellKeys k₁) (l₂ := cellKeys k₂) hkeys
    simpa only [cellKeys, canon_canon] using this
  have hval : ∀ r ∈ classes k₁, valueFact ctx k₁ r = valueFact ctx k₂ r := by
    intro r hr
    have hn : ((classCtx ctx k₁ r).getD ValueSet.top).normIn (meetAll ValueSet.top (valueParts k₁ r)) =
        ((classCtx ctx k₁ r).getD ValueSet.top).normIn (meetAll ValueSet.top (valueParts k₂ r)) := by
      obtain ⟨hnum, hobj⟩ := hVf r hr
      apply ValueSet.normIn_congr _ hnum hobj
      intro v hv
      apply hV r hr v
      intro C hC
      rw [hC, Option.getD_some] at hv
      exact hv
    simp only [valueFact, ← hctx r, hn]
  have hcell : ∀ c ∈ cellKeys k₁, cellFact k₁ c = cellFact k₂ c := by
    intro c hc
    obtain ⟨hnum, hobj⟩ := hWf c hc
    simp only [cellFact, ValueSet.normIn_congr (fun v _ => hW c hc v) hnum hobj]
  have hrep : rep k₁ = rep k₂ := funext (LinkClasses.rep_congr hG)
  show Knowledge.mk ((cellKeys k₁).map (cellFact k₁)) ((classes k₁).filterMap (valueFact ctx k₁))
      (LinkClasses.norm k₁.links) (SeparationNormal.compact (rep k₁) k₁.separation) k₁.elems =
    Knowledge.mk ((cellKeys k₂).map (cellFact k₂)) ((classes k₂).filterMap (valueFact ctx k₂))
      (LinkClasses.norm k₂.links) (SeparationNormal.compact (rep k₂) k₂.separation) k₂.elems
  rw [List.map_congr_left hcell, filterMap_congr hval, hck, hclasses, hL, hS, hrep, hE]

end unique

/-! ## Computing the normal form with one closure -/

/-- First read of each receiver and field, preserving the link order. -/
private def readIndex : HeapLinks.Links → Std.HashMap (Nat × PropKey) Nat
  | [] => {}
  | g :: gs =>
    let m := readIndex gs
    if g.alias then m else m.insert (g.cell, g.field) g.value

private theorem readIndex_get (ls : HeapLinks.Links) (x : Nat) (f : PropKey) :
    (readIndex ls)[(x, f)]? =
      (ls.find? fun g => !g.alias && g.cell == x && g.field == f).map (·.value) := by
  induction ls with
  | nil => simp [readIndex]
  | cons g gs ih =>
    cases ha : g.alias <;> by_cases hx : g.cell = x <;> by_cases hf : g.field = f <;>
      simp [readIndex, ha, hx, hf, Std.HashMap.getElem?_insert, ih, beq_false_of_ne]

/-- Contents grouped by a key, in the facts' order, retaining duplicates. -/
@[nospecialize] private def buckets {α : Type} [BEq α] [Hashable α]
    (key : HeapFacts.Fact → α) : HeapFacts.Facts → Std.HashMap α (List ValueSet)
  | [] => {}
  | F :: fs =>
    let m := buckets key fs
    let a := key F
    m.insert a (F.contents :: (m[a]?).getD [])

private theorem buckets_get {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (key : HeapFacts.Fact → α) (fs : HeapFacts.Facts) (a : α) :
    ((buckets key fs)[a]?).getD [] = (fs.filter fun F => key F == a).map (·.contents) := by
  induction fs with
  | nil => simp [buckets]
  | cons F fs ih =>
    by_cases h : key F = a <;>
      simp [buckets, Std.HashMap.getElem?_insert, h, ih]

/-- `norm`, computing the alias closure and the normal links once. -/
def normFast (ctx : Ctx) (k : Knowledge) : Knowledge :=
  let cs := LinkClasses.closure k.links
  let classesBySlot := Partitions.index cs
  let members := fun x => (classesBySlot[x]?).getD [x]
  let r := fun x => LinkClasses.least x (members x)
  let nl := canon (LinkClasses.linksIn k.links cs)
  let reads := readIndex nl
  let readDest := fun (x : Nat) (f : PropKey) => reads[(x, f)]?
  let classCtx := fun (x : Nat) => match (canon (members x)).filterMap ctx with
    | [] => none
    | C :: Cs => some (meetAll C Cs)
  let valuesByClass := buckets (fun f => r f.slot) k.values
  let cellsByRead := buckets (fun f => readDest (r f.slot) f.field) k.cells
  let valueParts := fun (x : Nat) =>
    (valuesByClass[x]?).getD [] ++ (cellsByRead[some x]?).getD []
  let classes := canon ((k.values.map fun f => r f.slot) ++ k.cells.filterMap fun f => readDest (r f.slot) f.field)
  let valueFact := fun (x : Nat) =>
    let C := (classCtx x).getD ValueSet.top
    let V := C.normIn (meetAll ValueSet.top (valueParts x))
    if (classCtx x).isSome && V == C.normIn ValueSet.top then none else some (⟨x, V, valueField⟩ : Fact)
  let cellKeys := canon (k.cells.filterMap fun f =>
    if readDest (r f.slot) f.field = none then some (⟨r f.slot, f.field⟩ : CellKey) else none)
  let cellsByKey := buckets (fun f => (r f.slot, f.field)) k.cells
  let cellParts := fun (c : CellKey) => (cellsByKey[(c.slot, c.field)]?).getD []
  ⟨cellKeys.map (fun c => ⟨c.slot, ValueSet.top.normIn (meetAll ValueSet.top (cellParts c)), c.field⟩),
   classes.filterMap valueFact, nl, SeparationNormal.compact r k.separation, k.elems⟩

theorem normFast_eq (ctx : Ctx) (k : Knowledge) : normFast ctx k = norm ctx k := by
  simp only [normFast, Partitions.index_cls, readIndex_get, buckets_get]
  rfl

end Verification.KnowledgeNormal
