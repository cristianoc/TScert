import Verification.Paper.TolerantFrames.Assertions
import Verification.Semantics.RegionBounds

/-! # The complete modality-free assertion support

The existing mechanism extended here is `SupportDomain.Supports`. The paper's
`all` keeps values and both kinds of spines at every old location; allocation
may add locations. Preservation covers the general assertion grammar except
boxes. It is forward preservation: allocation may supply new logical witnesses.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames

/-- Definition 14's support all = {val:keep, st:keep}. -/
def allKeep : Footprint := [(.cls .values, .keep), (.cls .spines, .keep)]

/-- Exactly the assertion grammar without a modality. -/
def Formula.ModalityFree : Formula → Prop
  | .and F G | .or F G => F.ModalityFree ∧ G.ModalityFree
  | .existsValue F => F.ModalityFree
  | .box _ _ => False
  | _ => True

/-- The two classes cover every old location. -/
theorem allKeep_prefix {ρ : Env} {s t : IndexedHeap} (ha : Admissible s t)
    (hs : Supported allKeep ρ s.h t.h) : s.h.IsPrefix t.h := by
  apply (Post.empty_iff (ρ := ρ)).mp
  refine ⟨ha.length_le, fun l v hv => ?_⟩
  have hget (c : Selector) (hm : c.selects v = true)
      (he : (Region.cls c, Change.keep) ∈ allKeep) : t.h[l]? = some v := by
    obtain ⟨v', hv', hh⟩ := hs _ he l v (by simpa [Region.mem, hv] using hm) hv
    exact hh ▸ hv'
  by_cases hsp : isArr v = true
  · exact ⟨v, hget .spines (by simpa using hsp) (by simp [allKeep]), .inl rfl⟩
  · exact ⟨v, hget .values (by simpa using hsp) (by simp [allKeep]), .inl rfl⟩

/-- Either collection spine's successful reading survives extension. -/
theorem collectionEntries_extend {h : Heap} (vs : List Val) {v : Val} {es : List (Option Nat)}
    (he : collectionEntries h v = some es) : collectionEntries (h ++ vs) v = some es := by
  simp only [collectionEntries, Option.bind_eq_some_iff] at he ⊢
  obtain ⟨s, hs, u, hu, he⟩ := he
  exact ⟨s, hs, u, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1]; exact hu, he⟩

/-- Holes stay undefined values; no density premise is needed. -/
theorem elementValue_extend {h : Heap} (vs : List Val) {v u : Val} {i : Int}
    (he : elementValue h v i = some u) : elementValue (h ++ vs) v i = some u := by
  by_cases hi : i < 0
  · simp [elementValue, hi] at he
  · simp only [elementValue, hi, ↓reduceIte, bind, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨es, hes, he⟩ := he
    refine ⟨es, collectionEntries_extend vs hes, ?_⟩
    split at he
    · cases he
    · exact he
    · rename_i l _
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]
      exact he

mutual
theorem Term.eval_extend {h : Heap} (vs : List Val) {ρ : Env} : ∀ {t : Term} {n : Int},
    t.eval ρ h = some n → t.eval ρ (h ++ vs) = some n
  | .literal _, _, he => he
  | .path _ _, _, he => by
    simp only [Term.eval, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hv, he⟩ := he
    exact ⟨v, readPath_extend vs hv, kindValue_extend vs he⟩
  | .element _ _ _ _ _, _, he => by
    simp only [Term.eval, bind, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hv, i, hi, u, hu, w, hw, he⟩ := he
    exact ⟨v, readPath_extend vs hv, i, Expression.eval_extend vs hi, u,
      elementValue_extend vs hu, w, readPath_extend vs hw, kindValue_extend vs he⟩

theorem Expression.eval_extend {h : Heap} (vs : List Val) {ρ : Env} : ∀ {e : Expression} {n : Int},
    e.eval ρ h = some n → e.eval ρ (h ++ vs) = some n
  | .constant _, _, he => he
  | .scale _ _, _, he => by
    simp only [Expression.eval, Option.map_eq_some_iff] at he ⊢
    obtain ⟨n, hn, he⟩ := he
    exact ⟨n, Term.eval_extend vs hn, he⟩
  | .add _ _, _, he => by
    simp only [Expression.eval, bind, pure, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨a, ha, b, hb, he⟩ := he
    exact ⟨a, Expression.eval_extend vs ha, b, Expression.eval_extend vs hb, he⟩
end

theorem BodyTerm.eval_extend {h : Heap} (vs : List Val) {ρ : Env} {z : Val} {i n : Int}
    {u : BodyTerm} (he : u.eval ρ h z i = some n) : u.eval ρ (h ++ vs) z i = some n := by
  cases u with
  | index => exact he
  | free _ => exact Term.eval_extend vs he
  | element _ =>
    simp only [BodyTerm.eval, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hv, he⟩ := he
    exact ⟨v, elementValue_extend vs hv, he⟩
  | project _ _ _ =>
    simp only [BodyTerm.eval, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hv, w, hw, he⟩ := he
    exact ⟨v, elementValue_extend vs hv, w, readPath_extend vs hw, kindValue_extend vs he⟩

theorem BodyExpression.eval_extend {h : Heap} (vs : List Val) {ρ : Env} {z : Val} {i : Int} :
    ∀ {e : BodyExpression} {n : Int}, e.eval ρ h z i = some n → e.eval ρ (h ++ vs) z i = some n
  | .constant _, _, he => he
  | .scale _ _, _, he => by
    simp only [BodyExpression.eval, Option.map_eq_some_iff] at he ⊢
    obtain ⟨n, hn, he⟩ := he
    exact ⟨n, BodyTerm.eval_extend vs hn, he⟩
  | .add _ _, _, he => by
    simp only [BodyExpression.eval, bind, pure, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨a, ha, b, hb, he⟩ := he
    exact ⟨a, BodyExpression.eval_extend vs ha, b, BodyExpression.eval_extend vs hb, he⟩

theorem Clause.holds_extend {h : Heap} (vs : List Val) {ρ : Env} {z : Val} {i : Int}
    {c : Clause} (hc : c.Holds ρ h z i) : c.Holds ρ (h ++ vs) z i := by
  induction c with
  | le e f =>
    obtain ⟨a, b, ha, hb, hab⟩ := hc
    exact ⟨a, b, BodyExpression.eval_extend vs ha, BodyExpression.eval_extend vs hb, hab⟩
  | or c d ihc ihd => exact hc.imp ihc ihd

theorem Body.holds_extend {h : Heap} (vs : List Val) {ρ : Env} {z : Val} {i : Int}
    {b : Body} (hb : b.Holds ρ h z i) : b.Holds ρ (h ++ vs) z i := by
  induction b with
  | clause c => exact Clause.holds_extend vs hb
  | and b c ihb ihc => exact ⟨ihb hb.1, ihc hb.2⟩

theorem optionalRead_extend {h : Heap} (vs : List Val) {ρ : Env} {p : Parity.Path} {f : String} {u : Val}
    (he : optionalRead ρ h p f = some u) : optionalRead ρ (h ++ vs) p f = some u := by
  simp only [optionalRead, bind, Option.bind_eq_some_iff] at he ⊢
  obtain ⟨v, hv, he⟩ := he
  refine ⟨v, readPath_extend vs hv, ?_⟩
  cases v <;> try cases he
  simp only at he ⊢
  split at he
  · exact he
  · rename_i l _; rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]; exact he

theorem Atom.holds_extend {h : Heap} (vs : List Val) {ρ : Env} {a : Atom}
    (ha : a.Holds ρ h) : a.Holds ρ (h ++ vs) := by
  cases a with
  | le e f =>
    obtain ⟨a, b, ha, hb, hab⟩ := ha
    exact ⟨a, b, Expression.eval_extend vs ha, Expression.eval_extend vs hb, hab⟩
  | equal p v => obtain ⟨u, hu, he⟩ := ha; exact ⟨u, readPath_extend vs hu, he⟩
  | optionalEqual p f v => obtain ⟨u, hu, he⟩ := ha; exact ⟨u, optionalRead_extend vs hu, he⟩
  | contents p V => obtain ⟨u, hu, he⟩ := ha; exact ⟨u, readPath_extend vs hu, he⟩
  | dense x e =>
    obtain ⟨s, es, n, hs, hes, hn, hd⟩ := ha
    exact ⟨s, es, n, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hes).1]; exact hes,
      Expression.eval_extend vs hn, hd⟩
  | element p e v =>
    obtain ⟨u, i, w, hu, hi, hw, he⟩ := ha
    exact ⟨u, i, w, readPath_extend vs hu, Expression.eval_extend vs hi, elementValue_extend vs hw, he⟩
  | every p e b =>
    obtain ⟨v, es, n, hv, hes, hn, hb⟩ := ha
    exact ⟨v, es, n, readPath_extend vs hv, collectionEntries_extend vs hes, Expression.eval_extend vs hn,
      fun i hi hin => Body.holds_extend vs (hb i hi hin)⟩

/-- A valid path cannot start reading a newly allocated location. -/
theorem readPath_eq_append {s : IndexedHeap} (vs : List Val) : ∀ (p : List String) {v : Val},
    RefsOk s.W v → readPath (s.h ++ vs) v p = readPath s.h v p
  | [], _, _ => rfl
  | f :: p, v, hv => by
    cases v with
    | objAt fs c i =>
      simp only [readPath]
      split
      · rename_i l hl
        obtain ⟨r, hr, -⟩ := field_bound hv (by simpa [fieldsOf] using hl)
        obtain ⟨u, hu, -, hru⟩ := s.ok.2 l r hr
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1, hu]
        exact readPath_eq_append vs p hru
      · rfl
    | _ => rfl

/-- The spines reachable from an old valid value keep exactly their listing. -/
theorem spineCells_eq_append {s : IndexedHeap} (vs : List Val) {v : Val} (hv : RefsOk s.W v) :
    spineCells (s.h ++ vs) v = spineCells s.h v := by
  cases v with
  | objAt fs c i =>
    have hf : entriesAt (s.h ++ vs) (fs.lookup arraySpineKey) = entriesAt s.h (fs.lookup arraySpineKey) := by
      cases hl : fs.lookup arraySpineKey with
      | none => rfl
      | some l =>
        obtain ⟨r, hr, -⟩ := field_bound hv (by simpa [fieldsOf] using hl)
        obtain ⟨u, hu, -⟩ := s.ok.2 l r hr
        simp only [entriesAt, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1]
    simp only [spineCells, fieldsOf, hf]
    congr 1
    cases c <;> try rfl
    rename_i st f n
    have hr := (hv (.view st f n (fs.lookup arraySpineKey).isNone) (by simp [refs])).2
    obtain ⟨u, hu, -⟩ := s.ok.2 st _ hr
    simp only [descriptorSpine, entriesAt, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1]
  | _ => rfl

/-- Extension preserves every region's membership at old locations. -/
theorem region_mem_eq_append {s t : IndexedHeap} (ha : Admissible s t) (vs : List Val)
    (hh : t.h = s.h ++ vs) {ρ : Env} (hρ : RootsOk s.W ρ) :
    ∀ (r : Region) {l : Nat}, l < s.h.length → r.mem ρ t.h l = r.mem ρ s.h l
  | .field _ _, _, _ | .fields _, _, _ => rfl
  | .cls c, _, hl => ha.cls_mem hl ρ c
  | .all, _, hl => by simp [Region.mem, hl, Nat.lt_of_lt_of_le hl ha.length_le]
  | .cells x, _, _ => by simp only [Region.mem, hh, spineCells_eq_append vs (hρ x)]
  | .path x p k, _, _ | .pathFields x p, _, _ | .spine x p, _, _ => by
    simp only [Region.mem, hh, readPath_eq_append vs p (hρ x)]
  | .pathCells x p, _, _ => by
    simp only [Region.mem, hh, readPath_eq_append vs p (hρ x)]
    split
    · rename_i v hv
      rw [spineCells_eq_append vs (readPath_refs s.ok p (hρ x) hv)]
    · rfl
  | .inCls r c, _, hl => by
    have hm := region_mem_eq_append ha vs hh hρ r hl
    have hc := ha.cls_mem hl ρ c
    simp only [Region.mem] at hc ⊢
    rw [hm, hc]

/-- A valid source witness extends the context at precisely its state. -/
theorem ValidContext.push {ρ m s} (hv : ValidContext ρ m s) {v : Val}
    (hs : isSourceVal v = true) (hr : RefsOk s.W v) : ValidContext (push v ρ) m s := by
  refine ⟨?_, ?_, hv.2.2⟩
  · intro x; cases x with
    | zero => exact hr
    | succ x => exact hv.1 x
  · intro x; cases x with
    | zero => exact hs
    | succ x => exact hv.2.1 x

/-- Allocation preserving old contents preserves the modality-free language.
This is one-way: later existential witnesses need not exist at entry. -/
theorem Formula.holds_prefix {F : Formula} (hn : F.ModalityFree) {ρ m s t}
    (hv : ValidContext ρ m s) (ha : Admissible s t) (hp : s.h.IsPrefix t.h)
    (hF : F.Holds ρ m s) : F.Holds ρ m t := by
  obtain ⟨vs, hvs⟩ := hp
  have hh : t.h = s.h ++ vs := hvs.symm
  induction F generalizing ρ with
  | truth => trivial
  | falsity => exact hF.elim
  | atom a => rw [Formula.Holds, hh]; exact Atom.holds_extend vs hF
  | and F G ihF ihG => exact ⟨ihF hn.1 hv hF.1, ihG hn.2 hv hF.2⟩
  | or F G ihF ihG => exact hF.imp (ihF hn.1 hv) (ihG hn.2 hv)
  | existsValue F ih =>
    obtain ⟨v, hsv, hrv, hF⟩ := hF
    exact ⟨v, hsv, ha.refsOk hrv, ih hn (hv.push hsv hrv) hF⟩
  | separated p q => rw [Formula.Holds, hh]; exact PathSpinesApart.extend vs hF
  | apart x y =>
    obtain ⟨u, w, st, st', es, es', hu, hw, ⟨hs, hd, he⟩, ⟨hs', hd', he'⟩, hne, hdis⟩ := hF
    refine ⟨u, w, st, st', es, es', ?_, ?_, ⟨hs, hd, ?_⟩, ⟨hs', hd', ?_⟩, hne, hdis⟩
    · rw [hh]; exact readPath_extend vs hu
    · rw [hh]; exact readPath_extend vs hw
    · rw [hh, List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]; exact he
    · rw [hh, List.getElem?_append_left (List.getElem?_eq_some_iff.mp he').1]; exact he'
  | fresh r =>
    intro l hl
    by_cases hlt : l < s.h.length
    · exact hF l (by rwa [region_mem_eq_append ha vs hh hv.1 r hlt] at hl)
    · exact Nat.le_trans hv.2.2 (Nat.le_of_not_lt hlt)
  | box Φ F ih => exact hn.elim

/-- Definition 14's all support at the complete assertion grammar. -/
theorem Formula.all_support {F : Formula} (hn : F.ModalityFree) :
    Supports (fun _ _ _ _ => True) F.meaning allKeep :=
  fun _ _ _ _ ha ⟨hv, _⟩ hF hs => F.holds_prefix hn hv ha (allKeep_prefix ha hs) hF

end Verification.Paper.TolerantFrames
