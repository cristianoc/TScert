import Verification.Semantics.ArgumentContracts
-- AllocationWorlds.lean proves allocation safe at the successor world its field contracts determine; without it the allocation rule has no safety proof.
import Verification.Semantics.AllocationWorlds
/-!
# Compatibility rules

The rules a program's safety proof should be assembled from, rather than traced
by hand. A call spends its dispatch step and uses the callee's contract one
level below the current budget.
-/
namespace Verification

/-- A ready call that omits trailing actuals. Every omitted position's contract
admits `undefined`, which is the value the machine binds there, so the selected
signature covers the padded list and the same body runs. -/
theorem call_elim_short {L : List (Fam × List Fam × Fam)} {p : Fam × List Fam × Fam}
    (hR : Adm p.1) (hA : ∀ A ∈ p.2.1, Adm A) (hAv : ∀ A ∈ p.2.1, ValOnly A)
    {n : Nat} {W : WorldT n} {f r : Tm} {args pad : List Tm} {heap : Heap}
    (hpad : ∀ a ∈ pad, a = .undef) (hrv : isVal r = true)
    (hf : callsT Ξ L n W f) (hp : p ∈ L) (hr : p.1 n W r) (ha : ArgsT p.2.1 n W (args ++ pad))
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe Ξ p.2.2 n W heap (.invoke f r args) := by
  exact ArgumentContracts.call_safe
    (P := ArgsShort p.2.1)
    (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer hA ha j hj U hx)) hR
    ⟨hf.1, hf.2 p hp⟩ hr hrv
    (fun a hm => ArgsT_values hAv ha a (List.mem_append_left pad hm))
    (ArgsShort_of_pad hpad ha) hw hh

/-- A binding consumes one step after its initializer has become a value. -/
theorem let_rule {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (hb : Safe Ξ B p (trunc p (Nat.le_succ p) W) h (subst 0 a b)) :
    Safe Ξ B (p + 1) W h (.letE a b) :=
  Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .letV hval,
    HeapOk_trunc p W h hok, hb⟩

/-! ## Storage -/


/-- **Read.** -/
theorem read_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := (hag p (by omega) _ v).mp (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .readField hf hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl (Or.inl ⟨hA _ _ _ hAv, hAv⟩)

/-- **Read through a view.** The location's contract implies the stated family,
which is all a read observes. -/
theorem read_view_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .readField hf hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl (Or.inl ⟨hA _ _ _ hAv, hAv⟩)

/-- A read whose location's contract implies `A` only in worlds extending the
current one: the read happens in the current world, so that is all it needs. -/
theorem read_view_rule_ext {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ (u : Val), c j hj U u → A j U u) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v :=
      hag p (by omega) _ (WExt_refl _) v (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .readField hf hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl (Or.inl ⟨hA _ _ _ hAv, hAv⟩)

/-- **Read through the prototype.** A key the object lacks is read from its
prototype, which the object's prototype location holds under a contract
implying `P`; a read of the key from any member of `P` is safe at `A`. The
delegation is a step, so the prototype is read one level down. -/
theorem read_proto_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {P A : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hmiss : flds.lookup f = none)
    (hpf : flds.lookup CallArguments.protoField = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → P j U u)
    (hP : ∀ j (U : WorldT j) (h' : Heap), WorldAdm U → HeapOk j U h' →
      ∀ u, P j U u → Safe Ξ A j U h' (.readAt f u)) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨pv, hpv, hmem⟩ := hok.2 l c hl
    exact Or.inr ⟨trunc p (Nat.le_succ p) W, h, .readAt f pv, WExt_refl _,
      WorldAdm_trunc _ hadm, .readProto hmiss hpf hpv, HeapOk_trunc p W h hok,
      hP p _ h (WorldAdm_trunc _ hadm) (HeapOk_trunc p W h hok) pv
        (hag p (by omega) _ pv (hmem p (by omega)))⟩

#print axioms read_proto_rule

/-- An index view covers every present field under a key its class admits,
while a missing key reads `undefined`. A lookup cannot discard that
alternative. -/
theorem read_dict_rule {flds : List (PropKey × Nat)} {f : PropKey} {K : IndexKeys} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hk : K.Admits f)
    (hd : dictViewT K A n W (.objAt flds .absent oid)) :
    Safe Ξ (unionT A undefT) n W h (.readAt f (.objAt flds .absent oid)) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := dictViewT_present hd hk hlook
    apply Safe_mono n (fun _ _ _ _ ha => Or.inl ha) W h _
      (read_view_rule hA n W h l hadm hok hlook hc hag)
  | none =>
    cases n with
    | zero => trivial
    | succ p =>
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _,
        WorldAdm_trunc _ hadm, .readMissing hlook (dictViewT_no_proto hd), HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl (Or.inl ⟨rfl, Or.inr rfl⟩)

/-- **Read an optional field.** Where the object has the key, its location's
contract implies `A`, as an optional field's (equal to it) or a readonly
optional field's does; where it does not, the read is `undefined`. A lookup
cannot discard that alternative. The object has no prototype, so a missing key
is not read elsewhere. -/
theorem read_optional_rule {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hp : flds.lookup f = none → flds.lookup CallArguments.protoField = none)
    (ho : ∀ l, flds.lookup f = some l → ∃ c : Ctr n, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u) :
    Safe Ξ (unionT A undefT) n W h (.readAt f (.objAt flds .absent oid)) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := ho l hlook
    apply Safe_mono n (fun _ _ _ _ ha => Or.inl ha) W h _
      (read_view_rule hA n W h l hadm hok hlook hc hag)
  | none =>
    cases n with
    | zero => trivial
    | succ p =>
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _,
        WorldAdm_trunc _ hadm, .readMissing hlook (hp hlook), HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl (Or.inl ⟨rfl, Or.inr rfl⟩)

/-- The same guarantee when the key was evaluated at runtime: a value whose
`ToPropertyKey` (`propertyKey`) the index's class admits. The caller must
separately prove the key's value is one. -/
theorem index_dict_rule {flds : List (PropKey × Nat)} {key : Tm} {f : PropKey} {K : IndexKeys}
    {A : Fam} (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hkey : propertyKey key = some f) (hk : K.Admits f)
    (hd : dictViewT K A n W (.objAt flds .absent oid)) :
    Safe Ξ (unionT A undefT) n W h (.indexAt (.objAt flds .absent oid) key) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := dictViewT_present hd hk hlook
    cases n with
    | zero => trivial
    | succ p =>
      obtain ⟨v, hv, hmem⟩ := hok.2 l c hc
      have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
        WorldAdm_trunc _ hadm, .indexField hkey hlook hv, HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl (Or.inl ⟨hA _ _ _ hAv, Or.inl hAv⟩)
  | none =>
    cases n with
    | zero => trivial
    | succ p =>
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _,
        WorldAdm_trunc _ hadm, .indexMissing hkey hlook (dictViewT_no_proto hd), HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl (Or.inl ⟨rfl, Or.inr rfl⟩)

#print axioms index_dict_rule

/-- **Write.** -/
theorem write_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) :
    Safe Ξ nulT n W h (.writeAt f (.objAt flds code oid) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.2 l c hl
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .nul, WExt_refl _,
      WorldAdm_trunc _ hadm, .writeField hval hf hlt, ?_, Safe_nul p _ _⟩
    refine write_sound p _ h l _ v (HeapOk_trunc p W h hok)
      (lookup_trunc (Nat.le_succ p) W l c hl) ?_
    intro i hi
    show c i _ _ v
    refine (hag i (by omega) _ v).mpr ?_
    have := hA.down_le (p + 1) i (by omega) W v hv
    rw [trunc_trunc]
    exact this

/-- **Allocating an object with named fields.** One step takes one fresh
location per field, so the world grows by one contract per field and the result
sees the whole record. The single-cell rule above is the one-field case. -/
theorem make_fields_rule {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List PropKey) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, p.1 n W p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip As) j U (.objAt (slots h.length ns) .absent (h.length + vs.length)) →
      Q j U (.objAt (slots h.length ns) code (h.length + vs.length))) :
    Safe Ξ Q n W h (.makeAt code ns vs) :=
  OperationWorlds.erase n W h (.makeAt code ns vs)
    (AllocationWorlds.allocation_safe hA hV n W h code ns vs hnd hns hAs hvals hadm hok
      (fun p hp j _ => (hA p.1 (List.of_mem_zip hp).1).down_le n j (by omega) W p.2 (hv p hp)) result)

/-- **Allocating named fields, from values known below the level.** The
allocation step spends a level, so each value need meet its family only at
the levels the heap is judged at after it. -/
theorem make_fields_rule_below {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List PropKey) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, ∀ (j : Nat) (hj : j + 1 < n), p.1 j (trunc j (by omega) W) p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip As) j U (.objAt (slots h.length ns) .absent (h.length + vs.length)) →
      Q j U (.objAt (slots h.length ns) code (h.length + vs.length))) :
    Safe Ξ Q n W h (.makeAt code ns vs) :=
  OperationWorlds.erase n W h (.makeAt code ns vs)
    (AllocationWorlds.allocation_safe hA hV n W h code ns vs hnd hns hAs hvals hadm hok hv result)

/-- **Allocating an object with no named field**, as `.bind` does: the
result meets `Q` at whatever identity the allocation gives it. -/
theorem make_empty_rule {Q : Fam} (hQ : Adm Q) (n : Nat) (W : WorldT n) (h : Heap)
    (code : CallCode) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ oid, Q n W (.objAt [] code oid)) : Safe Ξ Q n W h (.makeAt code [] []) :=
  make_fields_rule (As := []) (fun _ h => by simp at h) (fun _ h => by simp at h) n W h code [] [] List.nodup_nil rfl rfl
    (by simp) hadm hok (by simp) fun j hj U hx _ =>
      hQ.mono j _ U hx _ (hQ.down_le n j (Nat.le_of_lt hj) W _ (hv _))

/-- **Creating a function object.** Its one field, which gives it a location
and so an identity, holds the value; the result obligation supplies the view
of the fresh object its code gives. -/
theorem makeFn_rule {A Q : Fam} (hA : Adm A) (hV : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode) (v : Tm)
    (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : A n W v)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → Q j U (.fnObj h.length code)) :
    Safe Ξ Q n W h (.makeFn code v) :=
  make_fields_rule (As := [A]) (by intro B hB; rw [List.mem_singleton.mp hB]; exact hA)
    (by intro B hB; rw [List.mem_singleton.mp hB]; exact hV) n W h code
    [codeField] [v] (by simp) rfl rfl
    (by intro u hu; rw [List.mem_singleton.mp hu]; exact hval) hadm hok
    (by intro p hp; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp; exact hv)
    (fun j hj U hx _ => result j hj U hx)

/-- **A literal allocates a store.** One fresh location per element, each
under its family, and the store meets the claimed tuple contract by
`listT_alloc`; the continuation sees it at the extended world. The allocation
is a step, so the elements need their families below the budget only. -/
theorem arr_alloc_rule_below {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (vs : List Val)
    (hAs : As.length = vs.length) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, ∀ (j : Nat) (hj : j < n), p.1 j (trunc j (Nat.le_of_lt hj) W) p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      (∀ (i : Nat) (hi : i < As.length), lookup U (h.length + i) = some (res (As[i]'hi))) →
      Q j U (.arr (elemSlots h.length vs.length))) :
    Safe Ξ Q n W h (.arrLit vs) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : ∀ c ∈ As.map (fun A => (res A : Ctr p)), CtrAdm c := by
      intro c hc
      obtain ⟨A, hA', rfl⟩ := List.mem_map.mp hc
      exact ⟨fun i _ U U' hx w hw => (hA A hA').mono i U U' hx w hw, fun i _ U w hw => hV A hA' i U w hw⟩
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ q ∈ (As.map (fun A => (res A : Ctr p))).zip vs, ∀ (j : Nat) (hj : j < p),
        q.1 j hj (trunc j (Nat.le_of_lt hj) (trunc p (Nat.le_succ p) W)) q.2 := by
      rw [List.zip_map_left]
      rintro q hq j hj
      obtain ⟨⟨A, v⟩, hm, rfl⟩ := List.mem_map.mp hq
      show A j _ v
      rw [trunc_trunc]
      exact hv (A, v) hm j (by omega)
    refine Or.inr ⟨appendWs (trunc p (Nat.le_succ p) W) (As.map (fun A => (res A : Ctr p))),
      h ++ vs, .arr (elemSlots h.length vs.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .arrAlloc hvals,
      heap_allocs p _ (trunc p (Nat.le_succ p) W) h vs (HeapOk_trunc p W h hok)
        (WorldAdm_trunc _ hadm) hcadm (by simp [hAs]) hcont, ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl (Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩)
      intro i hi
      have hib : i < (As.map (fun A => (res A : Ctr (q + 1)))).length := by
        simp; omega
      have := lookup_appendWs (trunc (q + 1) (Nat.le_succ (q + 1)) W)
        (As.map (fun A => (res A : Ctr (q + 1)))) hib
      rw [← hlen] at this
      rw [this]
      simp [List.getElem?_map, List.getElem?_eq_getElem hi]

theorem arr_alloc_rule {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (vs : List Val)
    (hAs : As.length = vs.length) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, p.1 n W p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      (∀ (i : Nat) (hi : i < As.length), lookup U (h.length + i) = some (res (As[i]'hi))) →
      Q j U (.arr (elemSlots h.length vs.length))) :
    Safe Ξ Q n W h (.arrLit vs) :=
  arr_alloc_rule_below hA hV n W h vs hAs hvals hadm hok
    (fun p hp j hj => (hA p.1 (List.of_mem_zip hp).1).down_le n j (Nat.le_of_lt hj) W p.2 (hv p hp))
    result

/-- **An element read.** The index names a location; its contract implies
the family, which is all the read observes. -/
theorem elem_read_rule {ls : List (Option Nat)} {b : UInt64} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hl : elemLoc ls b = some l)
    {c : Ctr n} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u) :
    Safe Ξ A n W h (.elemAt (.arr ls) (.num b)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hc
    have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .elemRead hl hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl (Or.inl ⟨hA _ _ _ hAv, hAv⟩)

/-- **An absent element reads `undefined`.** -/
theorem elem_absent_rule {ls : List (Option Nat)} {b : UInt64} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hn : elemLoc ls b = none) (hq : ∀ m (U : WorldT m), Q m U .undef) :
    Safe Ξ Q n W h (.elemAt (.arr ls) (.num b)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _, WorldAdm_trunc _ hadm,
      .elemAbsent hn, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ rfl (hq _ _)

/-- **A write to a present element.** As a field write: the location's contract
admits the value, and the store, unchanged, is what the write yields. -/
theorem set_present_rule {ls : List (Option Nat)} {b : UInt64} {A Q : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hl : elemLoc ls b = some l) {c : Ctr n} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) (hq : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → Q j U (.arr ls)) :
    Safe Ξ Q n W h (.setElem (.arr ls) (.num b) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.2 l c hc
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .arr ls, WExt_refl _,
      WorldAdm_trunc _ hadm, .setPresent hval hl hlt, ?_, ?_⟩
    · refine write_sound p _ h l _ v (HeapOk_trunc p W h hok)
        (lookup_trunc (Nat.le_succ p) W l c hc) ?_
      intro i hi
      show c i _ _ v
      refine (hag i (by omega) _ v).mpr ?_
      have := hA.down_le (p + 1) i (by omega) W v hv
      rw [trunc_trunc]
      exact this
    · exact value_safe _ _ _ _ _ rfl (hq p (by omega) _ (WExt_refl _))

/-- **A write that grows the store.** A fresh location under the position's
family takes the value; the store the write yields records it. -/
theorem set_grow_rule {ls : List (Option Nat)} {b : UInt64} {k : Nat} {A Q : Fam}
    (hA : Adm A) (hV : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hk : indexOfBits b = some k) (hn : elemLoc ls b = none) (hv : A n W v)
    (hq : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      lookup U h.length = some (res A) → Q j U (.arr (placeAt ls k h.length))) :
    Safe Ξ Q n W h (.setElem (.arr ls) (.num b) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : ∀ c ∈ [(res A : Ctr p)], CtrAdm c := by
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact ⟨fun i _ U U' hx w hw => hA.mono i U U' hx w hw, fun i _ U w hw => hV i U w hw⟩
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ q ∈ [(res A : Ctr p)].zip [v], ∀ (j : Nat) (hj : j < p),
        q.1 j hj (trunc j (Nat.le_of_lt hj) (trunc p (Nat.le_succ p) W)) q.2 := by
      intro q hq j hj
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
      subst hq
      show A j _ v
      rw [trunc_trunc]
      exact hA.down_le (p + 1) j (by omega) W v hv
    refine Or.inr ⟨appendWs (trunc p (Nat.le_succ p) W) [res A], h ++ [v], .arr (placeAt ls k h.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .setGrow hval hk hn,
      heap_allocs p _ (trunc p (Nat.le_succ p) W) h [v] (HeapOk_trunc p W h hok)
        (WorldAdm_trunc _ hadm) hcadm rfl hcont, ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl (Or.inl ⟨rfl, hq (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩)
      rw [hlen]
      have := lookup_appendWs (trunc (q + 1) (Nat.le_succ (q + 1)) W) [(res A : Ctr (q + 1))]
        (i := 0) (by simp)
      simpa using this

/-- **A length read** is a number. -/
theorem len_rule {ls : List (Option Nat)} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hq : ∀ m (U : WorldT m), Q m U (.num (bitsOfNat ls.length))) :
    Safe Ξ Q n W h (.lenOf (.arr ls)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
      .lenV, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ rfl (hq _ _)

/-- **A string's length** is a number. -/
theorem len_str_rule {s : String} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hq : ∀ m (U : WorldT m), Q m U (.num (bitsOfNat (utf16Units s).length))) :
    Safe Ξ Q n W h (.lenOf (.str s)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
      .lenStr, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ rfl (hq _ _)

/-- **A string's index property** is a one-code-unit string or `undefined`. -/
theorem elem_str_rule {s : String} {b : UInt64} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hstr : ∀ m (U : WorldT m) (t : String), Q m U (.str t)) (hundef : ∀ m (U : WorldT m), Q m U .undef) :
    Safe Ξ Q n W h (.elemAt (.str s) (.num b)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
      .elemStr, HeapOk_trunc p W h hok, ?_⟩
    unfold codeUnitAt
    split
    · exact value_safe _ _ _ _ _ rfl (hstr _ _ _)
    · exact value_safe _ _ _ _ _ rfl (hundef _ _)


/-! ## Testing a value's shape, and branching on the answer

The two constructs a narrowing source language needs. A test of a value answers
in one step; a branch on that answer takes one more. Both are ordinary reduction
steps, so each spends a budget, which is why the rule below starts two above the
budget its branches are checked at. -/

/-- **A shape test answers.** -/
theorem test_value_safe (k : Tag) (v : Val) (hv : isVal v = true) (p : Nat)
    (W : WorldT (p + 1)) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) :
    Safe Ξ boolT (p + 1) W h (.test k v) := by
  refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
    .testV hv, HeapOk_trunc p W h hok, ?_⟩
  cases p with
  | zero => trivial
  | succ q =>
    refine Or.inl (Or.inl ⟨?_, ?_⟩) <;> cases tagHoldsIn h k v <;> simp [boolT, isVal]

/-- **An operator that answers is safe.** Where `binop` gives the operands'
result, the term takes one step to it, a value of whatever family `S` names. -/
theorem arith_value_safe {S : Fam} (op : Arith) (a b v : Tm) (hv : binop op a b = some v)
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hr : ∀ m (U : WorldT m), S m U v) :
    Safe Ξ S n W h (.arith op a b) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
      .arithV hv, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ (binop_values hv).2.2 (hr _ _)

/-- **An operator that throws is safe.** Where `binopThrows` holds of the
operands, the term takes one step to throwing a fresh error object, which is
an outcome at every type. -/
theorem arith_throw_safe {S : Fam} (op : Arith) (a b : Tm) (ht : binopThrows op a b = true)
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hΞ : ErrorsIn Ξ) : Safe Ξ S n W h (.arith op a b) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : CtrAdm (res nulT : Ctr p) :=
      ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => by rw [show _ = Tm.nul from h]; rfl⟩
    refine Or.inr ⟨appendW (trunc p (Nat.le_succ p) W) (res nulT), h ++ [.nul], _,
      WExt_appendW _ _, WorldAdm_append (WorldAdm_trunc _ hadm) hcadm, .arithThrow ht,
      heap_alloc p _ h (res nulT) .nul (HeapOk_trunc p W h hok) (WorldAdm_trunc _ hadm)
        (fun _ _ => rfl), ?_⟩
    exact thrown_safe _ _ _ _ ⟨thrownError h.length, .throwV rfl rfl, by simp [thrownError, Scoped], hΞ _ _ _⟩

/-- **Branching on a shape test.** The two branches are checked under the answer
they run in, which is what makes this narrowing rather than a plain conditional:
the `then` branch may assume the test succeeded. -/
theorem ite_test_rule {B : Fam} (k : Tag) (a : Val) (hv : isVal a = true) (u e : Tm)
    (p : Nat) (W : WorldT (p + 2)) (h : Heap) (hadm : WorldAdm W)
    (hok : HeapOk (p + 2) W h)
    (hthen : tagHoldsIn h k a = true → Safe Ξ B p (trunc p (by omega) W) h u)
    (helse : tagHoldsIn h k a = false → Safe Ξ B p (trunc p (by omega) W) h e) :
    Safe Ξ B (p + 2) W h (.ite (.test k a) u e) := by
  refine Or.inr ⟨trunc (p + 1) (Nat.le_succ _) W, h, _, WExt_refl _,
    WorldAdm_trunc _ hadm, .iteC (.testV hv), HeapOk_trunc (p + 1) W h hok, ?_⟩
  have hadm' : WorldAdm (trunc (p + 1) (Nat.le_succ _) W) := WorldAdm_trunc _ hadm
  have hok' : HeapOk (p + 1) (trunc (p + 1) (Nat.le_succ _) W) h := HeapOk_trunc (p + 1) W h hok
  cases hb : tagHoldsIn h k a with
  | true =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) _, h, u, WExt_refl _, WorldAdm_trunc _ hadm',
      by simp; exact Step.iteT, HeapOk_trunc p _ h hok', ?_⟩
    rw [trunc_trunc]
    exact hthen hb
  | false =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) _, h, e, WExt_refl _, WorldAdm_trunc _ hadm',
      by simp; exact Step.iteF, HeapOk_trunc p _ h hok', ?_⟩
    rw [trunc_trunc]
    exact helse hb


#print axioms let_rule

end Verification
