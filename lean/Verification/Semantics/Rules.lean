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
    (hw : WorldAdm W) (hh : HeapOk n W heap) (href : RefsOk W (.invoke f r args)) :
    Safe Ξ p.2.2 n W heap (.invoke f r args) := by
  exact ArgumentContracts.call_safe
    (P := ArgsShort p.2.1)
    (Adm.of_transfer (fun ha j hj U hx => ArgsShort_transfer hA ha j hj U hx)) hR
    ⟨hf.1, hf.2 p hp⟩ hr hrv
    (fun a hm => ArgsT_values hAv ha a (List.mem_append_left pad hm))
    (ArgsShort_of_pad hpad ha) hw hh href

/-- A binding consumes one step after its initializer has become a value. -/
theorem let_rule {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) (href : RefsOk W (.letE a b))
    (hb : Safe Ξ B p (trunc p (Nat.le_succ p) W) h (subst 0 a b)) :
    Safe Ξ B (p + 1) W h (.letE a b) :=
  ⟨href, Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .letV hval,
    HeapOk_trunc p W h hok, hb⟩⟩

/-- **A step that changes no heap**, to a term safe one level down at the
truncated world. -/
theorem pure_step {B : Fam} {p : Nat} {W : WorldT (p + 1)} {h : Heap} {t t' : Tm}
    (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) (href : RefsOk W t) (st : Step h t h t')
    (hs : Safe Ξ B p (trunc p (Nat.le_succ p) W) h t') : Safe Ξ B (p + 1) W h t :=
  ⟨href, Or.inr ⟨_, h, t', WExt_refl _, WorldAdm_trunc _ hadm, st, HeapOk_trunc p W h hok, hs⟩⟩

/-- **A read of a well-formed heap's location** yields a value whose
references are valid, at the truncated world. -/
theorem read_value_refs {p : Nat} {W : WorldT (p + 1)} {h : Heap} (hok : HeapOk (p + 1) W h)
    {l : Nat} {v : Val} (hv : h[l]? = some v) : RefsOk (trunc p (Nat.le_succ p) W) v :=
  RefsOk_trunc _ (hok.refs_at hv)

/-! ## Storage -/


/-- **Read.** -/
theorem read_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (href : RefsOk W (.readAt f (.objAt flds code oid))) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.1.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := (hag p (by omega) _ v).mp (hmem p (by omega))
    exact pure_step hadm hok href (.readField hf hv)
      (value_safe _ _ _ _ _ (hA _ _ _ hAv) hAv (read_value_refs hok hv))

/-- **Read through a view.** The location's contract implies the stated family,
which is all a read observes. -/
theorem read_view_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u)
    (href : RefsOk W (.readAt f (.objAt flds code oid))) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.1.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
    exact pure_step hadm hok href (.readField hf hv)
      (value_safe _ _ _ _ _ (hA _ _ _ hAv) hAv (read_value_refs hok hv))

/-- A read whose location's contract implies `A` only in worlds extending the
current one: the read happens in the current world, so that is all it needs. -/
theorem read_view_rule_ext {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ (u : Val), c j hj U u → A j U u)
    (href : RefsOk W (.readAt f (.objAt flds code oid))) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.1.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v :=
      hag p (by omega) _ (WExt_refl _) v (hmem p (by omega))
    exact pure_step hadm hok href (.readField hf hv)
      (value_safe _ _ _ _ _ (hA _ _ _ hAv) hAv (read_value_refs hok hv))

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
      ∀ u, P j U u → RefsOk U u → Safe Ξ A j U h' (.readAt f u))
    (href : RefsOk W (.readAt f (.objAt flds code oid))) :
    Safe Ξ A n W h (.readAt f (.objAt flds code oid)) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨pv, hpv, hmem⟩ := hok.1.2 l c hl
    exact pure_step hadm hok href (.readProto hmiss hpf hpv)
      (hP p _ h (WorldAdm_trunc _ hadm) (HeapOk_trunc p W h hok) pv
        (hag p (by omega) _ pv (hmem p (by omega))) (read_value_refs hok hpv))

/-- An index view covers every present field under a key its class admits,
while a missing key reads `undefined`. A lookup cannot discard that
alternative. -/
theorem read_dict_rule {flds : List (PropKey × Nat)} {f : PropKey} {K : IndexKeys} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hk : K.Admits f)
    (hd : dictViewT K A n W (.objAt flds .absent oid))
    (href : RefsOk W (.readAt f (.objAt flds .absent oid))) :
    Safe Ξ (unionT A undefT) n W h (.readAt f (.objAt flds .absent oid)) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := dictViewT_present hd hk hlook
    apply Safe_mono n (fun _ _ _ _ ha => Or.inl ha) W h _
      (read_view_rule hA n W h l hadm hok hlook hc hag href)
  | none =>
    cases n with
    | zero => exact href
    | succ p =>
      exact pure_step hadm hok href (.readMissing hlook (dictViewT_no_proto hd))
        (value_safe _ _ _ _ _ rfl (Or.inr rfl) RefsOk_undef)

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
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u)
    (href : RefsOk W (.readAt f (.objAt flds .absent oid))) :
    Safe Ξ (unionT A undefT) n W h (.readAt f (.objAt flds .absent oid)) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := ho l hlook
    apply Safe_mono n (fun _ _ _ _ ha => Or.inl ha) W h _
      (read_view_rule hA n W h l hadm hok hlook hc hag href)
  | none =>
    cases n with
    | zero => exact href
    | succ p =>
      exact pure_step hadm hok href (.readMissing hlook (hp hlook))
        (value_safe _ _ _ _ _ rfl (Or.inr rfl) RefsOk_undef)

/-- The same guarantee when the key was evaluated at runtime: a value whose
`ToPropertyKey` (`propertyKey`) the index's class admits. The caller must
separately prove the key's value is one. -/
theorem index_dict_rule {flds : List (PropKey × Nat)} {key : Tm} {f : PropKey} {K : IndexKeys}
    {A : Fam} (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hkey : propertyKey key = some f) (hk : K.Admits f)
    (hd : dictViewT K A n W (.objAt flds .absent oid))
    (href : RefsOk W (.indexAt (.objAt flds .absent oid) key)) :
    Safe Ξ (unionT A undefT) n W h (.indexAt (.objAt flds .absent oid) key) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := dictViewT_present hd hk hlook
    cases n with
    | zero => exact href
    | succ p =>
      obtain ⟨v, hv, hmem⟩ := hok.1.2 l c hc
      have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
      exact pure_step hadm hok href (.indexField hkey hlook hv)
        (value_safe _ _ _ _ _ (hA _ _ _ hAv) (Or.inl hAv) (read_value_refs hok hv))
  | none =>
    cases n with
    | zero => exact href
    | succ p =>
      exact pure_step hadm hok href (.indexMissing hkey hlook (dictViewT_no_proto hd))
        (value_safe _ _ _ _ _ rfl (Or.inr rfl) RefsOk_undef)

/-- **Write.** -/
theorem write_rule {code : CallCode} {flds : List (PropKey × Nat)} {f : PropKey} {A : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) (hcat : ∀ r, roleAt W l = some r → Cat r v)
    (href : RefsOk W (.writeAt f (.objAt flds code oid) v)) :
    Safe Ξ nulT n W h (.writeAt f (.objAt flds code oid) v) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.1.2 l c hl
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    have hsh := Kinds.writeField_shaped (HeapOk_trunc p W h hok).2 (RefsOk_trunc _ href) hf
      (fun r hr => hcat r (by simpa using hr))
    refine ⟨href, Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .nul, WExt_refl _,
      WorldAdm_trunc _ hadm, .writeField hval hf hlt, ⟨?_, hsh.1⟩, Safe_nul p _ _⟩⟩
    refine ⟨by simpa using (HeapOk_trunc p W h hok).1.1, fun k d hk => ?_⟩
    by_cases hkl : k = l
    · subst hkl
      rw [lookup_trunc (Nat.le_succ p) W k c hl] at hk; cases hk
      refine ⟨v, by simp [hlt], fun i hi => ?_⟩
      show c i _ _ v
      refine (hag i (by omega) _ v).mpr ?_
      have := hA.down_le (p + 1) i (by omega) W v hv
      rw [trunc_trunc]
      exact this
    · obtain ⟨w', hw', hmem⟩ := (HeapOk_trunc p W h hok).1.2 k d hk
      exact ⟨w', by rwa [List.getElem?_set_ne (fun hc => hkl hc.symm)], hmem⟩

/-- **Allocating an object with named fields.** One step takes one fresh
location per field, so the world grows by one contract per field and the result
sees the whole record. The single-cell rule above is the one-field case. -/
theorem make_fields_rule {Q : Fam} {ss : List StorageRole} {As : List Fam}
    (hss : ss.length = As.length) (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List PropKey) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, p.1 n W p.2)
    (hhold : ∀ (i : Nat) (s : StorageRole) (v : Val), ss[i]? = some s → vs[i]? = some v → s.Holds v)
    (hfits : ∀ (i : Nat) (s : StorageRole), ss[i]? = some s → ∀ key : PropKey, ns[i]? = some key → s.fitsKey key = true)
    (hmeta : ∀ (k : Nat) (rs : List Role), Kinds.concreteRoles ss vs = some rs → Kinds.MetaFit ns rs (As.map (fun A => (res A : Ctr k))))
    (href : RefsOk W (.makeAt code ns vs))
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip (ss.zip As)) j U (.objAt (slots h.length ns) .absent (h.length + vs.length)) →
      Q j U (.objAt (slots h.length ns) code (h.length + vs.length))) :
    Safe Ξ Q n W h (.makeAt code ns vs) :=
  OperationWorlds.erase n W h (.makeAt code ns vs)
    (AllocationWorlds.allocation_safe hss hA hV n W h code ns vs hnd hns hAs hvals hadm hok
      (fun p hp j _ => (hA p.1 (List.of_mem_zip hp).1).down_le n j (by omega) W p.2 (hv p hp))
      hhold hfits hmeta href result)

/-- **Allocating named fields, from values known below the level.** The
allocation step spends a level, so each value need meet its family only at
the levels the heap is judged at after it. -/
theorem make_fields_rule_below {Q : Fam} {ss : List StorageRole} {As : List Fam}
    (hss : ss.length = As.length) (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List PropKey) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, ∀ (j : Nat) (hj : j + 1 < n), p.1 j (trunc j (by omega) W) p.2)
    (hhold : ∀ (i : Nat) (s : StorageRole) (v : Val), ss[i]? = some s → vs[i]? = some v → s.Holds v)
    (hfits : ∀ (i : Nat) (s : StorageRole), ss[i]? = some s → ∀ key : PropKey, ns[i]? = some key → s.fitsKey key = true)
    (hmeta : ∀ (k : Nat) (rs : List Role), Kinds.concreteRoles ss vs = some rs → Kinds.MetaFit ns rs (As.map (fun A => (res A : Ctr k))))
    (href : RefsOk W (.makeAt code ns vs))
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip (ss.zip As)) j U (.objAt (slots h.length ns) .absent (h.length + vs.length)) →
      Q j U (.objAt (slots h.length ns) code (h.length + vs.length))) :
    Safe Ξ Q n W h (.makeAt code ns vs) :=
  OperationWorlds.erase n W h (.makeAt code ns vs)
    (AllocationWorlds.allocation_safe hss hA hV n W h code ns vs hnd hns hAs hvals hadm hok hv
      hhold hfits hmeta href result)

/-- **Allocating an object with no named field**, as `.bind` does: the
result meets `Q` at whatever identity the allocation gives it. -/
theorem make_empty_rule {Q : Fam} (hQ : Adm Q) (n : Nat) (W : WorldT n) (h : Heap)
    (code : CallCode) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ oid, Q n W (.objAt [] code oid)) (href : RefsOk W (.makeAt code [] [])) :
    Safe Ξ Q n W h (.makeAt code [] []) :=
  make_fields_rule (ss := []) (As := []) rfl (fun _ h => by simp at h) (fun _ h => by simp at h) n W h code [] [] List.nodup_nil rfl rfl
    (by simp) hadm hok (by simp) (fun _ _ _ h => by simp at h) (fun _ _ h => by simp at h)
    (fun _ _ _ => Kinds.MetaFit.of_not_mem (by simp) (by simp)) href fun j hj U hx _ =>
      hQ.mono j _ U hx _ (hQ.down_le n j (Nat.le_of_lt hj) W _ (hv _))

/-- **Creating a function object.** Its one field, which gives it a location
and so an identity, holds the value; the result obligation supplies the view
of the fresh object its code gives. -/
theorem makeFn_rule {A Q : Fam} (hA : Adm A) (hV : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode) (v : Tm)
    (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : A n W v)
    (hsrc : isSourceVal v = true) (href : RefsOk W (.makeFn code v))
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → Q j U (.fnObj h.length code)) :
    Safe Ξ Q n W h (.makeFn code v) :=
  make_fields_rule (ss := [.field]) (As := [A]) rfl (by intro B hB; rw [List.mem_singleton.mp hB]; exact hA)
    (by intro B hB; rw [List.mem_singleton.mp hB]; exact hV) n W h code
    [codeField] [v] (by simp) rfl rfl
    (by intro u hu; rw [List.mem_singleton.mp hu]; exact hval) hadm hok
    (by intro p hp; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp; exact hv)
    (fun i s u hs hu => by
      cases i with
      | zero => simp at hs hu; subst hs hu; exact hsrc
      | succ i => simp at hs)
    (fun i s hs key hk => by
      cases i with
      | zero => simp at hs hk; subst hs hk; decide
      | succ i => simp at hs)
    (fun _ _ _ => Kinds.MetaFit.of_not_mem (by decide) (by decide)) href
    (fun j hj U hx _ => result j hj U hx)

/-- **A literal allocates a store.** One fresh location per element, each
under its family and the role of an element cell, and the store meets the
claimed tuple contract by `listT_alloc`; the continuation sees it at the
extended world. The allocation is a step, so the elements need their
families below the budget only. Each element is a source value (its
payload's category) with valid references. -/
theorem arr_alloc_rule_below {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (vs : List Val)
    (hAs : As.length = vs.length) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hΞ : ErrorsIn Ξ)
    (hv : ∀ p ∈ As.zip vs, ∀ (j : Nat) (hj : j < n), p.1 j (trunc j (Nat.le_of_lt hj) W) p.2)
    (hsrc : ∀ v ∈ vs, isSourceVal v = true) (href : RefsOk W (.arrLit vs))
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      (∀ (i : Nat) (hi : i < As.length), lookup U (h.length + i) = some (res (As[i]'hi))) →
      vs.length ≤ maxArrayLength →
      Q j U (.arr (elemSlots h.length vs.length))) :
    Safe Ξ Q n W h (.arrLit vs) := by
  cases n with
  | zero => exact href
  | succ p =>
    by_cases hmax : vs.length ≤ maxArrayLength
    case neg =>
      obtain ⟨hadm', hok', hr'⟩ := (HeapOk_trunc p W h hok).error (WorldAdm_trunc _ hadm)
      refine ⟨href, Or.inr ⟨_, h ++ [.nul], _,
        WExt_appendW _ _ _, hadm', .arrAllocThrow hvals (by omega), hok', ?_⟩⟩
      exact thrown_safe _ _ _ _ ⟨thrownError h.length, .throwV rfl rfl, by simp [thrownError, Scoped], hΞ _ _ _⟩ hr'
    let cs : List (Ctr p) := As.map (fun A => (res A : Ctr p))
    let W₀ := trunc p (Nat.le_succ p) W
    let es := (vs.map fun _ => Role.elem).zip cs
    have hcadm : ∀ e ∈ es, CtrAdm e.2 := by
      intro e he
      have h2 : e.2 ∈ cs := (List.of_mem_zip he).2
      obtain ⟨A, hA', he2⟩ := List.mem_map.mp h2
      rw [← he2]
      exact ⟨fun i _ U U' hx w hw => (hA A hA').mono i U U' hx w hw, fun i _ U w hw => hV A hA' i U w hw⟩
    have hlen : h.length = (entries W₀).length := by
      have := hok.1.1; simp [W₀] at this ⊢; omega
    have hsnd : es.map Prod.snd = cs := by simp [es, cs, List.map_snd_zip, hAs]
    have hsh := Kinds.arrAlloc_shaped (W := W₀) cs hlen (Shaped_trunc _ hok.2) (by simp [cs, hAs])
      (RefsOk_trunc _ href) hsrc
    have hmeets : HeapMeets p (appendWs W₀ es) (h ++ vs) := by
      refine HeapMeets_appendWs (HeapOk_trunc p W h hok).1 (WorldAdm_trunc _ hadm) hcadm
        (by simp [es, cs, hAs]) ?_
      intro i c v hc hv' j hj
      rw [hsnd] at hc
      simp only [cs, List.getElem?_map] at hc
      obtain ⟨A, hAi, rfl⟩ := Option.map_eq_some_iff.mp hc
      show A j _ v
      rw [trunc_trunc]
      exact hv (A, v) (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨hAi, hv'⟩⟩) j (by omega)
    refine ⟨href, Or.inr ⟨appendWs W₀ es, h ++ vs, .arr (elemSlots h.length vs.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .arrAlloc hvals hmax, ⟨hmeets, hsh.1⟩, ?_⟩⟩
    cases p with
    | zero => exact hsh.2
    | succ q =>
      refine ⟨hsh.2, Or.inl (Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendWs _ _) ?_ hmax⟩)⟩
      intro i hi
      rw [hlen, lookup_appendWs_ge, hsnd]
      simp [cs, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem arr_alloc_rule {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (vs : List Val)
    (hAs : As.length = vs.length) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hΞ : ErrorsIn Ξ)
    (hv : ∀ p ∈ As.zip vs, p.1 n W p.2)
    (hsrc : ∀ v ∈ vs, isSourceVal v = true) (href : RefsOk W (.arrLit vs))
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      (∀ (i : Nat) (hi : i < As.length), lookup U (h.length + i) = some (res (As[i]'hi))) →
      vs.length ≤ maxArrayLength →
      Q j U (.arr (elemSlots h.length vs.length))) :
    Safe Ξ Q n W h (.arrLit vs) :=
  arr_alloc_rule_below hA hV n W h vs hAs hvals hadm hok hΞ
    (fun p hp j hj => (hA p.1 (List.of_mem_zip hp).1).down_le n j (Nat.le_of_lt hj) W p.2 (hv p hp))
    hsrc href result

/-- **An element read.** The index names a location; its contract implies
the family, which is all the read observes. -/
theorem elem_read_rule {ls : List (Option Nat)} {b : UInt64} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hl : elemLoc ls b = some l)
    {c : Ctr n} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u)
    (href : RefsOk W (.elemAt (.arr ls) (.num b))) :
    Safe Ξ A n W h (.elemAt (.arr ls) (.num b)) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.1.2 l c hc
    have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
    exact pure_step hadm hok href (.elemRead hl hv)
      (value_safe _ _ _ _ _ (hA _ _ _ hAv) hAv (read_value_refs hok hv))

/-- **An absent element reads `undefined`.** -/
theorem elem_absent_rule {ls : List (Option Nat)} {b : UInt64} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hn : elemLoc ls b = none) (hq : ∀ m (U : WorldT m), Q m U .undef)
    (href : RefsOk W (.elemAt (.arr ls) (.num b))) :
    Safe Ξ Q n W h (.elemAt (.arr ls) (.num b)) := by
  cases n with
  | zero => exact href
  | succ p =>
    exact pure_step hadm hok href (.elemAbsent hn) (value_safe _ _ _ _ _ rfl (hq _ _) RefsOk_undef)

/-- **A write to a present element.** As a field write: the location's contract
admits the value, and the store, unchanged, is what the write yields. The
location is an element cell, so the value is a source value. -/
theorem set_present_rule {ls : List (Option Nat)} {b : UInt64} {A Q : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hl : elemLoc ls b = some l) {c : Ctr n} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) (hq : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → Q j U (.arr ls))
    (hsrc : isSourceVal v = true) (href : RefsOk W (.setElem (.arr ls) (.num b) v)) :
    Safe Ξ Q n W h (.setElem (.arr ls) (.num b) v) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.1.2 l c hc
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    have hsh := Kinds.setPresent_shaped (HeapOk_trunc p W h hok).2 (RefsOk_trunc _ href) hl hsrc
    refine ⟨href, Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .arr ls, WExt_refl _,
      WorldAdm_trunc _ hadm, .setPresent hval hl hlt, ⟨?_, hsh.1⟩, ?_⟩⟩
    · refine ⟨by simpa using (HeapOk_trunc p W h hok).1.1, fun k d hk => ?_⟩
      by_cases hkl : k = l
      · subst hkl
        rw [lookup_trunc (Nat.le_succ p) W k c hc] at hk; cases hk
        refine ⟨v, by simp [hlt], fun i hi => ?_⟩
        show c i _ _ v
        refine (hag i (by omega) _ v).mpr ?_
        have := hA.down_le (p + 1) i (by omega) W v hv
        rw [trunc_trunc]
        exact this
      · obtain ⟨w', hw', hmem⟩ := (HeapOk_trunc p W h hok).1.2 k d hk
        exact ⟨w', by rwa [List.getElem?_set_ne (fun hc => hkl hc.symm)], hmem⟩
    · exact value_safe _ _ _ _ _ rfl (hq p (by omega) _ (WExt_refl _)) hsh.2

/-- **A write that grows the store.** A fresh element cell under the
position's family takes the value; the store the write yields records it. -/
theorem set_grow_rule {ls : List (Option Nat)} {b : UInt64} {k : Nat} {A Q : Fam}
    (hA : Adm A) (hV : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hk : indexOfBits b = some k) (hn : elemLoc ls b = none) (hv : A n W v)
    (hq : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      lookup U h.length = some (res A) → Q j U (.arr (placeAt ls k h.length)))
    (hsrc : isSourceVal v = true) (href : RefsOk W (.setElem (.arr ls) (.num b) v)) :
    Safe Ξ Q n W h (.setElem (.arr ls) (.num b) v) := by
  cases n with
  | zero => exact href
  | succ p =>
    let W₀ := trunc p (Nat.le_succ p) W
    have hcadm : ∀ e ∈ [((Role.elem : Role), (res A : Ctr p))], CtrAdm e.2 := by
      intro e he
      simp only [List.mem_singleton] at he; subst he
      exact ⟨fun i _ U U' hx w hw => hA.mono i U U' hx w hw, fun i _ U w hw => hV i U w hw⟩
    have hlen : h.length = (entries W₀).length := by
      have := hok.1.1; simp [W₀] at this ⊢; omega
    have hsh := Kinds.setGrow_shaped (kk := k) (res A : Ctr p) hlen (Shaped_trunc _ hok.2)
      (RefsOk_trunc _ href) hsrc
    have hmeets : HeapMeets p (appendWs W₀ [(.elem, res A)]) (h ++ [v]) := by
      refine HeapMeets_appendWs (HeapOk_trunc p W h hok).1 (WorldAdm_trunc _ hadm) hcadm rfl ?_
      intro i c u hc hu j hj
      obtain rfl : i = 0 := by have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
      simp at hc hu; subst hc hu
      show A j _ v
      rw [trunc_trunc]
      exact hA.down_le (p + 1) j (by omega) W v hv
    refine ⟨href, Or.inr ⟨appendWs W₀ [(.elem, res A)], h ++ [v], .arr (placeAt ls k h.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .setGrow hval hk hn, ⟨hmeets, hsh.1⟩, ?_⟩⟩
    cases p with
    | zero => exact hsh.2
    | succ q =>
      refine ⟨hsh.2, Or.inl (Or.inl ⟨rfl, hq (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩)⟩
      rw [hlen, show (entries W₀).length = (entries W₀).length + 0 from rfl, lookup_appendWs_ge]
      rfl

/-- **A length read** is a number. -/
theorem len_rule {ls : List (Option Nat)} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hq : ∀ m (U : WorldT m), Q m U (.num (bitsOfNat ls.length)))
    (href : RefsOk W (.lenOf (.arr ls))) :
    Safe Ξ Q n W h (.lenOf (.arr ls)) := by
  cases n with
  | zero => exact href
  | succ p =>
    exact pure_step hadm hok href .lenV (value_safe _ _ _ _ _ rfl (hq _ _) (RefsOk_of_nil rfl))

/-- **A string's length** is a number, its count of code units, where that
is at most `maxStringLength`; the length of a longer model string throws a
fresh error object, an outcome at every type. -/
theorem len_str_rule {s : String} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h) (hΞ : ErrorsIn Ξ)
    (hq : (utf16Units s).length ≤ maxStringLength → ∀ m (U : WorldT m), Q m U (.num (bitsOfNat (utf16Units s).length))) :
    Safe Ξ Q n W h (.lenOf (.str s)) := by
  have href : RefsOk W (.lenOf (.str s)) := RefsOk_of_nil rfl
  cases n with
  | zero => exact href
  | succ p =>
    by_cases hl : (utf16Units s).length ≤ maxStringLength
    · exact pure_step hadm hok href (.lenStr hl) (value_safe _ _ _ _ _ rfl (hq hl _ _) (RefsOk_of_nil rfl))
    · obtain ⟨hadm', hok', hr'⟩ := (HeapOk_trunc p W h hok).error (WorldAdm_trunc _ hadm)
      refine ⟨href, Or.inr ⟨_, h ++ [.nul], _,
        WExt_appendW _ _ _, hadm', .lenStrThrow (by omega), hok', ?_⟩⟩
      exact thrown_safe _ _ _ _ ⟨thrownError h.length, .throwV rfl rfl, by simp [thrownError, Scoped], hΞ _ _ _⟩ hr'

/-- **A string's index property** is a one-code-unit string or `undefined`. -/
theorem elem_str_rule {s : String} {b : UInt64} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hstr : ∀ m (U : WorldT m) (t : String), Q m U (.str t)) (hundef : ∀ m (U : WorldT m), Q m U .undef) :
    Safe Ξ Q n W h (.elemAt (.str s) (.num b)) := by
  have href : RefsOk W (.elemAt (.str s) (.num b)) := RefsOk_of_nil rfl
  cases n with
  | zero => exact href
  | succ p =>
    refine pure_step hadm hok href .elemStr ?_
    have hr : RefsOk (trunc p (Nat.le_succ p) W) (codeUnitAt s b) := RefsOk_of_nil (codeUnitAt_refs s b)
    revert hr
    unfold codeUnitAt
    split
    · exact fun hr => value_safe _ _ _ _ _ rfl (hstr _ _ _) hr
    · exact fun hr => value_safe _ _ _ _ _ rfl (hundef _ _) hr


/-! ## Testing a value's shape, and branching on the answer

The two constructs a narrowing source language needs. A test of a value answers
in one step; a branch on that answer takes one more. Both are ordinary reduction
steps, so each spends a budget, which is why the rule below starts two above the
budget its branches are checked at. -/

/-- **A shape test answers.** -/
theorem test_value_safe (k : Tag) (v : Val) (hv : isVal v = true) (p : Nat)
    (W : WorldT (p + 1)) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (href : RefsOk W (.test k v)) :
    Safe Ξ boolT (p + 1) W h (.test k v) := by
  refine pure_step hadm hok href (.testV hv) ?_
  apply value_safe _ _ _ _ _ <;> cases tagHoldsIn h k v <;> simp [boolT, isVal] <;>
    exact RefsOk_of_nil rfl

/-- **An operator that answers is safe.** Where `binop` gives the operands'
result, the term takes one step to it, a value of whatever family `S` names. -/
theorem arith_value_safe {S : Fam} (op : Arith) (a b v : Tm) (hv : binop op a b = some v)
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hr : ∀ m (U : WorldT m), S m U v) (href : RefsOk W (.arith op a b)) :
    Safe Ξ S n W h (.arith op a b) := by
  cases n with
  | zero => exact href
  | succ p =>
    exact pure_step hadm hok href (.arithV hv)
      (value_safe _ _ _ _ _ (binop_values hv).2.2 (hr _ _) (RefsOk_of_nil (binop_refs hv)))

/-- **An operator that throws is safe.** Where `binopThrows` holds of the
operands, the term takes one step to throwing a fresh error object, which is
an outcome at every type. -/
theorem arith_throw_safe {S : Fam} (op : Arith) (a b : Tm) (ht : binopThrows op a b = true)
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hΞ : ErrorsIn Ξ) (href : RefsOk W (.arith op a b)) : Safe Ξ S n W h (.arith op a b) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨hadm', hok', hr'⟩ := (HeapOk_trunc p W h hok).error (WorldAdm_trunc _ hadm)
    refine ⟨href, Or.inr ⟨_, h ++ [.nul], _,
      WExt_appendW _ _ _, hadm', .arithThrow ht, hok', ?_⟩⟩
    exact thrown_safe _ _ _ _ ⟨thrownError h.length, .throwV rfl rfl, by simp [thrownError, Scoped], hΞ _ _ _⟩ hr'

/-- **Branching on a shape test.** The two branches are checked under the answer
they run in, which is what makes this narrowing rather than a plain conditional:
the `then` branch may assume the test succeeded. -/
theorem ite_test_rule {B : Fam} (k : Tag) (a : Val) (hv : isVal a = true) (u e : Tm)
    (p : Nat) (W : WorldT (p + 2)) (h : Heap) (hadm : WorldAdm W)
    (hok : HeapOk (p + 2) W h) (href : RefsOk W (.ite (.test k a) u e))
    (hthen : tagHoldsIn h k a = true → Safe Ξ B p (trunc p (by omega) W) h u)
    (helse : tagHoldsIn h k a = false → Safe Ξ B p (trunc p (by omega) W) h e) :
    Safe Ξ B (p + 2) W h (.ite (.test k a) u e) := by
  have hadm' : WorldAdm (trunc (p + 1) (Nat.le_succ _) W) := WorldAdm_trunc _ hadm
  have hok' : HeapOk (p + 1) (trunc (p + 1) (Nat.le_succ _) W) h := HeapOk_trunc (p + 1) W h hok
  have hrefs : ∀ (b : Tm), (b = .tru ∨ b = .fls) →
      RefsOk (trunc (p + 1) (Nat.le_succ _) W) (.ite b u e) := by
    intro b hb r hr
    apply RefsOk_trunc _ href r
    rcases hb with rfl | rfl <;> simp only [refs, List.nil_append, List.mem_append] at hr ⊢ <;>
      rcases hr with hr | hr
    all_goals first | exact .inl (.inr hr) | exact .inr hr
  refine pure_step hadm hok href (.iteC (.testV hv)) ?_
  cases hb : tagHoldsIn h k a with
  | true =>
    refine pure_step hadm' hok' (by simpa using hrefs .tru (.inl rfl)) (by simp; exact Step.iteT) ?_
    rw [trunc_trunc]
    exact hthen hb
  | false =>
    refine pure_step hadm' hok' (by simpa using hrefs .fls (.inr rfl)) (by simp; exact Step.iteF) ?_
    rw [trunc_trunc]
    exact helse hb


end Verification
