import Verification.Semantics.Rules
import Verification.Types.ReferenceConjunctions
/-!
# Callable objects and their bags

A bag invariant forgets the call slot without changing the value: a callable
object's fields are read and written as a record's, whatever its code. The
positive graph exposes combined callable/property contracts through
`CallableConjunctions` and its `callable` clause.
-/
namespace Verification

/-- A writable bag invariant independent of the object's call slot. The plain
object in `recT` is only a semantic projection, never an allocation or coercion. -/
def bagT (P : Fields) : Fam := fun n W v =>
  ∃ flds code oid, v = .objAt flds code oid ∧ isVal v = true ∧ recT P n W (.objAt flds .absent oid)

theorem bagT_adm (P : Fields) : Adm (bagT P) := by
  constructor
  · rintro n W v ⟨l, code, oid, hv, hval, hr⟩
    exact ⟨l, code, oid, hv, hval, (recT_adm P).down n W _ hr⟩
  · rintro n W W' hx v ⟨l, code, oid, hv, hval, hr⟩
    exact ⟨l, code, oid, hv, hval, (recT_adm P).mono n W W' hx _ hr⟩

theorem bagT_contractive {ι : Type} (X Y : ι → Fam) (fs : List (Stored ι)) (n : Nat)
    (hag : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    bagT (ReferenceConjunctions.famsOf X fs) n W v ↔
      bagT (ReferenceConjunctions.famsOf Y fs) n W v := by
  constructor <;> rintro ⟨l, code, oid, hv, hval, hr⟩ <;> refine ⟨l, code, oid, hv, hval, ?_⟩
  · exact (ReferenceConjunctions.recT_congr_below X Y fs n hag W _).mp hr
  · exact (ReferenceConjunctions.recT_congr_below X Y fs n hag W _).mpr hr

theorem recT_bag {P : Fields} {n W v} (h : recT P n W v) : bagT P n W v := by
  obtain ⟨flds, oid, rfl, hr⟩ := h
  exact ⟨flds, .absent, oid, rfl, rfl, flds, oid, rfl, hr⟩

theorem bag_read {fs : Fields} {f : PropKey} {s : StorageRole} {P : Fam} (hP : ValOnly P)
    (hm : (f, s, P) ∈ fs) {n W h v}
    (hv : bagT fs n W v) (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (.readAt f v)) :
    Safe Ξ P n W h (.readAt f v) := by
  obtain ⟨flds, code, oid, rfl, _, hr⟩ := hv
  obtain ⟨flds', l, c, oid', he, hf, hl, hc⟩ := recT_at hm hr
  cases he
  exact read_rule (code := code) hP n W h l hw hh hf hl hc href

theorem bag_write {fs : Fields} {f : PropKey} {s : StorageRole} {P : Fam} (hP : Adm P)
    (hm : (f, s, P) ∈ fs) {n W h v a}
    (hv : bagT fs n W v) (ha : P n W a) (hval : isVal a = true)
    (hw : WorldAdm W) (hh : HeapOk n W h) (hs : s ≠ .viewStore) (hsrc : s.Holds a)
    (href : RefsOk W (.writeAt f v a)) :
    Safe Ξ nulT n W h (.writeAt f v a) := by
  obtain ⟨flds, code, oid, rfl, _, hr⟩ := hv
  obtain ⟨flds', l, c, oid', he, hf, hl, hc⟩ := recT_at hm hr
  cases he
  exact write_rule (code := code) hP n W h l a hval hw hh hf hl hc ha
    ((recT_role hm hr hf).cat hs hsrc) href

end Verification
