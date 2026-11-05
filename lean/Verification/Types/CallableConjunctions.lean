import Verification.Types.ReferenceConjunctions
import Verification.Programs.CallableObjects
import Verification.Semantics.CallEffects

/-! Nonempty bag conjunctions and overloads on one callable value. Invariant
operands remain separate, including at budget zero; normalization must not
replace incompatible operands by bottom. -/
namespace Verification.CallableConjunctions
open CallEffects

def propsT (A : Fields) (Bs : List Fields) : Fam := fun n W v =>
  bagT A n W v ∧ ∀ B ∈ Bs, bagT B n W v

def objectsT (Ξ : Fam) (A : Fields) (Bs : List Fields) (L : List (Arrow Fam)) : Fam :=
  interT (propsT A Bs) (CallEffects.callsT Ξ L)

/-- Readonly fields of an object whatever its code: views of its own fields,
as a record's (`viewT`) are of a plain object's. -/
def viewsT (vs : Fields) : Fam := fun n W v =>
  ∃ flds code oid, v = .objAt flds code oid ∧ viewT vs n W (.objAt flds .absent oid)

theorem views_adm (vs : Fields) : Adm (viewsT vs) := by
  constructor
  · rintro n W v ⟨flds, code, oid, rfl, h⟩
    exact ⟨flds, code, oid, rfl, (viewT_adm vs).down n W _ h⟩
  · rintro n W U hx v ⟨flds, code, oid, rfl, h⟩
    exact ⟨flds, code, oid, rfl, (viewT_adm vs).mono n W U hx _ h⟩

/-- No view holds of every object value. -/
theorem views_nil {fs : List (PropKey × Nat)} {code : CallCode} {oid n W} :
    viewsT [] n W (.objAt fs code oid) :=
  ⟨fs, code, oid, rfl, fun _ _ h => by simp at h⟩

theorem views_append (vs ws : Fields) {fs : List (PropKey × Nat)} {code : CallCode} {oid n W} :
    viewsT (vs ++ ws) n W (.objAt fs code oid) ↔
      viewsT vs n W (.objAt fs code oid) ∧ viewsT ws n W (.objAt fs code oid) := by
  constructor
  · rintro ⟨flds, code', oid', he, h⟩
    cases he
    exact ⟨⟨_, _, _, rfl, ((viewT_append vs ws n W _).mp h).1⟩, ⟨_, _, _, rfl, ((viewT_append vs ws n W _).mp h).2⟩⟩
  · rintro ⟨⟨flds, code', oid', he, h1⟩, ⟨flds', code'', oid'', he', h2⟩⟩
    cases he; cases he'
    exact ⟨_, _, _, rfl, (viewT_append vs ws n W _).mpr ⟨h1, h2⟩⟩

theorem views_congr_below {α : Type} (X Y : α → Fam) (vs : List (PropKey × α)) (n : Nat)
    (h : ∀ a, Agree (X a) (Y a) n) (W : WorldT n) (v : Val) :
    viewsT (ReferenceConjunctions.famsOf X vs) n W v ↔ viewsT (ReferenceConjunctions.famsOf Y vs) n W v := by
  constructor <;> rintro ⟨flds, code, oid, rfl, hv⟩ <;> refine ⟨flds, code, oid, rfl, ?_⟩
  · exact (ReferenceConjunctions.view_congr_below X Y vs n h W _).mp hv
  · exact (ReferenceConjunctions.view_congr_below X Y vs n h W _).mpr hv

/-- A view's field: its location, whose contract is within the view's. -/
theorem views_at {vs : Fields} {f : PropKey} {A : Fam} (hm : (f, A) ∈ vs) {n W v}
    (h : viewsT vs n W v) :
    ∃ (flds : List (PropKey × Nat)) (code : CallCode) (oid l : Nat) (c : Ctr n),
      v = .objAt flds code oid ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := by
  obtain ⟨flds, code, oid, rfl, hv⟩ := h
  obtain ⟨_, l, c, _, he, hf, hl, hag⟩ := viewT_at hm hv
  cases he
  exact ⟨_, code, _, l, c, rfl, hf, hl, hag⟩

theorem props_merge (A C : Fields) (Bs Ds : List Fields) (n W v) :
    propsT A (Bs ++ C :: Ds) n W v ↔ interT (propsT A Bs) (propsT C Ds) n W v := by
  simp only [propsT, List.mem_append, List.mem_cons, or_imp, forall_and, interT, forall_eq]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩; exact ⟨⟨ha,hb⟩,hc,hd⟩
  · rintro ⟨⟨ha,hb⟩,hc,hd⟩; exact ⟨ha,hb,hc,hd⟩

theorem merge (A C : Fields) (Bs Ds : List Fields) (L M : List (Arrow Fam)) (n W v) :
    objectsT Ξ A (Bs ++ C :: Ds) (L ++ M) n W v ↔
      interT (objectsT Ξ A Bs L) (objectsT Ξ C Ds M) n W v := by
  simp only [objectsT, interT, props_merge, CallEffects.callsT_append]
  exact ⟨fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩,
    fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩⟩

theorem calls_merge (A : Fields) (Bs : List Fields) (L M : List (Arrow Fam)) (n W v) :
    objectsT Ξ A Bs (L ++ M) n W v ↔ interT (objectsT Ξ A Bs L) (CallEffects.callsT Ξ M) n W v := by
  simp only [objectsT, interT, CallEffects.callsT_append]
  exact and_assoc.symm

theorem props_adm (A : Fields) (Bs : List Fields) : Adm (propsT A Bs) := by
  constructor
  · intro n W v h
    exact ⟨(bagT_adm A).down n W v h.1,fun B hb => (bagT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(bagT_adm A).mono n W U hx v h.1,fun B hb => (bagT_adm B).mono n W U hx v (h.2 B hb)⟩

theorem adm (A : Fields) (Bs : List Fields) (L : List (Arrow Fam)) : Adm (objectsT Ξ A Bs L) :=
  interT_adm _ _ (props_adm A Bs) (CallEffects.callsT_adm L)

/-- A bag stating no field holds of every object value. -/
theorem props_nil {fs : List (PropKey × Nat)} {code : CallCode} {oid n W} :
    propsT [] [] n W (.objAt fs code oid) :=
  ⟨⟨fs, code, oid, rfl, rfl, fs, oid, rfl, fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩, fun _ h => by simp at h⟩

theorem props_congr_below {α : Type} (X Y : α → Fam) (a : List (PropKey × α))
    (bs : List (List (PropKey × α))) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n) (W : WorldT n)
    (v : Val) :
    propsT (ReferenceConjunctions.famsOf X a) (bs.map (ReferenceConjunctions.famsOf X)) n W v ↔
      propsT (ReferenceConjunctions.famsOf Y a) (bs.map (ReferenceConjunctions.famsOf Y)) n W v := by
  simp only [propsT, List.forall_mem_map]
  apply and_congr (bagT_contractive X Y a n h W v)
  constructor <;> intro hb b hm
  · exact (bagT_contractive X Y b n h W v).mp (hb b hm)
  · exact (bagT_contractive X Y b n h W v).mpr (hb b hm)

theorem congr_below {Ξ Ξ' : Fam} {α : Type} (X Y : α → Fam) (a : List (PropKey × α))
    (bs : List (List (PropKey × α))) (L : List (Arrow α))
    (n : Nat) (hexc : Agree Ξ Ξ' n) (h : ∀ a, Agree (X a) (Y a) n) (W : WorldT n) (v : Val) :
    objectsT Ξ (ReferenceConjunctions.famsOf X a) (bs.map (ReferenceConjunctions.famsOf X))
        (L.map (Arrow.map X)) n W v ↔
      objectsT Ξ' (ReferenceConjunctions.famsOf Y a) (bs.map (ReferenceConjunctions.famsOf Y))
        (L.map (Arrow.map Y)) n W v := by
  simp only [objectsT, interT]
  have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
    intro As; induction As with
    | nil => exact .nil
    | cons a As ih => exact .cons (h a) ih
  exact and_congr (props_congr_below X Y a bs n h W v)
    (CallEffects.callsT_congr L (Arrow.map X) (Arrow.map Y) hexc (fun _ _ => rfl)
      (fun p _ => ⟨h p.receiver, hd p.arguments, h p.result⟩) W v)

end Verification.CallableConjunctions
