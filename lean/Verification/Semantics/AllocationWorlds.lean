-- OperationWorlds.lean fixes the world annotations of a modeled execution; without it an allocation's successor world is not determined independently of its result bound.
import Verification.Semantics.OperationWorlds
import Verification.Semantics.KindsCapabilities

namespace Verification.AllocationWorlds
open OperationResults OperationWorlds Kinds

/-- **The roles an allocation's entries record**, at the values it
allocates: each entry's tag's concrete role at its value
(`Kinds.concreteRoles`; `StorageRole.concrete_permits`,
`StorageRole.concrete_cat`, `StorageRole.concrete_view`), none where a value
is not of its tag's category. -/
def roles (Es : List (StorageRole × Fam)) (vs : List Val) : Option (List Role) :=
  Kinds.concreteRoles (Es.map Prod.fst) vs

/-- The allocation's entries, a role and a contents type per field, determine
the successor world: each field's entry is its tag's concrete role at the
value allocated there (`roles`), a view store's of that store's length, with
its type as the contract; the identity follows (`Kinds.objectEntries`). The
result bound Q does not participate in the choice. Where a value is not of
its tag's category no entry is recorded and the configuration is left as it
is: no typed allocation takes that step. -/
def next (Es : List (StorageRole × Fam)) : Config → Config
  | ⟨n+1,W,h,.makeAt code ns vs⟩ =>
      match roles Es vs with
      | some rs => ⟨n, appendWs (trunc n (Nat.le_succ n) W)
          (objectEntries rs (Es.map (fun e => (res e.2 : Ctr n)))),
          h ++ vs ++ [.nul], .objAt (slots h.length ns) code (h.length + vs.length)⟩
      | none => ⟨n+1,W,h,.makeAt code ns vs⟩
  | c => c

def policy (Es : List (StorageRole × Fam)) : Policy :=
  ⟨fun c d => next Es c = d, fun h₁ h₂ => h₁.symm.trans h₂⟩

/-- **An allocation is safe** at the world its entries determine. Beyond the
contents' types, the typing supplies what the kinded world requires of the
fresh locations: each initializer is of its tag's category (`hhold`), each
tag fits its key (`hfits`), the metadata keys fit (`hmeta`), and the
initializers' references are valid (`href`). The continuation sees the record
whose positions state the allocated roles. -/
theorem allocation_safe {Q : Fam} {ss : List StorageRole} {As : List Fam} (hss : ss.length = As.length) (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List PropKey) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, ∀ (j : Nat) (hj : j + 1 < n), p.1 j (trunc j (by omega) W) p.2)
    (hhold : ∀ (i : Nat) (s : StorageRole) (v : Val), ss[i]? = some s → vs[i]? = some v → s.Holds v)
    (hfits : ∀ (i : Nat) (s : StorageRole), ss[i]? = some s → ∀ key : PropKey, ns[i]? = some key → s.fitsKey key = true)
    (hmeta : ∀ (k : Nat) (rs : List Role), concreteRoles ss vs = some rs → MetaFit ns rs (As.map (fun A => (res A : Ctr k))))
    (href : RefsOk W (.makeAt code ns vs))
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip (ss.zip As)) j U (.objAt (slots h.length ns) .absent (h.length + vs.length)) →
      Q j U (.objAt (slots h.length ns) code (h.length + vs.length))) :
    SafeWith Ξ (policy (ss.zip As)) Q n W h (.makeAt code ns vs) := by
  cases n with
  | zero => exact href
  | succ p =>
    obtain ⟨rs, hrs⟩ := concreteRoles_of_holds (by omega) hhold
    obtain ⟨-, hrl, hri⟩ := concreteRoles_spec hrs
    have hroles : roles (ss.zip As) vs = some rs := by
      simp only [roles, List.map_fst_zip (show ss.length ≤ As.length by omega)]; exact hrs
    have hE : (ss.zip As).map (fun e => (res e.2 : Ctr p)) = As.map (fun A => (res A : Ctr p)) := by
      rw [show (fun e : StorageRole × Fam => (res e.2 : Ctr p)) = (fun A => (res A : Ctr p)) ∘ Prod.snd
        from rfl, ← List.map_map, List.map_snd_zip (by omega)]
    let cs : List (Ctr p) := As.map (fun A => (res A : Ctr p))
    let W₀ := trunc p (Nat.le_succ p) W
    have hcsl : cs.length = ns.length := by simp [cs]; omega
    have hlen : h.length = (entries W₀).length := by
      have := hok.1.1; simp [W₀] at this ⊢; omega
    have hcadm : ∀ e ∈ objectEntries rs cs, CtrAdm e.2 := by
      intro e he
      have h2 : e.2 ∈ (objectEntries rs cs).map Prod.snd := List.mem_map_of_mem he
      rw [Capability.objectEntries_snd (by omega)] at h2
      rcases List.mem_append.mp h2 with h2 | h2
      · obtain ⟨A, hA', he2⟩ := List.mem_map.mp h2
        rw [← he2]
        exact ⟨fun i _ U U' hx w hw => (hA A hA').mono i U U' hx w hw, fun i _ U w hw => hV A hA' i U w hw⟩
      · simp only [List.mem_singleton] at h2; rw [h2]; exact idCtr_adm
    have hsh := concrete_shaped (W := W₀) (c := code) cs hlen (Shaped_trunc _ hok.2) hnd
      (by omega) hcsl hns hrs (RefsOk_trunc _ href) hfits (hmeta p rs hrs)
    have hmeets : HeapMeets p (appendWs W₀ (objectEntries rs cs)) (h ++ vs ++ [.nul]) := by
      rw [List.append_assoc]
      refine HeapMeets_appendWs (HeapOk_trunc p W h hok).1 (WorldAdm_trunc _ hadm) hcadm
        (by rw [objectEntries_length (by omega)]; simp; omega) ?_
      intro i c v hc hv' j hj
      rw [Capability.objectEntries_snd (by omega)] at hc
      by_cases hi : i < cs.length
      · rw [List.getElem?_append_left hi] at hc
        rw [List.getElem?_append_left (by simp [cs] at hi; omega)] at hv'
        simp only [cs, List.getElem?_map] at hc
        obtain ⟨A, hAi, rfl⟩ := Option.map_eq_some_iff.mp hc
        show A j _ v
        rw [trunc_trunc]
        exact hv (A, v) (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨hAi, hv'⟩⟩) j (by omega)
      · rw [List.getElem?_append_right (by omega)] at hc hv'
        have h0 : i - cs.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simp at this; omega
        rw [h0] at hc; rw [show i - vs.length = 0 by simp [cs] at hi h0 ⊢; omega] at hv'
        simp at hc hv'; subst hc hv'; rfl
    refine ⟨href, Or.inr ⟨appendWs W₀ (objectEntries rs cs),
      h ++ vs ++ [.nul], .objAt (slots h.length ns) code (h.length + vs.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .makeFields hvals hns, ⟨hmeets, hsh.1⟩, by simp only [policy, next, hroles, hE, W₀, cs], ?_⟩⟩
    cases p with
    | zero => exact hsh.2
    | succ q =>
      refine ⟨hsh.2, Or.inl (Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩)⟩
      refine recT_alloc hnd (by omega) ?_ (by omega) ?_
      · intro i hi
        rw [hlen, lookup_appendWs_ge, Capability.objectEntries_snd (by omega),
          List.getElem?_append_left (by omega)]
        simp [cs, List.getElem?_map, List.getElem?_eq_getElem (show i < As.length by omega)]
      · intro i hi
        obtain ⟨r, hr, hc⟩ := hri i (ss[i]'(by omega)) (vs[i]'(by omega)) (List.getElem?_eq_getElem _)
          (List.getElem?_eq_getElem _)
        refine ⟨r, ?_, StorageRole.concrete_permits hc⟩
        rw [hlen, roleAt_appendWs', objectEntries_fst (by omega), List.getElem?_append_left (by omega)]
        exact hr

end Verification.AllocationWorlds
