-- OperationWorlds.lean fixes the world annotations of a modeled execution; without it an allocation's successor world is not determined independently of its result bound.
import Verification.Semantics.OperationWorlds
import Verification.Semantics.KindsCapabilities

namespace Verification.AllocationWorlds
open OperationResults OperationWorlds

/-- The allocation's entries, a role and a contents type per field, determine
the successor world: each field's contract is its entry's type. The result
bound Q does not participate in the choice. The world of this development
records contracts only; the role the kinded world records beside each
contract (`Kinds.objectEntries`) is the entry's tag's concrete role at the
value allocated there (`roles`), a view store's of that store's length. -/
def next (Es : List (StorageRole × Fam)) : Config → Config
  | ⟨n+1,W,h,.makeAt code ns vs⟩ =>
      ⟨n, appendWs (trunc n (Nat.le_succ n) W)
        (Es.map (fun e => (res e.2 : Ctr n)) ++ [res nulT]),
        h ++ vs ++ [.nul], .objAt (slots h.length ns) code (h.length + vs.length)⟩
  | c => c

/-- **The roles an allocation's entries record**, at the values it
allocates: each entry's tag's concrete role at its value
(`Kinds.concreteRoles`; `StorageRole.concrete_permits`,
`StorageRole.concrete_cat`, `StorageRole.concrete_view`), none where a value
is not of its tag's category. -/
def roles (Es : List (StorageRole × Fam)) (vs : List Val) : Option (List Kinds.Role) :=
  Kinds.concreteRoles (Es.map Prod.fst) vs

def policy (Es : List (StorageRole × Fam)) : Policy :=
  ⟨fun c d => next Es c = d, fun h₁ h₂ => h₁.symm.trans h₂⟩

theorem allocation_safe {Q : Fam} {ss : List StorageRole} {As : List Fam} (hss : ss.length = As.length) (hA : ∀ A ∈ As, Adm A) (hV : ∀ A ∈ As, ValOnly A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List PropKey) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, ∀ (j : Nat) (hj : j + 1 < n), p.1 j (trunc j (by omega) W) p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip (ss.zip As)) j U (.objAt (slots h.length ns) .absent (h.length + vs.length)) →
      Q j U (.objAt (slots h.length ns) code (h.length + vs.length))) :
    SafeWith Ξ (policy (ss.zip As)) Q n W h (.makeAt code ns vs) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hE : (ss.zip As).map (fun e => (res e.2 : Ctr p)) = As.map (fun A => (res A : Ctr p)) := by
      rw [show (fun e : StorageRole × Fam => (res e.2 : Ctr p)) = (fun A => (res A : Ctr p)) ∘ Prod.snd
        from rfl, ← List.map_map, List.map_snd_zip (by omega)]
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
    let contracts := As.map (fun A => (res A : Ctr p)) ++ [res nulT]
    have hcadm' : ∀ c ∈ contracts, CtrAdm c := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hcadm c hc
      · simp only [List.mem_singleton] at hc; subst c
        exact ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => by rw [show _ = Tm.nul from h]; rfl⟩
    have hcont' : ∀ q ∈ contracts.zip (vs ++ [.nul]), ∀ (j : Nat) (hj : j < p),
        q.1 j hj (trunc j (Nat.le_of_lt hj) (trunc p (Nat.le_succ p) W)) q.2 := by
      intro q hq
      simp only [contracts] at hq
      rw [List.zip_append (by simpa using hAs)] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hcont q hq
      · simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hq
        subst q; exact fun _ _ => rfl
    refine Or.inr ⟨appendWs (trunc p (Nat.le_succ p) W) contracts,
      h ++ vs ++ [.nul], .objAt (slots h.length ns) code (h.length + vs.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm',
      .makeFields hvals hns,
      by simpa only [List.append_assoc] using
        heap_allocs p contracts (trunc p (Nat.le_succ p) W) h (vs ++ [.nul]) (HeapOk_trunc p W h hok)
          (WorldAdm_trunc _ hadm) hcadm' (by simp [contracts, hAs]) hcont', (by simp only [policy, next, contracts, hE]), ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl (Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩)
      refine recT_alloc hnd (by omega) ?_
      intro i hi
      have hib : i < (As.map (fun A => (res A : Ctr (q + 1)))).length := by
        simp; omega
      have := lookup_appendWs (trunc (q + 1) (Nat.le_succ (q + 1)) W)
        (As.map (fun A => (res A : Ctr (q + 1))) ++ [res nulT]) (i := i) (by simp; omega)
      rw [← hlen] at this
      rw [this]
      simp [List.getElem?_append_left hib, List.getElem?_map, List.getElem?_eq_getElem (show i < As.length by omega)]

end Verification.AllocationWorlds
