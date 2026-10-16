import Verification.Semantics.Calculus

/-!
# Binding discipline

`Scoped d t` says that the free de Bruijn indices of `t` are below `d`.
Unlike `isVal`, it rules out callable code containing free variables. Substitution
in the machine is valid for closed arguments; the lemmas here state that
precondition explicitly.
-/
namespace Verification

mutual
def Scoped (d : Nat) : Tm → Prop
  | .var i => i < d
  | .objAt _ .absent _ => True
  | .objAt _ (.bound t r pre) _ => Scoped d t ∧ Scoped d r ∧ ScopedArgs d pre
  | .makeAt (.bound t r pre) _ args =>
      Scoped d t ∧ Scoped d r ∧ ScopedArgs d pre ∧ ScopedArgs d args
  | .makeAt .absent _ args => ScopedArgs d args
  | .letE a b => Scoped d a ∧ Scoped (d + 1) b
  | .invoke f r args => Scoped d f ∧ Scoped d r ∧ ScopedArgs d args
  | .construct f args => Scoped d f ∧ ScopedArgs d args
  | .readAt _ a | .test _ a => Scoped d a
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b =>
      Scoped d a ∧ Scoped d b
  | .ite c a b | .setElem c a b => Scoped d c ∧ Scoped d a ∧ Scoped d b
  | .arrLit args => ScopedArgs d args
  | .lenOf a => Scoped d a
  | .spread a => Scoped d a
  | .throw a => Scoped d a
  | .merge _ a b => Scoped d a ∧ Scoped d b
  | .makeKey a b => Scoped d a ∧ Scoped d b
  -- Graph code's node expressions are scoped by its own environment, which
  -- invocation supplies whole; only the captures are scoped here.
  | .objAt _ (.graph _ _ _ _ caps _ _) _ => ScopedArgs d caps
  | .makeAt (.graph _ _ _ _ caps _ _) _ args => ScopedArgs d caps ∧ ScopedArgs d args
  | .goto _ _ _ L x => ScopedArgs d L ∧ Scoped d x
  | .frame _ _ t L x _ _ => Scoped d t ∧ ScopedArgs d L ∧ Scoped d x
  | _ => True

def ScopedArgs (d : Nat) : List Tm → Prop
  | [] => True
  | a :: args => Scoped d a ∧ ScopedArgs d args
end

@[simp] theorem scopedArgs_iff (d : Nat) (args : List Tm) :
    ScopedArgs d args ↔ ∀ a ∈ args, Scoped d a := by
  induction args <;> simp_all [ScopedArgs]

theorem subst_above {t : Tm} {d j : Nat} (h : Scoped d t) (hj : d ≤ j) (a : Tm) :
    subst j a t = t := by
  induction t using Tm.induct generalizing d j <;> simp only [Scoped, scopedArgs_iff, subst, substArgs_eq_map] at *
  case var i => simp [show i ≠ j by omega, show ¬j < i by omega]
  case invoke f r args ihf ihr iha =>
    rw [ihf h.1 hj, ihr h.2.1 hj]
    congr 1
    simpa using (List.map_congr_left (g := id) (fun a ha => iha a ha (h.2.2 a ha) hj))
  case construct f args ihf iha =>
    rw [ihf h.1 hj]
    congr 1
    simpa using (List.map_congr_left (g := id) (fun a ha => iha a ha (h.2 a ha) hj))
  case letE x b ihx ihb => rw [ihx h.1 hj, ihb h.2 (by omega)]
  case objBound fs oid t r pre iht ihr ihp =>
    have hmap : pre.map (subst j a) = pre := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihp x hx (h.2.2 x hx) hj))
    rw [iht h.1 hj, ihr h.2.1 hj, hmap]
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    have hpre : pre.map (subst j a) = pre := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihp x hx (h.2.2.1 x hx) hj))
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h.2.2.2 x hx) hj))
    rw [iht h.1 hj, ihr h.2.1 hj, hpre, hmap]
  case write f b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case arith op b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case ite c b e ihc ihb ihe => rw [ihc h.1 hj, ihb h.2.1 hj, ihe h.2.2 hj]
  case alloc ns args ihargs =>
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h x hx) hj))
    rw [hmap]
  case arrLit args ihargs =>
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h x hx) hj))
    rw [hmap]
  case elemAt b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case setElem b c e ihb ihc ihe => rw [ihb h.1 hj, ihc h.2.1 hj, ihe h.2.2 hj]
  case lenOf b ih => rw [ih h hj]
  case spread b ih => rw [ih h hj]
  case throw b ih => rw [ih h hj]
  case merge dr b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case makeKey b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case read f b ih => rw [ih h hj]
  case index b key ihb ihkey => rw [ihb h.1 hj, ihkey h.2 hj]
  case test k b ih => rw [ih h hj]
  case objGraph fs oid n E K st caps _ _ _ ihc =>
    have hmap : caps.map (subst j a) = caps := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihc x hx (h x hx) hj))
    rw [hmap]
  case makeGraph n E K st caps _ _ ns args _ ihc iha =>
    have hc : caps.map (subst j a) = caps := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihc x hx (h.1 x hx) hj))
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => iha x hx (h.2 x hx) hj))
    rw [hc, hmap]
  case goto E K l L x _ ihL ihx =>
    have hL : L.map (subst j a) = L := by
      simpa using (List.map_congr_left (g := id) (fun y hy => ihL y hy (h.1 y hy) hj))
    rw [hL, ihx h.2 hj]
  case frame E K t L x k hd _ iht ihL ihx =>
    have hL : L.map (subst j a) = L := by
      simpa using (List.map_congr_left (g := id) (fun y hy => ihL y hy (h.2.1 y hy) hj))
    rw [iht h.1 hj, hL, ihx h.2.2 hj]
  all_goals rfl

theorem Scoped.closed {t : Tm} (h : Scoped 0 t) : Closed t :=
  fun j a => subst_above h (Nat.zero_le j) a

/-- Closing a lambda and applying it agrees with extending its environment. -/
theorem instantiate_beta (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i)) (a t : Tm) (d : Nat) :
    subst d a (instantiate (d + 1) ρ t) = instantiate d (push a ρ) t := by
  induction t using Tm.induct generalizing d <;> simp only [instantiate, instantiateArgs_eq_map, subst, substArgs_eq_map] at *
  case var i =>
    by_cases h : i < d
    · simp [show i < d + 1 by omega, h, subst, show i ≠ d by omega, show ¬d < i by omega]
    · by_cases he : i = d
      · subst i; simp [subst, push]
      · have hi : ¬ i < d + 1 := by omega
        have heq : i - d = (i - (d + 1)) + 1 := by omega
        simp only [if_neg hi, if_neg h, heq, push]
        exact (hρ _).closed d a
  case invoke f r args ihf ihr iha =>
    rw [ihf, ihr, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact iha a ha d
  case construct f args ihf iha =>
    rw [ihf, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact iha a ha d
  case letE a b iha ihb => rw [iha, ihb]
  case objBound fs oid t r pre iht ihr ihp =>
    have hmap : List.map (subst d a ∘ instantiate (d + 1) ρ) pre =
        List.map (instantiate d (push a ρ)) pre :=
      List.map_congr_left (fun x hx => ihp x hx d)
    rw [iht, ihr, List.map_map, hmap]
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    have hpre : List.map (subst d a ∘ instantiate (d + 1) ρ) pre =
        List.map (instantiate d (push a ρ)) pre :=
      List.map_congr_left (fun x hx => ihp x hx d)
    have hmap : List.map (subst d a ∘ instantiate (d + 1) ρ) args =
        List.map (instantiate d (push a ρ)) args :=
      List.map_congr_left (fun x hx => ihargs x hx d)
    rw [iht, ihr, List.map_map, List.map_map, hpre, hmap]
  case write f b c ihb ihc => rw [ihb, ihc]
  case arith op b c ihb ihc => rw [ihb, ihc]
  case ite c b e ihc ihb ihe => rw [ihc, ihb, ihe]
  case alloc ns args ihargs =>
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ihargs x hx d
  case arrLit args ihargs =>
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ihargs x hx d
  case elemAt b c ihb ihc => rw [ihb, ihc]
  case setElem b c e ihb ihc ihe => rw [ihb, ihc, ihe]
  case lenOf b ih => rw [ih]
  case spread b ih => rw [ih]
  case throw b ih => rw [ih]
  case merge dr b c ihb ihc => rw [ihb, ihc]
  case makeKey b c ihb ihc => rw [ihb, ihc]
  case read f b ih => rw [ih]
  case index b key ihb ihkey => rw [ihb, ihkey]
  case test k b ih => rw [ih]
  case objGraph fs oid n E K st caps _ _ _ ihc =>
    rw [List.map_map]
    congr 2
    exact List.map_congr_left (fun x hx => ihc x hx d)
  case makeGraph n E K st caps _ _ ns args _ ihc iha =>
    have hc : List.map (subst d a ∘ instantiate (d + 1) ρ) caps =
        List.map (instantiate d (push a ρ)) caps :=
      List.map_congr_left (fun x hx => ihc x hx d)
    have hmap : List.map (subst d a ∘ instantiate (d + 1) ρ) args =
        List.map (instantiate d (push a ρ)) args :=
      List.map_congr_left (fun x hx => iha x hx d)
    rw [List.map_map, List.map_map, hc, hmap]
  case goto E K l L x _ ihL ihx =>
    rw [List.map_map, ihx]
    congr 1
    exact List.map_congr_left (fun y hy => ihL y hy d)
  case frame E K t L x k hd _ iht ihL ihx =>
    rw [List.map_map, ihx, iht]
    congr 1
    exact List.map_congr_left (fun y hy => ihL y hy d)
  all_goals rfl

/-- Put parameters in declaration order before the captured environment.
Slot zero is the first parameter, not the last argument evaluated. -/
def prependArgs (args : List Tm) (ρ : Env) : Env := args.foldr push ρ

end Verification
