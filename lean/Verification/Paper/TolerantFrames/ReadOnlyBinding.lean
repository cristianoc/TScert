import Verification.Paper.TolerantFrames.ReadOnlyCharges

/-! # Read-only handles: the binding checks of a finite flow

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The binding checks"). A framed
plan's flow is a proposal; these checks, decided by the verifier from the
flow and the codes the lowering gives, bind it to the component's code:

- **The codes** (`codesCoverB`): the flow holds a proposal at the entry
  context for each code it is given, so a frame of one of them reads its
  allocation sites from the flow (`allocOf`), and the frame's `codes` are
  those codes (`codesCoverB_sound`).
- **The allocation sites are sites** (`allocSomeB`, the first half of the
  draft's `allocB`): every allocation site of every code at every context,
  per node key too, is a `some` site, so a frame of a covered code of `C`
  allocates at `some` sites (`allocOf_some`, `stepSite_some`), which
  `Held` reads as `C`'s storage.
- **The entry's signatures** (`entryFnB`): at a code's entry node, a slot
  names a signature only where it is one of the given slots, the sibling
  slots whose closures the realization fills (`entryFnB_sound`).
- **Two codes agreeing on a prefix** (`agreeB`): at every context of the
  first code, the second has a proposal, and the two give the same slots,
  value set, signatures and outside calls at each label below `n`, the
  same allocation sites at each of the given node keys, and the same
  return set (`agreeB_sound`); a realized code and its request's code are
  checked so (`realizedFlowB`, on the source side). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package}

/-! ## The codes -/

/-- **The flow covers the codes**, decided: each has a proposal at the entry
context. -/
def codesCoverB (F : FFlow P) (codes : List Code) : Bool := codes.all fun m => (F.at m entryCx).isSome

/-- **The codes' check is sound** (proved): every code given has a
proposal at the entry context. -/
theorem codesCoverB_sound [DecidableEq P.Site] {F : FFlow P} {codes : List Code} (h : codesCoverB F codes = true) :
    ∀ m ∈ codes, ∃ π, F.flow.code m entryCx = some π := by
  intro m hm
  have := List.all_eq_true.mp h m hm
  cases hc : F.at m entryCx with
  | none => rw [hc] at this; cases this
  | some fc => exact ⟨fc.flow, by simp [FFlow.flow, hc]⟩

/-! ## The allocation sites -/

/-- **Every allocation site is a site**, decided: at every code and
context, the default allocation sites and those of every node key. -/
def allocSomeB (F : FFlow P) : Bool :=
  F.codes.all fun mc => mc.2.all fun cc =>
    cc.2.alloc.obj.isSome && cc.2.alloc.arr.isSome && cc.2.allocs.all fun e => e.2.1.isSome && e.2.2.isSome

/-- **A code's allocation sites at a node key are sites** (proved): where
its default ones and every listed one are. -/
theorem allocAt_some {c : FCode P} (hd : c.alloc.obj.isSome = true ∧ c.alloc.arr.isSome = true)
    (hl : c.allocs.all (fun e => e.2.1.isSome && e.2.2.isSome) = true) (kx : NodeKey) :
    (c.allocAt kx).obj.isSome = true ∧ (c.allocAt kx).arr.isSome = true := by
  unfold FCode.allocAt
  split
  · rename_i e o a he
    have hm := List.mem_of_find?_eq_some he
    have := List.all_eq_true.mp hl _ hm
    simp only [Bool.and_eq_true] at this
    exact this
  · exact hd

/-- **The check is sound** (proved): every proposal of the flow allocates at
`some` sites at every node key. -/
theorem allocSomeB_sound {F : FFlow P} (h : allocSomeB F = true) {m : Code} {c : Nat} {fc : FCode P}
    (hfc : F.at m c = some fc) (kx : NodeKey) :
    (fc.allocAt kx).obj.isSome = true ∧ (fc.allocAt kx).arr.isSome = true := by
  obtain ⟨l, hl, hcl⟩ := FFlow.at_mem hfc
  have h₁ := List.all_eq_true.mp (List.all_eq_true.mp h _ hl) _ hcl
  simp only [Bool.and_eq_true] at h₁
  exact allocAt_some ⟨h₁.1.1, h₁.1.2⟩ h₁.2 kx

/-- **A frame of a covered code of `C` allocates at sites** (proved): the
flow's proposal at the entry context gives its allocation sites, each a
`some` site. -/
theorem allocOf_some [DecidableEq P.Site] {F : FFlow P} (h : allocSomeB F = true) {m : Code} {comp : ComponentTag} {kx : NodeKey}
    (hc : P.ofC comp = true) (hm : (F.at m entryCx).isSome = true) :
    (allocOf F.flow (some ((m, comp), kx))).obj.isSome = true ∧
      (allocOf F.flow (some ((m, comp), kx))).arr.isSome = true := by
  cases hfc : F.at m entryCx with
  | none => rw [hfc] at hm; cases hm
  | some fc =>
    have hcode : F.flow.code m entryCx = some fc.flow := by simp [FFlow.flow, hfc]
    simp only [allocOf, hc, if_true, hcode, Option.map_some, Option.getD_some]
    exact allocSomeB_sound h hfc kx

/-- **A step of a covered code of `C` allocates at a site** (proved): its
fresh locations' site, read at the innermost frame (`stepSite`), is a
`some` site when that frame runs a code of `C` the flow covers. -/
theorem stepSite_some [DecidableEq P.Site] {F : FFlow P} (h : allocSomeB F = true) {t : Tm} {m : Code} {comp : ComponentTag}
    {kx : NodeKey} (hfr : (activeFrame none t).1 = some ((m, comp), kx)) (hc : P.ofC comp = true)
    (hm : (F.at m entryCx).isSome = true) : (stepSite F.flow none t).isSome = true := by
  have ho := allocOf_some (kx := kx) h hc hm
  unfold stepSite
  split <;> rename_i heq <;> rw [heq] at hfr <;> simp only at hfr <;> subst hfr
  · exact ho.2
  · exact ho.2
  · exact ho.1

/-! ## The entry's signatures -/

/-- **The entry names signatures only at the given slots**, decided: at
the node `l` of the code's proposal at the entry context, every slot naming
a signature is one of `sib`. -/
def entryFnB (F : FFlow P) (m : Code) (l : Nat) (sib : List Nat) : Bool :=
  (F.at m entryCx).all fun c => (List.range (c.node l).fn.size).all fun i => ((c.node l).fnAt i).isNone || sib.contains i

/-- **The entry check is sound** (proved): at the entry node of the code's
proposal, a slot naming a signature is one of the given slots. -/
theorem entryFnB_sound [DecidableEq P.Site] {F : FFlow P} {m : Code} {l : Nat} {sib : List Nat} (h : entryFnB F m l sib = true)
    {π : CodeFlow P} (hπ : F.flow.code m entryCx = some π) {i : Nat} {σ : FnSig} (hi : π.fn l i = some σ) :
    i ∈ sib := by
  obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hπ
  unfold entryFnB at h
  rw [hfc] at h
  simp only [Option.all_some, List.all_eq_true, List.mem_range, Bool.or_eq_true, Option.isNone_iff_eq_none,
    List.contains_iff_mem] at h
  have hfn : (fc.node l).fnAt i ≠ none := by
    intro hn
    simp [FCode.flow, FCode.sigAt, hn] at hi
  have hlt : i < (fc.node l).fn.size := by
    refine Classical.byContradiction fun hge => hfn ?_
    simp [FNode.fnAt, Array.getD, hge]
  exact (h i hlt).resolve_left hfn

/-! ## Two codes agreeing on a prefix -/

/-- **Two nodes give the same proposal**, decided: slots, value set,
signatures (read through each code's table) and outside calls. -/
def nodeAgreeB [DecidableEq P.Site] (c₁ c₂ : FCode P) (l : Nat) : Bool :=
  let x := c₁.node l
  let y := c₂.node l
  decide (x.env = y.env) && decide (x.dflt = y.dflt) && decide (x.val = y.val) &&
    decide (c₁.sigAt x.vfn = c₂.sigAt y.vfn) && x.out == y.out &&
    (List.range (max x.fn.size y.fn.size)).all fun i => decide (c₁.sigAt (x.fnAt i) = c₂.sigAt (y.fnAt i))

/-- **The second code agrees with the first below `n`**, decided: at every
context of the first, the second has a proposal giving the same nodes
below `n`, the same allocation sites at each key of `keys`, and the same
return set. -/
def agreeB [DecidableEq P.Site] (F : FFlow P) (m₁ m₂ : Code) (keys : List NodeKey) (n : Nat) : Bool :=
  (F.ctxs m₁).all fun e => (F.at m₂ e.1).any fun f₂ =>
    (List.range n).all (nodeAgreeB e.2 f₂ ·) && decide (e.2.ret = f₂.ret) &&
      keys.all fun kx => decide ((e.2.allocAt kx).obj = (f₂.allocAt kx).obj ∧ (e.2.allocAt kx).arr = (f₂.allocAt kx).arr)

theorem nodeAgreeB_sound [DecidableEq P.Site] {c₁ c₂ : FCode P} {l : Nat} (h : nodeAgreeB c₁ c₂ l = true) :
    c₁.flow.env l = c₂.flow.env l ∧ c₁.flow.val l = c₂.flow.val l ∧ c₁.flow.fn l = c₂.flow.fn l ∧
      c₁.flow.vfn l = c₂.flow.vfn l ∧ c₁.flow.out l = c₂.flow.out l := by
  simp only [nodeAgreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨he, hd⟩, hv⟩, hvf⟩, ho⟩, hf⟩ := h
  refine ⟨funext fun i => ?_, hv, funext fun i => ?_, hvf, ho⟩
  · show (c₁.node l).envAt i = (c₂.node l).envAt i
    simp only [FNode.envAt, he, hd]
  · show c₁.sigAt ((c₁.node l).fnAt i) = c₂.sigAt ((c₂.node l).fnAt i)
    by_cases hi : i < max (c₁.node l).fn.size (c₂.node l).fn.size
    · exact hf i hi
    · have h₁ : (c₁.node l).fnAt i = none := by
        simp [FNode.fnAt, Array.getD, show ¬ i < (c₁.node l).fn.size by omega]
      have h₂ : (c₂.node l).fnAt i = none := by
        simp [FNode.fnAt, Array.getD, show ¬ i < (c₂.node l).fn.size by omega]
      rw [h₁, h₂]; rfl

/-- **The prefix check is sound** (proved): at every context of the first
code the second has a proposal with the same nodes below `n`, the same
allocation sites at each given key and the same return set. -/
theorem agreeB_sound [DecidableEq P.Site] {F : FFlow P} {m₁ m₂ : Code} {keys : List NodeKey} {n : Nat}
    (h : agreeB F m₁ m₂ keys n = true) {c : Nat} {π₁ : CodeFlow P} (h₁ : F.flow.code m₁ c = some π₁) :
    ∃ π₂, F.flow.code m₂ c = some π₂ ∧ π₁.ret = π₂.ret ∧ (∀ kx ∈ keys, π₁.alloc kx = π₂.alloc kx) ∧
      ∀ l, l < n → π₁.env l = π₂.env l ∧ π₁.val l = π₂.val l ∧ π₁.fn l = π₂.fn l ∧ π₁.vfn l = π₂.vfn l ∧
        π₁.out l = π₂.out l := by
  obtain ⟨f₁, hf₁, rfl⟩ := FFlow.code_at h₁
  have hc := List.all_eq_true.mp h _ (FFlow.at_ctxs hf₁)
  cases hf₂ : F.at m₂ c with
  | none => rw [hf₂] at hc; cases hc
  | some f₂ =>
    rw [hf₂] at hc
    simp only [Option.any_some, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
    obtain ⟨⟨hn, hr⟩, hk⟩ := hc
    refine ⟨f₂.flow, by simp [FFlow.flow, hf₂], hr, fun kx hkx => ?_, fun l hl => nodeAgreeB_sound (hn l hl)⟩
    obtain ⟨ho, ha⟩ := hk kx hkx
    show f₁.allocAt kx = f₂.allocAt kx
    cases h₁ : f₁.allocAt kx; cases h₂ : f₂.allocAt kx
    rw [h₁, h₂] at ho ha
    simp only at ho ha
    rw [ho, ha]

end Verification.TolerantFrames.ReadOnly
