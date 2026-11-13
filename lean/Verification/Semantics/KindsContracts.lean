import Verification.Semantics.KindsNatives
import Verification.Semantics.KindsStates
import Verification.Semantics.KindsCapabilities
/-!
# World-indexed postconditions and the native-contract condition

A **world-indexed postcondition** (`WPost`) is a predicate of an exit: the
budget left, the world the safety derivation chose there, the heap and the
result. A contract that must speak of roles reads the exit world, which is
the one typing and structural validity use.

**Safety with world-indexed postconditions** (`SafeW`) is the safety
predicate of `Semantics/ExceptionalPosts.lean` over kinded worlds, with the
references of the running term valid in the world at every budget, zero
included. Its steps, world extensions and heap invariant are those of
`Safe`; a heap meeting a kinded world has every role's shape at every budget.
So every execution prefix ends in a well-formed configuration under one
extension of the truncated entry world (`SafeW.run`).

**The native-contract condition** (`NativeContract`) is the one obligation
of every native and every call contract: from every well-formed entry
configuration meeting the input contract, the call is safe in that sense at
its result type, its normal postcondition and its exceptional one.

World-indexed postconditions (`WPost`, `WExc`) and the view-element write
(`ViewWrite`), a postcondition of that kind, are defined below the call
effects, in `Semantics/ElementWrites.lean`.
-/
namespace Verification.Kinds
open Verification

/-! ## Safety with world-indexed postconditions -/

/-- `t` throws a closed value of the exception family `Ξ`. -/
def Thrown (Ξ : Fam) (k : Nat) (W : WorldT k) (t : Tm) : Prop :=
  ∃ v, Raises t v ∧ Scoped 0 v ∧ Ξ k W v

/-- **Safety with world-indexed postconditions.** At every budget the
running term's references are valid in the world. At positive budget the
term is a value of `T` meeting `Q` at this world and heap, or throws a value
of `Ξ` with `R` at this world and heap, or steps to a heap meeting an
admissible extension of the truncated world, where safety continues. -/
def SafeW (Ξ T : Fam) (Q : WPost) (R : WExc) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, W, _, t => RefsOk W t
  | n + 1, W, h, t => RefsOk W t ∧
      (((isVal t = true ∧ T (n + 1) W t ∧ Q (n + 1) W h t) ∨ (Thrown Ξ (n + 1) W t ∧ R (n + 1) W h)) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧
          HeapOk n U h' ∧ SafeW Ξ T Q R n U h' t'))

/-- **The structural component holds at every budget**, zero included. -/
theorem SafeW.refs {Ξ T : Fam} {Q : WPost} {R : WExc} :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}, SafeW Ξ T Q R n W h t → RefsOk W t
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => h.1

/-- A thrown value's references are valid where the throwing term's are. -/
theorem Thrown.refs {Ξ : Fam} {k : Nat} {W : WorldT k} {t : Tm} (ht : Thrown Ξ k W t)
    (hr : RefsOk W t) : ∃ v, Raises t v ∧ Ξ k W v ∧ RefsOk W v :=
  let ⟨v, hv, _, hΞ⟩ := ht; ⟨v, hv, hΞ, fun r hm => hr r (raises_refs hv r hm)⟩

/-- Safety is monotone in both postconditions. -/
theorem SafeW.mono {Ξ T : Fam} {Q Q' : WPost} {R R' : WExc}
    (hQ : ∀ k (W : WorldT k) h v, Q k W h v → Q' k W h v)
    (hR : ∀ k (W : WorldT k) h, R k W h → R' k W h) :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}, SafeW Ξ T Q R n W h t → SafeW Ξ T Q' R' n W h t
  | 0, _, _, _, hs => hs
  | n + 1, _, _, _, ⟨hr, hs⟩ => by
    refine ⟨hr, ?_⟩
    rcases hs with (⟨hv, hT, hq⟩ | ⟨ht, hx⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · exact .inl (.inl ⟨hv, hT, hQ _ _ _ _ hq⟩)
    · exact .inl (.inr ⟨ht, hR _ _ _ hx⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh, SafeW.mono hQ hR hs'⟩

/-- **Every execution prefix ends in a well-formed configuration under one
extension of the truncated entry world**: after `k` steps of a term safe at
budget `j + k`, a world at budget `j` extends the entry world truncated to
`j`, the heap meets it in both parts, the term's references are valid in it,
and safety continues there. The budget left may be zero. -/
theorem SafeW.run {Ξ T : Fam} {Q : WPost} {R : WExc} :
    ∀ {k : Nat} {h : Heap} {t : Tm} {h' : Heap} {t' : Tm}, HeapObservations.Steps k h t h' t' →
      ∀ {n : Nat} {W : WorldT n}, k ≤ n → WorldAdm W → HeapOk n W h → SafeW Ξ T Q R n W h t →
      ∃ (j : Nat) (hj : j ≤ n) (U : WorldT j), j + k = n ∧ WExt (trunc j hj W) U ∧ WorldAdm U ∧
        HeapOk j U h' ∧ RefsOk U t' ∧ SafeW Ξ T Q R j U h' t' := by
  intro k h t h' t' hst
  induction hst with
  | refl =>
    intro n W _ hadm hok hs
    exact ⟨n, Nat.le_refl n, W, rfl, by rw [trunc_id]; exact WExt_refl _, hadm, hok, hs.refs, hs⟩
  | next st _ ih =>
    intro n W hk hadm hok hs
    cases n with
    | zero => omega
    | succ m =>
      rcases hs.2 with (⟨hv, -, -⟩ | ⟨⟨_, hr, -⟩, -⟩) | ⟨U, h₁, t₁, hx, hu, st', hh, hs'⟩
      · exact absurd st (value_no_step hv)
      · exact absurd st (raises_no_step hr)
      · obtain ⟨rfl, rfl⟩ := Step_det st st'
        obtain ⟨j, hj, U', hjk, hx', hu', hh', hr', hs''⟩ := ih (by omega) hu hh hs'
        refine ⟨j, by omega, U', by omega, ?_, hu', hh', hr', hs''⟩
        simpa only [trunc_trunc] using WExt_trans (WExt_trunc hj hx) hx'

/-! ## The native-contract condition -/

/-- A call's normal postcondition: given the receiver, the actuals, and the
entry budget, world and heap, a world-indexed postcondition of the exit. -/
abbrev CPost := Tm → List Tm → (j : Nat) → WorldT j → Heap → WPost

/-- A call's exceptional postcondition: given the receiver, the actuals, and
the entry budget, world and heap, a world-indexed postcondition of the
throwing configuration. -/
abbrev CExc := Tm → List Tm → (j : Nat) → WorldT j → Heap → WExc

/-- **The native-contract condition** of a callable value `v`, at budget `k`
and world `W`. From every well-formed entry configuration below `k` (a heap
meeting an admissible extension `U` of the truncated world, with the
references of the callee, the receiver and the actuals valid in `U`) that
meets the input contract (the receiver's type `Rc`, the actuals' `Acc`, the
precondition `requires`), the invocation is safe with world-indexed
postconditions: a normal result has the result type `R` and meets `post` at
its exit world, a throw is of the exception family `Ξ` and meets `excPost`
at its exit world, each given the entry world and heap, and every
configuration on the way is well-formed under one extension of `U`
(`NativeContract.run`). -/
def NativeContract (Ξ : Fam) (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc : Fam)
    (requires : Tm → List Tm → Heap → Prop) (R : Tm → List Tm → Fam)
    (post : CPost) (excPost : CExc)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U →
    ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ r, isVal r = true → Rc j U r → RefsOk U r →
      ∀ args, CallArguments.Values args → Acc j U args → (∀ a ∈ args, RefsOk U a) →
        requires r args heap →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafeW Ξ (R r args) (post r args j U heap) (excPost r args j U heap) j U heap result

/-- **A contract's every execution prefix is well-formed**: the configuration
`i` steps into the call meets one extension of the entry world truncated to
the budget left, in both parts of heap satisfaction and with valid
references. -/
theorem NativeContract.run {Ξ : Fam} {Acc : (j : Nat) → WorldT j → List Tm → Prop} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam}
    {post : CPost} {excPost : CExc}
    {k : Nat} {W : WorldT k} {v : Val} (hc : NativeContract Ξ Acc Rc requires R post excPost k W v)
    {j : Nat} (hj : j < k) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U) (hu : WorldAdm U)
    {heap : Heap} (hh : HeapOk j U heap) (hv : RefsOk U v) {r : Tm} (hr : isVal r = true)
    (hrc : Rc j U r) (hrr : RefsOk U r) {args : List Tm} (ha : CallArguments.Values args)
    (hacc : Acc j U args) (har : ∀ a ∈ args, RefsOk U a) (hreq : requires r args heap) :
    ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
      ∀ {i : Nat} {h' : Heap} {t' : Tm}, HeapObservations.Steps i heap result h' t' → i ≤ j →
        ∃ (m : Nat) (hm : m ≤ j) (U' : WorldT m), m + i = j ∧ WExt (trunc m hm U) U' ∧
          HeapOk m U' h' ∧ RefsOk U' t' := by
  obtain ⟨result, hi, hs⟩ := hc j hj U hx hu heap hh hv r hr hrc hrr args ha hacc har hreq
  refine ⟨result, hi, fun hst hle => ?_⟩
  obtain ⟨m, hm, U', hmi, hx', -, hh', hr', -⟩ := hs.run hst hle hu hh
  exact ⟨m, hm, U', hmi, hx', hh', hr'⟩

end Verification.Kinds
