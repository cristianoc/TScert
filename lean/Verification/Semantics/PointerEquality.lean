/-! A pointer-equality fast path at any type, a type variable included (the
verifier's generic code is generic in its labels `ι`). `sameObjectOr a b k h`
is `k ()`; the compiled verifier answers `true` without running `k` where `a`
and `b` are one object. Lean's `withPtrEq` is compiled only at types whose
values the compiler sees hold no types or type formers.

The replacement equals `k ()` where pointer-equal values are equal, which
holds at every type whose values hold no erased types, the verifier's labels,
terms and sets of sites among them. The proofs read the definition, `k ()`. -/
namespace Verification

/-- `k ()`, answered `true` at once where `a` and `b` are one object. -/
@[implemented_by withPtrEqUnsafe]
def sameObjectOr {α : Type u} (a b : α) (k : Unit → Bool) (_h : a = b → k () = true) : Bool :=
  k ()

end Verification
