import Verification.Semantics.Bindings

/-! # The capture graph of concrete closures

Graph closures have finite term-valued captures. Their direct capture graph
is acyclic. The invocation's implicit self slot is supplied by `graphEntry`
and is separate from those captures. A recursive group therefore needs an
encoding through self or heap locations, together with its correspondence
proof; a family of circular equations between concrete captures has no solution.
-/
namespace Verification.LinkingCaptures

/-- An edge from a graph closure to one of its explicitly stored captures.
This relation excludes the implicit self slot supplied at invocation. -/
inductive Captures : Tm → Tm → Prop where
  | graph {fs arity E K start caps kind rest oid v} : v ∈ caps →
      Captures (.objAt fs (.graph arity E K start caps kind rest) oid) v

/-- A nonempty path through explicit graph captures. -/
inductive CapturePath : Tm → Tm → Prop where
  | edge : Captures f g → CapturePath f g
  | next : Captures f g → CapturePath g h → CapturePath f h

/-- Every explicitly captured term is strictly smaller than its closure. -/
theorem Captures.size_lt {f g : Tm} (h : Captures f g) : sizeOf g < sizeOf f := by
  cases h with
  | graph hm =>
    have hlt := List.sizeOf_lt_of_mem hm
    simp only [Tm.objAt.sizeOf_spec, CallCode.graph.sizeOf_spec]
    omega

/-- Every nonempty capture path strictly decreases term size. -/
theorem CapturePath.size_lt {f g : Tm} (h : CapturePath f g) : sizeOf g < sizeOf f := by
  induction h with
  | edge he => exact he.size_lt
  | next he _ ih => exact Nat.lt_trans ih he.size_lt

/-- No finite graph closure reaches itself through explicit captures. -/
theorem no_capture_cycle {f : Tm} (h : CapturePath f f) : False :=
  Nat.lt_irrefl _ h.size_lt

/-- Two concrete graph closures cannot explicitly capture one another. -/
theorem no_mutual_captures {f g : Tm} (hfg : Captures f g) (hgf : Captures g f) : False :=
  no_capture_cycle (.next hfg (.edge hgf))

/-- A structural table of direct links inherits the capture graph's strict
size decrease, for any set of export identities. This is independent of
acceptance, signature interpretation, and heap or world assumptions. -/
theorem link_size_lt {ι : Type} {exports : ι → Tm} {links : ι → ι → Prop}
    (realizes : ∀ i j, links i j → Captures (exports i) (exports j))
    {i j : ι} (h : links i j) : sizeOf (exports j) < sizeOf (exports i) :=
  (realizes i j h).size_lt

/-- In particular, a direct-capture link table cannot realize two-way links.
Assuming its existence would exclude a mutually recursive group before any
step-indexed safety proof starts. -/
theorem no_two_way_links {ι : Type} {exports : ι → Tm} {links : ι → ι → Prop}
    (realizes : ∀ i j, links i j → Captures (exports i) (exports j))
    {i j : ι} (hij : links i j) (hji : links j i) : False :=
  no_mutual_captures (realizes i j hij) (realizes j i hji)

end Verification.LinkingCaptures
