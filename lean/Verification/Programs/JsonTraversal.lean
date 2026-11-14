import Verification.Programs.ObjectMerge

/-!
# The string-key traversal of a JSON value reaches no host object

`JSON.stringify` takes `JsonValue` (`library-globals.mts`), whose arms are
primitives, one dictionary indexed by every string key at `JsonValue`
itself, and one readonly array of `JsonValue | undefined`. Serialization
reads a non-array object's own string keys and descends into the values
found there. A host object's own keys are the package's internal fields
(HOST-FAMILIES.md, "Excluding host values"), so the contract is sound for
host values only if no object whose keys the traversal enumerates is one.
This module proves it for the primitive and dictionary arms; the array arm,
which serialization reads by its indices only, is argued in
HOST-FAMILIES.md and not stated here.

`reach_noHost`: in a world the heap satisfies, every value the traversal
reaches from a member of a JSON-shaped family within the step index is no
host object. Each object met is a dictionary (`dictViewT`), which owns no
`[[host]]`; the value under each of its string keys is a location whose
contract implies the family at every lower index, and the heap's
satisfaction of the world gives that location's value its contract, so the
argument descends by induction on the depth, one index per level. Symbol
keys, which the dictionary does not constrain, are not traversed.
-/

namespace Verification.JsonTraversal
open PositiveNormalization PositiveGraphs PositiveRules ObjectMerge

/-- The values the string-key traversal meets from `v` in `d` descents: `v`
itself, or, from an object, what the heap holds at the location of one of its
own string keys, and onward. -/
inductive Reach (h : Heap) : Nat → Val → Val → Prop
  | here (v : Val) : Reach h 0 v v
  | down {d : Nat} {fs : List (PropKey × Nat)} {c : CallCode} {oid l : Nat} {s : String} {w u : Val} :
      fs.lookup (.str s) = some l → h[l]? = some w → Reach h d w u →
      Reach h (d + 1) (.objAt fs c oid) u

/-- A family whose members are non-objects or dictionaries of string keys at
the family itself: `JsonValue`'s shape. -/
def JsonShaped (J : Fam) : Prop :=
  ∀ n W v, J n W v → (∀ fs c oid, v ≠ .objAt fs c oid) ∨ dictViewT .strings J n W v

/-- A member of a JSON-shaped family is no host object. -/
theorem noHost_of_shaped {J : Fam} (hJ : JsonShaped J) {n : Nat} {W : WorldT n} {v : Val}
    (hv : J n W v) : NoHost v := by
  rcases hJ n W v hv with hp | hd
  · intro flds oid he
    exact absurd he (hp flds .absent oid)
  · exact dictViewT_noHost hd

/-- **The traversal lemma.** Within the step index, in a world the heap
satisfies, the string-key traversal of a member of a JSON-shaped family
reaches no host object. -/
theorem reach_noHost {J : Fam} (hJ : JsonShaped J) {h : Heap} :
    ∀ {d n : Nat} {W : WorldT n} {v u : Val}, HeapOk n W h → J n W v → Reach h d v u → d < n →
      NoHost u := by
  intro d
  induction d with
  | zero =>
    intro n W v u _ hv hr _
    cases hr
    exact noHost_of_shaped hJ hv
  | succ d ih =>
    intro n W v u hok hv hr hd
    cases hr with
    | @down _ fs c oid l s w _ hl hw hrest =>
      rcases hJ n W _ hv with hp | hdict
      · exact absurd rfl (hp fs c oid)
      · obtain ⟨flds, oid', he, -, hkeys⟩ := hdict
        cases he
        obtain ⟨ctr, hW, himp⟩ := hkeys (.str s) l hl trivial
        obtain ⟨w', hw', hsat⟩ := hok.1.2 l ctr hW
        rw [hw] at hw'
        cases hw'
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hj : m < m + 1 := Nat.lt_succ_self m
        have hw'' : J m (trunc m (Nat.le_of_lt hj) W) w := himp m hj _ w (hsat m hj)
        exact ih (HeapOk_trunc m W h hok) hw'' hrest (by omega)

/-- A type whose every clause is a primitive one or a dictionary indexed by
every string key at the type itself is JSON-shaped. -/
theorem shaped_of_clauses {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {L : List ι}
    (hp : G.plainTy L = true)
    (hc : ∀ c ∈ expand G L, emptyClause c = true ∨ stringClause c = true ∨
      ∃ a bs vs ds os ms ks cs, c = .dict a bs vs ds os ms ks cs ∧ (IndexKeys.strings, L) ∈ ds) :
    JsonShaped (meaning G L) := by
  intro n W v hv
  obtain ⟨c, hm, hcv⟩ := (expand_sem G L hp n W v).mp hv
  rcases hc c hm with he | hs | ⟨a, bs, vs, ds, os, ms, ks, cs, rfl, hds⟩
  · refine .inl fun fs code oid hvo => ?_
    subst hvo
    obtain ⟨hcv, -⟩ := hcv
    cases c <;> simp_all [emptyClause, semWithArgs, nulT, undefT, boolT, numT, bigintT, symbolT]
    split at hcv <;> cases hcv
  · refine .inl fun fs code oid hvo => ?_
    subst hvo
    obtain ⟨hcv, -⟩ := hcv
    cases c <;> simp_all [stringClause, semWithArgs, strT]
  · obtain ⟨-, -, ⟨hd, -⟩, -⟩ := hcv.1
    exact .inr (hd _ hds)

end Verification.JsonTraversal
