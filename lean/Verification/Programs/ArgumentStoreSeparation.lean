import Verification.Programs.ArgumentPathTracking
import Verification.Semantics.HeapSeparation

/-! Checked caller witnesses for framing an array store against argument
paths. Facts require semantic evidence; membership in a proposed table alone
does not establish them. -/
namespace Verification.ArgumentStoreSeparation
open Footprints PointClaims

structure Fact where
  root : Nat
  path : List String
  other : Nat
  deriving Repr, DecidableEq

def Holds (facts : List Fact) (ρ : Env) (h : Heap) : Prop :=
  ∀ f ∈ facts, StoreApart h (ρ f.root) f.path (ρ f.other)

/-- Every target fact must be justified by its incoming slot mapping. -/
def checkMap (source target : List Fact) (mapping : Mapping) : Bool :=
  target.all fun f => source.contains ⟨slot mapping f.root, f.path, slot mapping f.other⟩

theorem checkMap_sound {source target : List Fact} {mapping : Mapping} {ρ : Env} {h : Heap}
    (hc : checkMap source target mapping = true) (hs : Holds source ρ h) :
    Holds target (mapEnv mapping ρ) h := by
  intro f hf
  exact hs _ (List.contains_iff_mem.mp (List.all_eq_true.mp hc f hf))

def shift (facts : List Fact) : List Fact :=
  facts.map fun f => ⟨f.root + 1, f.path, f.other + 1⟩

theorem shift_sound {facts : List Fact} {ρ : Env} {h : Heap}
    (hs : Holds facts ρ h) (v : Val) : Holds (shift facts) (push v ρ) h := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact hs g hg

/-- Stable paths keep a table through any heap meeting the same world. -/
theorem frame {facts : List Fact} {ρ : Env} {h h' : Heap} {n m : Nat}
    {W : WorldT n} {U : WorldT m} (hs : Holds facts ρ h)
    (hp : ∀ f ∈ facts, ∃ v, StablePath W (ρ f.root) f.path v)
    (hm : m ≤ n) (hn : 0 < m) (hx : WExt (trunc m hm W) U)
    (hh : HeapOk n W h) (hh' : HeapOk m U h') : Holds facts ρ h' := by
  intro f hf
  obtain ⟨v, hv⟩ := hp f hf
  apply (hs f hf).transport
  intro u hu
  have he : u = v := Option.some.inj (hu.symm.trans (hv.read (Nat.lt_of_lt_of_le hn hm) hh))
  subst u
  exact (hv.transfer hm hx).read hn hh'

/-- The existing own-location separation checker establishes distinct stores.
The store witnesses ensure separation is not vacuous for a non-array value. -/
theorem of_separation {S : HeapSeparation.Separation} {ρ : Env} {h : Heap}
    {root value other : Nat} {path : List String} {s t : Nat}
    (hc : HeapSeparation.apart S value arrayStoreKey other arrayStoreKey = true)
    (hs : HeapSeparation.Holds S ρ)
    (hp : HeapKnowledge.readPath h (ρ root) path = some (ρ value))
    (hv : storeOf (ρ value) = some s) (ho : storeOf (ρ other) = some t) :
    StoreApart h (ρ root) path (ρ other) := by
  refine ⟨ρ value, s, t, hp, hv, ho, ?_⟩
  cases he : ρ value <;> simp [storeOf, fieldsOf, he] at hv
  cases hf : ρ other <;> simp [storeOf, fieldsOf, hf] at ho
  exact HeapSeparation.apart_sound hc hs he hv hf ho

/-- Substituting a proven field read transports separation to an object
literal's field path, without inferring separation from field names. -/
theorem prepend {h : Heap} {x v y : Val} {field : String} {path : List String}
    (hr : HeapKnowledge.readPath h x [field] = some v) (ha : StoreApart h v path y) :
    StoreApart h x (field :: path) y := by
  obtain ⟨u, s, t, hp, hs, ht, hne⟩ := ha
  refine ⟨u, s, t, ?_, hs, ht, hne⟩
  change HeapKnowledge.readPath h x ([field] ++ path) = some u
  rw [GraphCode.ArgumentPathTracking.readPath_append, hr]
  exact hp

/-- The call-position mapping names the actual slot at each position. Every
allowed region needs separation from the array whose length is framed. -/
def checkFrame (facts : List Fact) (regions : List ArgumentStoreRegion)
    (actuals : Mapping) (other : Nat) : Bool :=
  regions.all fun r => facts.contains ⟨slot actuals r.position, r.path, other⟩

theorem checkFrame_sound {facts : List Fact} {regions : List ArgumentStoreRegion}
    {actuals : Mapping} {other : Nat} {ρ : Env} {h : Heap}
    (hc : checkFrame facts regions actuals other = true) (hs : Holds facts ρ h) :
    ∀ r ∈ regions, StoreApart h ((mapEnv actuals ρ) r.position) r.path (ρ other) := by
  intro r hr
  exact hs _ (List.contains_iff_mem.mp (List.all_eq_true.mp hc r hr))

/-- Checked caller separation is sufficient to retain an exact length under
the semantic regional effect. The source checker must establish both premises. -/
theorem frame_length {facts : List Fact} {regions : List ArgumentStoreRegion}
    {actuals : Mapping} {other : Nat} {ρ : Env} {h h' : Heap} {c : Footprints.Closed} {n : Int}
    (hc : checkFrame facts regions actuals other = true) (hs : Holds facts ρ h)
    (hw : ArgumentStoreRegionsWithin c regions (mapEnv actuals ρ) h h')
    (hk : c.store = .keep) (hl : HeapKnowledge.lengthOf h (ρ other) = some n) :
    HeapKnowledge.lengthOf h' (ρ other) = some n :=
  hw.frame_length (checkFrame_sound hc hs) hk hl

/-- A table meeting its meaning cannot justify framing an alias of a region. -/
theorem checkFrame_not_alias {facts : List Fact} {regions : List ArgumentStoreRegion}
    {actuals : Mapping} {other : Nat} {ρ : Env} {h : Heap} {r : ArgumentStoreRegion}
    (hs : Holds facts ρ h) (hr : r ∈ regions)
    (ha : HeapKnowledge.readPath h ((mapEnv actuals ρ) r.position) r.path = some (ρ other)) :
    checkFrame facts regions actuals other = false := by
  cases hc : checkFrame facts regions actuals other with
  | false => rfl
  | true => exact (StoreApart.not_alias ha (checkFrame_sound hc hs r hr)).elim

end Verification.ArgumentStoreSeparation
