import Verification.Programs.GraphCode
import Verification.Semantics.ArgumentStoreRegions
import Verification.Semantics.FootprintRebase

/-! Callee provenance names values read from the invocation's entry heap.
Slot maps carry these values through joins and handlers. A field read extends
the path only when its reading agrees with the entry path. -/
namespace Verification.GraphCode.ArgumentPathTracking
open PointClaims Footprints

/-- A slot holding the value of an entry argument path. -/
structure Fact where
  slot : Nat
  region : ArgumentStoreRegion
  deriving Repr, DecidableEq

def Holds (facts : List Fact) (ρ entry : Env) (h₀ : Heap) : Prop :=
  ∀ f ∈ facts, HeapKnowledge.readPath h₀ (entry f.region.position) f.region.path = some (ρ f.slot)

/-- Entry facts describe only the corresponding parameter itself. -/
def checkEntry (facts : List Fact) : Bool :=
  facts.all fun f => f.slot == f.region.position && f.region.path.isEmpty

theorem checkEntry_sound {facts : List Fact} (hc : checkEntry facts = true) (ρ : Env) (h : Heap) :
    Holds facts ρ ρ h := by
  intro f hf
  have hx := List.all_eq_true.mp hc f hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hx
  simp [hx.1, hx.2, HeapKnowledge.readPath]

def shift (facts : List Fact) : List Fact := facts.map fun f => { f with slot := f.slot + 1 }

theorem shift_sound {facts : List Fact} {ρ entry : Env} {h₀ : Heap}
    (hc : Holds facts ρ entry h₀) (v : Val) : Holds (shift facts) (push v ρ) entry h₀ := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact hc g hg

/-- Every target fact has an incoming witness at its mapped source slot. -/
def checkMap (source target : List Fact) (mapping : Mapping) : Bool :=
  target.all fun f => source.contains { f with slot := slot mapping f.slot }

theorem checkMap_sound {source target : List Fact} {mapping : Mapping} {ρ entry : Env} {h₀ : Heap}
    (hc : checkMap source target mapping = true) (hs : Holds source ρ entry h₀) :
    Holds target (mapEnv mapping ρ) entry h₀ := by
  intro f hf
  exact hs _ (List.contains_iff_mem.mp (List.all_eq_true.mp hc f hf))

/-- Facts at each label; the checker requires them at every incoming edge. -/
def atLabel (table : List (List Fact)) (label : Nat) : List Fact := table.getD label []

/-- A normal edge can bind a result whose origins are established by the
node. A handler binds the thrown value without assigning it an origin. -/
def afterPush (facts : List Fact) (origins : List ArgumentStoreRegion) : List Fact :=
  origins.map (fun r => ⟨0, r⟩) ++ shift facts

theorem afterPush_sound {facts : List Fact} {origins : List ArgumentStoreRegion}
    {ρ entry : Env} {h₀ : Heap} {v : Val} (hs : Holds facts ρ entry h₀)
    (hv : ∀ r ∈ origins, HeapKnowledge.readPath h₀ (entry r.position) r.path = some v) :
    Holds (afterPush facts origins) (push v ρ) entry h₀ := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    exact hv r hr
  · exact shift_sound hs v f hf

def checkEdges (table : List (List Fact)) (facts : List Fact) (origins : List ArgumentStoreRegion)
    (k : ControlFlow.Continuation) : Bool :=
  (CertificateProducer.successors k).all fun target =>
    checkMap (if pushes k then afterPush facts origins else facts) (atLabel table target.label) target.mapping

theorem checkEdges_sound {table : List (List Fact)} {facts : List Fact} {origins : List ArgumentStoreRegion}
    {k : ControlFlow.Continuation} {ρ entry : Env} {h₀ : Heap} {v : Val}
    (hc : checkEdges table facts origins k = true) (hs : Holds facts ρ entry h₀)
    (hv : ∀ r ∈ origins, HeapKnowledge.readPath h₀ (entry r.position) r.path = some v) :
    ∀ target ∈ CertificateProducer.successors k,
      Holds (atLabel table target.label)
        (mapEnv target.mapping (if pushes k then push v ρ else ρ)) entry h₀ := by
  intro target ht
  have he := List.all_eq_true.mp hc target ht
  cases hk : pushes k
  · simp only [hk, Bool.false_eq_true, if_false] at he ⊢
    exact checkMap_sound he hs
  · simp only [hk, if_true] at he ⊢
    exact checkMap_sound he (afterPush_sound hs hv)

def checkHandler (table : List (List Fact)) (facts : List Fact) (handler : Option ControlFlow.Target) : Bool :=
  handler.toList.all fun target => checkMap (shift facts) (atLabel table target.label) target.mapping

theorem checkHandler_sound {table : List (List Fact)} {facts : List Fact}
    {handler : Option ControlFlow.Target} {ρ entry : Env} {h₀ : Heap}
    (hc : checkHandler table facts handler = true) (hs : Holds facts ρ entry h₀)
    (target : ControlFlow.Target) (ht : handler = some target) (v : Val) :
    Holds (atLabel table target.label) (mapEnv target.mapping (push v ρ)) entry h₀ := by
  have he := List.all_eq_true.mp hc target (by simp [ht])
  exact checkMap_sound he (shift_sound hs v)

/-- A typed stable field and a successful own-field read supply the stable
path witness used by callee tracking. Optional absent fields supply none. -/
theorem stableField_path {G : PositiveGraphs.NormalGraph ι} {A : ProgramTyping.Ty ι}
    {field : String} {x v : Val} {n : Nat} {W : WorldT n} {h : Heap}
    (hc : HeapExpressionRules.stableField G A (.str field) = true)
    (ht : PositiveRules.meaning G A n W x) (hn : 0 < n) (hh : HeapOk n W h)
    (hr : HeapKnowledge.readPath h x [field] = some v) : StablePath W x [field] v := by
  obtain ⟨fs, oid, rfl, hs⟩ := HeapExpressionRules.stableField_at hc ht
  cases hf : fs.lookup (.str field) with
  | none => simp [HeapKnowledge.readPath, hf] at hr
  | some l =>
    obtain ⟨c, u, hl, hstable⟩ := hs.present hf
    have hu := hh.stable_value hn hl hstable
    have he : u = v := by simpa [HeapKnowledge.readPath, hf, hu] using hr
    subst v
    exact .cons hf hl hstable .nil

/-! ## The entry world's stable witnesses

A store region's path through a field, `R.f[*]`, is tracked from the field's
read in the body. The read agrees with the entry heap's because the field is
stable in the entry parameter's contract: the entry check
(`checkEntryFields`) supplies, at the invocation's entry world, the field's
stable witness; the graph proof carries it, transferred to each node's world
(`StableNow`); a read of the tracked slot then reads the entry value
(`read_now`). A stable-field check of a later context alone never extends a
path. -/

/-- The fields a region's path traverses from its position: a path of one
field, `(x, [f])`, names `f` of position `x`. -/
def stableFields (regions : List ArgumentStoreRegion) : List (Nat × String) :=
  regions.filterMap fun r => match r.path with
    | [f] => some (r.position, f)
    | _ => none

/-- Each traversed field, where the entry value has it, read a value at the
entry heap, and its read is fixed in the world `W` (`StablePath`): the entry
world's witness, transferred to `W`. Where the entry value has no such field
(`null`, `undefined`), no heap reads it. -/
def StableNow (fields : List (Nat × String)) (entry : Env) (h₀ : Heap) {n : Nat} (W : WorldT n) : Prop :=
  ∀ p ∈ fields, (Footprints.fieldsOf (entry p.1)).lookup (.str p.2) = none ∨
    ∃ v, isVal v = true ∧ HeapKnowledge.readPath h₀ (entry p.1) [p.2] = some v ∧
      StablePath W (entry p.1) [p.2] v

theorem StableNow.transfer {fields : List (Nat × String)} {entry : Env} {h₀ : Heap} {n m : Nat}
    {W : WorldT n} {U : WorldT m} (hs : StableNow fields entry h₀ W) (hm : m ≤ n)
    (hx : WExt (trunc m hm W) U) : StableNow fields entry h₀ U :=
  fun p hp => (hs p hp).imp id fun ⟨v, hv, hr, hsp⟩ => ⟨v, hv, hr, hsp.transfer hm hx⟩

/-- **Conditional agreement.** Where the current heap reads a traversed
field of its entry value, the entry heap read the same value. -/
theorem StableNow.agree {fields : List (Nat × String)} {entry : Env} {h₀ h : Heap} {n : Nat}
    {W : WorldT n} {x : Nat} {f : String} {v : Val} (hs : StableNow fields entry h₀ W) (hfld : (x, f) ∈ fields)
    (hn : 0 < n) (hh : HeapOk n W h) (hv : HeapKnowledge.readPath h (entry x) [f] = some v) :
    HeapKnowledge.readPath h₀ (entry x) [f] = some v := by
  rcases hs _ hfld with hnone | ⟨u, -, hu, hsp⟩
  · have hnil : HeapKnowledge.readPath h (entry x) [f] = none := by
      cases hx : entry x <;> simp only [hx, Footprints.fieldsOf] at hnone <;>
        simp [HeapKnowledge.readPath, hnone]
    rw [hnil] at hv
    cases hv
  · rw [hsp.read hn hh] at hv
    cases hv
    exact hu

/-- The alternatives of a type a field read fails on: `null` and `undefined`. -/
def absentClause : PositiveNormalization.Clause α → Bool
  | .nul | .undef => true
  | _ => false

/-- The alternatives of `A` a field read succeeds on. -/
def presentClauses (G : PositiveGraphs.NormalGraph ι) (A : ProgramTyping.Ty ι) :
    List (PositiveNormalization.Clause (ProgramTyping.Ty ι)) :=
  (PositiveRules.expand G A).filter fun c => !absentClause c

/-- A traversed field's entry contract: on every alternative of `A` a read
succeeds on, a field the read finds (`fieldOperand`) and a stable key, and
there is such an alternative. `null` and `undefined` alternatives read no
field. -/
def entryField [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι) (A : ProgramTyping.Ty ι) (f : String) : Bool :=
  G.plainTy A && HeapExpressionRules.fieldOperand (presentClauses G A) (.str f) &&
    (presentClauses G A).all fun c => c.stableKeys.contains (.str f)

/-- **The entry check of traversed fields.** Each is a field of its
position's entry contract `entryField` accepts, an input slot of the unit,
and every region's path has at most one field. -/
def checkEntryFields [DecidableEq ι] (G : PositiveGraphs.NormalGraph ι) (inputs : List (ProgramTyping.Ty ι))
    (regions : List ArgumentStoreRegion) : Bool :=
  regions.all (·.path.length ≤ 1) &&
  (stableFields regions).all fun (x, f) => match inputs[x]? with
    | some A => entryField G A f
    | none => false

theorem checkEntryFields_paths [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι} {inputs : List (ProgramTyping.Ty ι)}
    {regions : List ArgumentStoreRegion} (hc : checkEntryFields G inputs regions = true) :
    ∀ r ∈ regions, r.path.length ≤ 1 := by
  simp only [checkEntryFields, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  exact hc.1

/-- The entry check gives the stable witnesses at the entry world. -/
theorem checkEntryFields_sound [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {inputs : List (ProgramTyping.Ty ι)} {regions : List ArgumentStoreRegion}
    (hc : checkEntryFields G inputs regions = true) {entry : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : ProgramTyping.EnvOk G inputs entry n W) (hn : 0 < n) (hh : HeapOk n W h) :
    StableNow (stableFields regions) entry h W := by
  intro p hp
  simp only [checkEntryFields, Bool.and_eq_true, List.all_eq_true] at hc
  have hx := hc.2 p hp
  cases hA : inputs[p.1]? with
  | none => rw [hA] at hx; cases hx
  | some A =>
    rw [hA] at hx
    simp only [entryField, Bool.and_eq_true, List.all_eq_true] at hx
    obtain ⟨⟨hplain, hop⟩, hstable⟩ := hx
    have hv := he.2 p.1 A hA
    obtain ⟨c, hm, hcs, -⟩ := (PositiveRules.expand_sem G A hplain n W (entry p.1)).mp hv
    cases habs : absentClause c
    · have hmp : c ∈ presentClauses G A := List.mem_filter.mpr ⟨hm, by simp [habs]⟩
      have hfield : HeapExpressionRules.clauseField c (.str p.2) = true := by
        simp only [HeapExpressionRules.fieldOperand, Bool.and_eq_true, List.all_eq_true] at hop
        exact hop.2 c hmp
      obtain ⟨_, flds, code, oid, l, c', hobj, hl, hlw', htyped, -⟩ :=
        HeapExpressionRules.clauseField_typed hmp hfield hcs
      obtain ⟨flds', oid', hobj', hs⟩ :=
        PositiveNormalization.semWithArgs_stable hcs (List.contains_iff_mem.mp (hstable c hmp))
      rw [hobj] at hobj'
      cases hobj'
      obtain ⟨c, u, hlw, hstab⟩ := hs.present hl
      have hu := hh.stable_value hn hlw hstab
      rw [hlw] at hlw'
      cases hlw'
      obtain ⟨u', hu', hcu⟩ := hh.2 l _ hlw
      rw [hu] at hu'
      cases hu'
      have hval : isVal u = true :=
        (ProgramTyping.meaning_value (htyped 0 hn _ u (hcu 0 hn))).1
      refine .inr ⟨u, hval, ?_, ?_⟩
      · rw [hobj]; simp [HeapKnowledge.readPath, hl, hu]
      · rw [hobj]; exact .cons hl hlw hstab .nil
    · refine .inl ?_
      cases c <;> simp only [absentClause, Bool.false_eq_true] at habs
      · rw [show entry p.1 = .nul from hcs]; rfl
      · rw [show entry p.1 = .undef from hcs]; rfl

/-- A read of a tracked slot holding a position's entry value, through a
traversed field the value has, reads the field's entry value. -/
theorem read_now {facts : List Fact} {ρ entry : Env} {h₀ h : Heap} {fields : List (Nat × String)}
    {n : Nat} {W : WorldT n} {i x : Nat} {f : String}
    (hs : Holds facts ρ entry h₀) (hf : (⟨i, ⟨x, []⟩⟩ : Fact) ∈ facts) (hfld : (x, f) ∈ fields)
    (hst : StableNow fields entry h₀ W) (hn : 0 < n) (hh : HeapOk n W h)
    (hpresent : (Footprints.fieldsOf (ρ i)).lookup (.str f) ≠ none) :
    ∃ v, isVal v = true ∧ HeapKnowledge.readPath h₀ (entry x) [f] = some v ∧
      HeapKnowledge.readPath h (ρ i) [f] = some v := by
  have hx : entry x = ρ i := by
    have := hs _ hf
    simpa [HeapKnowledge.readPath] using this
  rcases hst _ hfld with hnone | ⟨v, hv, hr, hsp⟩
  · exact absurd (hx ▸ hnone) hpresent
  · exact ⟨v, hv, hr, hx ▸ hsp.read hn hh⟩

/-- Copying a tracked slot establishes the same path at the result slot. -/
theorem copy {facts : List Fact} {ρ entry : Env} {h₀ : Heap} {f : Fact}
    (hs : Holds facts ρ entry h₀) (hf : f ∈ facts) :
    Holds ({ f with slot := 0 } :: shift facts) (push (ρ f.slot) ρ) entry h₀ := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hs f hf
  · exact shift_sound hs _ g hg

/-- A read of a tracked value extends its entry path when the entry path's
reading is preserved. The result's array store may change independently. -/
theorem read {facts : List Fact} {ρ entry : Env} {h₀ h : Heap} {f : Fact} {field : String} {v : Val}
    (hs : Holds facts ρ entry h₀) (hf : f ∈ facts)
    (hr : HeapKnowledge.readPath h (ρ f.slot) [field] = some v)
    (hp : HeapKnowledge.readPath h₀ (ρ f.slot) [field] =
      HeapKnowledge.readPath h (ρ f.slot) [field]) :
    Holds (⟨0, ⟨f.region.position, f.region.path ++ [field]⟩⟩ :: shift facts)
      (push v ρ) entry h₀ := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp only [Footprints.readPath_append, hs f hf, Option.bind_some, push]
    exact hp.trans hr
  · exact shift_sound hs _ g hg

/-- A stable field supplies the read's preservation obligation in every
heap meeting an extension of the entry world, including alias mutations. -/
theorem read_stable {facts : List Fact} {ρ entry : Env} {h₀ h : Heap} {f : Fact}
    {field : String} {v : Val} {n m : Nat} {W : WorldT n} {U : WorldT m}
    (hs : Holds facts ρ entry h₀) (hf : f ∈ facts)
    (hp : StablePath W (ρ f.slot) [field] v) (hm : m ≤ n) (hn : 0 < m)
    (hx : WExt (trunc m hm W) U) (hh₀ : HeapOk n W h₀) (hh : HeapOk m U h) :
    Holds (⟨0, ⟨f.region.position, f.region.path ++ [field]⟩⟩ :: shift facts)
      (push v ρ) entry h₀ :=
  read hs hf ((hp.transfer hm hx).read hn hh)
    ((hp.read (Nat.lt_of_lt_of_le hn hm) hh₀).trans ((hp.transfer hm hx).read hn hh).symm)

/-- The store at a tracked slot is the store the entry region selects. -/
theorem resolve {facts : List Fact} {ρ entry : Env} {h₀ : Heap} {f : Fact}
    (hs : Holds facts ρ entry h₀) (hf : f ∈ facts) :
    f.region.resolve entry h₀ = storeOf (ρ f.slot) := by
  simp [ArgumentStoreRegion.resolve, hs f hf]

end Verification.GraphCode.ArgumentPathTracking
