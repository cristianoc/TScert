import Verification.Programs.GraphCode
import Verification.Semantics.ArgumentStoreRegions

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

/-- A normal edge can bind a result whose origin is established by the
node. A handler binds the thrown value without assigning it an origin. -/
def afterPush (facts : List Fact) (origin : Option ArgumentStoreRegion) : List Fact :=
  origin.toList.map (fun r => ⟨0, r⟩) ++ shift facts

theorem afterPush_sound {facts : List Fact} {origin : Option ArgumentStoreRegion}
    {ρ entry : Env} {h₀ : Heap} {v : Val} (hs : Holds facts ρ entry h₀)
    (hv : ∀ r, origin = some r → HeapKnowledge.readPath h₀ (entry r.position) r.path = some v) :
    Holds (afterPush facts origin) (push v ρ) entry h₀ := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    exact hv r (by simpa using hr)
  · exact shift_sound hs v f hf

def checkEdges (table : List (List Fact)) (facts : List Fact) (origin : Option ArgumentStoreRegion)
    (k : ControlFlow.Continuation) : Bool :=
  (CertificateProducer.successors k).all fun target =>
    checkMap (if pushes k then afterPush facts origin else facts) (atLabel table target.label) target.mapping

theorem checkEdges_sound {table : List (List Fact)} {facts : List Fact} {origin : Option ArgumentStoreRegion}
    {k : ControlFlow.Continuation} {ρ entry : Env} {h₀ : Heap} {v : Val}
    (hc : checkEdges table facts origin k = true) (hs : Holds facts ρ entry h₀)
    (hv : ∀ r, origin = some r → HeapKnowledge.readPath h₀ (entry r.position) r.path = some v) :
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

/-- Resolving a concatenated path is resolving its suffix from the prefix's value. -/
theorem readPath_append (h : Heap) (x : Val) (p q : List String) :
    HeapKnowledge.readPath h x (p ++ q) =
      (HeapKnowledge.readPath h x p).bind (fun v => HeapKnowledge.readPath h v q) := by
  induction p generalizing x with
  | nil => rfl
  | cons f p ih =>
    cases x <;> simp only [List.cons_append, HeapKnowledge.readPath, Option.bind_none]
    rename_i fs code oid
    split
    · split
      · exact ih _
      · rfl
    · rfl

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
  · simp only [readPath_append, hs f hf, Option.bind_some, push]
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

/-- A receiver-store call on a tracked slot fits the invocation's regional
bound. All other locations retain the closed footprint. -/
theorem receiver_call {c : Footprints.Closed} {regions : List ArgumentStoreRegion} {facts : List Fact}
    {ρ entry : Env} {h₀ h h' : Heap} {f : Fact}
    (hs : Holds facts ρ entry h₀) (hf : f ∈ facts) (hm : f.region ∈ regions)
    (hbefore : ArgumentStoreRegionsWithin c regions entry h₀ h)
    (hcall : c.HoldsOn (fun l => storeOf (ρ f.slot) ≠ some l) h h') :
    ArgumentStoreRegionsWithin c regions entry h₀ h' := by
  apply hbefore.trans_on
  apply hcall.weaken
  intro l hl heq
  exact hl.2 f.region hm ((resolve hs hf).trans heq)

/-- The receiver slot has a tracked origin among the declared regions. -/
def checkReceiver (facts : List Fact) (regions : List ArgumentStoreRegion) (receiver : Nat) : Bool :=
  facts.any fun f => f.slot == receiver && regions.contains f.region

/-- A checked receiver origin permits the existing receiver-store effect
inside the callee's regional bound. The footprint and own-field mode are
checked independently of the origin. -/
theorem checkReceiver_sound {c : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {facts : List Fact} {receiver : Nat} {ρ entry : Env} {h₀ h h' : Heap} {effect : CallEffects.Effect}
    (hc : checkReceiver facts regions receiver = true)
    (hs : Holds facts ρ entry h₀) (hbefore : ArgumentStoreRegionsWithin c regions entry h₀ h)
    (hcall : effect.within (ρ receiver) h h') (hstore : effect.receiverStore = true)
    (hown : effect.receiverOwn = false) (hle : effect.footprint.le c = true) :
    ArgumentStoreRegionsWithin c regions entry h₀ h' := by
  obtain ⟨f, hf, hx⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hx
  apply receiver_call hs hf hx.2 hbefore
  rw [hx.1]
  simp only [CallEffects.Effect.within, hstore, hown, Bool.false_eq_true, if_false, if_true] at hcall
  exact hcall.mono hle

end Verification.GraphCode.ArgumentPathTracking
