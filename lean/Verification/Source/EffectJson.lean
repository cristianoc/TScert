import Lean.Data.Json
import Verification.Semantics.CallEffects

/-! The one JSON form of a call signature's effect, read and written by the
Fragment's declaration document, the claims document and the evidence: a
closed `footprint`, `{"value", "store"}`; a `promise`, `null` or
`{"guards": {"param": p}}` or `{"asserts": {"param": p}}`; the Booleans
`fresh`, `receiverStore`, `onThrow`, `receiverOwn` and `freshObject`; and the
element predicates `requires` and `elements`, each `null` or its kinds in
order; the index-fact lists `pre` and `ensures`; the Boolean
`receiverGrows`; and `elementWrite`, `null`, `"stores"` or the exact write of an element type,
`"exactUint8"`, `"exactUint16"`, `"exactInt32"` or `"exactFloat64"`, whose
precondition states the value's range (`ElementKind.preFacts`, which
`ElementKind.takes_of_requires` reads as the range `ExactWrite` states). Each decoder
re-encodes what it read and refuses a document that differs, so a field
outside these, a `grow` on `value` or an `init` or `scalar` on `store`, is refused. -/
namespace Verification.EffectJson
open Lean CallEffects

/-- An element write's wire name. -/
def elementWriteName : ElementWrite → String
  | .stores => "stores"
  | .assign => "assign"
  | .exact .uint8 => "exactUint8"
  | .exact .uint16 => "exactUint16"
  | .exact .int32 => "exactInt32"
  | .exact .float64 => "exactFloat64"

private def elementWriteOf (name : String) : Except String ElementWrite :=
  match [ElementWrite.stores, .assign, .exact .uint8, .exact .uint16, .exact .int32, .exact .float64].find?
      (elementWriteName · == name) with
  | some w => pure w
  | none => throw s!"invalid element write '{name}'"

/-- A change's wire name. -/
def changeName : Footprints.Change → String
  | .keep => "keep"
  | .init => "init"
  | .scalar => "scalar"
  | .grow => "grow"
  | .any => "any"

private def changeOf (allowed : List Footprints.Change) (name : String) : Except String Footprints.Change :=
  match allowed.find? (changeName · == name) with
  | some d => pure d
  | none => throw s!"invalid footprint change '{name}'"

instance : ToJson Footprints.Closed :=
  ⟨fun c => Json.mkObj [("value", toJson (changeName c.value)), ("store", toJson (changeName c.stores))]⟩

/-- On a value `grow` is `scalar`, so `value` is `keep`, `init`, `scalar` or
`any`; on a store `init` and `scalar` are `keep`, so `store` is `keep`,
`grow` or `any`. The wire's `store` is the change of both store components
(`Footprints.Closed.ofStores`), and a closed footprint is written with its
store bound (`Footprints.Closed.stores`). -/
instance : FromJson Footprints.Closed := ⟨fun j => do
  let c : Footprints.Closed := .ofStores (← changeOf [.keep, .init, .scalar, .any] (← j.getObjValAs? String "value"))
    (← changeOf [.keep, .grow, .any] (← j.getObjValAs? String "store"))
  if toJson c != j then throw "a closed footprint has exactly the fields value and store"
  pure c⟩

instance : ToJson TypePromise := ⟨fun
  | .guards p => Json.mkObj [("guards", Json.mkObj [("param", toJson p)])]
  | .asserts p => Json.mkObj [("asserts", Json.mkObj [("param", toJson p)])]⟩

instance : FromJson TypePromise := ⟨fun j => do
  let p ← match j.getObjVal? "guards", j.getObjVal? "asserts" with
    | .ok g, .error _ => pure (TypePromise.guards (← g.getObjValAs? Nat "param"))
    | .error _, .ok a => pure (TypePromise.asserts (← a.getObjValAs? Nat "param"))
    | _, _ => throw "a promise is a guard's or an assertion function's"
  if toJson p != j then throw "a promise has exactly one field, and its parameter"
  pure p⟩

/-- An elements predicate is the list of the kinds it admits, in this order. -/
def predKinds (R : ElemPred) : List String :=
  [("null", R.nul), ("undefined", R.undef), ("boolean", R.bool), ("number", R.num), ("string", R.str),
    ("bigint", R.big), ("symbol", R.sym), ("object", R.obj)].filterMap fun (k, b) => if b then some k else none

def predOfKinds (ks : List String) : ElemPred :=
  ⟨ks.contains "null", ks.contains "undefined", ks.contains "boolean", ks.contains "number",
    ks.contains "string", ks.contains "bigint", ks.contains "symbol", ks.contains "object"⟩

private def predJson : Option ElemPred → Json
  | none => Json.null
  | some R => toJson (predKinds R)

private def predOf : Json → Except String (Option ElemPred)
  | .null => pure none
  | j => do pure (some (predOfKinds (← fromJson? j)))

-- An index fact, in a precondition at the call's positions (`0` the
-- receiver, `i + 1` the `i`-th actual), in a postcondition at the return's
-- positions (`0` the result, `i + 1` the call's position `i`) and in
-- diagnostics' knowledge: its
-- constructor's name holding its fields; a linear term is `{"kind", "slot",
-- "path"}`, its kind's name, its root and its fields, and an entry term
-- `old(t)` (the note "Tolerant frames", section 6) also `"atEntry": true`,
-- its root a position of the entry's.
deriving instance ToJson, FromJson for HeapKnowledge.Term.Kind
instance : ToJson HeapKnowledge.Term where
  toJson t := Json.mkObj ([("kind", toJson t.kind), ("slot", toJson t.slot), ("path", toJson t.path)] ++
    if t.atEntry then [("atEntry", toJson true)] else [])
instance : FromJson HeapKnowledge.Term where
  fromJson? j := do
    let kind ← j.getObjValAs? HeapKnowledge.Term.Kind "kind"
    let slot ← j.getObjValAs? Nat "slot"
    let path ← j.getObjValAs? (List String) "path"
    let atEntry ← match j.getObjVal? "atEntry" with
      | .ok v => fromJson? v
      | .error _ => pure false
    return if atEntry then .old kind slot path else .now kind slot path
deriving instance ToJson, FromJson for HeapKnowledge.Bound
deriving instance ToJson, FromJson for Linear.Fact
private def clauseJson [ToJson V] : HeapKnowledge.LinearClause V → Json
  | .atom F => toJson F
  | .either A B => Json.mkObj [("either", Json.mkObj [("left", clauseJson A), ("right", clauseJson B)])]

instance [ToJson V] : ToJson (HeapKnowledge.LinearClause V) := ⟨clauseJson⟩

private partial def clauseOf [ToJson V] [FromJson V] (j : Json) : Except String (HeapKnowledge.LinearClause V) := do
  let c ← match j.getObjVal? "either" with
    | .ok b => do pure (.either (← clauseOf (← b.getObjVal? "left")) (← clauseOf (← b.getObjVal? "right")))
    | .error _ => HeapKnowledge.LinearClause.atom <$> fromJson? j
  if toJson c != j then throw "a linear clause has exactly its constructor's fields"
  pure c

instance [ToJson V] [FromJson V] : FromJson (HeapKnowledge.LinearClause V) := ⟨clauseOf⟩

-- A guard's tag is a nullish or Boolean literal; a guarded fact is
-- `{"guarded": {"slot", "path", "tag", "body"}}`.
instance : ToJson HeapKnowledge.GuardTag := ⟨fun
  | .null => "null"
  | .undef => "undefined"
  | .tru => "true"
  | .fls => "false"⟩
instance : FromJson HeapKnowledge.GuardTag := ⟨fun
  | .str "null" => pure .null
  | .str "undefined" => pure .undef
  | .str "true" => pure .tru
  | .str "false" => pure .fls
  | _ => throw "a guard's tag is a nullish or Boolean literal"⟩
deriving instance ToJson, FromJson for HeapKnowledge.IndexFact

/-! ## The wire form of an effect

The document's fields of an effect are their own datatype (`WireEffect`).
A value of it read from a document is elaborated into the effect it states
(`WireEffect.elaborate`); an effect is written only where it is exactly
the elaboration of a valid wire value (`Representable`, `encodeOld`), so
writing never weakens an effect. -/

/-- **An effect as the documents write it**: its footprint, its promise,
`null` when there is none, whether its result's array store is fresh,
whether its footprint excepts its receiver's store, whether the footprint
also holds on a throw, whether it excepts its receiver's own locations, and
whether its result is an object every own location of which is fresh, its
precondition on the receiver's elements and its elements promise, its
precondition on the call's values (`pre`) and the facts a normal return
states (`ensures`), whether it grows its receiver's store, its element
write, and, where it states any, its frame's store regions, each a position
and a path (`regions`). Its footprint is the frame's closed bound. -/
structure WireEffect where
  closed : Footprints.Closed
  promise : Option TypePromise
  fresh : Bool
  receiverStore : Bool
  onThrow : Bool
  receiverOwn : Bool
  freshObject : Bool
  requires : Option ElemPred
  elements : Option ElemPred
  pre : List HeapKnowledge.IndexFact
  ensures : List HeapKnowledge.IndexFact
  receiverGrows : Bool
  elementWrite : Option ElementWrite
  regions : List Footprints.ArgumentStoreRegion
  deriving Repr, DecidableEq

/-- **A valid wire value**: its footprint is one the wire writes (a value
change `keep`, `init`, `scalar` or `any`, one store change `keep`, `grow`
or `any` for both stores, `Footprints.Closed.ofStores`), and an exact
element write states its value's range in its precondition
(`ElementKind.preFacts`, which `ElementKind.takes_of_requires` reads). -/
def WireEffect.valid (w : WireEffect) : Bool :=
  Footprints.Closed.ofStores w.closed.value w.closed.stores == w.closed &&
    [Footprints.Change.keep, .init, .scalar, .any].contains w.closed.value &&
    [Footprints.Change.keep, .grow, .any].contains w.closed.stores &&
    match w.elementWrite with
    | some (.exact k) => k.preFacts.all w.pre.contains
    | _ => true

def WireEffect.Valid (w : WireEffect) : Prop := w.valid = true

/-- The receiver's entries a wire value's frame states: with `receiverOwn`,
its own locations holding a value at `any` (one holding a store stays at
the closed bound's stores); else, with `receiverStore`, its store's location
at `any`. -/
def WireEffect.receiverEntries (w : WireEffect) : Footprints.Footprint :=
  if w.receiverOwn then [(.inCls (.own 0) .values, .any)]
  else if w.receiverStore then [(.field 0 arrayStoreKey, .any)] else []

/-- **The frame a wire value states**: its closed bound's three class
entries, its receiver's entries and its argument store regions, read at the
call's positions. -/
def WireEffect.frame (w : WireEffect) : Footprints.Footprint :=
  w.closed.fp ++ w.receiverEntries ++ w.regions.map regionEntry

/-- **The postconditions a wire value states of a normal return**: the
result's fresh store and fresh object, the receiver's elements where the
result is `true`, the index facts, the receiver's growth and the append of
the actuals, and a typed array's element write
(`ElementWrite.schemaPosts`). -/
def WireEffect.normalSchema (w : WireEffect) : List Parity.FormulaSchema :=
  (if w.fresh then [.operation (.freshStore 0)] else [] : List Parity.FormulaSchema) ++
  (if w.freshObject then [.operation (.freshObject 0)] else [] : List Parity.FormulaSchema) ++
  (match w.elements with
    | some R => [.operation (.elementsWhen 0 .tru 1 R)]
    | none => [] : List Parity.FormulaSchema) ++
  w.ensures.map (fun F => (.operation (.fact .after 0 F) : Parity.FormulaSchema)) ++
  (if w.receiverGrows then
    [.transition [(.field 0 arrayStoreKey, .any)], .operation (.storeExtends 0),
      .operation (.push 0 1 (.restFrom 1))] else [] : List Parity.FormulaSchema) ++
  (match w.elementWrite with
    | some k => k.schemaPosts
    | none => [])

/-- **The effect a wire value states**: the normal exit its frame and its
postconditions, the exceptional exit its frame where it states `onThrow`,
the note's `⊤` otherwise, with no postcondition; its promise and
preconditions. -/
def WireEffect.elaborate (w : WireEffect) : Effect :=
  ⟨⟨⟨w.frame, w.normalSchema⟩, if w.onThrow then ⟨w.frame, []⟩ else ⟨Parity.topEffect, []⟩⟩,
    w.promise, w.requires, w.pre⟩

/-- **The canonical wire value of the effect a wire value states**: two wire
values state one effect where they differ only in `receiverStore` beside
`receiverOwn`, whose entry covers the store, or in `onThrow` where the frame
is `⊤`; the canonical one states neither. -/
def WireEffect.canonicalize (w : WireEffect) : WireEffect :=
  { w with receiverStore := w.receiverStore && !w.receiverOwn,
           onThrow := w.onThrow && !decide (w.frame = Parity.topEffect) }

/-- A wire value is canonical where it is its own canonical value. -/
def WireEffect.Canonical (w : WireEffect) : Prop := w.canonicalize = w

theorem WireEffect.valid_canonicalize (w : WireEffect) : w.canonicalize.valid = w.valid := rfl

private theorem WireEffect.frame_canonicalize (w : WireEffect) : w.canonicalize.frame = w.frame := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  cases ro <;> simp [WireEffect.frame, WireEffect.canonicalize, WireEffect.receiverEntries]

/-- **The canonical value states the same effect** (proved). -/
theorem WireEffect.elaborate_canonicalize (w : WireEffect) : w.canonicalize.elaborate = w.elaborate := by
  have hf := WireEffect.frame_canonicalize w
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  simp only [WireEffect.elaborate, hf]
  simp only [WireEffect.canonicalize]
  cases o <;> by_cases ht : WireEffect.frame ⟨c, p, f, rs, true, ro, fo, rq, el, pr, en, rg, ew, regs⟩ = Parity.topEffect <;>
    simp_all [WireEffect.normalSchema, WireEffect.frame, WireEffect.receiverEntries]

/-! ### Reading a wire value back from the exits it states -/

/-- The receiver's own entry of a frame. -/
private def ownEntry : Footprints.Region × Footprints.Change := (.inCls (.own 0) .values, .any)

/-- The receiver's store entry of a frame. -/
private def storeEntry : Footprints.Region × Footprints.Change := (.field 0 arrayStoreKey, .any)

/-- The argument store region an entry of a frame states, where it is one
(`ArgumentStoreRegion.entry`). -/
private def storeRegionOf : Footprints.Region × Footprints.Change → Option Footprints.ArgumentStoreRegion
  | (.path p path k, .any) => if k = arrayStoreKey then some ⟨p, path⟩ else none
  | _ => none

/-- The format a postcondition states View-Write at, where it is one. -/
private def viewWriteFormatOf : Parity.FormulaSchema → Option (Option ViewFormat)
  | .operation (.viewWrite 1 2 3 g) => some g
  | _ => none

/-- **The element write a list of postconditions states**: an exact write
at the element type of the format its View-Write states, an element
assignment where it states View-Write at the typed array's own format, the
views' growth alone otherwise. -/
private def elementWriteIn (q : List Parity.FormulaSchema) : Option ElementWrite :=
  match (q.filterMap viewWriteFormatOf).head? with
  | some (some f) => some (.exact (ElementKind.ofFormat f))
  | some none => some .assign
  | none => if Parity.FormulaF.transition [(.cls .views, .grow)] ∈ q then some .stores else none

/-- **The wire value an effect is read as**: each field from the reader of
the exit that states it (the frame's class bound, receiver entries and store
regions; the normal exit's fresh result, fresh object, elements, facts,
growth and element write; the throw flag where the exceptional exit is the
normal frame and the frame is no `⊤`). It is the canonical wire value of
every effect a wire value states (`wireOf_elaborate`). -/
def wireOf (e : Effect) : WireEffect :=
  let q := e.schema.normal
  let own := decide (ownEntry ∈ q.frame)
  ⟨q.frame.classBound, e.promise, q.freshResult, decide (storeEntry ∈ q.frame) && !own,
    decide (e.schema.exceptional = ⟨q.frame, []⟩) && !decide (q.frame = Parity.topEffect), own,
    q.freshObjectResult, e.requires, q.elementsWhenTrue.head?, e.pre, q.facts,
    decide (Parity.FormulaF.operation (.storeExtends 0) ∈ q.ensures), elementWriteIn q.ensures,
    q.frame.filterMap storeRegionOf⟩

section Readers
variable (w : WireEffect)

private theorem frame_classBound : w.frame.classBound = w.closed := by
  have hr : w.receiverEntries.filter (·.1.isClass) = [] := by
    unfold WireEffect.receiverEntries
    split
    · rfl
    · split <;> rfl
  have hg : (w.regions.map regionEntry).filter (·.1.isClass) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    simp [regionEntry, Footprints.ArgumentStoreRegion.entry, Footprints.Region.isClass]
  have hc : w.closed.fp.filter (·.1.isClass) = w.closed.fp := rfl
  have hf := Footprints.Closed.closed?_fp w.closed
  simp only [Footprints.Footprint.closed?] at hf
  split at hf
  · simp only [Footprints.Footprint.classBound, Footprints.Footprint.classes, WireEffect.frame,
      List.filter_append, hr, hg, hc, List.append_nil]
    exact Option.some.inj hf
  · cases hf

private theorem mem_frame_receiver {x : Footprints.Region × Footprints.Change} (hx : x = ownEntry ∨ x = storeEntry) :
    x ∈ w.frame ↔ x ∈ w.receiverEntries := by
  simp only [WireEffect.frame, List.mem_append, List.mem_map]
  constructor
  · rintro ((h | h) | ⟨r, -, rfl⟩)
    · rcases hx with rfl | rfl <;> simp [Footprints.Closed.fp, ownEntry, storeEntry] at h
    · exact h
    · rcases hx with h | h <;> simp [regionEntry, Footprints.ArgumentStoreRegion.entry, ownEntry, storeEntry] at h
  · exact fun h => .inl (.inr h)

private theorem frame_own : decide (ownEntry ∈ w.frame) = w.receiverOwn := by
  simp only [mem_frame_receiver w (.inl rfl)]
  by_cases ho : w.receiverOwn = true <;> by_cases hs : w.receiverStore = true <;>
    simp [WireEffect.receiverEntries, ho, hs, ownEntry]

private theorem frame_store : (decide (storeEntry ∈ w.frame) && !decide (ownEntry ∈ w.frame)) =
    (w.receiverStore && !w.receiverOwn) := by
  simp only [mem_frame_receiver w (.inr rfl), frame_own]
  by_cases ho : w.receiverOwn = true <;> by_cases hs : w.receiverStore = true <;>
    simp [WireEffect.receiverEntries, ho, hs, storeEntry]

private theorem frame_regions : w.frame.filterMap storeRegionOf = w.regions := by
  have hr : w.receiverEntries.filterMap storeRegionOf = [] := by
    unfold WireEffect.receiverEntries
    split
    · rfl
    · split <;> rfl
  have hc : w.closed.fp.filterMap storeRegionOf = [] := rfl
  simp only [WireEffect.frame, List.filterMap_append, hr, hc, List.nil_append, List.filterMap_map]
  induction w.regions with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.filterMap_cons, Function.comp_apply, ih]
    simp [storeRegionOf, regionEntry, Footprints.ArgumentStoreRegion.entry]

private theorem exceptional_throw :
    (decide ((if w.onThrow = true then (⟨w.frame, []⟩ : ExitSchema) else ⟨Parity.topEffect, []⟩) = ⟨w.frame, []⟩) &&
      !decide (w.frame = Parity.topEffect)) = (w.onThrow && !decide (w.frame = Parity.topEffect)) := by
  by_cases ht : w.frame = Parity.topEffect
  · cases w.onThrow <;> simp [ht]
  · have ht' : Parity.topEffect ≠ w.frame := Ne.symm ht
    cases w.onThrow <;> simp [ht, ht']

private theorem noForm_writes {F : Parity.FormulaSchema} (hF : ∀ k G, F ≠ .operation (.fact .before k G))
    (hT : ∀ Φ, F ≠ .transition Φ) (hV : ∀ x i v g, F ≠ .operation (.viewWrite x i v g))
    (hθ : ∀ θ, F ≠ .transport θ) (k : ElementWrite) : F ∉ k.schemaPosts := by
  cases k <;> simp_all [ElementWrite.schemaPosts]
  intro x _ h
  exact hF 0 x h.symm

private theorem normal_fresh : decide (Parity.FormulaF.operation (.freshStore 0) ∈ w.normalSchema) = w.fresh := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  have hw := noForm_writes (F := .operation (.freshStore 0)) (by simp) (by simp) (by simp) (by simp)
  simp only [WireEffect.normalSchema, List.mem_append]
  cases f <;> cases fo <;> cases rg <;> cases el <;>
    cases ew <;> simp [hw]

private theorem normal_freshObject : decide (Parity.FormulaF.operation (.freshObject 0) ∈ w.normalSchema) = w.freshObject := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  have hw := noForm_writes (F := .operation (.freshObject 0)) (by simp) (by simp) (by simp) (by simp)
  simp only [WireEffect.normalSchema, List.mem_append]
  cases f <;> cases fo <;> cases rg <;> cases el <;>
    cases ew <;> simp [hw]

private theorem normal_grows : decide (Parity.FormulaF.operation (.storeExtends 0) ∈ w.normalSchema) = w.receiverGrows := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  have hw := noForm_writes (F := .operation (.storeExtends 0)) (by simp) (by simp) (by simp) (by simp)
  simp only [WireEffect.normalSchema, List.mem_append]
  cases f <;> cases fo <;> cases rg <;> cases el <;>
    cases ew <;> simp [hw]

private theorem write_select {α : Type} (f : Parity.FormulaSchema → Option α) (hf : ∀ F, (∃ k G, F = .operation (.fact .before k G)) ∨
      (∃ Φ, F = .transition Φ) ∨ (∃ x i v g, F = .operation (.viewWrite x i v g)) ∨ (∃ θ, F = .transport θ) → f F = none)
    (k : ElementWrite) : k.schemaPosts.filterMap f = [] := by
  have hpre : ∀ (l : List HeapKnowledge.IndexFact),
      (l.map fun G => (Parity.FormulaF.operation (.fact .before 0 G) : Parity.FormulaSchema)).filterMap f = [] := by
    intro l; induction l with
    | nil => rfl
    | cons G l ih => rw [List.map_cons, List.filterMap_cons, hf _ (.inl ⟨0, G, rfl⟩), ih]
  cases k with
  | stores => simp [ElementWrite.schemaPosts, hf _ (.inr (.inl ⟨_, rfl⟩))]
  | assign =>
    simp [ElementWrite.schemaPosts, hf _ (.inr (.inl ⟨_, rfl⟩)), hf _ (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩))),
      hf _ (.inr (.inr (.inr ⟨_, rfl⟩)))]
  | exact k =>
    simp only [ElementWrite.schemaPosts, List.filterMap_cons, List.filterMap_append, hpre,
      hf _ (.inr (.inl ⟨_, rfl⟩)), hf _ (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩))),
      hf _ (.inr (.inr (.inr ⟨_, rfl⟩)))]
    rfl

private theorem normal_elements : (ExitSchema.mk w.frame w.normalSchema).elementsWhenTrue.head? = w.elements := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  have hw := write_select elementsWhenTrueOf (by rintro F (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩) <;> rfl)
  have hens : (en.map fun F => (Parity.FormulaF.operation (.fact .after 0 F) : Parity.FormulaSchema)).filterMap
      elementsWhenTrueOf = [] := by
    induction en with
    | nil => rfl
    | cons _ _ ih => rw [List.map_cons, List.filterMap_cons]; exact ih
  simp only [ExitSchema.elementsWhenTrue, WireEffect.normalSchema, List.filterMap_append, hens]
  cases el <;> cases hwr : ew <;> cases f <;> cases fo <;>
    cases rg <;> simp [hw, elementsWhenTrueOf, List.filterMap_cons]

private theorem normal_facts : (ExitSchema.mk w.frame w.normalSchema).facts = w.ensures := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  have hw := write_select factAfterOf (by rintro F (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩) <;> rfl)
  have hens : (en.map fun F => (Parity.FormulaF.operation (.fact .after 0 F) : Parity.FormulaSchema)).filterMap
      factAfterOf = en := by
    induction en with
    | nil => rfl
    | cons _ _ ih => rw [List.map_cons, List.filterMap_cons]; exact congrArg _ ih
  simp only [ExitSchema.facts, WireEffect.normalSchema, List.filterMap_append, hens]
  cases el <;> cases hwr : ew <;> cases f <;> cases fo <;>
    cases rg <;> simp [hw, factAfterOf, List.filterMap_cons]

private theorem normal_write : elementWriteIn w.normalSchema = w.elementWrite := by
  rcases w with ⟨c, p, f, rs, o, ro, fo, rq, el, pr, en, rg, ew, regs⟩
  have hens : (en.map fun F => (Parity.FormulaF.operation (.fact .after 0 F) : Parity.FormulaSchema)).filterMap
      viewWriteFormatOf = [] := by
    induction en with
    | nil => rfl
    | cons _ _ ih => rw [List.map_cons, List.filterMap_cons]; exact ih
  unfold elementWriteIn
  simp only [WireEffect.normalSchema, List.filterMap_append, hens, List.mem_append]
  cases hk : ew with
  | none =>
    cases el <;> cases f <;> cases fo <;> cases rg <;>
      simp [viewWriteFormatOf, List.findSome?_cons]
  | some k =>
    cases k with
    | stores =>
      cases el <;> cases f <;> cases fo <;> cases rg <;>
        simp [viewWriteFormatOf, ElementWrite.schemaPosts, List.findSome?_cons]
    | assign =>
      cases el <;> cases f <;> cases fo <;> cases rg <;>
        simp [viewWriteFormatOf, ElementWrite.schemaPosts, List.findSome?_cons]
    | exact k =>
      have hk' : ElementKind.ofFormat k.format = k := by cases k <;> rfl
      cases el <;> cases f <;> cases fo <;> cases rg <;>
        simp [viewWriteFormatOf, ElementWrite.schemaPosts, hk', List.findSome?_cons]

end Readers

/-- **Reading the exits a wire value states gives its canonical value**
(proved, each field by its reader). -/
theorem wireOf_elaborate (w : WireEffect) : wireOf w.elaborate = w.canonicalize := by
  simp only [wireOf, WireEffect.elaborate, Effect.schema, ExitSchema.freshResult, ExitSchema.freshObjectResult,
    frame_classBound, frame_regions, normal_elements, normal_facts, normal_write, WireEffect.canonicalize]
  congr 1 <;> first | exact normal_fresh w | exact frame_store w | exact exceptional_throw w | exact frame_own w |
    exact normal_freshObject w | exact normal_grows w

/-- **An effect the wire represents exactly**: the elaboration of a valid
wire value. -/
def Representable (e : Effect) : Prop := ∃ w : WireEffect, w.Valid ∧ w.elaborate = e

/-- **The encoder**: the wire value an effect is the elaboration of, where
it is valid; refused otherwise. -/
def encodeOld (e : Effect) : Except String WireEffect :=
  if (wireOf e).valid && decide ((wireOf e).elaborate = e) then .ok (wireOf e)
  else .error "an effect the documents' format does not represent exactly"

/-- **What the encoder writes states the effect** (proved). -/
theorem encodeOld_sound {e : Effect} {w : WireEffect} (h : encodeOld e = .ok w) : w.Valid ∧ w.elaborate = e := by
  unfold encodeOld at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc
  · cases h

/-- **The encoder writes every representable effect** (proved), as its
canonical wire value (`wireOf_elaborate`). -/
theorem encodeOld_complete {e : Effect} (h : Representable e) : encodeOld e = .ok (wireOf e) := by
  obtain ⟨w, hv, rfl⟩ := h
  unfold encodeOld
  rw [wireOf_elaborate, WireEffect.elaborate_canonicalize, WireEffect.valid_canonicalize]
  simp only [WireEffect.Valid] at hv
  simp [hv]

instance : ToJson WireEffect := ⟨fun e => Json.mkObj [("footprint", toJson e.closed),
  ("promise", match e.promise with | some p => toJson p | none => Json.null),
  ("fresh", toJson e.fresh), ("receiverStore", toJson e.receiverStore), ("onThrow", toJson e.onThrow),
  ("receiverOwn", toJson e.receiverOwn), ("freshObject", toJson e.freshObject),
  ("requires", predJson e.requires), ("elements", predJson e.elements), ("pre", toJson e.pre),
  ("ensures", toJson e.ensures), ("receiverGrows", toJson e.receiverGrows),
  ("elementWrite", match e.elementWrite with | some w => toJson (elementWriteName w) | none => Json.null)] |>.mergeObj
  (if e.regions.isEmpty then Json.mkObj [] else
    Json.mkObj [("regions", Json.arr (e.regions.map fun r =>
      Json.mkObj [("position", toJson r.position), ("path", toJson r.path)]).toArray)])⟩

/-- A document's effect as the wire value its fields state. -/
private def parseWire (j : Json) : Except String WireEffect := do
  let footprint ← j.getObjValAs? Footprints.Closed "footprint"
  let promise ← match ← j.getObjVal? "promise" with
    | .null => pure none
    | p => some <$> fromJson? p
  return ⟨footprint, promise, ← j.getObjValAs? Bool "fresh", ← j.getObjValAs? Bool "receiverStore",
    ← j.getObjValAs? Bool "onThrow", ← j.getObjValAs? Bool "receiverOwn", ← j.getObjValAs? Bool "freshObject",
    ← predOf (← j.getObjVal? "requires"), ← predOf (← j.getObjVal? "elements"),
    ← fromJson? (← j.getObjVal? "pre"), ← fromJson? (← j.getObjVal? "ensures"),
    ← j.getObjValAs? Bool "receiverGrows", ← match ← j.getObjVal? "elementWrite" with
      | .null => pure none
      | w => do some <$> elementWriteOf (← w.getStr?), ← match j.getObjVal? "regions" with
      | .ok rs => do
          let rs ← rs.getArr?
          rs.toList.mapM fun r => do
            pure (⟨← r.getObjValAs? Nat "position", ← r.getObjValAs? (List String) "path"⟩ :
              Footprints.ArgumentStoreRegion)
      | .error _ => pure []⟩

/-- A parsed wire value, kept where it re-encodes to the document read and
is valid. -/
private def checkWire (j : Json) (e : WireEffect) : Except String WireEffect :=
  if toJson e != j then
    .error ("an effect has exactly the fields footprint, promise, fresh, receiverStore, onThrow, receiverOwn, " ++
      "freshObject, requires, elements, a predicate its kinds in order, pre, ensures, receiverGrows and elementWrite, " ++
      "and regions where its frame states store regions")
  else if !e.valid then
    match e.elementWrite with
    | some (.exact k) =>
      .error s!"an exact element write '{elementWriteName (.exact k)}' states its value's range in its precondition"
    | _ => .error "an effect's footprint is one the documents write"
  else .ok e

/-- **The decoder**: a document's effect as a wire value, refused unless it
re-encodes to exactly the document read and is valid. -/
def decodeOld (j : Json) : Except String WireEffect := parseWire j >>= checkWire j

/-- **What the decoder reads is valid and re-encodes to the document read**
(proved; Json's equality). -/
theorem decodeOld_sound {j : Json} {w : WireEffect} (h : decodeOld j = .ok w) :
    w.Valid ∧ (toJson w == j) = true := by
  unfold decodeOld at h
  cases hp : parseWire j with
  | error _ => rw [hp] at h; cases h
  | ok e =>
    rw [hp] at h
    change checkWire j e = .ok w at h
    unfold checkWire at h
    split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · cases h
        rename_i hj hv
        refine ⟨by simpa [WireEffect.Valid] using hv, ?_⟩
        simpa [bne] using hj

/-- An effect is read through its wire value (`decodeOld`), and is the
effect that value states (`WireEffect.elaborate`): natives and library
declarations arrive through it. -/
instance : FromJson Effect := ⟨fun j => WireEffect.elaborate <$> decodeOld j⟩

/-- **An effect is written through the encoder** (`encodeOld`): refused where
the documents' format does not represent it exactly. -/
def effectJson (e : Effect) : Except String Json := toJson <$> encodeOld e

/-- **An effect inside a derived document** (a types table, evidence, a
diagnostic, a claim): the encoder's wire value (`encodeOld`), or, where the
encoder refuses, an object naming the refusal, `{"unrepresentable":
reason}`, which no decoder reads (`decodeOld` requires every field of the
wire). It writes no effect other than the one it is given. A writer that
can refuse uses `effectJson`. -/
instance : ToJson Effect := ⟨fun e => match encodeOld e with
  | .ok w => toJson w
  | .error msg => Json.mkObj [("unrepresentable", toJson msg)]⟩

/-- **Reading and writing are inverse on what is read** (proved): an effect
read from a document holding a canonical wire value (`WireEffect.Canonical`)
is written back as that document (Json's equality). A document holding
another wire value of the same effect is read as that effect and written as
its canonical value. -/
theorem effectJson_decode {j : Json} {w : WireEffect} (h : decodeOld j = .ok w) (hc : w.Canonical) :
    ∃ j', effectJson w.elaborate = .ok j' ∧ (j' == j) = true := by
  obtain ⟨hv, hj⟩ := decodeOld_sound h
  refine ⟨toJson w, ?_, hj⟩
  rw [effectJson, encodeOld_complete ⟨w, hv, rfl⟩, wireOf_elaborate, hc]
  rfl

/-- **An effect as a declaration's result annotation states it**
(`Modifies<P, T>`, the Fragment's and the request's `stated`): a closed
footprint, whether it also bounds a throw, whether the result's array store
is fresh, and the store regions it excepts. This is the documents' shape;
the effect it states is `StatedEffect.effect`. -/
structure StatedEffect where
  closed : Footprints.Closed
  onThrow : Bool
  fresh : Bool
  regions : List Footprints.ArgumentStoreRegion
  deriving Repr, DecidableEq

/-- **The effect a statement states** (`Effect.ofStated`), with the
precondition `pre` its declaration states and no promise. -/
def StatedEffect.effect (s : StatedEffect) (pre : List HeapKnowledge.IndexFact := []) : Effect :=
  Effect.ofStated s.closed none s.onThrow s.fresh pre [] s.regions

/-- The closed bound a statement gives its unit's claim: its closed footprint
without store regions, `top` with them. -/
def StatedEffect.footprint (s : StatedEffect) : Footprints.Closed :=
  if s.regions.isEmpty then s.closed else .top

/-- An ordinary arrow's guarantee as a wire value. -/
private def ordinaryWire : WireEffect :=
  ⟨.top, none, false, false, false, false, false, none, none, [], [], false, none, []⟩

/-- An exact element write is decoded with its value's range in its
precondition, and refused without it. -/
private def decodes (w : WireEffect) : Bool :=
  match effectJson w.elaborate with
  | .ok j => match (fromJson? j : Except String Effect) with
    | .ok d => d == w.elaborate
    | .error _ => false
  | .error _ => false

#guard ordinaryWire.elaborate == Effect.ordinary
#guard decodes { ordinaryWire with elementWrite := some (.exact .uint8), pre := ElementKind.preFacts .uint8 }
#guard decodes { ordinaryWire with elementWrite := some (.exact .float64), pre := ElementKind.preFacts .float64 }
#guard !decodes { ordinaryWire with elementWrite := some (.exact .uint8) }
#guard !decodes { ordinaryWire with elementWrite := some (.exact .int32), pre := ElementKind.preFacts .uint8 }

end Verification.EffectJson
