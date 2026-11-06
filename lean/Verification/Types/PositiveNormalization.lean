import Verification.Types.CallableConjunctions
import Verification.Types.MethodMembers
import Verification.Programs.RestCalls

/-! Finite positive normalization with nonempty reference conjunctions. Operands
are parameters: normalization never distributes through invariant contracts or
arrow results. Taking operands to be graph-label lists supports recursive graphs.
-/
namespace Verification.PositiveNormalization
open ReferenceConjunctions MethodMembers Tower CallEffects

/-- A tuple contract: required positions, optional positions, and the contract
any further position must hold, if the array may have any. -/
structure Tuple (α : Type) where
  required : List α
  optional : List α
  rest : Option α
  readonly : Bool
  presence : ArrayPresence
  deriving DecidableEq, Repr

/-- The operand a tuple contract states for an index, as `positionFam` states
its family. -/
def Tuple.position (t : Tuple α) (i : Nat) : Option α :=
  match t.required[i]? with
  | some a => some a
  | none => match t.optional[i - t.required.length]? with
    | some a => some a
    | none => if t.required.length + t.optional.length ≤ i then t.rest else none

/-- The families a tuple contract denotes, position by position. -/
def tupleFams {α : Type} (X : α → Fam) (t : Tuple α) : TupleF :=
  ⟨t.required.map X, t.optional.map X, t.rest.map X, t.readonly, t.presence⟩

inductive Clause (α : Type) where
  | nul | bool
  /-- A location under one or more record contracts. An operand is a finite map
  from field names to labels and names only the fields it constrains, so
  operands naming different fields describe different locations of the same
  object rather than one location twice. Optional fields constrain a key
  only where the object has it (`optT`). Methods are host-relative members
  (`methodT`): read from the object and invoked on it. Each key bound says
  which keys the object may own (`ownKeysT`). Each stable key is owned at a
  location whose contract admits one value, or not owned by an object without
  a prototype (`stableKeysT`, HOST-FAMILIES.md,
  "Stable keys"). -/
  | refs (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (views : List (PropKey × α)) (optional : List (OptionalField α) := [])
      (methods : List (MethodMembers.Sig α) := []) (bounds : List KeyBound := [])
      (stable : List PropKey := [])
  /-- A plain object with invariant named fields, readonly named views,
  index views (`dictViewT`) and writable index contracts (`dictCellT`), each
  over the keys its class admits (`IndexKeys`): every string key, the
  canonical numeric ones, or every symbol key. The index operands apply to
  every present own field under an admitted key, including named ones. A
  writable index is also listed among the views, which is what reads use. A
  first record operand fixes the object shape; it may be empty for a pure
  dictionary. -/
  | dict (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (views : List (PropKey × α)) (indexes : List (IndexKeys × α))
      (optional : List (OptionalField α) := [])
      (methods : List (MethodMembers.Sig α) := []) (bounds : List KeyBound := [])
      (cells : List (IndexKeys × α) := [])
      (stable : List PropKey := [])
  /-- A callable value meeting every fixed signature, `(receiver, parameters,
  result)`, and every variadic one, `(receiver, fixed parameters, element,
  result)`: the receiver a call may pass, the contract of each actual, and
  the result. They describe the calls a caller may write, not the callee's
  code; a signature indifferent to its receiver has receiver `top`. -/
  | arrs (arrows : List (Arrow α)) (variadic : List (RestArrow α))
  | boolLit (value : Bool)
  /-- Numbers, and one number. The spelling is canonical, so `numLit` singletons
  are distinct exactly when the numbers are. -/
  | num
  | numLit (bits : UInt64)
  /-- The value a body produces by completing rather than returning. -/
  | undef
  /-- A callable object: its code meets every signature, as an `arrs`
  clause's, its property bag is under the invariant record operands `first`
  and `rest` (`CallableConjunctions.objectsT`), and each method is a
  host-relative member (`methodT`), read from the object and invoked on it,
  as a record's: `Number`, called and read through `Number.isFinite`. -/
  | callable (first : List (PropKey × α)) (rest : List (List (PropKey × α)))
      (arrows : List (Arrow α)) (variadic : List (RestArrow α))
      (methods : List (MethodMembers.Sig α) := [])
  /-- Semantic top: every value. Membership grants no operation, so nothing
  reads, calls or tests through it without a narrowing fact. `unknown`
  denotes it. Source `void` denotes the union of primitives and objects. -/
  | top
  /-- Every closed JavaScript value, excluding internal stores. -/
  | source
  /-- Strings, and one string; appended last so every earlier case order holds. -/
  | str
  | strLit (value : String)
  /-- An array store under one or more tuple contracts. The array object
  holds the store in its store field; the contracts describe the store. -/
  | list (first : Tuple α) (rest : List (Tuple α))
  /-- Bigints and symbols; appended last so every earlier case order holds. -/
  | bigint
  | symbol
  /-- A class value meeting every construct signature `(parameters, result)`:
  `new` with actuals at the parameters is safe at the result; and every
  variadic one `(parameters, rest, result)`, whose actuals past the parameters
  are, as one pack, at the rest. Its code has `[[Construct]]` only, so no
  callable clause meets it. Its property bag, its static fields, is under
  the invariant record operands `first` and `rest`, as a callable object's
  (`CallableConjunctions.propsT`), and the readonly `views`
  (`CallableConjunctions.viewsT`); with none it states no field. -/
  | ctors (signatures : List (MethodArrow α)) (variadic : List (MethodRestArrow α) := [])
      (first : List (PropKey × α) := []) (rest : List (List (PropKey × α)) := [])
      (views : List (PropKey × α) := [])
  /-- An argument list under one or more tuple contracts: what a rest
  parameter's type says of the actuals after the fixed ones. Only a signature's
  rest meets one; no program value is one. -/
  | pack (first : Tuple α) (rest : List (Tuple α))
  /-- One bigint, below the `bigint` family as a number singleton is below
  the number family; appended last so every earlier case order holds. -/
  | bigintLit (value : Int)
  /-- One symbol, below the `symbol` family: the symbol of a `unique symbol`
  constant, by its identity; appended last so every earlier case order holds. -/
  | symbolLit (id : Nat)
  /-- A finite set of numbers, by bit pattern: a **tag set** (HOST-FAMILIES.md,
  "Tag sets"). A union of number singletons is one; the wire and the
  normal forms keep its list sorted, distinct and of at least two patterns,
  which no meaning depends on. Appended last so every earlier case order
  holds. -/
  | numIn (bits : List UInt64)
  /-- A finite set of strings, a tag set of strings; kept sorted, distinct and
  of at least two values as `numIn` is. -/
  | strIn (values : List String)
  deriving Repr, DecidableEq

/-- Every value. A closed value, as every member of every family is. -/
def topT : Fam := fun _ _ v => isVal v = true ∧ Scoped 0 v

def sourceT : Fam := fun _ _ v => isSourceVal v = true ∧ Scoped 0 v

def semWithArgs (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) : Clause α → Fam
  | .top => topT
  | .source => sourceT
  | .list a bs => fun n W v => listT (tupleFams X a) n W v ∧ ∀ b ∈ bs, listT (tupleFams X b) n W v
  | .nul => nulT
  | .undef => undefT
  | .bool => boolT
  | .boolLit b => fun _ _ v => v = (if b then .tru else .fls)
  | .num => numT
  | .numLit b => fun _ _ v => v = .num b
  | .str => strT
  | .strLit s => fun _ _ v => v = .str s
  | .bigint => bigintT
  | .bigintLit i => fun _ _ v => v = .bigint i
  | .symbolLit i => fun _ _ v => v = .sym i
  | .numIn bs => fun _ _ v => ∃ b ∈ bs, v = .num b
  | .strIn ss => fun _ _ v => ∃ s ∈ ss, v = .str s
  | .symbol => symbolT
  | .refs a bs vs os ms ks st => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧ viewsT (famsOf X vs) n W v ∧
        optT (os.map (·.map X)) n W v ∧ methodT Ξ (ms.map (Member.of X P)) n W v ∧
        (∀ K ∈ ks, ownKeysT K n W v) ∧ stableKeysT st n W v
  | .dict a bs vs ds os ms ks cs st => fun n W v =>
      refsT (famsOf X a) (bs.map (famsOf X)) n W v ∧
      viewsT (famsOf X vs) n W v ∧
        ((∀ d ∈ ds, dictViewT d.1 (X d.2) n W v) ∧ ∀ d ∈ cs, dictCellT d.1 (X d.2) n W v) ∧
        optT (os.map (·.map X)) n W v ∧ methodT Ξ (ms.map (Member.of X P)) n W v ∧
        (∀ K ∈ ks, ownKeysT K n W v) ∧ stableKeysT st n W v
  | .arrs L S => interT (CallEffects.callsT Ξ (L.map (Arrow.map X)))
      (CallEffects.restsT Ξ (S.map (RestArrow.mapWith X P)))
  | .callable a bs L S ms =>
      interT (interT (CallableConjunctions.objectsT Ξ (famsOf X a) (bs.map (famsOf X))
        (L.map (Arrow.map X)))
        (CallEffects.restsT Ξ (S.map (RestArrow.mapWith X P))))
        (methodT Ξ (ms.map (Member.of X P)))
  | .ctors L S a bs vs => interT (interT (ctorsT Ξ (L.map (MethodArrow.map X)))
      (ctorRestsT Ξ (S.map (MethodRestArrow.mapWith X P))))
      (interT (CallableConjunctions.propsT (famsOf X a) (bs.map (famsOf X)))
        (CallableConjunctions.viewsT (famsOf X vs)))
  -- An argument list is not a runtime value: a pack clause's members are
  -- lists, read by `clauseArguments`.
  | .pack _ _ => fun _ _ _ => False

/-- The argument-list component of a clause. Grouping arguments spends no
approximation step; only a surrounding runtime operation supplies a guard. -/
def clauseArguments (X : α → Fam) : Clause α → ArgFam
  | .pack a bs => fun n W vs => ∀ t ∈ a :: bs,
      ArgumentContracts.Fits (tupleFams X t) n W vs
  | _ => fun _ _ _ => False

def semList (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) (L : List (Clause α)) : Fam :=
  setSem (semWithArgs Ξ X P) L

/-- The clause of a finite set of numbers: none for the empty set, the
singleton for one pattern, the kind set otherwise. -/
def numSet : List UInt64 → List (Clause α)
  | [] => []
  | [b] => [.numLit b]
  | bs => [.numIn bs]

/-- The clause of a finite set of strings, as `numSet`. -/
def strSet : List String → List (Clause α)
  | [] => []
  | [s] => [.strLit s]
  | ss => [.strIn ss]

theorem strSet_sem (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) (ss : List String) (n W v) :
    setSem (semWithArgs Ξ X P) (strSet ss) n W v ↔ ∃ s ∈ ss, v = .str s := by
  match ss with
  | [] => simp [strSet, setSem]
  | [s] => simp [strSet, setSem, semWithArgs]
  | s :: t :: ss => simp [strSet, setSem, semWithArgs]

theorem mem_strSet {d : Clause α} {L : List String} (h : d ∈ strSet L) :
    (∃ s, d = .strLit s) ∨ ∃ L', d = .strIn L' := by
  match L, h with
  | [s], h => exact .inl ⟨s, by simpa [strSet] using h⟩
  | s :: t :: ss, h => exact .inr ⟨_, by simpa [strSet] using h⟩

theorem mem_numSet {d : Clause α} {L : List UInt64} (h : d ∈ numSet L) :
    (∃ b, d = .numLit b) ∨ ∃ L', d = .numIn L' := by
  match L, h with
  | [b], h => exact .inl ⟨b, by simpa [numSet] using h⟩
  | b :: c :: bs, h => exact .inr ⟨_, by simpa [numSet] using h⟩

theorem numSet_sem (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) (bs : List UInt64) (n W v) :
    setSem (semWithArgs Ξ X P) (numSet bs) n W v ↔ ∃ b ∈ bs, v = .num b := by
  match bs with
  | [] => simp [numSet, setSem]
  | [b] => simp [numSet, setSem, semWithArgs]
  | b :: c :: bs => simp [numSet, setSem, semWithArgs]

/-- A clause as the clauses of its elements: a tag set as its literals, any
other clause as itself. A consumer enumerating literals reads a type's
clauses through it. -/
def Clause.elements : Clause α → List (Clause α)
  | .numIn bs => bs.map .numLit
  | .strIn ss => ss.map .strLit
  | c => [c]

/-- A clause list with its tag sets as their literals. -/
def splitSets (cs : List (Clause α)) : List (Clause α) := cs.flatMap Clause.elements

theorem elements_sem (Ξ : Fam) (X : α → Fam) (P : α → ArgFam) (c : Clause α) (n W v) :
    setSem (semWithArgs Ξ X P) c.elements n W v ↔ semWithArgs Ξ X P c n W v := by
  cases c <;> simp only [Clause.elements, setSem, List.mem_singleton, exists_eq_left]
  all_goals first
    | rfl
    | (simp only [List.mem_map, semWithArgs]
       constructor
       · rintro ⟨_, ⟨b, hb, rfl⟩, hv⟩; exact ⟨b, hb, hv⟩
       · rintro ⟨b, hb, hv⟩; exact ⟨_, ⟨b, hb, rfl⟩, hv⟩)

/-- The numbers a number literal or number set clause is. -/
def Clause.numBits : Clause α → Option (List UInt64)
  | .numLit b => some [b]
  | .numIn bs => some bs
  | _ => none

/-- The strings a string literal or string set clause is. -/
def Clause.strVals : Clause α → Option (List String)
  | .strLit s => some [s]
  | .strIn ss => some ss
  | _ => none

/-- A list of numbers' one spelling: sorted and distinct. -/
def canonNums (bs : List UInt64) : List UInt64 := (bs.mergeSort (· ≤ ·)).eraseDups
def canonStrs (ss : List String) : List String := (ss.mergeSort fun a b => decide (a ≤ b)).eraseDups

theorem mem_canonNums {b : UInt64} {bs : List UInt64} : b ∈ canonNums bs ↔ b ∈ bs := by
  simp [canonNums, List.mem_eraseDups]
theorem mem_canonStrs {s : String} {ss : List String} : s ∈ canonStrs ss ↔ s ∈ ss := by
  simp [canonStrs, List.mem_eraseDups]

/-- **Tag-set normalization of a clause list** (HOST-FAMILIES.md, "Tag sets"):
its literals and tag sets of one primitive as one tag set, sorted and
distinct; every other clause as it is. A list with at most one such clause of
each primitive is left as it is. -/
def mergeSets (cs : List (Clause α)) : List (Clause α) :=
  if (cs.filterMap Clause.numBits).length ≤ 1 && (cs.filterMap Clause.strVals).length ≤ 1 then cs
  else cs.filter (fun c => c.numBits.isNone && c.strVals.isNone) ++
    numSet (canonNums (cs.filterMap Clause.numBits).flatten) ++
    strSet (canonStrs (cs.filterMap Clause.strVals).flatten)

/-- A clause of a merged list is one of the list's or a literal or tag set. -/
theorem mem_mergeSets {cs : List (Clause α)} {c : Clause α} (h : c ∈ mergeSets cs) :
    c ∈ cs ∨ (c.numBits.isSome ∨ c.strVals.isSome) := by
  unfold mergeSets at h
  split at h
  · exact .inl h
  · simp only [List.mem_append, List.mem_filter] at h
    rcases h with (⟨hc, -⟩ | hn) | hs
    · exact .inl hc
    · right; left
      rcases mem_numSet hn with ⟨b, rfl⟩ | ⟨L, rfl⟩ <;> rfl
    · right; right
      rcases mem_strSet hs with ⟨b, rfl⟩ | ⟨L, rfl⟩ <;> rfl

/-- Merging keeps the members of a union, read through any clause meaning
under which literals and tag sets mean their elements. -/
theorem setSem_mergeSets {F : Clause α → Fam}
    (hnum : ∀ c bs, c.numBits = some bs → ∀ n W v, F c n W v ↔ ∃ b ∈ bs, v = .num b)
    (hstr : ∀ c ss, c.strVals = some ss → ∀ n W v, F c n W v ↔ ∃ s ∈ ss, v = .str s)
    (cs : List (Clause α)) (n W v) :
    setSem F (mergeSets cs) n W v ↔ setSem F cs n W v := by
  unfold mergeSets
  split
  · rfl
  · -- The literal-free part, and each primitive's set.
    have hset : ∀ (L : List (Clause α)), (∀ c ∈ L, ∃ bs, c.numBits = some bs) →
        (setSem F L n W v ↔ ∃ b ∈ (L.filterMap Clause.numBits).flatten, v = .num b) := by
      intro L hL
      constructor
      · rintro ⟨c, hc, hv⟩
        obtain ⟨bs, hbs⟩ := hL c hc
        obtain ⟨b, hb, rfl⟩ := (hnum c bs hbs n W v).mp hv
        exact ⟨b, List.mem_flatten.mpr ⟨bs, List.mem_filterMap.mpr ⟨c, hc, hbs⟩, hb⟩, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨bs, hbs, hb⟩ := List.mem_flatten.mp hb
        obtain ⟨c, hc, hcb⟩ := List.mem_filterMap.mp hbs
        exact ⟨c, hc, (hnum c bs hcb n W _).mpr ⟨b, hb, rfl⟩⟩
    have numSetF : ∀ bs, setSem F (numSet bs) n W v ↔ ∃ b ∈ bs, v = .num b := by
      intro bs
      match bs with
      | [] => simp [numSet, setSem]
      | [b] => simp [numSet, setSem, hnum (.numLit b) [b] rfl n W v]
      | b :: c :: bs => simp [numSet, setSem, hnum (.numIn (b :: c :: bs)) _ rfl n W v]
    have strSetF : ∀ ss, setSem F (strSet ss) n W v ↔ ∃ s ∈ ss, v = .str s := by
      intro ss
      match ss with
      | [] => simp [strSet, setSem]
      | [s] => simp [strSet, setSem, hstr (.strLit s) [s] rfl n W v]
      | s :: t :: ss => simp [strSet, setSem, hstr (.strIn (s :: t :: ss)) _ rfl n W v]
    constructor
    · rintro ⟨c, hc, hv⟩
      simp only [List.mem_append, List.mem_filter] at hc
      rcases hc with (⟨hc, -⟩ | hn) | hs
      · exact ⟨c, hc, hv⟩
      · obtain ⟨b, hb, rfl⟩ := (numSetF _).mp ⟨c, hn, hv⟩
        obtain ⟨bs, hbs, hb⟩ := List.mem_flatten.mp (mem_canonNums.mp hb)
        obtain ⟨d, hd, hdb⟩ := List.mem_filterMap.mp hbs
        exact ⟨d, hd, (hnum d bs hdb n W _).mpr ⟨b, hb, rfl⟩⟩
      · obtain ⟨s, hs', rfl⟩ := (strSetF _).mp ⟨c, hs, hv⟩
        obtain ⟨ss, hss, hs'⟩ := List.mem_flatten.mp (mem_canonStrs.mp hs')
        obtain ⟨d, hd, hds⟩ := List.mem_filterMap.mp hss
        exact ⟨d, hd, (hstr d ss hds n W _).mpr ⟨s, hs', rfl⟩⟩
    · rintro ⟨c, hc, hv⟩
      cases hcn : c.numBits with
      | some bs =>
        obtain ⟨b, hb, rfl⟩ := (hnum c bs hcn n W v).mp hv
        obtain ⟨d, hd, hdv⟩ := (numSetF (canonNums _)).mpr
          ⟨b, mem_canonNums.mpr (List.mem_flatten.mpr ⟨bs, List.mem_filterMap.mpr ⟨c, hc, hcn⟩, hb⟩), rfl⟩
        exact ⟨d, by simp [hd], hdv⟩
      | none =>
        cases hcs : c.strVals with
        | some ss =>
          obtain ⟨s, hs, rfl⟩ := (hstr c ss hcs n W v).mp hv
          obtain ⟨d, hd, hdv⟩ := (strSetF (canonStrs _)).mpr
            ⟨s, mem_canonStrs.mpr (List.mem_flatten.mpr ⟨ss, List.mem_filterMap.mpr ⟨c, hc, hcs⟩, hs⟩), rfl⟩
          exact ⟨d, by simp [hd], hdv⟩
        | none => exact ⟨c, by simp [hc, hcn, hcs], hv⟩

theorem numBits_sem {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {c : Clause α} {bs : List UInt64}
    (h : c.numBits = some bs) (n W v) : semWithArgs Ξ X P c n W v ↔ ∃ b ∈ bs, v = .num b := by
  cases c <;> simp [Clause.numBits] at h <;> subst h <;> simp [semWithArgs]

theorem strVals_sem {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {c : Clause α} {ss : List String}
    (h : c.strVals = some ss) (n W v) : semWithArgs Ξ X P c n W v ↔ ∃ s ∈ ss, v = .str s := by
  cases c <;> simp [Clause.strVals] at h <;> subst h <;> simp [semWithArgs]

/-- Intersection of clauses: preserve all constraints of the same shape. -/
def meet : Clause α → Clause α → List (Clause α)
  | .top, c | c, .top => [c]
  | .source, .list .. | .list .., .source | .source, .pack .. | .pack .., .source => []
  | .source, c | c, .source => [c]
  | .list a bs, .list c ds => [.list a (bs ++ c :: ds)]
  | .nul, .nul => [.nul]
  | .undef, .undef => [.undef]
  | .bool, .bool => [.bool]
  | .bool, .boolLit b | .boolLit b, .bool => [.boolLit b]
  | .boolLit a, .boolLit b => if a == b then [.boolLit a] else []
  | .num, .num => [.num]
  | .num, .numLit b | .numLit b, .num => [.numLit b]
  | .numLit a, .numLit b => if a == b then [.numLit a] else []
  | .str, .str => [.str]
  | .str, .strLit s | .strLit s, .str => [.strLit s]
  | .strLit a, .strLit b => if a == b then [.strLit a] else []
  | .bigint, .bigint => [.bigint]
  | .bigint, .bigintLit i | .bigintLit i, .bigint => [.bigintLit i]
  | .bigintLit a, .bigintLit b => if a == b then [.bigintLit a] else []
  | .symbol, .symbol => [.symbol]
  | .symbol, .symbolLit i | .symbolLit i, .symbol => [.symbolLit i]
  | .symbolLit a, .symbolLit b => if a == b then [.symbolLit a] else []
  | .num, .numIn S | .numIn S, .num => [.numIn S]
  | .numLit b, .numIn S | .numIn S, .numLit b => if S.contains b then [.numLit b] else []
  | .numIn S, .numIn T => numSet (S.filter T.contains)
  | .str, .strIn S | .strIn S, .str => [.strIn S]
  | .strLit s, .strIn S | .strIn S, .strLit s => if S.contains s then [.strLit s] else []
  | .strIn S, .strIn T => strSet (S.filter T.contains)
  -- Object contracts meet on one object: their first operands are one record
  -- (`ReferenceConjunctions.flatten`), whose named fields the read rules find.
  | .refs a bs vs os ms ks st, .refs c ds ws ps ns ls su =>
      [.refs (a ++ c) (bs ++ ds) (vs ++ ws) (os ++ ps) (ms ++ ns) (ks ++ ls) (st ++ su)]
  | .refs a bs vs os ms ks st, .dict c ds ws ix ps ns ls cy su =>
      [.dict (a ++ c) (bs ++ ds) (vs ++ ws) ix (os ++ ps) (ms ++ ns) (ks ++ ls) cy (st ++ su)]
  | .dict a bs vs ix os ms ks cx st, .refs c ds ws ps ns ls su =>
      [.dict (a ++ c) (bs ++ ds) (vs ++ ws) ix (os ++ ps) (ms ++ ns) (ks ++ ls) cx (st ++ su)]
  | .dict a bs vs ix os ms ks cx st, .dict c ds ws iy ps ns ls cy su =>
      [.dict (a ++ c) (bs ++ ds) (vs ++ ws) (ix ++ iy) (os ++ ps) (ms ++ ns) (ks ++ ls) (cx ++ cy) (st ++ su)]
  | .arrs L S, .arrs M T => [.arrs (L ++ M) (S ++ T)]
  -- Two bags on one object are both; two bagless ones stay bagless.
  | .ctors L S [] [] [], .ctors M T [] [] [] => [.ctors (L ++ M) (S ++ T)]
  | .ctors L S a bs vs, .ctors M T c ds ws => [.ctors (L ++ M) (S ++ T) a (bs ++ c :: ds) (vs ++ ws)]
  | .pack a bs, .pack c ds => [.pack a (bs ++ c :: ds)]
  | .callable a bs L S ms, .callable c ds M T ns => [.callable a (bs ++ c :: ds) (L ++ M) (S ++ T) (ms ++ ns)]
  | .callable a bs L S ms, .arrs M T => [.callable a bs (L ++ M) (S ++ T) ms]
  | .arrs L S, .callable a bs M T ms => [.callable a bs (M ++ L) (T ++ S) ms]
  | _, _ => []

/-- The primitive clause whose values a class's keys are the `ToPropertyKey`
of: strings for every string key, numbers for the canonical numeric ones
(`numeric_admits_number`), symbols for the symbol keys. A computed key of
that clause reads through an index over that class. -/
def keyClause : IndexKeys → Clause α
  | .strings => .str
  | .numeric => .num
  | .symbols => .symbol

/-- A dictionary's indexes, the canonical numeric keys' first: where a key
is admitted by both a number index and a string one, the number index's
contract is the narrower (TypeScript requires it within the string index's),
so a read through it is the more precise. -/
def numericFirst (ix : List (IndexKeys × α)) : List (IndexKeys × α) :=
  ix.filter (·.1 == .numeric) ++ ix.filter (·.1 != .numeric)

/-- **The array shape**, the one definition every layer reads arrays from: an
object holding its store under the store key, invariantly or, readonly, as a
view; holding `Array.prototype` as a view under the prototype key; and owning
none of `excluded`, the keys the prototype provides, so a read of one of them
continues at the prototype. Any other own key it may have: an array may carry
further keys, such as a runtime's hidden marker. -/
def arrayClauseOf (store proto : α) (excluded : List PropKey) (readonly : Bool) : Clause α :=
  .refs (if readonly then [] else [(CallArguments.arrayStoreField, store)]) []
    ((if readonly then [(CallArguments.arrayStoreField, store)] else []) ++
      [(CallArguments.protoField, proto)])
    [] [] [⟨false, excluded⟩]

/-- A record or dictionary clause: the clauses the array invariant applies to
(`PositiveGraphs.builtinInvariant`). The source-value universe constrains only
the outer value form and carries no record invariant. -/
def Clause.record : Clause α → Bool
  | .refs .. | .dict .. => true
  | _ => false

/-- The clauses the built-in array invariant applies to in a row
(`PositiveGraphs.builtinInvariant`): records, dictionaries and `source`, the
builtins's `unknown`. -/
def Clause.carriesInvariant : Clause α → Bool
  | .refs .. | .dict .. | .source => true
  | _ => false

/-- The keys an object clause says its object owns: its fields' and views'. -/
def Clause.presentKeys : Clause α → List PropKey
  | .refs a bs vs .. | .dict a bs vs .. => ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).map (·.1)
  | _ => []

/-- An object clause's key bounds. -/
def Clause.keyBounds : Clause α → List KeyBound
  | .refs _ _ _ _ _ ks _ | .dict _ _ _ _ _ _ ks _ _ => ks
  | _ => []

/-- A clause whose bounds admit every key it says the object owns. Any other
has no member: a meet in which one operand owns a key another's bound
excludes, such as an array with an own `map`, is empty. -/
def Clause.consistent (c : Clause α) : Bool :=
  c.presentKeys.all fun k => c.keyBounds.all (·.admits k)

/-- The meet of two clause lists: each pair's meet, without clauses a bound
contradicts. -/
def meetLists (A B : List (Clause α)) : List (Clause α) :=
  A.flatMap fun a => B.flatMap fun b => (meet a b).filter Clause.consistent

private theorem singleton_sem (X : α → Fam) (P : α → ArgFam) (c : Clause α) (n W v) :
    semList Ξ X P [c] n W v ↔ semWithArgs Ξ X P c n W v := by simp [semList, setSem]

private theorem nil_sem (X : α → Fam) (P : α → ArgFam) (n W v) : ¬ semList Ξ X P [] n W v := by
  simp [semList, setSem]

def shape : Clause α → Nat
  | .nul => 0 | .bool | .boolLit _ => 1 | .refs .. | .dict .. => 2 | .arrs .. | .callable .. => 3
  | .undef => 4 | .num | .numLit _ | .numIn _ => 5 | .str | .strLit _ | .strIn _ => 6
  | .top => 7 | .list .. => 8 | .bigint | .bigintLit _ => 9 | .symbol | .symbolLit _ => 10 | .ctors .. => 11
  | .pack .. => 12
  | .source => 7

def valueShape : Val → Nat
  | .nul => 0 | .tru | .fls => 1 | .objAt _ .absent _ => 2 | .undef => 4
  | .objAt _ (.bound _ _ _) _ | .objAt _ (.graph _ _ _ _ _ .call _) _
  | .objAt _ (.graph _ _ _ _ _ .sloppy _) _ => 3
  | .objAt _ (.graph _ _ _ _ _ .construct _) _ => 11
  | .num _ => 5
  | .str _ => 6
  | .arr _ => 8
  | .bigint _ => 9
  | .sym _ => 10
  | _ => 7

/-- Every member of a clause is a closed value; top says nothing more. -/
theorem semWithArgs_value {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs Ξ X P c n W v) : isVal v = true ∧ Scoped 0 v := by
  cases c with
  | top => exact h
  | source => exact ⟨sourceVal_isVal h.1, h.2⟩
  | list a bs => obtain ⟨ls, rfl, _⟩ := h.1; exact ⟨rfl, trivial⟩
  | nul => subst v; exact ⟨rfl, trivial⟩
  | bool => rcases h with rfl | rfl <;> exact ⟨rfl, trivial⟩
  | boolLit b => cases b <;> cases h <;> exact ⟨rfl, trivial⟩
  | num => obtain ⟨b, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | numLit b => subst v; exact ⟨rfl, trivial⟩
  | refs a rest => obtain ⟨flds, _, rfl, _⟩ := h.1.1; exact ⟨rfl, trivial⟩
  | dict a rest vs ds os ms ks cs => obtain ⟨flds, _, rfl, _⟩ := h.1.1; exact ⟨rfl, trivial⟩
  | arrs L S => exact ⟨h.1.1.val, h.1.1.scoped⟩
  | callable a bs L S ms => exact ⟨h.1.1.2.1.val, h.1.1.2.1.scoped⟩
  | undef => subst v; exact ⟨rfl, trivial⟩
  | str => obtain ⟨s, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | strLit s => subst v; exact ⟨rfl, trivial⟩
  | bigint => obtain ⟨i, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | bigintLit i => subst v; exact ⟨rfl, trivial⟩
  | symbolLit i => subst v; exact ⟨rfl, trivial⟩
  | symbol => obtain ⟨i, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | ctors L S a bs vs => obtain ⟨_, _, _, _, _, _, _, _, rfl, hs⟩ := h.1.1.1; exact ⟨rfl, hs⟩
  | pack a bs => exact h.elim
  | numIn bs => obtain ⟨b, -, rfl⟩ := h; exact ⟨rfl, trivial⟩
  | strIn ss => obtain ⟨s, -, rfl⟩ := h; exact ⟨rfl, trivial⟩


/-- A member's shape is its clause's, except under the two value universes. -/
theorem semWithArgs_shape {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : c ≠ .top) (hj : c ≠ .source) (h : semWithArgs Ξ X P c n W v) : valueShape v = shape c := by
  cases c with
  | top => exact absurd rfl hc
  | source => exact absurd rfl hj
  | list a bs => obtain ⟨ls, rfl, _⟩ := h.1; rfl
  | nul => cases h; rfl
  | bool => rcases h with h | h <;> cases h <;> rfl
  | boolLit b => cases b <;> cases h <;> rfl
  | num => obtain ⟨b, rfl⟩ := h; rfl
  | numLit b => cases h; rfl
  | refs a bs => obtain ⟨flds, _, rfl, _⟩ := h.1.1; rfl
  | dict a bs vs ds os ms ks cs => obtain ⟨flds, _, rfl, _⟩ := h.1.1; rfl
  | arrs L S =>
    obtain ⟨fs, code, _, rfl, hc, -⟩ := h.1.1
    cases code
    case graph kind _ => cases kind <;> simp_all [valueShape, shape, CallCode.callable]
    all_goals simp_all [valueShape, shape, CallCode.callable]
  | undef => cases h; rfl
  | callable a bs L S ms =>
    obtain ⟨fs, code, _, rfl, hc, -⟩ := h.1.1.2.1
    cases code
    case graph kind _ => cases kind <;> simp_all [valueShape, shape, CallCode.callable]
    all_goals simp_all [valueShape, shape, CallCode.callable]
  | str => obtain ⟨s, rfl⟩ := h; rfl
  | strLit s => cases h; rfl
  | bigint => obtain ⟨i, rfl⟩ := h; rfl
  | bigintLit i => cases h; rfl
  | symbolLit i => cases h; rfl
  | symbol => obtain ⟨i, rfl⟩ := h; rfl
  | ctors L S a bs vs =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := h.1.1.1
    rfl
  | pack a bs => exact h.elim
  | numIn bs => obtain ⟨b, -, rfl⟩ := h; rfl
  | strIn ss => obtain ⟨s, -, rfl⟩ := h; rfl

/-- Every inhabited clause other than calculus top or an element-store clause
contains only JavaScript values. Argument-pack clauses have no term members. -/
theorem semWithArgs_source {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (ht : c ≠ .top) (hl : ∀ a bs, c ≠ .list a bs)
    (h : semWithArgs Ξ X P c n W v) : sourceT n W v := by
  have hv := semWithArgs_value h
  refine ⟨?_, hv.2⟩
  by_cases hj : c = .source
  · subst c; exact h.1
  have hs := semWithArgs_shape ht hj h
  cases v <;> simp_all [isSourceVal, isVal, valueShape]
  cases c <;> simp_all [shape]

/-- The property bag a clause states of a value with code: a callable
object's fields, or a class value's static fields. -/
def Clause.bag : Clause α → Option (List (PropKey × α) × List (List (PropKey × α)))
  | .callable a bs _ _ _ | .ctors _ _ a bs _ => some (a, bs)
  | _ => none

/-- The readonly fields a clause states of a value with code: a class
value's readonly static fields. -/
def Clause.bagViews : Clause α → List (PropKey × α)
  | .ctors _ _ _ _ vs => vs
  | _ => []

/-- The first operand of a clause's bag: the fields a read or write finds. -/
def Clause.bagFields (c : Clause α) : List (PropKey × α) :=
  match c.bag with
  | some (P, _) => P
  | none => []

theorem bag_sem {X : α → Fam} {P : α → ArgFam} {c : Clause α} {a : List (PropKey × α)}
    {bs : List (List (PropKey × α))} (hc : c.bag = some (a, bs)) {n W v}
    (h : semWithArgs Ξ X P c n W v) :
    CallableConjunctions.propsT (famsOf X a) (bs.map (famsOf X)) n W v := by
  cases c <;> simp only [Clause.bag, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  · obtain ⟨rfl, rfl⟩ := hc; exact h.1.1.1
  · obtain ⟨rfl, rfl⟩ := hc; exact h.2.1

theorem bagViews_sem {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs Ξ X P c n W v) (hne : c.bagViews ≠ []) :
    CallableConjunctions.viewsT (famsOf X c.bagViews) n W v := by
  cases c <;> simp only [Clause.bagViews, ne_eq, not_true_eq_false] at hne
  exact h.2.2

/-- An empty bag adds nothing to a family of object values. -/
theorem bag_nil_absorb {A : Fam} {X : α → Fam}
    (hA : ∀ n W v, A n W v → ∃ fs code oid, v = Tm.objAt fs code oid) :
    interT A (interT (CallableConjunctions.propsT (famsOf X [])
      (([] : List (List (PropKey × α))).map (famsOf X)))
      (CallableConjunctions.viewsT (famsOf X []))) = A := by
  funext n W v
  apply propext
  constructor
  · exact And.left
  · intro h
    obtain ⟨fs, code, oid, rfl⟩ := hA n W v h
    exact ⟨h, CallableConjunctions.props_nil, CallableConjunctions.views_nil⟩

/-- A clause whose term members are source values. -/
def sourceClause : Clause α → Bool
  | .top | .list .. => false
  | _ => true

theorem sourceClause_sound {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : sourceClause c = true) (h : semWithArgs Ξ X P c n W v) : sourceT n W v := by
  apply semWithArgs_source (by intro e; subst c; cases hc) (by intros a bs e; subst c; cases hc) h

private theorem meet_source (X : α → Fam) (P : α → ArgFam) (c : Clause α) (n W v) :
    semList Ξ X P (meet .source c) n W v ↔ sourceT n W v ∧ semWithArgs Ξ X P c n W v := by
  unfold meet
  cases c with
  | top =>
    simp only [singleton_sem, semWithArgs]
    exact ⟨fun h => ⟨h, sourceVal_isVal h.1, h.2⟩, And.left⟩
  | source => simp [singleton_sem, semWithArgs]
  | list a bs =>
    simp only [semList, setSem, List.not_mem_nil, false_and, exists_false, false_iff]
    rintro ⟨hj, hv⟩
    obtain ⟨ls, rfl, _⟩ := hv.1
    exact Bool.noConfusion hj.1
  | pack a bs => simp [semList, setSem, semWithArgs]
  | _ =>
    simp only [singleton_sem]
    exact ⟨fun h => ⟨semWithArgs_source (by simp) (by intros; simp) h, h⟩, And.right⟩

theorem meet_ctors (L M : List (MethodArrow α)) (S T : List (MethodRestArrow α))
    (a c : List (PropKey × α)) (bs ds : List (List (PropKey × α))) (vs ws : List (PropKey × α)) :
    meet (.ctors L S a bs vs) (.ctors M T c ds ws) =
      if a = [] ∧ bs = [] ∧ vs = [] ∧ c = [] ∧ ds = [] ∧ ws = [] then [.ctors (L ++ M) (S ++ T)]
      else [.ctors (L ++ M) (S ++ T) a (bs ++ c :: ds) (vs ++ ws)] := by
  cases a <;> cases bs <;> cases vs <;> cases c <;> cases ds <;> cases ws <;> simp [meet]

theorem meet_numIn_num (X : α → Fam) (P : α → ArgFam) (S : List UInt64) (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet (.numIn S) .num) n W v ↔
      interT (semWithArgs Ξ X P (.numIn S)) (semWithArgs Ξ X P .num) n W v := by
  simp only [meet, singleton_sem, semWithArgs, interT, numT]
  exact ⟨fun h => ⟨h, by obtain ⟨b, -, rfl⟩ := h; exact ⟨b, rfl⟩⟩, And.left⟩

theorem meet_numIn_numLit (X : α → Fam) (P : α → ArgFam) (S : List UInt64) (c : UInt64)
    (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet (.numIn S) (.numLit c)) n W v ↔
      interT (semWithArgs Ξ X P (.numIn S)) (semWithArgs Ξ X P (.numLit c)) n W v := by
  simp only [meet, interT, semWithArgs]
  by_cases hc : c ∈ S
  · simp only [List.contains_iff_mem, hc, if_true, singleton_sem, semWithArgs]
    exact ⟨fun h => ⟨⟨c, hc, h⟩, h⟩, And.right⟩
  · simp only [List.contains_iff_mem, hc, if_false, semList, setSem, List.not_mem_nil, false_and,
      exists_false, false_iff, not_and]
    rintro ⟨b, hb, rfl⟩ he
    cases he
    exact hc hb

theorem meet_numIn_numIn (X : α → Fam) (P : α → ArgFam) (S T : List UInt64) (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet (.numIn S) (.numIn T)) n W v ↔
      interT (semWithArgs Ξ X P (.numIn S)) (semWithArgs Ξ X P (.numIn T)) n W v := by
  simp only [meet, semList, numSet_sem, interT, semWithArgs, List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨b, ⟨hs, ht⟩, rfl⟩
    exact ⟨⟨b, hs, rfl⟩, ⟨b, by simpa using ht, rfl⟩⟩
  · rintro ⟨⟨b, hs, rfl⟩, ⟨c, ht, he⟩⟩
    cases he
    exact ⟨b, ⟨hs, by simpa using ht⟩, rfl⟩

theorem meet_strIn_str (X : α → Fam) (P : α → ArgFam) (S : List String) (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet (.strIn S) .str) n W v ↔
      interT (semWithArgs Ξ X P (.strIn S)) (semWithArgs Ξ X P .str) n W v := by
  simp only [meet, singleton_sem, semWithArgs, interT, strT]
  exact ⟨fun h => ⟨h, by obtain ⟨b, -, rfl⟩ := h; exact ⟨b, rfl⟩⟩, And.left⟩

theorem meet_strIn_strLit (X : α → Fam) (P : α → ArgFam) (S : List String) (c : String)
    (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet (.strIn S) (.strLit c)) n W v ↔
      interT (semWithArgs Ξ X P (.strIn S)) (semWithArgs Ξ X P (.strLit c)) n W v := by
  simp only [meet, interT, semWithArgs]
  by_cases hc : c ∈ S
  · simp only [List.contains_iff_mem, hc, if_true, singleton_sem, semWithArgs]
    exact ⟨fun h => ⟨⟨c, hc, h⟩, h⟩, And.right⟩
  · simp only [List.contains_iff_mem, hc, if_false, semList, setSem, List.not_mem_nil, false_and,
      exists_false, false_iff, not_and]
    rintro ⟨b, hb, rfl⟩ he
    cases he
    exact hc hb

theorem meet_strIn_strIn (X : α → Fam) (P : α → ArgFam) (S T : List String) (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet (.strIn S) (.strIn T)) n W v ↔
      interT (semWithArgs Ξ X P (.strIn S)) (semWithArgs Ξ X P (.strIn T)) n W v := by
  simp only [meet, semList, strSet_sem, interT, semWithArgs, List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨b, ⟨hs, ht⟩, rfl⟩
    exact ⟨⟨b, hs, rfl⟩, ⟨b, by simpa using ht, rfl⟩⟩
  · rintro ⟨⟨b, hs, rfl⟩, ⟨c, ht, he⟩⟩
    cases he
    exact ⟨b, ⟨hs, by simpa using ht⟩, rfl⟩

theorem meet_sound (X : α → Fam) (P : α → ArgFam) (a b : Clause α) (n : Nat) (W : WorldT n) (v : Val) :
    semList Ξ X P (meet a b) n W v ↔ interT (semWithArgs Ξ X P a) (semWithArgs Ξ X P b) n W v := by
  by_cases ha : a = .top
  · subst ha
    rw [show meet .top b = [b] from rfl, singleton_sem]
    exact ⟨fun h => ⟨semWithArgs_value h, h⟩, fun h => h.2⟩
  by_cases hb : b = .top
  · subst hb
    have hm : meet a .top = [a] := by
      cases a <;> first | exact absurd rfl ha | rfl
    rw [hm, singleton_sem]
    exact ⟨fun h => ⟨h, semWithArgs_value h⟩, fun h => h.1⟩
  by_cases hja : a = .source
  · subst a; exact meet_source X P b n W v
  by_cases hjb : b = .source
  · subst b
    have hm : meet a .source = meet .source a := by cases a <;> rfl
    rw [hm, meet_source]
    exact and_comm
  by_cases hs : shape a = shape b
  · by_cases hna : ∃ S, a = .numIn S
    · obtain ⟨S, rfl⟩ := hna
      cases b <;> (try simp [shape] at hs)
      · exact meet_numIn_num X P S n W v
      · rename_i c; exact meet_numIn_numLit X P S c n W v
      · rename_i T; exact meet_numIn_numIn X P S T n W v
    by_cases hnb : ∃ S, b = .numIn S
    · obtain ⟨S, rfl⟩ := hnb
      have swap : ∀ {p q : Prop}, (p ∧ q) ↔ (q ∧ p) := and_comm
      cases a <;> (try simp [shape] at hs)
      · exact (meet_numIn_num X P S n W v).trans swap
      · rename_i c; exact (meet_numIn_numLit X P S c n W v).trans swap
      · exact absurd ⟨_, rfl⟩ hna
    by_cases hsa : ∃ S, a = .strIn S
    · obtain ⟨S, rfl⟩ := hsa
      cases b <;> (try simp [shape] at hs)
      · exact meet_strIn_str X P S n W v
      · rename_i c; exact meet_strIn_strLit X P S c n W v
      · rename_i T; exact meet_strIn_strIn X P S T n W v
    by_cases hsb : ∃ S, b = .strIn S
    · obtain ⟨S, rfl⟩ := hsb
      have swap : ∀ {p q : Prop}, (p ∧ q) ↔ (q ∧ p) := and_comm
      cases a <;> (try simp [shape] at hs)
      · exact (meet_strIn_str X P S n W v).trans swap
      · rename_i c; exact (meet_strIn_strLit X P S c n W v).trans swap
      · exact absurd ⟨_, rfl⟩ hsa
    unfold meet
    cases a <;> cases b <;> simp only [shape] at hs
    all_goals try contradiction
    all_goals try exact absurd ⟨_, rfl⟩ hna
    all_goals try exact absurd ⟨_, rfl⟩ hnb
    all_goals try exact absurd ⟨_, rfl⟩ hsa
    all_goals try exact absurd ⟨_, rfl⟩ hsb
    · simp [singleton_sem, semWithArgs, interT]
    · simp [singleton_sem, semWithArgs, interT]
    · rename_i b
      cases b <;> simp [singleton_sem, semWithArgs, interT, boolT]
      all_goals intro hv; subst v; simp
    · simp only [singleton_sem, semWithArgs, List.map_append]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, stableKeysT_append, interT,
        List.mem_append, or_imp, forall_and]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩ =>
          ⟨⟨r1, v1, o1, m1, k1, s1⟩, ⟨r2, v2, o2, m2, k2, s2⟩⟩,
        fun ⟨⟨r1, v1, o1, m1, k1, s1⟩, ⟨r2, v2, o2, m2, k2, s2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩⟩
    · -- refs ∩ dictionary
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, stableKeysT_append, interT,
        List.mem_append, or_imp, forall_and]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d2, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩ =>
          ⟨⟨r1, v1, o1, m1, k1, s1⟩, ⟨r2, v2, d2, o2, m2, k2, s2⟩⟩,
        fun ⟨⟨r1, v1, o1, m1, k1, s1⟩, ⟨r2, v2, d2, o2, m2, k2, s2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d2, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩⟩
    · -- dictionary ∩ refs
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, stableKeysT_append, interT,
        List.mem_append, or_imp, forall_and]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d1, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩ =>
          ⟨⟨r1, v1, d1, o1, m1, k1, s1⟩, ⟨r2, v2, o2, m2, k2, s2⟩⟩,
        fun ⟨⟨r1, v1, d1, o1, m1, k1, s1⟩, ⟨r2, v2, o2, m2, k2, s2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, d1, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩⟩
    · -- dictionary ∩ dictionary
      simp only [singleton_sem, semWithArgs, List.map_append,
        List.mem_append, or_imp, forall_and]
      rw [famsOf_append, flatten _ _ _ _ n W v]
      simp only [famsOf_append, viewsT_append, optT_append, methodT_append, stableKeysT_append, interT]
      exact ⟨fun ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨⟨d1, d2⟩, ⟨c1, c2⟩⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩ =>
          ⟨⟨r1, v1, ⟨d1, c1⟩, o1, m1, k1, s1⟩, ⟨r2, v2, ⟨d2, c2⟩, o2, m2, k2, s2⟩⟩,
        fun ⟨⟨r1, v1, ⟨d1, c1⟩, o1, m1, k1, s1⟩, ⟨r2, v2, ⟨d2, c2⟩, o2, m2, k2, s2⟩⟩ =>
          ⟨⟨r1, r2⟩, ⟨v1, v2⟩, ⟨⟨d1, d2⟩, ⟨c1, c2⟩⟩, ⟨o1, o2⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, ⟨s1, s2⟩⟩⟩
    · -- arrs ∩ arrs
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [interT, CallEffects.callsT_append, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    · -- arrs ∩ callable
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [interT, interT, CallableConjunctions.calls_merge, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨⟨o, c⟩, t, r⟩, m⟩ => ⟨⟨c, r⟩, ⟨o, t⟩, m⟩,
        fun ⟨⟨c, r⟩, ⟨o, t⟩, m⟩ => ⟨⟨⟨o, c⟩, t, r⟩, m⟩⟩
    · rename_i b
      cases b <;> simp [singleton_sem, semWithArgs, interT, boolT]
      all_goals intro hv; subst v; simp
    · rename_i b c
      cases b <;> cases c <;> simp [semWithArgs, interT, semList, setSem]
      all_goals intro hv; subst v; simp
    · -- num ∩ num
      simp [singleton_sem, semWithArgs, interT, numT]
    · -- num ∩ numLit: the singleton already implies the family
      rename_i b
      simp [singleton_sem, semWithArgs, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ num
      rename_i b
      simp [singleton_sem, semWithArgs, interT, numT]
      intro hv; subst v; exact ⟨b, rfl⟩
    · -- numLit ∩ numLit: equal spellings are equal numbers
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · simp [singleton_sem, semWithArgs, interT]
    · -- callable ∩ arrs
      simp only [singleton_sem, semWithArgs, List.map_append]
      rw [interT, interT, CallableConjunctions.calls_merge, CallEffects.restsT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨⟨o, c⟩, r, t⟩, m⟩ => ⟨⟨⟨o, r⟩, m⟩, c, t⟩,
        fun ⟨⟨⟨o, r⟩, m⟩, c, t⟩ => ⟨⟨⟨o, c⟩, r, t⟩, m⟩⟩
    · -- callable ∩ callable
      simp only [singleton_sem, semWithArgs, List.map_append, List.map_cons]
      rw [interT, interT, CallableConjunctions.merge, CallEffects.restsT_append, methodT_append]
      simp only [interT]
      exact ⟨fun ⟨⟨⟨o, p⟩, r, t⟩, m1, m2⟩ => ⟨⟨⟨o, r⟩, m1⟩, ⟨p, t⟩, m2⟩,
        fun ⟨⟨⟨o, r⟩, m1⟩, ⟨p, t⟩, m2⟩ => ⟨⟨⟨o, p⟩, r, t⟩, m1, m2⟩⟩
    · -- str ∩ str
      simp [singleton_sem, semWithArgs, interT, strT]
    · -- str ∩ strLit
      rename_i s
      simp [singleton_sem, semWithArgs, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ str
      rename_i s
      simp [singleton_sem, semWithArgs, interT, strT]
      intro hv; subst v; exact ⟨s, rfl⟩
    · -- strLit ∩ strLit
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · -- list ∩ list: every contract of both, on the one store
      simp only [singleton_sem, semWithArgs, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq, interT]
      exact ⟨fun ⟨ha, hb, hc, hd⟩ => ⟨⟨ha, hb⟩, hc, hd⟩, fun ⟨⟨ha, hb⟩, hc, hd⟩ => ⟨ha, hb, hc, hd⟩⟩
    · -- bigint ∩ bigint
      simp [singleton_sem, semWithArgs, interT, bigintT]
    · -- bigint ∩ bigintLit: the singleton already implies the family
      rename_i i
      simp [singleton_sem, semWithArgs, interT, bigintT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- symbol ∩ symbol
      simp [singleton_sem, semWithArgs, interT, symbolT]
    · -- symbol ∩ symbolLit: the singleton already implies the family
      rename_i i
      simp [singleton_sem, semWithArgs, interT, symbolT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- ctors ∩ ctors: every construct signature of both, both bags
      rename_i L S a bs vs M T c ds ws
      show semList Ξ X P (meet (.ctors L S a bs vs) (.ctors M T c ds ws)) n W v ↔ _
      rw [meet_ctors]
      split
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ‹_ ∧ _›
        simp only [singleton_sem, semWithArgs, List.map_append, List.map_nil, interT]
        rw [ctorsT_append, ctorRestsT_append]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hb⟩
          exact ⟨⟨⟨h1, h3⟩, hb⟩, ⟨h2, h4⟩, hb⟩
        · rintro ⟨⟨⟨h1, h3⟩, hb⟩, ⟨h2, h4⟩, -⟩
          exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, hb⟩
      · simp only [singleton_sem, semWithArgs, List.map_append, List.map_cons, interT]
        rw [ctorsT_append, ctorRestsT_append, CallableConjunctions.props_merge, famsOf_append]
        simp only [interT]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨hp, hq⟩, hv⟩
          obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := h1.1
          obtain ⟨hv1, hv2⟩ := (CallableConjunctions.views_append _ _).mp hv
          exact ⟨⟨⟨h1, h3⟩, hp, hv1⟩, ⟨h2, h4⟩, hq, hv2⟩
        · rintro ⟨⟨⟨h1, h3⟩, hp, hv1⟩, ⟨h2, h4⟩, hq, hv2⟩
          obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := h1.1
          exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨hp, hq⟩, (CallableConjunctions.views_append _ _).mpr ⟨hv1, hv2⟩⟩
    · -- pack ∩ pack: every contract of both, on the one list
      rename_i a bs c ds
      simp [singleton_sem, semWithArgs, interT]
    · -- bigintLit ∩ bigint
      rename_i i
      simp [singleton_sem, semWithArgs, interT, bigintT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- bigintLit ∩ bigintLit: equal integers are equal bigints
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
    · -- symbolLit ∩ symbol
      rename_i i
      simp [singleton_sem, semWithArgs, interT, symbolT]
      intro hv; subst v; exact ⟨i, rfl⟩
    · -- symbolLit ∩ symbolLit: equal identities are equal symbols
      rename_i a b
      by_cases hab : a = b
      · subst hab; simp [singleton_sem, semWithArgs, interT]
      · simp [semList, setSem, semWithArgs, interT, hab]
        intro hv; subst hv; simp [hab]
  · have hm : meet a b = [] := by
      cases a <;> cases b <;> first
        | rfl | exact absurd rfl hs | exact absurd rfl ha | exact absurd rfl hb
        | exact absurd rfl hja | exact absurd rfl hjb
    rw [hm]
    constructor
    · intro h; exact False.elim (nil_sem X P n W v h)
    · rintro ⟨hva, hvb⟩
      exact False.elim (hs ((semWithArgs_shape ha hja hva).symm.trans (semWithArgs_shape hb hjb hvb)))

/-- Every key a member's clause says it owns, each bound admits: a clause
with a member is consistent. -/
theorem semWithArgs_consistent {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (h : semWithArgs Ξ X P c n W v) : c.consistent = true := by
  -- What an object clause says: its fields and views are at locations of its
  -- one object, whose own keys each bound admits.
  have present : ∀ (a : List (PropKey × α)) (bs : List (List (PropKey × α)))
      (vs : List (PropKey × α)) (ks : List KeyBound),
      ReferenceConjunctions.refsT (famsOf X a) (bs.map (famsOf X)) n W v →
      viewsT (famsOf X vs) n W v → (∀ K ∈ ks, ownKeysT K n W v) →
      (((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).map (·.1)).all (fun k => ks.all (·.admits k)) = true := by
    intro a bs vs ks hr hw hk
    simp only [List.all_eq_true, List.mem_map]
    rintro k ⟨p, hp, rfl⟩ K hK
    have hat : ∃ (flds : List (PropKey × Nat)) (l : Nat) (oid : Nat), v = .objAt flds .absent oid ∧
        flds.lookup p.1 = some l := by
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
        have hrec : recT (famsOf X L) n W v := by
          rcases List.mem_cons.mp hL with rfl | hL
          · exact hr.1
          · exact hr.2.1 _ (List.mem_map_of_mem hL)
        obtain ⟨flds, l, -, oid, he, hl, -⟩ := recT_at (mem_famsOf.mpr ⟨p.2, hpL, rfl⟩) hrec
        exact ⟨flds, l, oid, he, hl⟩
      · obtain ⟨hp, hpl⟩ := List.mem_filter.mp hp
        obtain ⟨flds, l, -, oid, he, hl, -⟩ := viewsT_at (mem_famsOf.mpr ⟨p.2, hp, rfl⟩) (by simpa using hpl) hw
        exact ⟨flds, l, oid, he, hl⟩
    obtain ⟨flds, l, oid, rfl, hl⟩ := hat
    exact ownKeysT_admits (hk K hK) hl
  cases c with
  | refs a bs vs os ms ks => exact present a bs vs ks h.1 h.2.1 h.2.2.2.2.1
  | dict a bs vs ds os ms ks cs => exact present a bs vs ks h.1 h.2.1 h.2.2.2.2.2.1
  | _ => simp [Clause.consistent, Clause.presentKeys]

/-- A member of an object clause owns every key the clause says it owns. -/
theorem semWithArgs_owns {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v} {k : PropKey}
    (h : semWithArgs Ξ X P c n W v) (hk : k ∈ c.presentKeys) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (oid : Nat), v = .objAt flds .absent oid ∧ flds.lookup k = some l := by
  have present : ∀ (a : List (PropKey × α)) (bs : List (List (PropKey × α)))
      (vs : List (PropKey × α)),
      ReferenceConjunctions.refsT (famsOf X a) (bs.map (famsOf X)) n W v →
      viewsT (famsOf X vs) n W v → k ∈ ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).map (·.1) →
      ∃ (flds : List (PropKey × Nat)) (l : Nat) (oid : Nat), v = .objAt flds .absent oid ∧ flds.lookup k = some l := by
    intro a bs vs hr hw hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
      have hrec : recT (famsOf X L) n W v := by
        rcases List.mem_cons.mp hL with rfl | hL
        · exact hr.1
        · exact hr.2.1 _ (List.mem_map_of_mem hL)
      obtain ⟨flds, l, -, oid, he, hl, -⟩ := recT_at (mem_famsOf.mpr ⟨p.2, hpL, rfl⟩) hrec
      exact ⟨flds, l, oid, he, hl⟩
    · obtain ⟨hp, hpl⟩ := List.mem_filter.mp hp
      obtain ⟨flds, l, -, oid, he, hl, -⟩ := viewsT_at (mem_famsOf.mpr ⟨p.2, hp, rfl⟩) (by simpa using hpl) hw
      exact ⟨flds, l, oid, he, hl⟩
  cases c with
  | refs a bs vs os ms ks => exact present a bs vs h.1 h.2.1 hk
  | dict a bs vs ds os ms ks cs => exact present a bs vs h.1 h.2.1 hk
  | _ => simp [Clause.presentKeys] at hk

/-- A member of an object clause meets each of the clause's key bounds. -/
theorem semWithArgs_bounded {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v} {K : KeyBound}
    (h : semWithArgs Ξ X P c n W v) (hK : K ∈ c.keyBounds) : ownKeysT K n W v := by
  cases c with
  | refs a bs vs os ms ks => exact h.2.2.2.2.1 K hK
  | dict a bs vs ds os ms ks cs => exact h.2.2.2.2.2.1 K hK
  | _ => simp [Clause.keyBounds] at hK

/-- The stable keys a record or dictionary clause states. -/
def Clause.stableKeys : Clause α → List PropKey
  | .refs _ _ _ _ _ _ st | .dict _ _ _ _ _ _ _ _ st => st
  | _ => []

/-- A member of a clause stating a stable key reads the key one way for its
life: owned at a location whose contract admits one value, or not owned by an
object without a prototype (HOST-FAMILIES.md, "Stable keys"). -/
theorem semWithArgs_stable {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v} {k : PropKey}
    (h : semWithArgs Ξ X P c n W v) (hk : k ∈ c.stableKeys) :
    ∃ (flds : List (PropKey × Nat)) (oid : Nat),
      v = .objAt flds .absent oid ∧ StableAt W flds k := by
  cases c with
  | refs a bs vs os ms ks st => exact stableKeysT_at h.2.2.2.2.2 hk
  | dict a bs vs ds os ms ks cs st => exact stableKeysT_at h.2.2.2.2.2.2 hk
  | _ => simp [Clause.stableKeys] at hk

/-- All constructors remain admissible, without assumptions on the operand
families. Invariant comparison and arrow guards supply the required stability. -/
theorem semWithArgs_adm (X : α → Fam) (P : α → ArgFam) (c : Clause α) : Adm (semWithArgs Ξ X P c) := by
  cases c with
  | nul => exact nulT_adm
  | bool => exact boolT_adm
  | boolLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | num => exact numT_adm
  | numLit b => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | numIn _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | strIn _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | refs a bs vs os ms ks => exact ⟨fun n W v h => ⟨(adm _ _).down n W v h.1, (viewsT_adm _).down n W v h.2.1,
        (optT_adm _).down n W v h.2.2.1, (methodT_adm _).down n W v h.2.2.2.1,
        fun K hK => (ownKeysT_adm K).down n W v (h.2.2.2.2.1 K hK),
        (stableKeysT_adm _).down n W v h.2.2.2.2.2⟩,
      fun n W U hx v h => ⟨(adm _ _).mono n W U hx v h.1, (viewsT_adm _).mono n W U hx v h.2.1,
        (optT_adm _).mono n W U hx v h.2.2.1, (methodT_adm _).mono n W U hx v h.2.2.2.1,
        fun K hK => (ownKeysT_adm K).mono n W U hx v (h.2.2.2.2.1 K hK),
        (stableKeysT_adm _).mono n W U hx v h.2.2.2.2.2⟩⟩
  | dict a bs vs ds os ms ks cs =>
    refine ⟨?_, ?_⟩
    · intro n W v h
      exact ⟨(adm _ _).down n W v h.1, (viewsT_adm _).down n W v h.2.1,
        ⟨fun d hd => (dictViewT_adm _ _).down n W v (h.2.2.1.1 d hd),
          fun d hd => (dictCellT_adm _ _).down n W v (h.2.2.1.2 d hd)⟩, (optT_adm _).down n W v h.2.2.2.1,
        (methodT_adm _).down n W v h.2.2.2.2.1,
        fun K hK => (ownKeysT_adm K).down n W v (h.2.2.2.2.2.1 K hK),
        (stableKeysT_adm _).down n W v h.2.2.2.2.2.2⟩
    · intro n W U hx v h
      exact ⟨(adm _ _).mono n W U hx v h.1, (viewsT_adm _).mono n W U hx v h.2.1,
        ⟨fun d hd => (dictViewT_adm _ _).mono n W U hx v (h.2.2.1.1 d hd),
          fun d hd => (dictCellT_adm _ _).mono n W U hx v (h.2.2.1.2 d hd)⟩, (optT_adm _).mono n W U hx v h.2.2.2.1,
        (methodT_adm _).mono n W U hx v h.2.2.2.2.1,
        fun K hK => (ownKeysT_adm K).mono n W U hx v (h.2.2.2.2.2.1 K hK),
        (stableKeysT_adm _).mono n W U hx v h.2.2.2.2.2.2⟩
  | arrs L S => exact interT_adm _ _ (CallEffects.callsT_adm _) (CallEffects.restsT_adm _)
  | callable a bs L S ms =>
    exact interT_adm _ _
      (interT_adm _ _ (CallableConjunctions.adm _ _ _) (CallEffects.restsT_adm _)) (methodT_adm _)
  | ctors L S a bs vs =>
    exact interT_adm _ _ (interT_adm _ _ (ctorsT_adm _) (ctorRestsT_adm _))
      (interT_adm _ _ (CallableConjunctions.props_adm _ _) (CallableConjunctions.views_adm _))
  | pack a bs => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | bigintLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | symbolLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | undef => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | top | source => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | list a bs => exact ⟨fun n W v h => ⟨(listT_adm _).down n W v h.1,
        fun b hb => (listT_adm _).down n W v (h.2 b hb)⟩,
      fun n W U hx v h => ⟨(listT_adm _).mono n W U hx v h.1,
        fun b hb => (listT_adm _).mono n W U hx v (h.2 b hb)⟩⟩
  | str => exact strT_adm
  | strLit _ => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | bigint => exact bigintT_adm
  | symbol => exact symbolT_adm


theorem positionFam_tupleFams (X : α → Fam) (t : Tuple α) (i : Nat) :
    positionFam (tupleFams X t) i = (t.position i).map X := by
  simp only [positionFam, Tuple.position, tupleFams, List.getElem?_map, List.length_map]
  cases t.required[i]? <;> simp
  cases t.optional[i - t.required.length]? <;> simp
  split <;> simp

/-- Past the required and optional positions, every index has the rest. -/
theorem Tuple.position_beyond {t : Tuple α} {i : Nat}
    (h : t.required.length + t.optional.length ≤ i) : t.position i = t.rest := by
  simp only [Tuple.position, List.getElem?_eq_none (show t.required.length ≤ i by omega),
    List.getElem?_eq_none (show t.optional.length ≤ i - t.required.length by omega), h, if_true]

/-- An index without a position is past the fixed positions of a contract
without a rest. -/
theorem Tuple.position_none {t : Tuple α} {i : Nat} (h : t.position i = none) :
    t.required.length + t.optional.length ≤ i ∧ t.rest = none := by
  simp only [Tuple.position] at h
  cases hr : t.required[i]? <;> simp only [hr, reduceCtorEq] at h
  cases ho : t.optional[i - t.required.length]? <;> simp only [ho, reduceCtorEq] at h
  rw [List.getElem?_eq_none_iff] at hr ho
  have hi : t.required.length + t.optional.length ≤ i := by omega
  simp only [hi, if_true] at h
  exact ⟨hi, h⟩

/-- Current-level tuple membership preserves current-level agreement. -/
theorem arguments_congr (X Y : α → Fam) (t : Tuple α) (n : Nat) {W : WorldT n}
    (h : ∀ a v, X a n W v ↔ Y a n W v) (vs : List Val) :
    ArgumentContracts.Fits (tupleFams X t) n W vs ↔
      ArgumentContracts.Fits (tupleFams Y t) n W vs := by
  apply TupleFits.congr (by simp [tupleFams]) (by simp [tupleFams]) (by simp [tupleFams])
  intro i
  simp only [positionFam_tupleFams]
  refine ⟨by simp, fun A B hA hB v => ?_⟩
  cases hp : t.position i <;> simp [hp] at hA hB
  subst hA; subst hB
  exact h _ v

theorem clauseArguments_congr (X Y : α → Fam) (c : Clause α) (n : Nat) (W : WorldT n)
    (h : ∀ a v, X a n W v ↔ Y a n W v) (vs : List Val) :
    clauseArguments X c n W vs ↔ clauseArguments Y c n W vs := by
  cases c <;> try exact Iff.rfl
  rename_i a bs
  exact forall_congr' fun t => forall_congr' fun _ => arguments_congr X Y t n h vs

theorem storePresence_congr (X Y : α → Fam) (t : Tuple α) (j : Nat)
    (h : ∀ a (U : WorldT j), X a j U .undef ↔ Y a j U .undef) (ls : List (Option Nat)) :
    StorePresence (tupleFams X t) ls j ↔ StorePresence (tupleFams Y t) ls j := by
  cases ht : t.presence with
  | dense => simp [StorePresence, tupleFams, ht]
  | sparse => simp [StorePresence, tupleFams, ht]
  | readable =>
    simp only [StorePresence, show (tupleFams X t).presence = .readable from ht,
      show (tupleFams Y t).presence = .readable from ht, positionFam_tupleFams]
    constructor
    · intro hp i hi A hA U
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hA
      exact (h a U).mp (hp i hi (X a) (by simp [ha]) U)
    · intro hp i hi A hA U
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hA
      exact (h a U).mpr (hp i hi (Y a) (by simp [ha]) U)

/-- Position by position, a tuple contract's meaning depends on its labels'
meanings only below the budget, as a record's does. -/
theorem list_congr_below (X Y : α → Fam) (t : Tuple α) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    listT (tupleFams X t) n W v ↔ listT (tupleFams Y t) n W v := by
  constructor <;> rintro ⟨ls, rfl, hd, hlen, hmax, hbound, hreq, hopt, hrest⟩ <;>
    simp only [listT, tupleFams, List.length_map, List.getElem?_map, Option.map_eq_none_iff,
      Option.map_eq_some_iff] at hlen hbound hreq hopt hrest ⊢ <;>
    refine ⟨ls, rfl, ?_, hlen, hmax, hbound, ?_, ?_, ?_⟩
  · intro j hj
    exact (storePresence_congr X Y t j (fun a U => h a j hj U .undef) ls).mp (hd j hj)
  · rintro i A ⟨a, ha, rfl⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (X a) ⟨a, ha, rfl⟩
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u)⟩
  · rintro i A l ⟨a, ha, rfl⟩ hl
    obtain ⟨c, hw, hag⟩ := hopt i (X a) l ⟨a, ha, rfl⟩ hl
    exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u)⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l hi hl
    exact ⟨Y e, c, ⟨e, he, rfl⟩, hw, fun j hj W' u => (hag j hj W' u).congr (h e j hj W' u)⟩
  · intro j hj
    exact (storePresence_congr X Y t j (fun a U => h a j hj U .undef) ls).mpr (hd j hj)
  · rintro i A ⟨a, ha, rfl⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (Y a) ⟨a, ha, rfl⟩
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u).symm⟩
  · rintro i A l ⟨a, ha, rfl⟩ hl
    obtain ⟨c, hw, hag⟩ := hopt i (Y a) l ⟨a, ha, rfl⟩ hl
    exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).congr (h a j hj W' u).symm⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l hi hl
    exact ⟨X e, c, ⟨e, he, rfl⟩, hw, fun j hj W' u => (hag j hj W' u).congr (h e j hj W' u).symm⟩

theorem semWithArgs_congr {Ξ Ξ' : Fam} (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat)
    (hexc : Agree Ξ Ξ' n) (h : ∀ a, Agree (X a) (Y a) n)
    (hP : ∀ a, Agree (P a) (Q a) n) (c : Clause α) (W : WorldT n) (v : Val) :
    semWithArgs Ξ X P c n W v ↔ semWithArgs Ξ' Y Q c n W v := by
  cases c with
  | nul => rfl
  | bool => rfl
  | boolLit _ => rfl
  | num => rfl
  | numLit _ => rfl
  | numIn _ => rfl
  | strIn _ => rfl
  | str => rfl
  | strLit _ => rfl
  | bigint => rfl
  | bigintLit _ => rfl
  | symbol => rfl
  | symbolLit _ => rfl
  | undef => rfl
  | top | source => rfl
  | list a bs =>
    exact and_congr (list_congr_below X Y a n h W v) (forall_congr' fun b => forall_congr' fun _ => list_congr_below X Y b n h W v)
  | refs a bs vs os ms ks =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (views_congr_below X Y vs n h W v)
        (and_congr (opt_congr_below X Y os n h W v)
          (and_congr (methodT_congr X Y P Q n hexc h hP ms W v) Iff.rfl)))
  | dict a bs vs ds os ms ks cs =>
    exact and_congr (congr_below X Y a bs n h W v)
      (and_congr (views_congr_below X Y vs n h W v)
        (and_congr (and_congr (forall_congr' fun d => forall_congr' fun _ => dictViewT_congr (h d.2) W v)
            (forall_congr' fun d => forall_congr' fun _ => dictCellT_congr (h d.2) W v))
          (and_congr (opt_congr_below X Y os n h W v)
            (and_congr (methodT_congr X Y P Q n hexc h hP ms W v) Iff.rfl))))
  | arrs L S =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (CallEffects.callsT_congr L (Arrow.map X) (Arrow.map Y) hexc (fun _ _ => rfl)
      (fun p _ => ⟨h p.receiver, hd p.arguments, h p.result⟩) W v)
      (CallEffects.restsT_congr S (RestArrow.mapWith X P) (RestArrow.mapWith Y Q) hexc (fun _ _ => rfl)
        (fun s _ => ⟨h s.receiver, hd s.arguments.1, hP s.arguments.2, h s.result⟩) W v)
  | callable a bs L S ms =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (and_congr (CallableConjunctions.congr_below X Y a bs L n hexc h W v)
      (CallEffects.restsT_congr S (RestArrow.mapWith X P) (RestArrow.mapWith Y Q) hexc (fun _ _ => rfl)
        (fun s _ => ⟨h s.receiver, hd s.arguments.1, hP s.arguments.2, h s.result⟩) W v))
      (methodT_congr X Y P Q n hexc h hP ms W v)
  | ctors L S a bs vs =>
    have hd : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y) := by
      intro As; induction As with
      | nil => exact .nil
      | cons a As ih => exact .cons (h a) ih
    exact and_congr (and_congr (ctorsT_congr L (MethodArrow.map X) (MethodArrow.map Y) hexc
        (fun p _ => ⟨rfl, hd p.arguments, h p.result⟩) W v)
      (ctorRestsT_congr S (MethodRestArrow.mapWith X P) (MethodRestArrow.mapWith Y Q) hexc
        (fun s _ => ⟨rfl, hd s.arguments.1, hP s.arguments.2, h s.result⟩) W v))
      (and_congr (CallableConjunctions.props_congr_below X Y a bs n h W v)
        (CallableConjunctions.views_congr_below X Y vs n h W v))
  | pack a bs => rfl

/-! ## Renaming operands

`Clause.map` renames every operand; the meaning of a renamed clause is the
clause read through the renaming (`semWithArgs_map`). A renaming fixing every operand
changes nothing (`map_of_operands`). -/

def Tuple.map (f : α → β) (t : Tuple α) : Tuple β :=
  ⟨t.required.map f, t.optional.map f, t.rest.map f, t.readonly, t.presence⟩

def Tuple.operands (t : Tuple α) : List α := t.required ++ t.optional ++ t.rest.toList

def mapFields {κ : Type} (f : α → β) (fs : List (κ × α)) : List (κ × β) :=
  fs.map fun q => (q.1, f q.2)

def Clause.map (f : α → β) : Clause α → Clause β
  | .top => .top
  | .source => .source
  | .nul => .nul
  | .undef => .undef
  | .bool => .bool
  | .boolLit b => .boolLit b
  | .num => .num
  | .numLit v => .numLit v
  | .str => .str
  | .strLit v => .strLit v
  | .bigint => .bigint
  | .bigintLit v => .bigintLit v
  | .symbol => .symbol
  | .symbolLit v => .symbolLit v
  | .list a bs => .list (a.map f) (bs.map (·.map f))
  | .refs a bs vs os ms ks st => .refs (mapFields f a) (bs.map (mapFields f)) (mapFields f vs)
      (os.map (·.map f)) (ms.map (Sig.map f)) ks st
  | .dict a bs vs ds os ms ks cs st => .dict (mapFields f a) (bs.map (mapFields f)) (mapFields f vs)
      (mapFields f ds) (os.map (·.map f)) (ms.map (Sig.map f)) ks (mapFields f cs) st
  | .arrs L S => .arrs (L.map (Arrow.map f))
      (S.map (RestArrow.map f))
  | .callable a bs L S ms => .callable (mapFields f a) (bs.map (mapFields f))
      (L.map (Arrow.map f))
      (S.map (RestArrow.map f)) (ms.map (Sig.map f))
  | .ctors L S a bs vs => .ctors (L.map (MethodArrow.map f))
      (S.map (MethodRestArrow.map f)) (mapFields f a) (bs.map (mapFields f))
      (mapFields f vs)
  | .pack a bs => .pack (a.map f) (bs.map (·.map f))
  | .numIn bs => .numIn bs
  | .strIn ss => .strIn ss

theorem Clause.carriesInvariant_of_record {c : Clause α} (h : c.record = true) : c.carriesInvariant = true := by
  cases c <;> simp_all [Clause.record, Clause.carriesInvariant]

@[simp] theorem Clause.carriesInvariant_map (f : α → β) (c : Clause α) : (c.map f).carriesInvariant = c.carriesInvariant := by
  cases c <;> rfl

/-- A clause of a meet the built-ins' invariant applies to comes from an operand
it applies to. -/
theorem carriesInvariant_of_meet {a b d : Clause α} (h : d ∈ meet a b) (hd : d.carriesInvariant = true) :
    a.carriesInvariant = true ∨ b.carriesInvariant = true := by
  cases a <;> cases b <;> unfold meet at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h <;>
    (try split at h) <;> (try simp only [List.mem_singleton, List.not_mem_nil] at h) <;>
    (try subst h) <;> first
      | (simp_all [Clause.carriesInvariant]; done)
      | (rcases mem_numSet h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp_all [Clause.carriesInvariant])
      | (rcases mem_strSet h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp_all [Clause.carriesInvariant])

/-- Only top meets top in top. -/
theorem top_of_meet {a b : Clause α} (h : Clause.top ∈ meet a b) : a = .top ∧ b = .top := by
  cases a <;> cases b <;> unfold meet at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h <;>
    (try split at h) <;> (try simp only [List.mem_singleton, List.not_mem_nil] at h) <;>
    first
      | (simp_all; done)
      | (rcases mem_numSet h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he)
      | (rcases mem_strSet h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he)

/-- A member of a clause other than top that the built-ins' invariant does not
apply to is no plain object: its shape is a primitive's, a store's or a
callable's. -/
theorem semWithArgs_not_plain {X : α → Fam} {P : α → ArgFam} {c : Clause α} {n W v}
    (hc : c ≠ .top) (hr : c.carriesInvariant = false) (h : semWithArgs Ξ X P c n W v) :
    ∀ flds oid, v ≠ .objAt flds .absent oid := by
  intro flds oid he
  subst he
  have hs := semWithArgs_shape hc (by rintro rfl; cases hr) h
  cases c <;> simp_all [valueShape, shape, Clause.carriesInvariant]

/-- Every operand of a clause. -/
def Clause.operands : Clause α → List α
  | .list a bs => a.operands ++ bs.flatMap Tuple.operands
  | .refs a bs vs os ms _ _ => (a ++ bs.flatten ++ vs).map (·.2) ++ os.map (·.type) ++
      ms.flatMap Sig.operands
  | .dict a bs vs ds os ms _ cs _ => (a ++ bs.flatten ++ vs).map (·.2) ++ os.map (·.type) ++
      ds.map (·.2) ++ ms.flatMap Sig.operands ++ cs.map (·.2)
  | .arrs L S => L.flatMap Arrow.operands ++
      S.flatMap RestArrow.operands
  | .callable a bs L S ms => (a ++ bs.flatten).map (·.2) ++
      L.flatMap Arrow.operands ++
      S.flatMap RestArrow.operands ++ ms.flatMap Sig.operands
  | .ctors L S a bs vs => L.flatMap MethodArrow.operands ++ S.flatMap MethodRestArrow.operands ++
      (a ++ bs.flatten ++ vs).map (·.2)
  | .pack a bs => a.operands ++ bs.flatMap Tuple.operands
  | _ => []

private theorem famsOf_fun (X : α → Fam) :
    famsOf X = fun fs => fs.map fun p => (p.1, X p.2) := rfl

theorem tupleFams_map (Y : β → Fam) (f : α → β) (t : Tuple α) :
    tupleFams Y (t.map f) = tupleFams (fun a => Y (f a)) t := by
  simp [tupleFams, Tuple.map, Function.comp_def]

/-- Operand substitution transports value and list operands independently.
-/
theorem semWithArgs_map (Y : β → Fam) (P : β → ArgFam) (f : α → β) (c : Clause α) :
    semWithArgs Ξ Y P (c.map f) = semWithArgs Ξ (fun a => Y (f a)) (fun a => P (f a)) c := by
  cases c
  case dict =>
    simp only [semWithArgs, Clause.map, mapFields, List.forall_mem_map]
    simp [mapFields, famsOf_fun, Function.comp_def, Member.of_map, OptionalField.map]
  all_goals simp [semWithArgs, Clause.map, mapFields, famsOf_fun, tupleFams, Tuple.map, Function.comp_def,
    Member.of_map, OptionalField.map, Arrow.map, RestArrow.map, RestArrow.mapWith, MethodArrow.map,
    MethodRestArrow.map, MethodRestArrow.mapWith, Contract.map] <;> rfl


/-- The same syntactic operand substitution preserves the argument component,
read at the current level. -/
theorem clauseArguments_map (Y : β → Fam) (f : α → β) (c : Clause α) :
    clauseArguments Y (c.map f) = clauseArguments (fun a => Y (f a)) c := by
  cases c <;> try rfl
  rename_i a bs
  funext n W vs
  apply propext
  simp [clauseArguments, Clause.map, tupleFams_map]

private theorem map_self {l : List α} {f : α → α} (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [h.1, ih h.2]

private theorem mapFields_self {κ : Type} {fs : List (κ × α)} {f : α → α}
    (h : ∀ a ∈ fs.map (·.2), f a = a) : mapFields f fs = fs :=
  map_self fun q hq => by
    have := h q.2 (List.mem_map_of_mem hq)
    simp [this]

private theorem opt_self {os : List (OptionalField α)} {f : α → α}
    (h : ∀ a ∈ os.map (·.type), f a = a) : os.map (·.map f) = os :=
  map_self fun q hq => by
    have := h q.type (List.mem_map_of_mem hq)
    simp [OptionalField.map, this]

private theorem tuple_self {t : Tuple α} {f : α → α} (h : ∀ a ∈ t.operands, f a = a) :
    t.map f = t := by
  obtain ⟨r, o, e, b⟩ := t
  simp only [Tuple.operands, List.mem_append] at h
  have h1 := map_self (l := r) fun a ha => h a (.inl (.inl ha))
  have h2 := map_self (l := o) fun a ha => h a (.inl (.inr ha))
  have h3 : e.map f = e := by cases e <;> simp_all
  simp [Tuple.map, h1, h2, h3]

private theorem sig_self {m : Sig α} {f : α → α} (h : ∀ a ∈ m.operands, f a = a) :
    m.map f = m := by
  obtain ⟨k, cs, rs, ss, os⟩ := m
  simp only [Sig.operands, List.mem_append, List.mem_flatMap] at h
  simp only [Sig.map, Sig.mk.injEq, true_and]
  refine ⟨?_, ?_, map_self fun a ha => h a (.inl (.inr ha)), map_self fun a ha => h a (.inr ha)⟩
  · exact map_self fun p hp => MethodArrow.map_of_operands fun x hx =>
      h x (.inl (.inl (.inl ⟨p, hp, hx⟩)))
  · exact map_self fun p hp => MethodRestArrow.map_of_operands fun x hx =>
      h x (.inl (.inl (.inr ⟨p, hp, hx⟩)))

/-- A renaming fixing every operand fixes the clause. -/
theorem map_of_operands {c : Clause α} {f : α → α} (h : ∀ a ∈ c.operands, f a = a) :
    c.map f = c := by
  cases c with
  | list a bs =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.list.injEq]
    exact ⟨tuple_self fun x hx => h x (.inl hx),
      map_self fun t ht => tuple_self fun x hx => h x (.inr ⟨t, ht, hx⟩)⟩
  | refs a bs vs os ms ks =>
    simp only [Clause.operands, List.map_append, List.mem_append] at h
    simp only [Clause.map, Clause.refs.injEq, and_true]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl hx)))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inl (.inr ?_)))),
      mapFields_self fun x hx => h x (.inl (.inl (.inr hx))),
      opt_self fun x hx => h x (.inl (.inr hx)),
      map_self fun m hm => sig_self fun x hx => h x (.inr (List.mem_flatMap.mpr ⟨m, hm, hx⟩))⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | dict a bs vs ds os ms ks cs =>
    simp only [Clause.operands, List.map_append, List.mem_append] at h
    simp only [Clause.map, Clause.dict.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl (.inl (.inl hx)))))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl (.inl (.inr ?_)))))),
      mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl (.inr hx))))),
      mapFields_self fun x hx => h x (.inl (.inl (.inr hx))),
      opt_self fun x hx => h x (.inl (.inl (.inl (.inr hx)))),
      map_self fun m hm => sig_self fun x hx => h x (.inl (.inr (List.mem_flatMap.mpr ⟨m, hm, hx⟩))),
      trivial, mapFields_self fun x hx => h x (.inr hx), trivial⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | arrs L S =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.arrs.injEq]
    exact ⟨map_self fun p hp => Arrow.map_of_operands fun x hx => h x (.inl ⟨p, hp, hx⟩),
      map_self fun p hp => RestArrow.map_of_operands fun x hx => h x (.inr ⟨p, hp, hx⟩)⟩
  | callable a bs L S ms =>
    simp only [Clause.operands, List.map_append, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.callable.injEq]
    refine ⟨mapFields_self fun x hx => h x (.inl (.inl (.inl (.inl hx)))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inl (.inl (.inl (.inr ?_)))),
      map_self fun p hp => Arrow.map_of_operands fun x hx => h x (.inl (.inl (.inr ⟨p, hp, hx⟩))),
      map_self fun p hp => RestArrow.map_of_operands fun x hx => h x (.inl (.inr ⟨p, hp, hx⟩)),
      map_self fun m hm => sig_self fun x hx => h x (.inr ⟨m, hm, hx⟩)⟩
    simp only [List.mem_map, List.mem_flatten] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | ctors L S a bs vs =>
    simp only [Clause.operands, List.map_append, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.ctors.injEq]
    refine ⟨map_self fun q hq => MethodArrow.map_of_operands fun x hx => h x (.inl (.inl ⟨q, hq, hx⟩)),
      map_self fun q hq => MethodRestArrow.map_of_operands fun x hx => h x (.inl (.inr ⟨q, hq, hx⟩)),
      mapFields_self fun x hx => h x (.inr (.inl (.inl hx))),
      map_self fun fs hfs => mapFields_self fun x hx => h x (.inr (.inl (.inr ?_))),
      mapFields_self fun x hx => h x (.inr (.inr hx))⟩
    · simp only [List.mem_map, List.mem_flatten] at hx ⊢
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, ⟨fs, hfs, hq⟩, rfl⟩
  | pack a bs =>
    simp only [Clause.operands, List.mem_append, List.mem_flatMap] at h
    simp only [Clause.map, Clause.pack.injEq]
    exact ⟨tuple_self fun x hx => h x (.inl hx),
      map_self fun t ht => tuple_self fun x hx => h x (.inr ⟨t, ht, hx⟩)⟩
  | _ => rfl


/-- A closed constant body, used to exhibit an occupied method cell. -/
private def witnessResult (b : Bool) : Val := if b then .tru else .num 0

private def witnessCode (b : Bool) : CallCode :=
  .graph 1 [witnessResult b] [(.ret, none)] 0 [] .call false

private theorem witness_calls (b : Bool) (fs : List (PropKey × Nat)) (oid : Nat)
    (Rc : Fam) (n : Nat) (W : WorldT n) :
    CallEffects.callsT Ξ [⟨Rc, [topT], (if b then boolT else numT), .ordinary⟩]
      n W (.objAt fs (witnessCode b) oid) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fs, witnessCode b, oid, rfl, rfl, ?_⟩
    cases b <;> simp [witnessCode, witnessResult, Scoped]
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    intro j hj U hx hu heap hh r hr hrc args hv ha _
    refine ⟨_, CallArguments.Invoke.graph hr hv rfl, ?_⟩
    cases j with
    | zero => trivial
    | succ j =>
      refine Or.inr ⟨_, heap, _, WExt_refl _, WorldAdm_trunc _ hu,
        Step.gotoEnter rfl rfl, HeapOk_trunc _ _ _ hh, ?_⟩
      cases j with
      | zero => trivial
      | succ j =>
        refine Or.inr ⟨_, heap, witnessResult b, WExt_refl _, WorldAdm_trunc _ (WorldAdm_trunc _ hu),
          ?_, HeapOk_trunc _ _ _ (HeapOk_trunc _ _ _ hh), ?_⟩
        · cases b <;> exact Step.frameRet rfl
        · apply HeapObservations.SafePostExc.value
          · cases b <;> rfl
          · cases b <;> simp [Effect.result, Effect.ordinary, Effect.ofFootprint,
              witnessResult, boolT, numT]
          · simp [Effect.ordinary, Footprints.Closed.holds_top]

/-- A callable with a number result and an `isFinite` method with a Boolean
result has an inhabitant at every budget. The method cell contains closed
executable code, and its singleton contract admits that value in every world.
This proves inhabitation of the contract shape, not the native implementation
of `Number` or the numerical meaning of `isFinite`. -/
theorem callable_methods_inhabited (Ξ : Fam) (n : Nat) :
    ∃ (W : WorldT n) (heap : Heap) (v : Val), WorldAdm W ∧ HeapOk n W heap ∧
      semWithArgs Ξ id (fun _ => fun _ _ _ => True)
        (.callable [] [] [⟨topT, [topT], numT, .ordinary⟩] []
          [⟨"isFinite", [⟨(), [topT], boolT, .ordinary⟩], [], [], []⟩]) n W v := by
  let u : Val := .objAt [] (witnessCode true) 1
  let c : Ctr n := fun _ _ _ v => v = u
  let W : WorldT n := ofList [c]
  let v : Val := .objAt [("isFinite", 0)] (witnessCode false) 0
  have cell : ∀ l d, lookup W l = some d → l = 0 ∧ d = c := by
    intro l d hl
    cases l <;> simp [W, lookup, toList_ofList] at hl ⊢
    exact hl.symm
  refine ⟨W, [u], v, ?_, ?_, ?_⟩
  · intro l d hl
    obtain ⟨rfl, rfl⟩ := cell l d hl
    exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv ▸ rfl⟩
  · refine ⟨by simp [W, toList_ofList], ?_⟩
    intro l d hl
    obtain ⟨rfl, rfl⟩ := cell l d hl
    exact ⟨u, rfl, fun _ _ => rfl⟩
  · refine ⟨⟨⟨CallableConjunctions.props_nil, ?_⟩, ?_⟩, ?_⟩
    · exact witness_calls false _ _ topT n W
    · exact ⟨(witness_calls (Ξ := Ξ) false _ _ topT n W).1, by simp⟩
    · intro m hm
      simp only [List.map, List.mem_singleton] at hm
      subst m
      apply memberT_own (c := c) (l := 0) rfl
        (by simp [W, lookup, toList_ofList])
      intro j hj U hx u' he
      change u' = u at he
      subst u'
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · exact witness_calls true [] 1 _ j U
      · exact ⟨(witness_calls (Ξ := Ξ) true [] 1 topT j U).1, by simp [Member.of]⟩
      · simp [boundOn, Member.of]

end Verification.PositiveNormalization
