import Verification.Programs.VariadicTyping

/-!
# Program typing over positive recursive types

Types are finite unions of graph labels. Constructor rules inspect a singleton
expanded clause; subsumption is justified by the existing checked certificates.
The typing judgement is syntactic. Semantic environments enter only its soundness
proof, not its rules.
-/
namespace Verification.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower
open CallEffects (Arrow RestArrow MethodArrow MethodRestArrow Contract Effect PromiseWith ctorsT ctorsT_select
  ctorRestsT)
open HeapObservations (SafePost)

variable {ι : Type}

variable [DecidableEq ι]

/-- Subsumption checked at the body's assignment. A qualified body can use
its enclosing descriptor evidence here; structural subtyping retains its
independent, universally quantified checker. -/
structure BodySubtyping (G : NormalGraph ι) where
  check : Ty ι → Ty ι → PositiveCertificates.SubtypeChoices ι → Bool
  sound : ∀ {A B proof}, check A B proof = true → FamLe (meaning G A) (meaning G B)

@[nospecialize] def BodySubtyping.ordinary (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) : BodySubtyping G where
  check := PositiveCertificates.checkUsing G images
  sound := PositiveCertificates.acceptedUsing

/-- Constructor views avoid any semantic normalization assumption. -/
inductive HasTyWith (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (subtyping : BodySubtyping G) : List (Ty ι) → Tm → Ty ι → Prop where
  | var : Γ[i]? = some A → HasTyWith G images subtyping Γ (.var i) A
  | nul : Represents G A .nul → HasTyWith G images subtyping Γ .nul A
  | undef : Represents G A .undef → HasTyWith G images subtyping Γ .undef A
  | tru : Represents G A .bool → HasTyWith G images subtyping Γ .tru A
  | fls : Represents G A .bool → HasTyWith G images subtyping Γ .fls A
  | truLit : Represents G A (.boolLit true) → HasTyWith G images subtyping Γ .tru A
  | flsLit : Represents G A (.boolLit false) → HasTyWith G images subtyping Γ .fls A
  | numLit : Represents G A (.numLit b) → HasTyWith G images subtyping Γ (.num b) A
  /-- Every number is a number, as every Boolean is a Boolean. Without this a
  literal claimed at the family rather than at its own singleton has no rule. -/
  | num : Represents G A .num → HasTyWith G images subtyping Γ (.num b) A
  /-- A bigint, at its own singleton or at the family, as a number is. -/
  | bigintLit : Represents G A (.bigintLit i) → HasTyWith G images subtyping Γ (.bigint i) A
  | bigint : Represents G A .bigint → HasTyWith G images subtyping Γ (.bigint i) A
  | strLit : Represents G A (.strLit s) → HasTyWith G images subtyping Γ (.str s) A
  | str : Represents G A .str → HasTyWith G images subtyping Γ (.str s) A
  /-- **Graph code.** A function whose body is a control-flow graph, as a
  function body is: the code meets each signature it offers (`CodeOffers`:
  each checked by the graph checker, `GraphCodeSpec`; with a rest, from the
  frame holding the store of the further actuals), with its captures, slots
  of this context, at the types the code was checked with. Its kind binds
  the receivers of every signature it offers (`KindOffers`): sloppy code
  offers signatures whose receivers are objects. -/
  | funGraph {Γ : List (Ty ι)} {F : Ty ι} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {arity start : Nat} {E : List Tm}
      {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {As : List (Ty ι)} :
      Represents G F (.arrs L S) →
      KindOffers G kind L S →
      CodeOffers G arity E K start (caps.map Prod.fst) rest L S As →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeFn (.graph arity E K start (caps.map fun c => .var c.2) kind rest) .nul) F
  /-- **A generic closure.** The code meets each signature at every permitted
  assignment of the scheme's binders. Its captures are slots whose types read
  none of those binders (`FreeOk`), so they mean the same at every instantiation.
  Arity and rest-store formation are checked independently of the assignment. -/
  | funScheme {Γ : List (Ty ι)} {j : ι} {s : SchemeRow ι} {arity start : Nat} {E : List Tm}
      {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {As : List (Ty ι)} :
      G.params j = false → G.schemes j = some s → s.construct = false →
      KindOffers G kind s.signatures s.variadic →
      (∀ η Bs, Bs.length = s.binders.length → G.domain.allowed s Bs →
        CodeOffers (reassign G (assign η s.binders Bs)) arity E K start
          (caps.map Prod.fst) rest s.signatures s.variadic As) →
      CodeOffersShape G arity rest s.signatures s.variadic As →
      capturesFree G s (caps.map Prod.fst) = true →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeFn (.graph arity E K start (caps.map fun c => .var c.2) kind rest) .nul) [j]
  /-- **A class value.** Construct-only graph code, checked at each construct
  signature, with its effect, from the frame with `undefined` for the receiver
  `new` passes, and at each variadic one, whose effect is plain, with an
  element rest `El` at the row `ctorRestParams` gives: the further positions it
  binds at `El` or `undefined`; allocated with its code field and its static
  fields, named by the program, as a callable object's bag is. -/
  | ctorGraph {Γ : List (Ty ι)} {F U : Ty ι} {L : List (MethodArrow (Ty ι))}
      {S : List (MethodRestArrow (Ty ι))} {arity start : Nat}
      {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {parts : List (PropKey × Ty ι × Tm)} :
      Represents G F (.ctors L S (parts.map fun p => (p.1, p.2.1)) []) → Represents G U .undef →
      (codeField :: parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      (∀ p ∈ L, GraphCodeSpec G arity E K start (caps.map Prod.fst) ⟨U, p.arguments, p.result, p.effect⟩) →
      (∀ s ∈ S, s.effect.plain = true ∧ ∃ El, restElem G s.arguments.2 = some El ∧
        GraphCodeSpec G arity E K start (caps.map Prod.fst)
          ⟨U, ctorRestParams arity s.arguments.1 El U, s.result, s.effect⟩) →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeAt (.graph arity E K start (caps.map fun c => .var c.2) .construct)
        (codeField :: parts.map Prod.fst) (.nul :: parts.map fun p => p.2.2)) F
  /-- **A callable object.** The bag is allocated as a record's is, its fields
  named by the program, with graph code that meets the signatures it offers,
  as a function's does. -/
  | callableGraph {Γ : List (Ty ι)} {F : Ty ι} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {arity start : Nat} {E : List Tm}
      {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
      {caps : List (Ty ι × Nat)} {kind : Invoke} {rest : Bool} {As : List (Ty ι)}
      {parts : List (PropKey × Ty ι × Tm)} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] L S) →
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      KindOffers G kind L S →
      CodeOffers G arity E K start (caps.map Prod.fst) rest L S As →
      (∀ c ∈ caps, c.2 < Γ.length) →
      (∀ c ∈ caps, HasTyWith G images subtyping Γ (.var c.2) c.1) →
      HasTyWith G images subtyping Γ (.makeAt (.graph arity E K start (caps.map fun c => .var c.2) kind rest)
        (parts.map Prod.fst) (parts.map fun p => p.2.2)) F
  /-- `new f(args)`: `f` at a construct signature with a plain effect, each
  actual at its parameter, whatever static fields its class states. As a call
  may, `new` may omit trailing positions whose contracts admit `undefined`, the
  value the machine binds there. -/
  | construct {Γ : List (Ty ι)} {f : Tm} {F B : Ty ι} {L : List (MethodArrow (Ty ι))}
      {S : List (MethodRestArrow (Ty ι))} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)}
      {a : List (PropKey × Ty ι)} {bs : List (List (PropKey × Ty ι))} {vs : List (PropKey × Ty ι)}
      {e : Effect} :
      HasTyWith G images subtyping Γ f F → Represents G F (.ctors L S a bs vs) →
      ⟨(), xs.map Prod.fst ++ Us, B, e⟩ ∈ L → e.plain = true →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) →
      HasTyWith G images subtyping Γ (.construct f (xs.map Prod.snd)) B
  /-- **A variadic construction.** `new f(args)` at a variadic construct
  signature with a plain effect: the fixed actuals at its parameters, then
  parts that fit its rest (`RestParts`), as a variadic call's do. -/
  | constructRest {Γ : List (Ty ι)} {f : Tm} {F P B : Ty ι} {L : List (MethodArrow (Ty ι))}
      {S : List (MethodRestArrow (Ty ι))} {xs : List (Ty ι × Tm)} {parts : List (Bool × Ty ι × Tm)}
      {a : List (PropKey × Ty ι)} {bs : List (List (PropKey × Ty ι))} {vs : List (PropKey × Ty ι)}
      {e : Effect} :
      HasTyWith G images subtyping Γ f F → Represents G F (.ctors L S a bs vs) →
      ⟨(), (xs.map Prod.fst, P), B, e⟩ ∈ S → e.plain = true →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      RestParts G P (parts.map fun p => (p.1, p.2.1)) →
      HasTyWith G images subtyping Γ (.construct f (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2))) B
  /-- A call writes the actuals it writes, and passes the receiver `r`, typed
  at the selected signature's receiver. `Us` are the trailing positions the
  signature declares and this call omits; each admits `undefined`, which is
  the value the machine binds there. `Us = []` is the exact-arity call. -/
  | callCallable {effect : Effect} {Γ : List (Ty ι)} {f r : Tm} {F Rt B : Ty ι} {P : List (PropKey × Ty ι)}
      {Ps : List (List (PropKey × Ty ι))} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTyWith G images subtyping Γ f F → Represents G F (.callable P Ps L S) →
      ⟨Rt, xs.map Prod.fst ++ Us, B, effect⟩ ∈ L → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) →
      effect.plain = true → HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd)) B
  /-- A field of a value with code: a callable object's bag field, or a
  class value's static field. -/
  | readCallable {c : Clause (Ty ι)} : HasTyWith G images subtyping Γ a F → Represents G F c →
      c.bag = some (P, Ps) → (f, A) ∈ P →
      HasTyWith G images subtyping Γ (.readAt f a) A
  /-- A readonly static field of a class value: a view of its own field. -/
  | readBagView {c : Clause (Ty ι)} : HasTyWith G images subtyping Γ a F → Represents G F c →
      (f, A) ∈ c.bagViews → HasTyWith G images subtyping Γ (.readAt f a) A
  | writeCallable {c : Clause (Ty ι)} : HasTyWith G images subtyping Γ a F → Represents G F c →
      c.bag = some (P, Ps) → (f, A) ∈ P →
      HasTyWith G images subtyping Γ b A → Represents G N .nul → HasTyWith G images subtyping Γ (.writeAt f a b) N
  | app {effect : Effect} {Γ : List (Ty ι)} {f r : Tm} {F Rt B : Ty ι} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTyWith G images subtyping Γ f F → Represents G F (.arrs L S) →
      ⟨Rt, xs.map Prod.fst ++ Us, B, effect⟩ ∈ L → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) →
      effect.plain = true → HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd)) B
  | letE : HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping (A :: Γ) b B → HasTyWith G images subtyping Γ (.letE a b) B
  /-- **Allocation.** One object, one fresh location per named field. The field
  names are distinct, which is what makes the object a map from them. Its own
  keys are exactly those names, so any bound admitting them holds of it. -/
  | alloc {parts : List (PropKey × Ty ι × Tm)} {ks : List KeyBound} :
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      Represents G Ref (.refs (parts.map fun p => (p.1, p.2.1)) [] [] [] [] ks) →
      (∀ K ∈ ks, ∀ p ∈ parts, K.admits p.1 = true) →
      allocBuiltins G (parts.map fun p => (p.1, p.2.1)) = true →
      HasTyWith G images subtyping Γ (.makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2)) Ref
  /-- **Allocation at a dictionary.** A literal allocated directly at a
  dictionary type: its fields are the clause's first operand, with no key the
  model keeps for its prototype, and each field whose key an index's class may
  admit is at exactly that index's type. The object owns no other key, so each
  index holds of it, writable ones included, and it lacks each optional field
  the clause states, which a key added at a writable index's contract keeps
  (the field at that contract, or none meets it). No own-key bound is stated,
  since code holding the dictionary may add keys. -/
  | allocDict {parts : List (PropKey × Ty ι × Tm)} {ix cs : List (IndexKeys × Ty ι)}
      {os : List (OptionalField (Ty ι))} :
      (parts.map Prod.fst).Nodup → CallArguments.protoField ∉ parts.map Prod.fst →
      CallArguments.arrayStoreField ∉ parts.map Prod.fst →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      Represents G Ref (.dict (parts.map fun p => (p.1, p.2.1)) [] [] ix os [] [] cs) →
      (∀ p ∈ parts, ∀ y ∈ ix ++ cs, y.1.may p.1 = true → p.2.1 = y.2) →
      (∀ o ∈ os, o.key ∉ parts.map Prod.fst) →
      (∀ o ∈ os, ∀ y ∈ cs, y.1.may o.key = true → o.type = y.2 ∨ PositiveRules.Uninhabited G y.2) →
      HasTyWith G images subtyping Γ (.makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2)) Ref
  /-- A named field, of a record or of a dictionary, reads at its contract. -/
  | read : HasTyWith G images subtyping Γ a Ref → Represents G Ref c → namedMembers c = some (fs, vs) →
      (f, A) ∈ fs → HasTyWith G images subtyping Γ (.readAt f a) A
  /-- A view field reads at its bound: a capability, never a write permission.
  A view of `length` is read so where its type excludes a number, so that no
  array meets it (`lengthExcluded`). -/
  | readView : HasTyWith G images subtyping Γ a Ref → Represents G Ref c → namedMembers c = some (fs, vs) →
      (f, A) ∈ vs → (f ≠ lengthKey ∨ lengthExcluded G A = true) → HasTyWith G images subtyping Γ (.readAt f a) A
  /-- **`length` through a view.** A view of `length` admits an array, whose
  `length` is its store's: the read tests the slot's value, and reads an
  array's store length, a number the view's type holds, or any other object's
  own `length` location. -/
  | lenView {Γ : List (Ty ι)} {i : Nat} {Ref A : Ty ι} {c : Clause (Ty ι)} {fs vs : List (PropKey × Ty ι)} :
      Γ[i]? = some Ref → Represents G Ref c → namedMembers c = some (fs, vs) → (lengthKey, A) ∈ vs →
      PositiveRules.numIn G A = true →
      HasTyWith G images subtyping Γ (lengthRead i) A
  /-- **A read through the prototype.** A key one of the object's key bounds
  does not admit is not its own, so the read continues at the prototype, which the
  object holds under the reserved key at `P`; the prototype's field or view
  for the key gives the type. -/
  | readProto {a : Tm} {Ref P : Ty ι} {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
      {ms : List (MethodMembers.Sig (Ty ι))} {ks : List KeyBound} {K : KeyBound}
      {gs ws : List (PropKey × Ty ι)} {os' : List (OptionalField (Ty ι))}
      {ms' : List (MethodMembers.Sig (Ty ι))}
      {ks' : List KeyBound} {f : PropKey} {A : Ty ι} :
      HasTyWith G images subtyping Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → K ∈ ks → K.admits f = false →
      (CallArguments.protoField, P) ∈ fs ++ vs → Represents G P (.refs gs [] ws os' ms' ks') →
      (f, A) ∈ gs ++ ws.filter (·.1 != lengthKey) → HasTyWith G images subtyping Γ (.readAt f a) A
  /-- An optional field, writable or readonly, reads at its type or, where the
  object lacks the key, as `undefined`. -/
  | readOptional {a : Tm} {Ref : Ty ι} {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
      {ms : List (MethodMembers.Sig (Ty ι))} {ks : List KeyBound} {f : PropKey} {r : Bool}
      {A U : Ty ι} :
      HasTyWith G images subtyping Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → ⟨f, r, A⟩ ∈ os →
      Represents G U .undef → inheritedKey f = false → HasTyWith G images subtyping Γ (.readAt f a) (A ++ U)
  /-- A dictionary read may miss even when every present value has type `A`.
  An index says nothing of a key its class does not admit, so a key is read
  through one only where its class surely admits it: any string key through
  a string index, a canonical numeric one ("0", "1.5") through a number
  index, a symbol key through a symbol index. -/
  | readDict {f : PropKey} {K : IndexKeys} : HasTyWith G images subtyping Γ a Ref →
      Represents G Ref (.dict fs [] vs ix os ms ks cs) →
      (K, A) ∈ ix → K.surely f = true → Represents G U .undef → inheritedKey f = false →
      HasTyWith G images subtyping Γ (.readAt f a) (A ++ U)
  /-- A computed key of the key clause of a class within the index's reads
  through it: a string through a string index, a number through a number
  index or a string one, a symbol through a symbol index. -/
  | indexDict {K KK : IndexKeys} : HasTyWith G images subtyping Γ a Ref → Represents G Ref (.dict fs [] vs ix os ms ks cs) →
      HasTyWith G images subtyping Γ key Kt → Represents G Kt (keyClause KK) → KK.within K = true →
      (K, A) ∈ ix → Represents G U .undef → KK ≠ .strings →
      HasTyWith G images subtyping Γ (.indexAt a key) (A ++ U)
  | write : HasTyWith G images subtyping Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → (f, A) ∈ fs →
      HasTyWith G images subtyping Γ b A → Represents G N .nul → HasTyWith G images subtyping Γ (.writeAt f a b) N
  /-- A binary operator needs operand types it answers for, pair by pair
  (`Operands`), and yields the family of its result kind: no singleton, since
  the result's value is not typed. -/
  | arith : HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping Γ b B → OperatorTypes G op A B N →
      HasTyWith G images subtyping Γ (.arith op a b) N
  /-- A literal allocates a store: one fresh location per element, each
  under the position's contract of the tuple the store is claimed at, whose
  bounds the element count respects. -/
  | arrLit {Γ : List (Ty ι)} {L : Ty ι} {T : Tuple (Ty ι)} {xs : List (Ty ι × Tm)} :
      Represents G L (.list T []) → T.required.length ≤ xs.length →
      (T.rest = none → xs.length ≤ T.required.length + T.optional.length) →
      (∀ p ∈ xs.zipIdx, positionTy T p.2 = some p.1.1) →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → HasTyWith G images subtyping Γ (.arrLit (xs.map Prod.snd)) L
  /-- A required position, named by a literal index, reads at its contract. -/
  | elem {Γ : List (Ty ι)} {a i : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → HasTyWith G images subtyping Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → T.required[k]? = some A → HasTyWith G images subtyping Γ (.elemAt a i) A
  /-- An optional or rest position, named by a literal index, reads at its
  contract or `undefined`: it may be a hole or past the end. -/
  | elemOpt {Γ : List (Ty ι)} {a i : Tm} {L I A U : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → HasTyWith G images subtyping Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → T.required[k]? = none → positionTy T k = some A →
      Represents G U .undef → HasTyWith G images subtyping Γ (.elemAt a i) (A ++ U)
  /-- Any numeric index into a homogeneous array reads an element or
  `undefined`; no index is in bounds by type alone. -/
  | elemAny {Γ : List (Ty ι)} {a i : Tm} {L I E U : Ty ι} {ro : Bool} {presence : ArrayPresence} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list ⟨[], [], some E, ro, presence⟩ []) → HasTyWith G images subtyping Γ i I →
      Answers G I .isNum true → Represents G U .undef → HasTyWith G images subtyping Γ (.elemAt a i) (E ++ U)
  /-- A write at a literal index into a position the contract names keeps the
  contract: into the element's location, or a fresh one the store records.
  The index is at most the required length, so the write is in bounds or
  appends at the end: it never leaves a hole, and the store stays dense. -/
  | setElem {Γ : List (Ty ι)} {a i v : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → HasTyWith G images subtyping Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → positionTy T k = some A → k ≤ T.required.length →
      T.readonly = false → HasTyWith G images subtyping Γ v A → HasTyWith G images subtyping Γ (.setElem a i v) L
  | len {Γ : List (Ty ι)} {a : Tm} {L N : Ty ι} {T : Tuple (Ty ι)} :
      HasTyWith G images subtyping Γ a L → Represents G L (.list T []) → Represents G N .num → HasTyWith G images subtyping Γ (.lenOf a) N
  /-- A string's own `length` is a number. -/
  | lenStr {Γ : List (Ty ι)} {a : Tm} {S N : Ty ι} :
      HasTyWith G images subtyping Γ a S → Answers G S .isStr true → Represents G N .num → HasTyWith G images subtyping Γ (.lenOf a) N
  /-- A string read at any numeric index is a string, or `undefined` past its
  end or at a key that is not an index. -/
  | elemStr {Γ : List (Ty ι)} {a i : Tm} {S I T U : Ty ι} :
      HasTyWith G images subtyping Γ a S → Answers G S .isStr true → HasTyWith G images subtyping Γ i I → Answers G I .isNum true →
      Represents G T .str → Represents G U .undef → HasTyWith G images subtyping Γ (.elemAt a i) (T ++ U)
  /-- A tag test whose answer the operand's type does not settle is still a
  Boolean: its type holds both literals. -/
  | test : HasTyWith G images subtyping Γ a A → (.boolLit true) ∈ expand G B → (.boolLit false) ∈ expand G B →
      HasTyWith G images subtyping Γ (.test k a) B
  | ifBool : HasTyWith G images subtyping Γ c C → Answers G C .isBool true →
      HasTyWith G images subtyping Γ t A → HasTyWith G images subtyping Γ e A → HasTyWith G images subtyping Γ (.ite c t e) A
  /-- The condition still evaluates; its singleton type selects the reachable arm. -/
  | ifKnown : HasTyWith G images subtyping Γ c C → Represents G C (.boolLit q) →
      HasTyWith G images subtyping Γ (if q then t else e) A → HasTyWith G images subtyping Γ (.ite c t e) A
  | ifBoolVar : Γ[i]? = some C → Answers G C .isBool true →
      Represents G T (.boolLit true) → Represents G F (.boolLit false) →
      HasTyWith G images subtyping (Γ.set i T) t A → HasTyWith G images subtyping (Γ.set i F) e A →
      HasTyWith G images subtyping Γ (.ite (.var i) t e) A
  | ifTag : Γ[i]? = some A → Answers G A tag q →
      (q = true → HasTyWith G images subtyping Γ u B) → (q = false → HasTyWith G images subtyping Γ e B) →
      HasTyWith G images subtyping Γ (.ite (.test tag (.var i)) u e) B
  /-- Eliminate a finite union in one immutable environment slot. Every member
  must establish the same term and result, without changing other bindings. -/
  | unionVar : Γ[i]? = some C →
      (∀ a ∈ C, HasTyWith G images subtyping (Γ.set i [a]) t A) → HasTyWith G images subtyping Γ t A
  /-- **A literal with spreads.** `[a, ...s, b]` allocates a fresh store of
  its parts' values in order: each plain part at the element type `E`, each
  spread the elements of the store it evaluates to, read where it is written,
  which spread into `E`. The store's length is not known, so its contract is
  `E` at every position. -/
  | arrParts {Γ : List (Ty ι)} {T E : Ty ι} {ro : Bool} {presence : ArrayPresence}
      {parts : List (Bool × Ty ι × Tm)} :
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      (∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E) →
      Represents G T (.list ⟨[], [], some E, ro, presence⟩ []) →
      HasTyWith G images subtyping Γ (.arrLit (parts.map fun p => spreadTerm (p.1, p.2.2))) T
  /-- **A variadic call.** The fixed actuals meet the selected signature's
  parameters, less trailing ones `Us` the call omits, each admitting
  `undefined`, and a call that omits a fixed position writes nothing further.
  The further parts fit the rest (`RestParts`): with a spread, each part is at
  the element rest's element or spreads into it; without one, the parts are
  at the positions of the rest's tuple contract. The signature may be a
  function's or a callable object's. -/
  | callRest {effect : Effect} {Γ : List (Ty ι)} {f r : Tm} {F Rt : Ty ι}
      {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} {P B : Ty ι} {parts : List (Bool × Ty ι × Tm)} :
      HasTyWith G images subtyping Γ f F → ⟨Rt, (xs.map Prod.fst ++ Us, P), B, effect⟩ ∈ restSigs G F → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → (∀ A ∈ Us, HasTyWith G images subtyping Γ .undef A) → (Us = [] ∨ parts = []) →
      (∀ p ∈ parts, HasTyWith G images subtyping Γ p.2.2 p.2.1) →
      RestParts G P (parts.map fun p => (p.1, p.2.1)) → effect.plain = true →
      HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2))) B
  /-- **A spread of a packed value.** A call at a variadic signature whose
  rest admits a packed binder `t`'s argument lists, after its fixed actuals,
  spreads the store of a value of `t`, or of a meet row of it: its elements
  are one of `t`'s lists. -/
  | callPacked {effect : Effect} {Γ : List (Ty ι)} {f r a : Tm} {F Rt A B P : Ty ι}
      {xs : List (Ty ι × Tm)} {t : ι} :
      HasTyWith G images subtyping Γ f F → ⟨Rt, (xs.map Prod.fst, P), B, effect⟩ ∈ restSigs G F →
      t ∈ P → HasTyWith G images subtyping Γ r Rt →
      (∀ p ∈ xs, HasTyWith G images subtyping Γ p.2 p.1) → HasTyWith G images subtyping Γ a A → PackedBy G A t →
      effect.plain = true → HasTyWith G images subtyping Γ (.invoke f r (xs.map Prod.snd ++
        [.spread (.readAt CallArguments.arrayStoreField a)])) B
  /-- **A bound function.** `.bind` saved its target, receiver and prefix in
  slots; allocation stores those values, as they are, in a forwarding
  descriptor with no fields. The result takes the positions the target's
  selected signatures have after the prefix, with any receiver: the one it is
  later called with is dropped for the saved one. Each keeps its effect, a
  promise about a parameter past the prefix shifted onto the positions left. -/
  | bindE {Γ : List (Ty ι)} {F T Rt : Ty ι} {t r : Nat} {slots : List Nat}
      {Ps : List (Ty ι)} {L : List (Arrow (Ty ι))} :
      Γ[t]? = some T → Γ[r]? = some Rt → slots.map (Γ[·]?) = Ps.map some → L ≠ [] →
      (∀ a ∈ L, ∃ s ∈ callSigs G T, s.receiver = Rt ∧ s.arguments = Ps ++ a.arguments ∧
        s.result = a.result ∧ s.effect.keeps slots.length = true ∧
        s.effect.drop slots.length = a.effect) →
      Represents G F (.arrs L []) →
      HasTyWith G images subtyping Γ (.makeAt (.bound (.var t) (.var r) (slots.map .var)) [] []) F
  /-- **A bound variadic function.** As `bindE`, for a variadic signature of
  the target whose rest is an element rest: the prefix takes its first fixed
  positions, and past them the element; the result is the positions left, then
  the rest, at any receiver. -/
  | bindRestE {effect : Effect} {Γ : List (Ty ι)} {F T Rt E El R Rc : Ty ι} {t r : Nat} {slots : List Nat}
      {Ps Qs : List (Ty ι)} :
      Γ[t]? = some T → ⟨Rt, (Ps, E), R, effect⟩ ∈ restSigs G T → restElem G E = some El →
      Γ[r]? = some Rt → slots.map (Γ[·]?) = Qs.map some →
      Qs = Ps.take slots.length ++ List.replicate (slots.length - Ps.length) El → effect.keeps slots.length = true →
      Represents G F (.arrs [] [⟨Rc, (Ps.drop slots.length, E), R, effect.drop slots.length⟩]) →
      HasTyWith G images subtyping Γ (.makeAt (.bound (.var t) (.var r) (slots.map .var)) [] []) F
  /-- **A member bound to its host.** The member is read from the object in a
  slot, before anything else runs, and bound to that same object: the bound
  function meets the member's signatures whatever receiver it is later given,
  and each fixed or variadic signature one of them covers. The host's type is
  within each type the member's host must meet, by checked proofs. This is how
  a method call `o.m(args)` keeps JavaScript's order, reading the member before
  the actuals, while the member's contract stays host-relative. -/
  | bindMember {Γ : List (Ty ι)} {F O : Ty ι} {i : Nat} {k : PropKey}
      {m : MethodMembers.Sig (Ty ι)} {L : List (Arrow (Ty ι))}
      {S : List (RestArrow (Ty ι))} :
      Γ[i]? = some O → memberOf G O k = some m → Represents G F (.arrs L S) →
      (∀ q ∈ L, ∃ c ∈ m.calls, CoveredCallUsing G images q c) →
      (∀ s ∈ S, ∃ c ∈ m.rests, CoveredRestUsing G images s c) →
      (∀ T ∈ m.receivers, ∃ p, PositiveCertificates.checkUsing G images O T p = true) →
      HasTyWith G images subtyping Γ (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) F
  /-- **A member bound to its host, at its quantified signatures.** As
  `bindMember`, the member is read from the object in a slot and bound to that
  same object; a generic method's signatures are a scheme the bound function
  meets, whatever receiver it is later given. A call names its instance below
  the scheme. -/
  | bindScheme {Γ : List (Ty ι)} {F O : Ty ι} {i : Nat} {k : PropKey}
      {m : MethodMembers.Sig (Ty ι)} :
      Γ[i]? = some O → memberOf G O k = some m → F ∈ m.schemes → expand G F = [] →
      HasTyWith G images subtyping Γ (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) F
  /-- `throw a` has every type: it never produces a value, and a throw is an
  outcome safety admits. Its operand runs first and must produce a
  JavaScript value. -/
  | throw : SourceValues G A → HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping Γ (.throw a) B
  /-- **An allocation from parts.** The accumulator, then the source; the
  result is what `MergeOk` states each pair of their clauses gives: a fresh
  plain object holding the accumulator's own fields and, over them, the own
  enumerable data properties the source has when it is copied, less the
  dropped keys (`ObjectMerge.merge_values_safe`). -/
  | merge {d : List PropKey} {a b : Tm} {A B R : Ty ι} :
      HasTyWith G images subtyping Γ a A → HasTyWith G images subtyping Γ b B → ObjectMerge.MergeOk G d A B R = true →
      HasTyWith G images subtyping Γ (.merge d a b) R
  /-- **An allocation at a computed key.** The key, then the initializer; the
  result is the one-key object `KeyedOk` states each clause of the key's type
  gives: the one field a literal key names, or the dictionary over the class
  of a family's keys, writable at the initializer's type
  (`ComputedKey.keyed_values_safe`). -/
  | makeKey {k a : Tm} {K A R : Ty ι} :
      HasTyWith G images subtyping Γ k K → HasTyWith G images subtyping Γ a A →
      ComputedKey.KeyedOk G K A R = true →
      HasTyWith G images subtyping Γ (.makeKey k a) R
  | sub : HasTyWith G images subtyping Γ t A → subtyping.check A B cert = true → HasTyWith G images subtyping Γ t B

/-- Body typing with the ordinary checker as its default. -/
abbrev HasTyUsing (G : NormalGraph ι) (images : PositiveCertificates.InstanceImageCheck G)
    (Γ : List (Ty ι)) (t : Tm) (A : Ty ι)
    (subtyping : BodySubtyping G := BodySubtyping.ordinary G images) : Prop :=
  HasTyWith G images subtyping Γ t A

namespace HasTyUsing
export HasTyWith (var nul undef tru fls truLit flsLit numLit num bigintLit bigint strLit str funGraph funScheme ctorGraph callableGraph construct constructRest callCallable readCallable readBagView writeCallable app letE alloc allocDict read readView lenView readProto readOptional readDict indexDict write arith arrLit elem elemOpt elemAny setElem len lenStr elemStr test ifBool ifKnown ifBoolVar ifTag unionVar arrParts callRest callPacked bindE bindRestE bindMember bindScheme throw merge makeKey sub)
end HasTyUsing

/-- A type reading none of a scheme's binders means the same at every
instantiation of them (`agree_freeWith`). -/
theorem meaning_assign_free {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) {bs : List ι} {A : Ty ι}
    (hA : ∀ l ∈ A, l ∈ D ∧ ∀ p ∈ fv V l, p ∉ bs) (As : List MixedFamily) {n W v}
    (h : meaning G A n W v) : meaning (reassign G (assign G.env bs As)) A n W v := by
  obtain ⟨l, hl, hv⟩ := h
  refine ⟨l, hl, ?_⟩
  change qDenoteWithArgs G (mixedParameters G) (assign G.env bs As, l) n W v
  rw [agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF) _ G.env l (hA l hl).1
    (fun p hp => by rw [assign_nmem G.env bs As ((hA l hl).2 p hp)])]
  exact hv

omit [DecidableEq ι] in
/-- **Captured values.** Slots of a context meeting it, each safe at the type
its code was checked with, hold closed values meeting those types in every
later world: what graph code captures when it is created. -/
theorem captures_sem {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n}
    {h : Heap} {caps : List (Ty ι × Nat)} (he : EnvOk G Γ ρ n W)
    (hlt : ∀ c ∈ caps, c.2 < Γ.length)
    (ih : ∀ c ∈ caps, Safe (excOf G) (meaning G c.1) n W h (ρ c.2))
    {j : Nat} (hj : j < n) {V : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) V) :
    (∀ v ∈ caps.map (fun c => ρ c.2), Scoped 0 v) ∧
      EnvOk G (caps.map Prod.fst) (envOf (caps.map fun c => ρ c.2) .nul) j V ∧
      ∀ c ∈ caps, meaning G c.1 j V (ρ c.2) := by
  have hvals : ∀ c ∈ caps, isVal (ρ c.2) = true ∧ Scoped 0 (ρ c.2) := by
    intro c hc
    obtain ⟨B, hB⟩ : ∃ B, Γ[c.2]? = some B :=
      ⟨_, List.getElem?_eq_getElem (hlt c hc)⟩
    exact meaning_value (he.2 _ _ hB)
  have hcapv : ∀ c ∈ caps, meaning G c.1 j V (ρ c.2) := by
    intro c hc
    cases n with
    | zero => omega
    | succ p =>
      have hm := safe_value_mem (hvals c hc).1 (ih c hc)
      exact (meaning_adm G c.1).mono j _ V hx _
        ((meaning_adm G c.1).down_le (p+1) j (Nat.le_of_lt hj) W _ hm)
  have hsc : ∀ v ∈ caps.map (fun c => ρ c.2), Scoped 0 v := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    exact (hvals c hc).2
  refine ⟨hsc, ?_, hcapv⟩
  apply EnvOk.envOf_nul hsc (by simp)
  intro i A hA v hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hA hv
  obtain ⟨c, hc, rfl⟩ := hA
  obtain ⟨c', hc', rfl⟩ := hv
  cases hc.symm.trans hc'
  exact hcapv c (List.mem_of_getElem? hc)

/-- Every derivation is safe in every admissible world and satisfying heap. -/
theorem HasTyUsing.sound {G : NormalGraph ι} {images : PositiveCertificates.InstanceImageCheck G}
    {subtyping : BodySubtyping G} {Γ t A}
    (ht : HasTyUsing G images (subtyping := subtyping) Γ t A) :
    ∀ n W h ρ, EnvOk G Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (excOf G) (meaning G A) n W h (instantiate 0 ρ t) := by
  induction ht with
  | var hi =>
    intro n W h ρ he hw hh
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact value_safe _ _ _ _ _ (meaning_value (he.2 _ _ hi)).1 (he.2 _ _ hi)
  | nul hr | undef hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | tru hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) (Or.inl rfl))
  | fls hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) (Or.inr rfl))
  | truLit hr | flsLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | numLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | @num _ _ b hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) ⟨b, rfl⟩)
  | bigintLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | @bigint _ _ i hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) ⟨i, rfl⟩)
  | strLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) rfl)
  | @str _ _ s hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_back hr n W _) ⟨s, rfl⟩)
  | @funGraph Γ F L S arity start E K caps kind rest As hr hkind hspec hlt hcap ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map]
    apply makeFn_rule nulT_adm nulT_valOnly n W h _ .nul rfl hw hh rfl
    intro j hj V hx
    obtain ⟨hsc, henv, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ih c hc n W h ρ he hw hh) hj hx
    have ho := offers_sem (oid := h.length + 1) [(codeField, h.length)] hkind hspec henv hsc (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1)
    exact (represents_back hr j V _) ⟨ho.1, ho.2⟩
  | @funScheme Γ i s arity start E K caps kind rest Ss hp hq hcon hkind hspec _hshape hcf hlt hcap ih =>
    obtain ⟨hF, hfree⟩ := capturesFree_sound hcf
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map]
    apply makeFn_rule nulT_adm nulT_valOnly n W h _ .nul rfl hw hh rfl
    intro j hj U hx
    obtain ⟨hsc, -, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ih c hc n W h ρ he hw hh) hj hx
    let vs := caps.map fun c => ρ c.2
    -- The captures, at every instantiation of the scheme's binders: their
    -- types read none of them.
    have henv : ∀ As : List MixedFamily,
        EnvOk (reassign G (assign G.env s.binders As)) (caps.map Prod.fst) (envOf vs .nul) j U := by
      intro As
      apply EnvOk.envOf_nul hsc (by simp)
      intro k A hA v hv
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hA hv
      obtain ⟨c, hc, rfl⟩ := hA
      obtain ⟨c', hc', rfl⟩ := hv
      cases hc.symm.trans hc'
      exact meaning_assign_free hF (hfree c.1 (List.mem_map_of_mem (List.mem_of_getElem? hc))) As
        (hcapv c (List.mem_of_getElem? hc))
    have hsig : ∀ As : List MixedFamily, As.length = s.binders.length →
        G.domain.allowed s As → instanceTWithArgs (excOf G) (fun η S => mixedValues G η S) G.env s As (graphArguments G) j U
          (Tm.fnObj h.length (.graph arity E K start vs kind rest)) := by
      intro As hlen hal
      have ho := offers_sem (G := reassign G (assign G.env s.binders As)) (oid := h.length + 1)
        [(codeField, h.length)] hkind
        (hspec G.env As hlen hal) (henv As) hsc (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1)
      simp only [instanceTWithArgs, sigsT, hcon, Bool.false_eq_true, if_false]
      exact ⟨ho.1, ho.2⟩
    refine ⟨i, List.mem_singleton_self i, ?_⟩
    change qDenoteWithArgs G (mixedParameters G) (G.env, i) j U _
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hp, hq, Bool.false_eq_true, if_false]
    refine ⟨?_, fun q hq As hlen hal _ => (instanceTWithArgs_adm _ _ _ _ _).down_le j q hq U _ (hsig As hlen hal)⟩
    simp only [Callee, hcon, Bool.false_eq_true, if_false]
    exact ⟨_, _, _, rfl, callable_of_kind hkind.1, by simpa [Scoped, vs, instantiate] using hsc⟩
  | @ctorGraph Γ F U L S arity start E K caps parts hr hu hnd hp hspec hrest hlt hcap ih ihc =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, List.map_cons, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.graph arity E K start (caps.map fun c => ρ c.2) .construct)
        (codeField :: parts.map Prod.fst) (.nul :: args))
      (fun hs => CallArguments.Step.makeArgs (.tail rfl hs)) (fun hr => (CallArguments.ArgRaises.tail rfl hr).make)
      hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu' heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlenA := ArgsT_length hargs
    apply make_fields_rule (As := nulT :: parts.map fun p => meaning G p.2.1)
      (by
        intro A hA'
        rcases List.mem_cons.mp hA' with rfl | hA'
        · exact nulT_adm
        · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by
        intro A hA'
        rcases List.mem_cons.mp hA' with rfl | hA'
        · exact nulT_valOnly
        · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap (.graph arity E K start (caps.map fun c => ρ c.2) .construct) _ (.nul :: args) hnd
      (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · rfl
        · exact ArgsT_values
            (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
            hargs v hv)
      hu' hok
      (by
        intro q hq
        simp only [List.zip_cons_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · rfl
        · exact ArgsT_zip hargs q hq)
    intro k' hk' V hy hrec
    have hWV : WExt (trunc k' (by omega) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hk') hx
    obtain ⟨hsc, henv, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ihc c hc n W h ρ he hw hh) (by omega) hWV
    have hvals : CallArguments.Values (caps.map fun c => ρ c.2) := by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1
    have hc := ctorsT_of_graph (oid := heap.length + (.nul :: args).length)
      (slots heap.length (codeField :: parts.map Prod.fst)) hspec hu henv hsc hvals
    have hcr := ctorRestsT_of_graph (oid := heap.length + (.nul :: args).length)
      (slots heap.length (codeField :: parts.map Prod.fst)) hrest hu henv hsc hvals
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    have hbag : recT (ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))) k' V
        (.objAt (slots heap.length (codeField :: parts.map Prod.fst)) .absent
          (heap.length + (.nul :: args).length)) := by
      obtain ⟨flds, oid, he', hall⟩ := hrec
      refine ⟨flds, oid, he', fun f T hm => hall f T ?_⟩
      rw [hfam] at hm
      simp only [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hm
    exact (represents_back hr k' V _)
      ⟨⟨hc, hcr⟩, ⟨⟨_, _, _, rfl, rfl, hbag⟩, by simp⟩, CallableConjunctions.views_nil⟩
  | @callableGraph Γ F L S arity start E K caps kind rest As parts hr hnd hp hkind hspec hlt hcap ih ihc =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.graph arity E K start (caps.map fun c => ρ c.2) kind rest)
        (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) (fun hr => hr.make) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlenA := ArgsT_length hargs
    apply make_fields_rule (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap (.graph arity E K start (caps.map fun c => ρ c.2) kind rest) _ args hnd
      (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k' hk' V hy hrec
    have hWV : WExt (trunc k' (by omega) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hk') hx
    obtain ⟨hsc, henv, hcapv⟩ := captures_sem he hlt
      (fun c hc => by simpa [instantiate] using ihc c hc n W h ρ he hw hh) (by omega) hWV
    have ho := offers_sem (oid := heap.length + args.length) (slots heap.length (parts.map Prod.fst)) hkind hspec henv hsc (by
      intro v hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      exact (meaning_value (hcapv c hc)).1)
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    exact (represents_back hr k' V _)
      ⟨⟨⟨⟨_, _, _, rfl, rfl, by rw [hfam]; exact hrec⟩, by simp⟩, ho.1⟩, ho.2⟩
  | @construct Γ f F B L S xs Us a bs vs e hf hr hp hpl hx hu ihf ihx ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := construct_safe (Ξ := excOf G) (B := meaning G B) hpl
      (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)) (Us.map (meaning G))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      hw hh (f := instantiate 0 ρ f) ?_ ?_ ?_
    · simpa only [List.map_map, Function.comp_def] using hs
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map, Function.comp_def, List.map_append] using
        ctorsT_select ((represents_raw hr k U v) hv).1.1
          (List.mem_map.mpr ⟨⟨(), xs.map Prod.fst ++ Us, B, e⟩, hp,
            by simp [MethodArrow.map, Contract.map, List.map_append, List.map_map, Function.comp_def]⟩)
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact ihx q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @constructRest Γ f F P B L S xs parts a bs vs e hf hr hmem hpl hx hp hparts ihf ihx ihp =>
    intro n W h ρ he hw hh
    have hfF : Safe (excOf G) (ctorRestsT (excOf G) [⟨(), (xs.map fun p => meaning G p.1, argMeaning G P), meaning G B, e⟩])
        n W h (instantiate 0 ρ f) := by
      apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k _ U v hv
      have hc := ((represents_raw hr k U v) hv).1.2
      refine ⟨hc.1, fun q hq => ?_⟩
      rw [List.mem_singleton] at hq
      subst hq
      exact hc.2 _ (List.mem_map.mpr ⟨⟨(), (xs.map Prod.fst, P), B, e⟩, hmem,
        by simp [MethodRestArrow.mapWith, Contract.map, List.map_map, Function.comp_def]⟩)
    unfold RestParts at hparts
    split at hparts
    · -- A spread: the rest is an element rest.
      rename_i hany
      split at hparts
      · rename_i E hel
        have hterm : instantiate 0 ρ (.construct f
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .construct (instantiate 0 ρ f)
              ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
              (parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
                instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p _
          rcases p with ⟨_ | _, A, t⟩ <;> rfl
        have hpart : ∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E :=
          fun p hp' => hparts (p.1, p.2.1) (List.mem_map_of_mem hp')
        rw [hterm]
        apply construct_rest_safe hpl (Ps := xs.map fun p => meaning G p.1)
          (E := meaning G E) (P := argMeaning G P) (R := meaning G B)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q.1)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q.1)
          (meaning_adm G E) (meaning_valOnly G E) (argMeaning_adm G P)
          (fun k W xs hxs => (restElem_args hel).mpr hxs)
          _ (by simp [List.map_map, Function.comp_def]) _
          (by
            intro q hq S hS
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
            rcases p with ⟨_ | _, A, t⟩
            · simp at hS
            · simp only [if_true, Option.some.injEq] at hS
              subst hS
              have := hpart _ hp'
              simp only [if_true] at this
              exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
          hw hh hfF
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          rcases p with ⟨_ | _, A, t⟩
          · have hA : A = E := by simpa using hpart _ hp'
            subst hA
            exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
    · -- No spread: the parts are at the positions of the rest's tuple contract.
      rename_i hany
      split at hparts
      · rename_i T hPT
        obtain ⟨hreq, hbound, hpos⟩ := hparts
        simp only [List.any_map, List.any_eq_true, not_exists, not_and, Function.comp_def,
          Bool.not_eq_true] at hany
        have hterm : instantiate 0 ρ (.construct f
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .construct (instantiate 0 ρ f)
              ((xs.map (fun p => (meaning G p.1, instantiate 0 ρ p.2)) ++
                parts.map (fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))).map Prod.snd) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p hp'
          simp [spreadTerm, hany p hp']
        rw [hterm]
        apply construct_pack_safe hpl (Ps := xs.map fun p => meaning G p.1)
          (Qs := parts.map fun p => meaning G p.2.1)
          (P := argMeaning G P) (R := meaning G B)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_adm G _)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_valOnly G _)
          (argMeaning_adm G P)
          (fun k W extra ha => restParts_pack hPT (Qs := parts.map (·.2.1))
            (by simpa using hreq) (by simpa using hbound)
            (by
              intro i hi
              have := hpos i (by simpa using hi)
              simpa [List.getElem?_map, Option.map_map, Function.comp_def] using this)
            (by simpa [List.map_map, Function.comp_def] using ha))
          _ (by simp [List.map_map, Function.comp_def])
          hw hh hfF
        · intro q hq j hj U hxU hu heap hok
          rcases List.mem_append.mp hq with hq | hq <;> obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          · exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
  | @callCallable effect Γ f r F Rt B P Ps L S xs Us hf hr hp hrt ha hu hplain ihf ihrt iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (Ξ := excOf G) (Rc := meaning G Rt) (B := meaning G B) (f := instantiate 0 ρ f)
      (r := instantiate 0 ρ r)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (meaning_adm G Rt) (meaning_valOnly G Rt)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa [Arrow.map, Contract.map, Arrow.plain, List.map_map, List.map_append, Function.comp_def] using
        CallEffects.callsT_erase (by simpa [Arrow.map, Contract.map] using hplain)
          (CallEffects.callsT_select (((represents_raw hr k U v) hv).1.2) (List.mem_map_of_mem hp))
    · intro j hj U hx hu' heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @readCallable Γ a Ref P Ps f A c ha hr hc hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact bag_read (meaning_valOnly G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      (bag_sem hc ((represents_raw hr j U v) ha')).1 hu hok
  | @readBagView Γ a Ref f A c ha hr hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, code, oid, l, c', rfl, hf, hl, hag⟩ :=
      CallableConjunctions.views_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
        (bagViews_sem ((represents_raw hr j U v) ha') (List.ne_nil_of_mem hm))
    exact read_view_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @writeCallable Γ a Ref P Ps f A b N c ha hr hc hm hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 Raises.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.writeAt f av) (Step.writeC2 hav) (Raises.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    apply Safe_mono k (fun i _ X v hval => (represents_back hn i X v) hval)
    exact bag_write (meaning_adm G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      (bag_sem hc ((represents_raw hr k V av) ha'')).1 hb' hbval hv hok'
  | @app effect Γ f r F Rt B L S xs Us hf hr hp hrt ha hu hplain ihf ihrt iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (Ξ := excOf G) (Rc := meaning G Rt) (B := meaning G B) (f := instantiate 0 ρ f)
      (r := instantiate 0 ρ r)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (meaning_adm G Rt) (meaning_valOnly G Rt)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa [Arrow.map, Contract.map, Arrow.plain, List.map_map, List.map_append, Function.comp_def] using
        CallEffects.callsT_erase (by simpa [Arrow.map, Contract.map] using hplain)
          (CallEffects.callsT_select ((represents_raw hr k U v) hv).1 (List.mem_map_of_mem hp))
    · intro j hj U hx hu' heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @letE Γ a A b B ha hb iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .letE a (instantiate 1 ρ b)) Step.letC Raises.letC n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    cases j with
    | zero => trivial
    | succ k =>
      apply let_rule _ _ hav k U heap hu hok
      rw [instantiate_beta ρ he.1]
      have he' := ((he.transfer (k+1) hj U hx).push ha').transfer k (Nat.le_succ k)
        (trunc k (Nat.le_succ k) U) (WExt_refl _)
      exact ihb k _ heap (push av ρ) he' (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @alloc Γ Ref parts ks hnd hp hr hbound hreal ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt .absent (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) (fun hr => hr.make) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply make_fields_rule
      (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap .absent _ args hnd (by simpa using hlen.symm) (by simpa using hlen.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hrec
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    have hrec' := hrec
    rw [← hfam] at hrec'
    refine (represents_sem hr k V _).mpr ⟨⟨⟨hrec', by simp⟩, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      ⟨by simpa [ReferenceConjunctions.famsOf] using optT_nil, MethodMembers.methodT_nil _ _ _,
        fun K hK => ownKeysT_slots fun n hn => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
          exact hbound K hK p hp⟩⟩, ?_⟩
    have hinv := allocBuiltins_sound hreal (by simpa [List.map_map, Function.comp_def] using hnd)
      (.refs (parts.map fun p => (p.1, p.2.1)) [] [] [] [] ks) (base := heap.length) (k := k) (V := V)
      (by simpa [List.map_map, Function.comp_def] using hrec)
    simpa [List.map_map, Function.comp_def] using hinv
  | @allocDict Γ Ref parts ix cs os hnd hproto hstore hp hr hix habs _ ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt .absent (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) (fun hr => hr.make) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply make_fields_rule
      (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
      j U heap .absent _ args hnd (by simpa using hlen.symm) (by simpa using hlen.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hrec
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    -- The object owns exactly the fields, each at its part's type.
    have hown : ∀ f l, (slots heap.length (parts.map Prod.fst)).lookup f = some l →
        ∃ T, (f, T) ∈ (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      intro f l hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (slots_lookup_mem hl)
      exact ⟨meaning G p.2.1, by
        rw [← hfam]; exact List.mem_map.mpr ⟨(p.1, p.2.1), List.mem_map_of_mem hp, rfl⟩⟩
    have hnp := slots_lookup_none (base := heap.length) hproto
    have hcell : ∀ y ∈ ix ++ cs,
        dictCellT y.1 (meaning G y.2) k V (.objAt (slots heap.length (parts.map Prod.fst)) .absent (heap.length + args.length)) := by
      intro y hy
      refine dictCellT_of_recT hrec hown hnp fun f T hT hk => ?_
      rw [← hfam] at hT
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hT
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      cases hqe
      rw [hix p hp y hy (IndexKeys.may_of_admits hk)]
      exact fun _ _ _ _ => Iff.rfl
    have hrec' := hrec
    rw [← hfam] at hrec'
    refine (represents_sem hr k V _).mpr ⟨⟨⟨hrec', by simp⟩,
      fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      ⟨fun y hy => dictCellT_view (hcell y (List.mem_append_left _ hy)),
        fun y hy => hcell y (List.mem_append_right _ hy)⟩,
      ⟨_, _, rfl, fun _ _ _ => hnp, fun o ho l hl => by
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        rw [show (OptionalField.map (meaning G) o').key = o'.key from rfl,
          slots_lookup_none (habs o' ho')] at hl
        cases hl⟩, MethodMembers.methodT_nil _ _ _,
      fun K hK => by simp at hK⟩, builtinInvariant_of_lookup (slots_lookup_none hstore)⟩
  | @read Γ a Ref c fs vs f A ha hr hc hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, l, c, oid', rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) (namedMembers_sem hr hc ha').1
    exact read_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @readView Γ a Ref c fs vs f A ha hr hc hm hlen ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    have hviews := (namedMembers_sem hr hc ha').2
    have hmA : (f, meaning G A) ∈ ReferenceConjunctions.famsOf (meaning G) vs :=
      ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩
    cases j with
    | zero => trivial
    | succ j =>
      obtain ⟨flds, l, c, oid', rfl, hf, hl, hag⟩ : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr (j + 1))
          (oid : Nat), v = .objAt flds .absent oid ∧ flds.lookup f = some l ∧ lookup U l = some c ∧
          ∀ (i : Nat) (hi : i < j + 1) (W' : WorldT i) (u : Val), c i hi W' u → meaning G A i W' u := by
        rcases hlen with hlen | hex
        · exact viewsT_at hmA hlen hviews
        · rcases hviews f _ hmA with hv1 | ⟨-, -, hall⟩
          · exact viewT_at (List.mem_singleton_self _) hv1
          · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hex
            exact absurd (hall 0 (by omega) (ofList []) w) (numWitness_sound hw)
      exact read_view_rule (meaning_valOnly G A) (j + 1) U heap l hu hok hf hl hag
  | @lenView Γ i Ref A c fs vs hi hr hc hm hnum =>
    intro n W h ρ henv hw hh
    have hval := (meaning_value (henv.2 i Ref hi)).1
    simp only [lengthRead, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ n =>
      cases n with
      | zero =>
        exact Or.inr ⟨trunc 0 (by omega) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
          .iteC (.testV hval), HeapOk_trunc 0 W h hh, trivial⟩
      | succ k =>
        have henv' := henv.transfer k (by omega) _ (WExt_refl _)
        have hv := henv'.2 i Ref hi
        have hw' : WorldAdm (trunc k (by omega) W) := WorldAdm_trunc _ hw
        have hh' : HeapOk k (trunc k (by omega) W) h := by
          simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh)
        obtain ⟨hsem, hinv⟩ := (represents_sem hr k _ (ρ i)).mp hv
        obtain ⟨hrec, hviews⟩ := namedMembers_sem hr hc hv
        obtain ⟨flds, oid, hρ, -⟩ := hrec
        apply ite_test_rule .isArray (ρ i) hval _ _ k W h hw hh
        · -- An array: its store is a list, whose length the view's type holds.
          intro ht
          rw [hρ] at ht ⊢
          have hst : (flds.lookup CallArguments.arrayStoreField).isSome = true := ht
          have hinv' := hinv
          rw [hρ] at hinv'
          obtain ⟨l, c', hf, hl, hag⟩ := builtinInvariant_store (namedMembers_carriesInvariant hc) hinv' hst
          apply bind Tm.lenOf Step.lenC Raises.lenC k _ h _ hw' hh'
            (read_view_rule (A := fun _ _ u => ∃ ls, u = .arr ls) (fun _ _ _ ⟨ls, he⟩ => by subst he; rfl)
              k _ h l hw' hh' hf hl hag)
          intro j _ U _ hu heap av hok _ ⟨ls, hav⟩
          subst hav
          exact len_rule j U heap hu hok (fun m U' => numIn_sound hnum G.env _)
        · -- Any other object: no store, so the view is at its own location.
          intro hf
          rw [hρ] at hf ⊢
          have hf2 : (flds.lookup CallArguments.arrayStoreField).isSome = false := hf
          have hns : flds.lookup CallArguments.arrayStoreField = none := by
            cases hl : flds.lookup CallArguments.arrayStoreField with
            | none => rfl
            | some l => rw [hl] at hf2; cases hf2
          rw [hρ] at hviews
          obtain ⟨flds', l, c', oid', he', hf', hl, hag⟩ :=
            viewsT_at_plain (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) hns hviews
          cases he'
          exact read_view_rule (meaning_valOnly G A) k _ h l hw' hh' hf' hl hag
  | @readProto Γ a Ref P fs vs os ms ks K gs ws os' ms' ks' f A ha hr hK hf hpr hP hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    have hs := (represents_raw hr j U v) ha'
    have hloc : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr j) (oid : Nat), v = .objAt flds .absent oid ∧
        flds.lookup CallArguments.protoField = some l ∧ lookup U l = some c ∧
        ∀ (i : Nat) (hi : i < j) (V : WorldT i) (u : Val), c i hi V u → meaning G P i V u := by
      rcases List.mem_append.mp hpr with hpr | hpr
      · obtain ⟨flds, l, c, oid', he, hf', hl, hag⟩ :=
          recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨P, hpr, rfl⟩) hs.1.1
        exact ⟨flds, l, c, oid', he, hf', hl, fun i hi V u hu => (hag i hi V u).mp hu⟩
      · exact viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨P, hpr, rfl⟩) (by decide) hs.2.1
    obtain ⟨flds, l, c, oid, rfl, hpf, hl, hag⟩ := hloc
    have hmiss := ownKeysT_lookup (hs.2.2.2.2 K hK) hf
    apply read_proto_rule j U heap l hu hok hmiss hpf hl hag
    intro i V h' hV hh' u hu
    have hp := (represents_raw hP i V u) hu
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨flds', l', c', oid'', rfl, hf', hl', hag'⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) hp.1.1
      exact read_rule (meaning_valOnly G A) i V h' l' hV hh' hf' hl' hag'
    · obtain ⟨hm, hml⟩ := List.mem_filter.mp hm
      obtain ⟨flds', l', c', oid'', rfl, hf', hl', hag'⟩ :=
        viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) (by simpa using hml) hp.2.1
      exact read_view_rule (meaning_valOnly G A) i V h' l' hV hh' hf' hl' hag'
  | @readOptional Γ a Ref fs vs os ms ks f r A U ha hr hm hUnd _ ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj V hx hv heap v hok hval ha'
    have hs := (represents_raw hr j V v) ha'
    obtain ⟨flds, oid, rfl, _⟩ := hs.1.1
    apply Safe_mono j (fun k _ X u hu => (meaning_append G A U k X u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_back hUnd k X u) h)))) V heap _
      (read_optional_rule (meaning_valOnly G A) j V heap hv hok
        (optT_no_proto (List.mem_map_of_mem hm) hs.2.2.1)
        (fun l hl => by
          obtain ⟨c, hc, hag⟩ := optT_present (List.mem_map_of_mem hm) hs.2.2.1 hl
          exact ⟨c, hc, fun i hi U u hu => (hag i hi U u).1 hu⟩))

  | @readDict Γ a Ref fs vs ix os ms ks cs A U f K ha hr hm hsure hUnd _ ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC Raises.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj V hx hv heap v hok hval ha'
    have hd := ((represents_raw hr j V v) ha').2.2.1.1 (K, A) hm
    obtain ⟨flds, oid, rfl, _⟩ := ((represents_raw hr j V v) ha').1.1
    apply Safe_mono j (fun k _ X u hu => (meaning_append G A U k X u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_back hUnd k X u) h)))) V heap _
      (read_dict_rule (meaning_valOnly G A) j V heap hv hok (IndexKeys.surely_admits hsure) hd)
  | @indexDict Γ a Ref fs vs ix os ms ks cs key Kt A U K KK ha hr hk hStr hwithin hm hUnd _ iha ihk =>
    intro n W h ρ he hw hh
    apply bind (fun v => .indexAt v (instantiate 0 ρ key)) Step.indexC1 Raises.indexC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj V hx hv heap av hok hav ha'
    apply bind (Tm.indexAt av) (Step.indexC2 hav) (Raises.indexC2 hav) j V heap _ hv hok
      (ihk j V heap ρ (he.transfer j hj V hx) hv hok)
    intro k hk X hy hX heap' kv hok' hkv hk'
    have ha'' := (meaning_adm G Ref).mono k _ X hy av
      ((meaning_adm G Ref).down_le j k hk V av ha')
    obtain ⟨f, hkey, hadmits⟩ := keyClause_admits ((represents_raw hStr k X kv) hk')
    have hd := dictViewT_within hwithin (((represents_raw hr k X av) ha'').2.2.1.1 (K, A) hm)
    obtain ⟨flds, oid, rfl, _⟩ := ((represents_raw hr k X av) ha'').1.1
    apply Safe_mono k (fun i _ Y u hu => (meaning_append G A U i Y u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_back hUnd i Y u) h)))) X heap' _
      (index_dict_rule (meaning_valOnly G A) k X heap' hX hok' hkey hadmits hd)
  | @arrLit Γ L T xs hr hreq hbound hpos hx ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd
        = xs.map fun x => instantiate 0 ρ x.2 := by simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.1)
      (fun args => .arrLit args) (fun hs => CallArguments.Step.arrArgs hs) (fun hr => hr.arrLit) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.fst
        = xs.map fun p => meaning G p.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply arr_alloc_rule (As := xs.map fun p => meaning G p.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.1)
      j U heap args hlen.symm
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hl
    refine (represents_back hr k V _) ⟨?_, by simp⟩
    rw [hlen]
    apply listT_alloc
    · simpa [tupleFams] using hreq
    · intro hn
      simp only [tupleFams, List.length_map, Option.map_eq_none_iff] at hn ⊢
      exact hbound hn
    · intro i A hA
      rw [positionFam_tupleFams]
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hA
      obtain ⟨p, hp, rfl⟩ := hA
      have := hpos (p, i) (by simpa [List.mem_zipIdx_iff_getElem?] using hp)
      simp [this]
    · exact hl
  | @elem Γ a i L I A T b k ha hr hi hI hk hA iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U heap _ hu hok
      (ihi j U heap ρ (he.transfer j hj U hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U av ha')
    obtain ⟨ls, rfl, -, -, -, hreq, -, -⟩ := ((represents_raw hr m V av) ha'').1
    simp only [tupleFams, List.getElem?_map] at hreq
    have hb : iv = .num b := (represents_raw hI m V iv) hi'
    subst hb
    obtain ⟨l, c, hl, hw', hag⟩ := hreq k (meaning G A) (by simp [hA])
    exact elem_read_rule (meaning_valOnly G A) m V heap' l hv hok' (by simp [elemLoc, hk, hl]) hw'
      (fun j hj U u => (hag j hj U u).1)
  | @elemOpt Γ a i L I A U T b k ha hr hi hI hk hnone hA hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U' av ha')
    obtain ⟨ls, rfl, -, -, -, -, hopt, hrest⟩ := ((represents_raw hr m V av) ha'').1
    simp only [tupleFams, List.length_map, List.getElem?_map] at hopt hrest
    have hb : iv = .num b := (represents_raw hI m V iv) hi'
    subst hb
    have hundef : ∀ m' (U'' : WorldT m'), meaning G (A ++ U) m' U'' .undef := fun m' U'' =>
      (meaning_append G A U m' U'' _).mpr (Or.inr ((represents_back hU m' U'' _) rfl))
    cases hloc : elemLoc ls b with
    | none => exact elem_absent_rule m V heap' hv hok' hloc hundef
    | some l =>
      have hl : ls[k]? = some (some l) := by
        simp only [elemLoc, hk, Option.bind_some] at hloc
        cases hls : ls[k]? with
        | none => simp [hls] at hloc
        | some o => cases o with
          | none => simp [hls] at hloc
          | some l' => simp [hls] at hloc; subst hloc; rfl
      have hpos := hA
      simp only [positionTy, hnone] at hpos
      have key : ∃ c : Ctr m, lookup V l = some c ∧
          ∀ (j : Nat) (hj : j < m) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (meaning G A j W' u) := by
        split at hpos
        · rename_i hopt'
          cases hpos
          have hk' : T.required.length + (k - T.required.length) = k := by
            have := (List.getElem?_eq_none_iff.mp hnone); omega
          exact hopt (k - T.required.length) (meaning G A) l
            (by simp [hopt']) (by rw [hk']; exact hl)
        · split at hpos
          · rename_i hge
            obtain ⟨E, c, hE, hw', hag⟩ := hrest k l hge hl
            simp only [Option.map_eq_some_iff] at hE
            obtain ⟨e, he, rfl⟩ := hE
            rw [he] at hpos
            cases hpos
            exact ⟨c, hw', hag⟩
          · cases hpos
      obtain ⟨c, hw', hag⟩ := key
      apply Safe_mono m (fun m' _ U'' u hu => (meaning_append G A U m' U'' u).mpr (Or.inl hu))
      exact elem_read_rule (meaning_valOnly G A) m V heap' l hv hok' hloc hw' (fun j hj U u => (hag j hj U u).1)
  | @elemAny Γ a i L I E U ro presence ha hr hi hq hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U' av ha')
    obtain ⟨ls, rfl, -, -, -, -, -, hrest⟩ := ((represents_raw hr m V av) ha'').1
    have hnum := answers_sound hq hi'
    obtain ⟨b, rfl⟩ : ∃ b, iv = .num b := by
      cases iv <;> simp [tagHolds] at hnum; exact ⟨_, rfl⟩
    have hundef : ∀ m' (U'' : WorldT m'), meaning G (E ++ U) m' U'' .undef := fun m' U'' =>
      (meaning_append G E U m' U'' _).mpr (Or.inr ((represents_back hU m' U'' _) rfl))
    cases hloc : elemLoc ls b with
    | none => exact elem_absent_rule m V heap' hv hok' hloc hundef
    | some l =>
      obtain ⟨k, hk, hl⟩ : ∃ k, indexOfBits b = some k ∧ ls[k]? = some (some l) := by
        simp only [elemLoc] at hloc
        cases hkb : indexOfBits b with
        | none => simp [hkb] at hloc
        | some k =>
          simp only [hkb, Option.bind_some] at hloc
          cases hls : ls[k]? with
          | none => simp [hls] at hloc
          | some o => cases o with
            | none => simp [hls] at hloc
            | some l' => simp [hls] at hloc; subst hloc; exact ⟨k, rfl, hls⟩
      obtain ⟨E', c, hE, hw', hag⟩ := hrest k l (by simp [tupleFams]) hl
      simp only [tupleFams, List.map_nil, Option.map_some, Option.some.injEq] at hE
      subst hE
      apply Safe_mono m (fun m' _ U'' u hu => (meaning_append G E U m' U'' u).mpr (Or.inl hu))
      exact elem_read_rule (meaning_valOnly G E) m V heap' l hv hok' hloc hw' (fun j hj U u => (hag j hj U u).1)
  | @setElem Γ a i v L I A T b k ha hr hi hI hk hA hkle hro hv iha ihi ihv =>
    intro n W h ρ he hw hh
    apply bind (fun a => .setElem a (instantiate 0 ρ i) (instantiate 0 ρ v)) Step.setC1 Raises.setC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (fun i => .setElem av i (instantiate 0 ρ v)) (Step.setC2 hav) (Raises.setC2 hav) j U heap _ hu hok
      (ihi j U heap ρ (he.transfer j hj U hx) hu hok)
    intro m hm V hy hvw heap' iv hok' hival hi'
    apply bind (.setElem av iv) (Step.setC3 hav hival) (Raises.setC3 hav hival) m V heap' _ hvw hok'
      (ihv m V heap' ρ ((he.transfer j hj U hx).transfer m hm V hy) hvw hok')
    intro p hp X hz hxw heap'' vv hok'' hvval hv'
    have hav' := (meaning_adm G L).mono p _ X hz av ((meaning_adm G L).down_le m p hp V av
      ((meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U av ha')))
    have hlist := ((represents_raw hr p X av) hav').1
    obtain ⟨ls, rfl, -, hlen, -, hreq, hopt, hrest⟩ := hlist
    simp only [tupleFams, List.length_map, List.getElem?_map] at hreq hopt hrest hlen
    have rwContract : ∀ P Q : Prop, SlotContract T.readonly P Q ↔ (P ↔ Q) := by
      intro P Q; simp [SlotContract, hro, iff_def]
    simp only [rwContract] at hreq hopt hrest
    have hb : iv = .num b := (meaning_adm G I).mono p _ X hz iv ((meaning_adm G I).down_le m p hp V iv hi')
      |> (represents_raw hI p X iv)
    subst hb
    have hkeep : ∀ j' (hj' : j' < p) (U' : WorldT j'), WExt (trunc j' (Nat.le_of_lt hj') X) U' →
        meaning G L j' U' (.arr ls) := fun j' hj' U' hx' =>
      (meaning_adm G L).mono j' _ U' hx' _ ((meaning_adm G L).down_le p j' (by omega) X _ hav')
    cases hloc : elemLoc ls b with
    | some l =>
      have hl : ls[k]? = some (some l) := by
        simp only [elemLoc, hk, Option.bind_some] at hloc
        cases hls : ls[k]? with
        | none => simp [hls] at hloc
        | some o => cases o with
          | none => simp [hls] at hloc
          | some l' => simp [hls] at hloc; subst hloc; rfl
      have key : ∃ c : Ctr p, lookup X l = some c ∧
          ∀ (j : Nat) (hj : j < p) (W' : WorldT j) (u : Val), c j hj W' u ↔ meaning G A j W' u := by
        have hpos := hA
        simp only [positionTy] at hpos
        split at hpos
        · rename_i hreq'
          cases hpos
          obtain ⟨l', c, hl', hw', hag⟩ := hreq k (meaning G A) (by simp [hreq'])
          cases Option.some.inj (Option.some.inj (hl.symm.trans hl'))
          exact ⟨c, hw', hag⟩
        · rename_i hnone
          split at hpos
          · rename_i hopt'
            cases hpos
            have hk' : T.required.length + (k - T.required.length) = k := by
              have := (List.getElem?_eq_none_iff.mp hnone); omega
            exact hopt (k - T.required.length) (meaning G A) l
              (by simp [hopt']) (by rw [hk']; exact hl)
          · split at hpos
            · rename_i hge
              obtain ⟨E, c, hE, hw', hag⟩ := hrest k l hge hl
              simp only [Option.map_eq_some_iff] at hE
              obtain ⟨e, he, rfl⟩ := hE
              rw [he] at hpos
              cases hpos
              exact ⟨c, hw', hag⟩
            · cases hpos
      obtain ⟨c, hw', hag⟩ := key
      exact set_present_rule (meaning_adm G A) p X heap'' l vv hvval hxw hok'' hloc hw' hag hv' hkeep
    | none =>
      apply set_grow_rule (meaning_adm G A) (meaning_valOnly G A) p X heap'' vv hvval hxw hok'' hk hloc hv'
      intro j' hj' U' hx' hm'
      refine (represents_back hr j' U' _) ⟨?_, by simp⟩
      have hold := ((represents_raw hr j' U' _) (hkeep j' hj' U' hx')).1
      apply listT_grow hold
      · rw [positionFam_tupleFams, hA]; rfl
      · simp only [elemLoc, hk, Option.bind_some] at hloc; exact hloc
      · omega
      · exact hm'
  | @len Γ a L N T ha hr hn ih =>
    intro n W h ρ he hw hh
    apply bind Tm.lenOf Step.lenC Raises.lenC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    obtain ⟨ls, rfl, -⟩ := ((represents_raw hr j U av) ha').1
    exact len_rule j U heap hu hok (fun m U' => (represents_back hn m U' _) ⟨_, rfl⟩)
  | @lenStr Γ a S N ha hs hn ih =>
    intro n W h ρ he hw hh
    apply bind Tm.lenOf Step.lenC Raises.lenC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    have hstr := answers_sound hs ha'
    obtain ⟨s, rfl⟩ : ∃ s, av = .str s := by
      cases av <;> simp [tagHolds] at hstr; exact ⟨_, rfl⟩
    exact len_str_rule j U heap hu hok (fun m U' => (represents_back hn m U' _) ⟨_, rfl⟩)
  | @elemStr Γ a i S I T U ha hs hi hq hT hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 Raises.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) (Raises.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G S).mono m _ V hy av ((meaning_adm G S).down_le j m hm U' av ha')
    have hstr := answers_sound hs ha''
    obtain ⟨s, rfl⟩ : ∃ s, av = .str s := by
      cases av <;> simp [tagHolds] at hstr; exact ⟨_, rfl⟩
    have hnum := answers_sound hq hi'
    obtain ⟨b, rfl⟩ : ∃ b, iv = .num b := by
      cases iv <;> simp [tagHolds] at hnum; exact ⟨_, rfl⟩
    exact elem_str_rule m V heap' hv hok'
      (fun m' U'' t => (meaning_append G T U m' U'' _).mpr (Or.inl ((represents_back hT m' U'' _) ⟨t, rfl⟩)))
      (fun m' U'' => (meaning_append G T U m' U'' _).mpr (Or.inr ((represents_back hU m' U'' _) rfl)))
  | @test Γ a A B k ha ht hf ih =>
    intro n W h ρ he hw hh
    apply bind (.test k) Step.testC Raises.testC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    cases j with
    | zero => trivial
    | succ p =>
      apply Safe_mono (p+1) (fun m _ X v hv => ?_) U heap _ (test_value_safe k av hav p U heap hu hok)
      rcases hv with rfl | rfl
      · exact expand_sem_mpr ⟨_, expand_sub ht, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
      · exact expand_sem_mpr ⟨_, expand_sub hf, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
  | @merge Γ d a b A B R ha hb hm iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .merge d a (instantiate 0 ρ b)) Step.mergeC1 Raises.mergeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.merge d av) (Step.mergeC2 hav) (Raises.mergeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G A).mono k _ V hy av ((meaning_adm G A).down_le j k hk U av ha')
    exact ObjectMerge.merge_values_safe hm hv hok' ha'' hb'
  | @makeKey Γ k a K A R hk ha hm ihk iha =>
    intro n W h ρ he hw hh
    apply bind (fun k => .makeKey k (instantiate 0 ρ a)) Step.makeKeyC1 Raises.makeKeyC1 n W h _ hw hh
      (ihk n W h ρ he hw hh)
    intro j hj U hx hu heap kv hok hkv hk'
    apply bind (.makeKey kv) (Step.makeKeyC2 hkv) (Raises.makeKeyC2 hkv) j U heap _ hu hok
      (iha j U heap ρ (he.transfer j hj U hx) hu hok)
    intro i hi V hy hv heap' av hok' haval ha'
    have hk'' := (meaning_adm G K).mono i _ V hy kv ((meaning_adm G K).down_le j i hi U kv hk')
    exact ComputedKey.keyed_values_safe hm hv hok' hk'' ha'
  | @arith Γ a A b B op N ha hb hopt iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .arith op a (instantiate 0 ρ b)) Step.arithC1 Raises.arithC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.arith op av) (Step.arithC2 hav) (Raises.arithC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G A).mono k _ V hy av ((meaning_adm G A).down_le j k hk U av ha')
    rcases hopt with hopt | ⟨hdec, hn⟩
    case inr =>
      have hres : ∃ z, binop op av bv = some z ∧ OpResult.bool.holds z := by
        rcases hdec with ⟨hp, hall⟩ | ⟨hp, hall⟩
        · obtain ⟨c, hc, hca, -⟩ := (expand_sem G A hp k V av).mp ha''
          exact (decidingClause_sound (hall c hc) hca hbval).1
        · obtain ⟨d, hd, hdb, -⟩ := (expand_sem G B hp k V bv).mp hb'
          exact (decidingClause_sound (hall d hd) hdb hav).2
      obtain ⟨z, hz, hr⟩ := hres
      refine arith_value_safe op av bv z hz k V heap' hv hok' (fun m U => ?_)
      rcases hr with rfl | rfl
      · exact expand_sem_mpr ⟨_, expand_sub hn.1, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
      · exact expand_sem_mpr ⟨_, expand_sub hn.2, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
    unfold ClauseOperatorTypes at hopt
    split at hopt
    case h_2 => exact hopt.elim
    rename_i r _
    obtain ⟨hops, hn⟩ := hopt
    obtain ⟨c, hc, hca, -⟩ := (expand_sem G A hops.1 k V av).mp ha''
    obtain ⟨d, hd, hdb, -⟩ := (expand_sem G B hops.2.1 k V bv).mp hb'
    rcases opResult_sound (hops.2.2 c hc d hd) hca hdb with ⟨z, hz, hr⟩ | hthrow
    case inr => exact arith_throw_safe op av bv hthrow k V heap' hv hok' (builtinExc_errors G _)
    refine arith_value_safe op av bv z hz k V heap' hv hok' (fun m U => ?_)
    cases r with
    | num => obtain ⟨x, rfl⟩ := hr; exact (represents_back hn m U _) ⟨x, rfl⟩
    | bigint => obtain ⟨i, rfl⟩ := hr; exact (represents_back hn m U _) ⟨i, rfl⟩
    | str => obtain ⟨s, rfl⟩ := hr; exact (represents_back hn m U _) ⟨s, rfl⟩
    | bool =>
      rcases hr with rfl | rfl
      · exact expand_sem_mpr ⟨_, expand_sub hn.1, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
      · exact expand_sem_mpr ⟨_, expand_sub hn.2, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
  | @write Γ a Ref fs vs os ms ks f A b N ha hr hm hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 Raises.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.writeAt f av) (Step.writeC2 hav) (Raises.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    obtain ⟨flds, l, c, oid', rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) ((represents_raw hr k V av) ha'').1.1
    apply Safe_mono k (fun i _ X v hval => (represents_back hn i X v) hval)
    exact write_rule (meaning_adm G A) k V heap' l bv hbval hv hok' hf hl hag hb'
  | @ifBool Γ c C t A e hc hbool ht he ihc iht ihe =>
    intro n W h ρ henv hw hh
    apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC Raises.iteC
      n W h _ hw hh (ihc n W h ρ henv hw hh)
    intro j hj U hx hu heap v hok hv ha
    have hb := answers_sound hbool ha
    have shape : v = .tru ∨ v = .fls := by cases v <;> simp_all [tagHolds]
    rcases shape with rfl | rfl
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
          WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
          WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
        exact ihe k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @ifKnown Γ c C q t e A hc hq ht ihc iht =>
    intro n W h ρ henv hw hh
    apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC Raises.iteC
      n W h _ hw hh (ihc n W h ρ henv hw hh)
    intro j hj U hx hu heap v hok hv ha
    have hvalue := (represents_raw hq j U v) ha
    cases q <;> simp only [semWithArgs] at hvalue <;> subst v
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
          WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
          WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @ifBoolVar Γ i C T F t A e hi hb hT hF ht he iht ihe =>
    intro n W h ρ henv hw hh
    have hshape := answers_sound hb (henv.2 i C hi)
    have shape : ρ i = .tru ∨ ρ i = .fls := by
      cases hv : ρ i <;> simp_all [tagHolds]
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ k =>
      rcases shape with hv | hv
      · have refined := henv.refine hi (represents_back hT (k+1) W (ρ i) rfl (by simp [hv, semWithArgs]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ t,WExt_refl _,
          WorldAdm_trunc _ hw,.iteT,HeapOk_trunc k W h hh,?_⟩
        exact iht k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
      · have refined := henv.refine hi (represents_back hF (k+1) W (ρ i) rfl (by simp [hv, semWithArgs]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ e,WExt_refl _,
          WorldAdm_trunc _ hw,.iteF,HeapOk_trunc k W h hh,?_⟩
        exact ihe k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    intro n W h ρ henv hw hh
    have hval := (meaning_value (henv.2 i A hi)).1
    have htag := answers_heap h hq (henv.2 i A hi)
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ n =>
      cases n with
      | zero =>
        exact Or.inr ⟨trunc 0 (by omega) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
          .iteC (.testV hval), HeapOk_trunc 0 W h hh, trivial⟩
      | succ k =>
        apply ite_test_rule tag (ρ i) hval _ _ k W h hw hh
        · intro ht
          exact iht (htag.symm.trans ht) k _ h ρ
            (henv.transfer k (by omega) _ (WExt_refl _))
            (WorldAdm_trunc _ hw) (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh))
        · intro he
          exact ihe (htag.symm.trans he) k _ h ρ
            (henv.transfer k (by omega) _ (WExt_refl _))
            (WorldAdm_trunc _ hw) (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh))
  | @unionVar Γ i C t A hi ht ih =>
    intro n W h ρ henv hw hh
    obtain ⟨a, ha, hv⟩ := henv.2 i C hi
    apply ih a ha n W h ρ (henv.refine hi ?_) hw hh
    exact ⟨a, by simp, hv⟩
  | @arrParts Γ T E ro presence parts hp hparts hr ih =>
    intro n W h ρ he hw hh
    have hterm : instantiate 0 ρ (.arrLit (parts.map fun p => spreadTerm (p.1, p.2.2)))
        = .arrLit ((parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
            instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
      simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
        instantiate_spreadTerm]
      congr 1
      apply List.map_congr_left
      intro p _
      rcases p with ⟨_ | _, A, t⟩ <;> rfl
    rw [hterm]
    apply RestCalls.store_parts_safe (meaning_adm G E) (meaning_valOnly G E) _ n W h
      (by
        intro q hq S hS
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
        rcases p with ⟨_ | _, A, t⟩
        · simp at hS
        · simp only [if_true, Option.some.injEq] at hS
          subst hS
          have := hparts _ hp'
          simp only [if_true] at this
          exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
      hw hh
      (by
        intro q hq j hj U hxU hu heap hok
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
        rcases p with ⟨_ | _, A, t⟩
        · have hA : A = E := by simpa using hparts _ hp'
          subst hA
          exact ih _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · exact ih _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok)
    intro j _ U _ hu heap extra hok hex
    apply Safe_mono j _ U heap _
      (fresh_store_safe ro presence (meaning_adm G E) (meaning_valOnly G E) hu hok hex)
    intro k _ V v hv
    exact (represents_back hr k V v) ⟨by simpa [tupleFams] using hv, by simp⟩
  | @callPacked effect Γ f r a F Rt A B P xs t hf hmem htP hrt hx ha hpk hplain ihf ihrt ihx iha =>
    intro n W h ρ he hw hh
    have hfF : Safe (excOf G) (restsT (excOf G) [(meaning G Rt, (xs.map Prod.fst).map (meaning G), argMeaning G P,
        meaning G B)]) n W h (instantiate 0 ρ f) :=
      Safe_mono n (fun m _ U v hv => CallEffects.restsT_erase (by simpa [RestArrow.mapWith, Contract.map] using hplain)
        (restsT_of_restSigs hmem hv)) W h _ (ihf n W h ρ he hw hh)
    have hterm : instantiate 0 ρ (.invoke f r (xs.map Prod.snd ++
          [.spread (.readAt CallArguments.arrayStoreField a)])) =
        .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
          ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
            [.spread (.readAt CallArguments.arrayStoreField (instantiate 0 ρ a))]) := by
      simp [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    rw [hterm]
    apply packed_call_safe (Rc := meaning G Rt) (Ps := (xs.map Prod.fst).map (meaning G))
      (R := meaning G B) (V := meaning G A) (P := argMeaning G P)
      (meaning_adm G Rt)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      (argMeaning_adm G P)
      (fun n W vs hvs v hv => ((graphArguments_valid G G.env _ (fun S => meaning_valueFam G S) P).2
        n W vs hvs v hv).1)
      (fun n W v hv => Packable_mono (fun m U vs ⟨i, hi, h'⟩ => ⟨i, by
        rw [List.mem_singleton] at hi; subst hi; exact htP, h'⟩) (packedBy_sound hpk hv))
      _ (by simp [List.map_map, Function.comp_def]) hw hh hfF
    · intro j hj U hxU hu heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
    · intro q hq j hj U hxU hu heap hok
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
      exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
    · intro j hj U hxU hu heap hok
      exact iha j U heap ρ (he.transfer j hj U hxU) hu hok
  | @callRest effect Γ f r F Rt xs Us P B parts hf hmem hrt hx hu hshort hp hparts hplain
      ihf ihrt ihx ihu ihp =>
    intro n W h ρ he hw hh
    have hfF : Safe (excOf G) (restsT (excOf G) [(meaning G Rt, (xs.map Prod.fst ++ Us).map (meaning G), argMeaning G P,
        meaning G B)]) n W h (instantiate 0 ρ f) :=
      Safe_mono n (fun m _ U v hv => CallEffects.restsT_erase (by simpa [RestArrow.mapWith, Contract.map] using hplain)
        (restsT_of_restSigs hmem hv)) W h _ (ihf n W h ρ he hw hh)
    unfold RestParts at hparts
    split at hparts
    · -- A spread: the rest is an element rest.
      rename_i hany
      split at hparts
      · rename_i E hel
        have hUs : Us = [] := by
          rcases hshort with h | h
          · exact h
          · subst h; simp at hany
        subst hUs
        have hterm : instantiate 0 ρ (.invoke f r
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
              ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
              (parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
                instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p _
          rcases p with ⟨_ | _, A, t⟩ <;> rfl
        have hpart : ∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E :=
          fun p hp' => hparts (p.1, p.2.1) (List.mem_map_of_mem hp')
        rw [hterm]
        apply rest_call_safe (Rc := meaning G Rt) (Ps := xs.map fun p => meaning G p.1)
          (E := meaning G E) (P := argMeaning G P) (R := meaning G B)
          (meaning_adm G Rt)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q.1)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q.1)
          (meaning_adm G E) (meaning_valOnly G E) (argMeaning_adm G P)
          (fun k W xs hxs => (restElem_args hel).mpr hxs)
          _ (by simp [List.map_map, Function.comp_def]) _
          (by
            intro q hq S hS
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
            rcases p with ⟨_ | _, A, t⟩
            · simp at hS
            · simp only [if_true, Option.some.injEq] at hS
              subst hS
              have := hpart _ hp'
              simp only [if_true] at this
              exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
          hw hh (by simpa [List.map_map, Function.comp_def] using hfF)
        · intro j hj U hxU hu heap hok
          exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          rcases p with ⟨_ | _, A, t⟩
          · have hA : A = E := by simpa using hpart _ hp'
            subst hA
            exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
    · -- No spread: the parts are at the positions of the rest's tuple contract.
      rename_i hany
      split at hparts
      · rename_i T hPT
        obtain ⟨hreq, hbound, hpos⟩ := hparts
        simp only [List.any_map, List.any_eq_true, not_exists, not_and, Function.comp_def,
          Bool.not_eq_true] at hany
        have hterm : instantiate 0 ρ (.invoke f r
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
              ((xs.map (fun p => (meaning G p.1, instantiate 0 ρ p.2)) ++
                parts.map (fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))).map Prod.snd) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p hp'
          simp [spreadTerm, hany p hp']
        rw [hterm]
        apply pack_call_safe (Rc := meaning G Rt) (Ps := xs.map fun p => meaning G p.1)
          (Us := Us.map (meaning G)) (Qs := parts.map fun p => meaning G p.2.1)
          (P := argMeaning G P) (R := meaning G B)
          (meaning_adm G Rt)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_adm G _)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_valOnly G _)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
          (fun k W extra ha => restParts_pack hPT (Qs := parts.map (·.2.1))
            (by simpa using hreq) (by simpa using hbound)
            (by
              intro i hi
              have := hpos i (by simpa using hi)
              simpa [List.getElem?_map, Option.map_map, Function.comp_def] using this)
            (by simpa [List.map_map, Function.comp_def] using ha))
          _ (by simp [List.map_map, Function.comp_def])
          (by rcases hshort with h | h <;> simp [h])
          hw hh (by simpa [List.map_map, Function.comp_def] using hfF)
        · intro j hj U hxU hu heap hok
          exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          rcases List.mem_append.mp hq with hq | hq <;> obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          · exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro A hA j hj U hxU hu' heap hok
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
          exact ihu q hq j U heap ρ (he.transfer j hj U hxU) hu' hok
      · exact hparts.elim
  | @bindE Γ F T Rt t r saved Ps L ht hr hpre hne hL hF =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ m =>
      have hpv := ArgsT_slots he hpre
      apply make_empty_rule (meaning_adm G F) (m + 1) W h _ hw hh
      intro oid
      have hone : ∀ a ∈ L, CallEffects.callsT (excOf G) [a.map (meaning G)] (m + 1) W
          (.objAt [] (.bound (ρ t) (ρ r) (saved.map ρ)) oid) := by
        intro a ha
        obtain ⟨⟨Rt', args, R, eff⟩, hsig, h1, h2, h3, hk, hd⟩ := hL a ha
        rcases a with ⟨Rc, Ds, Ra, ea⟩
        simp only at h1 h2 h3 hk hd
        subst h1 h2 h3 hd
        have hcall := callsT_of_callSigs hsig (he.2 t T ht)
        simp only [Arrow.map, Contract.map, List.map_append] at hcall
        have hbound := CallEffects.callsT_bound (Rc := meaning G Rc) (fs := []) (oid := oid)
          (meaning_adm G Rt') (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
          (by simpa using hk) hcall (meaning_value (he.2 r Rt' hr)).1 (he.1 r) (he.2 r Rt' hr) hpv
          (ArgsT_values (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q) hpv)
          (by intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact he.1 q)
        simpa [Arrow.map, Contract.map, List.length_map] using hbound
      obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil L hne
      have hinv := (hone a₀ ha₀).1
      exact (represents_back hF (m + 1) _ _)
        ⟨CallEffects.callsT_of_signatures hinv (by
          intro p hp
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
          exact hone a ha), hinv, by simp⟩
  | @bindRestE effect Γ F T Rt E El R Rc t r saved Ps Qs ht hsig hel hr hpre hQs hkeeps hF =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ m =>
      have hrest := restsT_of_restSigs hsig (he.2 t T ht)
      have hpv := ArgsT_slots he hpre
      subst hQs
      have hlen : (saved.map ρ).length = saved.length := List.length_map _
      have hvals := ArgsT_values (by
        intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q) hpv
      have hsplit := ArgsT_take_drop Ps.length hpv
      rw [← List.map_take, ← List.map_drop, (prefix_take_drop Ps saved.length El).1,
        (prefix_take_drop Ps saved.length El).2, List.map_replicate] at hsplit
      have hpv' : ArgsT ((Ps.map (meaning G)).take (saved.map ρ).length) (m + 1) W
          ((saved.map ρ).take (Ps.map (meaning G)).length) := by
        simpa [List.map_take, hlen] using hsplit.1
      have hext : ∀ j (hj : j ≤ m + 1) (U : WorldT j), WExt (trunc j hj W) U →
          ∀ ys, argMeaning G E j U ys →
            argMeaning G E j U ((saved.map ρ).drop (Ps.map (meaning G)).length ++ ys) := by
        intro j hj U hx ys hy
        refine mixed_restElem_append hel (fun u hu => ?_) hy
        have hu' := ArgsT_replicate_all hsplit.2 u (by simpa using hu)
        exact (meaning_adm G El).transfer hu' j hj U hx
      apply make_empty_rule (meaning_adm G F) (m + 1) W h _ hw hh
      intro oid
      have hbound := CallEffects.restsT_bound (Rc := meaning G Rc) (fs := []) (oid := oid)
        (meaning_adm G Rt) (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        (argMeaning_adm G E) (by simpa using hkeeps) hrest (meaning_value (he.2 r Rt hr)).1 (he.1 r) (he.2 r Rt hr) hpv'
        hext hvals (by intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact he.1 q)
      refine (represents_back hF (m + 1) _ _) ⟨⟨hbound.1, by simp⟩, ?_⟩
      simpa [RestArrow.mapWith, Contract.map, List.map_drop, hlen] using hbound
  | @bindMember Γ F O i k m L S hi hmo hF hL hS hR =>
    intro n W h ρ he hw hh
    obtain ⟨hkey, hmem⟩ := memberOf_at hmo (he.2 i O hi)
    have hscope : Scoped 0 (ρ i) := he.1 i
    have hvalρ : isVal (ρ i) = true := (meaning_value (he.2 i O hi)).1
    have hterm : instantiate 0 ρ
        (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) =
        .letE (.readAt k (ρ i)) (.makeAt (.bound (.var 0) (ρ i) []) [] []) := by
      simp [instantiate, instantiateArgs_eq_map]
    rw [hterm]
    have hread : Safe (excOf G) (MethodMembers.onHost (excOf G) (ρ i) (MethodMembers.Member.of (meaning G) (argMeaning G) m))
        n W h (.readAt k (ρ i)) := by
      have := member_read_safe hw hh hmem
      rwa [show (MethodMembers.Member.of (meaning G) (argMeaning G) m).key = k from hkey] at this
    apply bind (fun a => Tm.letE a (.makeAt (.bound (.var 0) (ρ i) []) [] [])) Step.letC Raises.letC
      n W h _ hw hh hread
    intro j hj U hx hu h' u hok hval hon
    cases j with
    | zero => trivial
    | succ p =>
      apply let_rule _ u hval p U h' hu hok
      have hsub : subst 0 u (.makeAt (.bound (.var 0) (ρ i) []) [] []) =
          .makeAt (.bound u (ρ i) []) [] [] := by
        simp [subst, substArgs_eq_map, subst_above hscope (Nat.zero_le 0)]
      rw [hsub]
      cases p with
      | zero => trivial
      | succ q =>
        -- The host is in each type the member's host must meet.
        have hO : meaning G O (q + 2) U (ρ i) :=
          (meaning_adm G O).mono _ _ _ hx _ ((meaning_adm G O).down_le n (q + 2) hj W _ (he.2 i O hi))
        have hhost : MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)) (q + 2) U (ρ i) := by
          refine ⟨rfl, fun T hT => ?_⟩
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hT
          obtain ⟨pr, hpr⟩ := hR t ht
          exact PositiveCertificates.acceptedUsing hpr _ U _ hO
        have hRadm : Adm (MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G))) :=
          MethodMembers.hostIn_adm _ fun A hA => by
            obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b
        apply make_empty_rule (meaning_adm G F) (q + 1) _ h' _ (WorldAdm_trunc _ hu)
          (HeapOk_trunc (q + 1) U h' hok)
        intro oid
        refine (meaning_adm G F).down_le (q + 2) (q + 1) (by omega) U _ ?_
        have hinv : Invocable (.objAt [] (.bound u (ρ i) []) oid) :=
          ⟨[], _, _, rfl, rfl, by simp only [Scoped, scopedArgs_iff]; exact ⟨hon.1.1.scoped, hscope, by simp⟩⟩
        have hcalls : CallEffects.callsT (excOf G) (L.map (Arrow.map (meaning G)))
            (q + 2) U (.objAt [] (.bound u (ρ i) []) oid) := by
          refine CallEffects.callsT_of_signatures hinv fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨c, hc, hlen, hps, ⟨pr, hpr⟩, heff⟩ := hL y hy
          have hc' := CallEffects.callsT_select hon.1 (List.mem_map_of_mem (List.mem_map_of_mem hc))
          have hle := CoveredCallUsing.params hlen hps
          have ht : CallEffects.callsT (excOf G) [⟨MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)), y.arguments.map (meaning G), meaning G y.result, c.effect⟩]
              (q + 2) U u :=
            ⟨hc'.1, fun p hp => by
              cases List.mem_singleton.mp hp
              exact (hc'.2 _ (List.mem_singleton_self _)).weaken (Effect.Covers.refl _) (fun _ _ _ r h => h)
                (fun _ _ _ args ha => ArgsShort_mono hle ha)
                (fun m _ V w hw => PositiveCertificates.acceptedUsing hpr m V w hw)⟩
          have hb := CallEffects.callsT_bound (Ps := []) (pre := []) (oid := oid) (fs := [])
            (Rc := meaning G y.receiver) hRadm (by simp)
            (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b)
            (Effect.keeps_zero _) ht hvalρ hscope hhost trivial (by simp [CallArguments.Values]) (by simp)
          refine ⟨hb.1, fun p hp => ?_⟩
          cases List.mem_singleton.mp hp
          exact (hb.2 _ (List.mem_singleton_self _)).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
            (fun _ _ _ args ha => by simpa [Arrow.map, Contract.map] using ha) (fun _ _ _ w hw => hw)
        have hrests : CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) (q + 2) U (.objAt [] (.bound u (ρ i) []) oid) := by
          refine CallEffects.restsT_of_signatures hinv fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨c, hc, hlen, hps, ⟨pe, hpe⟩, ⟨pr, hpr⟩, heff⟩ := hS y hy
          have hc' := CallEffects.restsT_select hon.2.1 (List.mem_map_of_mem (List.mem_map_of_mem hc))
          have hle := CoveredCallUsing.params hlen hps
          have ht : CallEffects.restsT (excOf G) [⟨MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)), (y.arguments.1.map (meaning G), argMeaning G y.arguments.2),
              meaning G y.result, c.effect⟩] (q + 2) U u :=
            ⟨hc'.1, fun p hp => by
              cases List.mem_singleton.mp hp
              exact (hc'.2 _ (List.mem_singleton_self _)).weaken (Effect.Covers.refl _) (fun _ _ _ r h => h)
                (fun _ _ _ args ha => ArgsRest_mono hle (fun vs hv => argsAcceptedUsing hpe _ _ vs hv) ha)
                (fun m _ V w hw => PositiveCertificates.acceptedUsing hpr m V w hw)⟩
          have hb := CallEffects.restsT_bound (Rc := meaning G y.receiver) (pre := []) (fs := []) (oid := oid)
            hRadm
            (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b)
            (argMeaning_adm G _) (Effect.keeps_zero _)
            (show CallEffects.restsT (excOf G) [⟨MethodMembers.hostIn (ρ i) (m.receivers.map (meaning G)), (y.arguments.1.map (meaning G), argMeaning G y.arguments.2),
              meaning G y.result, c.effect⟩] (q + 2) U u from ht)
            hvalρ hscope hhost (by simp only [List.take_nil, List.take_zero, List.length_nil]; exact trivial)
            (fun _ _ _ _ ys hys => by simpa using hys)
            (by simp [CallArguments.Values]) (by simp)
          refine ⟨hb.1, fun p hp => ?_⟩
          cases List.mem_singleton.mp hp
          exact ((by simpa using hb.2 _ (List.mem_singleton_self _)) :
            PromiseWith (excOf G) (c.effect.drop 0) (ArgsRest (y.arguments.1.map (meaning G)) (argMeaning G y.arguments.2))
              (meaning G y.receiver) (meaning G y.result) (q + 2) U _).weaken
            (Effect.covers_sound heff) (fun _ _ _ r h => h) (fun _ _ _ args ha => ha) (fun _ _ _ w hw => hw)
        exact represents_back hF (q + 2) U _ rfl ⟨hcalls, hrests⟩
  | @bindScheme Γ F O i k m hi hmo hF _ =>
    intro n W h ρ he hw hh
    obtain ⟨hkey, hmem⟩ := memberOf_at hmo (he.2 i O hi)
    have hscope : Scoped 0 (ρ i) := he.1 i
    have hterm : instantiate 0 ρ
        (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) =
        .letE (.readAt k (ρ i)) (.makeAt (.bound (.var 0) (ρ i) []) [] []) := by
      simp [instantiate, instantiateArgs_eq_map]
    rw [hterm]
    have hread : Safe (excOf G) (MethodMembers.onHost (excOf G) (ρ i) (MethodMembers.Member.of (meaning G) (argMeaning G) m))
        n W h (.readAt k (ρ i)) := by
      have := member_read_safe hw hh hmem
      rwa [show (MethodMembers.Member.of (meaning G) (argMeaning G) m).key = k from hkey] at this
    apply bind (fun a => Tm.letE a (.makeAt (.bound (.var 0) (ρ i) []) [] [])) Step.letC Raises.letC
      n W h _ hw hh hread
    intro j hj U hx hu h' u hok hval hon
    cases j with
    | zero => trivial
    | succ p =>
      apply let_rule _ u hval p U h' hu hok
      have hsub : subst 0 u (.makeAt (.bound (.var 0) (ρ i) []) [] []) =
          .makeAt (.bound u (ρ i) []) [] [] := by
        simp [subst, substArgs_eq_map, subst_above hscope (Nat.zero_le 0)]
      rw [hsub]
      cases p with
      | zero => trivial
      | succ q =>
        -- The member bound to its host meets each of its schemes.
        apply make_empty_rule (meaning_adm G F) (q + 1) _ h' _ (WorldAdm_trunc _ hu)
          (HeapOk_trunc (q + 1) U h' hok)
        intro oid
        exact (meaning_adm G F).down_le (q + 2) (q + 1) (by omega) U _
          (hon.2.2 oid _ (List.mem_map_of_mem hF))
  | throw hA ha iha =>
    intro n W h ρ he hw hh
    apply bind Tm.throw Step.throwC Raises.throwC n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact thrown_safe _ _ _ _ ⟨v, .throwV hv (hA.sound ha'), (meaning_value ha').2, hA.exc ha'⟩
  | sub ht hc ih =>
    intro n W h ρ he hw hh
    exact Safe_mono n (fun k _ V v hv => subtyping.sound hc k V v hv)
      W h _ (ih n W h ρ he hw hh)

end Verification.ProgramTyping
