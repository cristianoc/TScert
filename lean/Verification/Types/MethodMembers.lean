import Verification.Types.ReferenceConjunctions
import Verification.Semantics.CallEffects

/-! # Host-relative method members

A method member's contract is relative to its host: reading the member from
an object and invoking it **with that object as receiver** behaves as typed.
It promises nothing for another receiver, so a member's signatures carry no
receiver. A member may state types its host must meet (TypeScript's
`this: T` on a method): then it promises its signatures only when the host
is in each of them. This is self-application, as in Abadi and Cardelli's object
calculus, and exactly the shape method-call syntax lowers to: read the member
from the saved object, then invoke it with that object.

A member is at a location of its host whose contract implies, below the
level and in every world extending the current one, the member's signatures
with the host as the one receiver. The host is fixed when the member is read;
every field keeps its location contract, so the pair (value read, host) keeps
its contract as the world grows.

A generic method's signatures are quantified: they hold at every
instantiation of the method's binders. Such a member states them as a
**scheme**, a family of callables meeting the signatures at every instance,
which the member bound to its host meets: the forwarding function `.bind`
makes of the value read and the host, whatever receiver it is later given.
That is the same host-relative promise, read through binding, so a scheme's
own receivers are the forwarding function's and say nothing of the host. -/
namespace Verification.MethodMembers
open CallEffects

/-- One member: its key, its fixed signatures `(parameters, result)` and its
variadic ones `(parameters, rest, result)`, none with a receiver, its
quantified signatures: families the member bound to its host meets, and the
families its host must be in for its fixed and variadic signatures to hold. -/
structure Member where
  key : PropKey
  calls : List (MethodArrow Fam)
  rests : List (Contract Unit (List Fam × ArgFam) Fam)
  schemes : List Fam := []
  receivers : List Fam := []

/-- The host as the one receiver a member admits, when it is in each of
`Rs`. -/
def hostIn (v : Val) (Rs : List Fam) : Fam := fun k W r => r = v ∧ ∀ R ∈ Rs, R k W r

theorem hostIn_adm (v : Val) {Rs : List Fam} (h : ∀ R ∈ Rs, Adm R) : Adm (hostIn v Rs) :=
  ⟨fun n W r hr => ⟨hr.1, fun R hR => (h R hR).down n W r (hr.2 R hR)⟩,
    fun n W W' hx r hr => ⟨hr.1, fun R hR => (h R hR).mono n W W' hx r (hr.2 R hR)⟩⟩

/-- The forwarding function `.bind` makes of a value and a host, at the
identity its allocation gives it: invoked with any receiver, it invokes the
value with the host. -/
def boundTo (u v : Val) (oid : Nat) : Val := .objAt [] (.bound u v []) oid

/-- Values that, bound to host `v` at any identity, meet every family of `Fs`. -/
def boundOn (v : Val) (Fs : List Fam) : Fam := fun k W u =>
  ∀ oid, ∀ F ∈ Fs, F k W (boundTo u v oid)

/-- What a member promises of a value read from host `v`: its signatures, each
with receiver `v` when `v` is in each of the member's receivers, and its
quantified ones, met bound to `v`. -/
def onHost (Ξ : Fam) (v : Val) (m : Member) : Fam :=
  interT (CallEffects.callsT Ξ (m.calls.map (Contract.withReceiver (hostIn v m.receivers))))
    (interT (CallEffects.restsT Ξ (m.rests.map (Contract.withReceiver (hostIn v m.receivers))))
      (boundOn v m.schemes))

/-- `v` holds `key` at a location whose contract implies `A` below the level,
in every world extending the current one. -/
def holdsAt (key : PropKey) (A : Fam) : Fam := fun k W v =>
  ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid : Nat),
    v = .objAt flds .absent oid ∧ flds.lookup key = some l ∧ lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ (u : Val), c j hj U u → A j U u

theorem holdsAt_adm (key : PropKey) (A : Fam) : Adm (holdsAt key A) := by
  refine ⟨?_, ?_⟩
  · intro n W v h
    obtain ⟨flds, l, c, oid, hv, hf, hl, hag⟩ := h
    refine ⟨flds, l, _, oid, hv, hf, lookup_trunc (Nat.le_succ n) W l c hl, ?_⟩
    intro j hj U hx u hu
    exact hag j (by omega) U (by rwa [trunc_trunc] at hx) u hu
  · intro n W W' hx v h
    obtain ⟨flds, l, c, oid, hv, hf, hl, hag⟩ := h
    exact ⟨flds, l, c, oid, hv, hf, WExt_lookup hx hl, fun j hj U hU u hu =>
      hag j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hU) u hu⟩

/-- A weaker family below the level is held wherever a stronger one is. -/
theorem holdsAt_mono {key : PropKey} {A B : Fam} {k : Nat}
    (h : ∀ j, j < k → ∀ (U : WorldT j) u, A j U u → B j U u) {W : WorldT k} {v : Val}
    (hv : holdsAt key A k W v) : holdsAt key B k W v := by
  obtain ⟨flds, l, c, oid, hρ, hf, hl, hag⟩ := hv
  exact ⟨flds, l, c, oid, hρ, hf, hl, fun j hj U hU u hu => h j hj U u (hag j hj U hU u hu)⟩

/-- `v` holds `key` along its prototype chain, `d` prototypes up: at `d = 0`
its own location for the key, whose contract implies `A`; at `d + 1` it lacks
the key and its prototype location's contract implies the same `d` up. The
family `A` is fixed, so the host a member is read from stays the receiver
however far up its key is found. -/
def along (key : PropKey) (A : Fam) : Nat → Fam
  | 0 => holdsAt key A
  | d + 1 => fun k W v => ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid ∧
      flds.lookup key = none ∧ holdsAt CallArguments.protoField (along key A d) k W v

theorem along_adm (key : PropKey) (A : Fam) : ∀ d, Adm (along key A d)
  | 0 => holdsAt_adm key A
  | d + 1 => by
    refine ⟨?_, ?_⟩
    · rintro n W v ⟨flds, oid, hρ, hmiss, h⟩
      exact ⟨flds, oid, hρ, hmiss, (holdsAt_adm _ (along key A d)).down n W v h⟩
    · rintro n W W' hx v ⟨flds, oid, hρ, hmiss, h⟩
      exact ⟨flds, oid, hρ, hmiss, (holdsAt_adm _ (along key A d)).mono n W W' hx v h⟩

/-- A weaker family below the level is found wherever a stronger one is, the
same number of prototypes up. -/
theorem along_mono {key : PropKey} {A B : Fam} : ∀ (d : Nat) {k : Nat},
    (∀ j, j < k → ∀ (U : WorldT j) u, A j U u → B j U u) →
    ∀ {W : WorldT k} {v : Val}, along key A d k W v → along key B d k W v
  | 0, _, h, _, _, hv => holdsAt_mono h hv
  | d + 1, _, h, _, _, ⟨flds, oid, hρ, hmiss, hv⟩ =>
    ⟨flds, oid, hρ, hmiss, holdsAt_mono (fun j hj U u hu =>
      along_mono d (fun i hi U' u' => h i (by omega) U' u') hu) hv⟩

/-- **Host-relative members.** A member of `v` is where JavaScript's lookup
finds its key: at `v`'s own location for it, or, when `v` lacks the key, where
its prototype chain has it, some prototypes up (`along`). The contract found
there implies, in every world extending the current one, the member's
signatures invoked on `v`. The implication is not claimed in unrelated
worlds: there the object's own locations need not hold their contracts, and a
method reading them could not be safe. -/
def memberT (Ξ : Fam) (m : Member) : Fam := fun k W v => ∃ d, along m.key (onHost Ξ v m) d k W v

theorem memberT_adm (m : Member) : Adm (memberT Ξ m) := by
  refine ⟨?_, ?_⟩
  · rintro n W v ⟨d, h⟩
    exact ⟨d, (along_adm _ _ d).down n W v h⟩
  · rintro n W W' hx v ⟨d, h⟩
    exact ⟨d, (along_adm _ _ d).mono n W W' hx v h⟩

/-- A member whose signatures imply another's below the level, found by the
same key, is that member. -/
theorem memberT_mono {Ξ Ξ' : Fam} {m m' : Member} (hkey : m.key = m'.key) {k : Nat}
    (h : ∀ v, ∀ j, j < k → ∀ (U : WorldT j) u, onHost Ξ v m j U u → onHost Ξ' v m' j U u)
    {W : WorldT k} {v : Val} (hv : memberT Ξ m k W v) : memberT Ξ' m' k W v := by
  obtain ⟨d, hv⟩ := hv
  exact ⟨d, hkey ▸ along_mono d (h v) hv⟩

def methodT (Ξ : Fam) (ms : List Member) : Fam := fun k W v => ∀ m ∈ ms, memberT Ξ m k W v

theorem methodT_adm (ms : List Member) : Adm (methodT Ξ ms) :=
  ⟨fun n W v h m hm => (memberT_adm m).down n W v (h m hm),
    fun n W W' hx v h m hm => (memberT_adm m).mono n W W' hx v (h m hm)⟩

theorem methodT_nil (k : Nat) (W : WorldT k) (v : Val) : methodT Ξ [] k W v := by
  intro m hm
  simp at hm

theorem methodT_append (ms ns : List Member) (k : Nat) (W : WorldT k) (v : Val) :
    methodT Ξ (ms ++ ns) k W v ↔ methodT Ξ ms k W v ∧ methodT Ξ ns k W v := by
  simp only [methodT, List.mem_append, or_imp, forall_and]

/-- A member of the object, read from it. -/
theorem methodT_at {ms : List Member} {m : Member} (hm : m ∈ ms) {k} {W : WorldT k} {v}
    (h : methodT Ξ ms k W v) : memberT Ξ m k W v :=
  h m hm

/-- A member's syntax: its key, fixed signatures `(parameters, result)` and
variadic ones `(parameters, rest, result)`, its quantified signatures, each
an operand naming a scheme, and the types its host must meet; operands of any
sort. -/
structure Sig (α : Type) where
  key : PropKey
  calls : List (MethodArrow α)
  rests : List (MethodRestArrow α) := []
  schemes : List α := []
  receivers : List α := []
  deriving Repr, DecidableEq

/-- The member a signature denotes, operands read by `X` and rests by `P`. -/
def Member.of {α : Type} (X : α → Fam) (P : α → ArgFam) (m : Sig α) : Member :=
  ⟨m.key, m.calls.map (MethodArrow.map X), m.rests.map (MethodRestArrow.mapWith X P),
    m.schemes.map X, m.receivers.map X⟩

private theorem argsAgree_map {α : Type} {X Y : α → Fam} {n : Nat}
    (h : ∀ a, Agree (X a) (Y a) n) : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y)
  | [] => .nil
  | a :: As => .cons (h a) (argsAgree_map h As)

/-- A member's host-relative family depends on its operands only below the
budget, as a call clause's does. -/
theorem onHost_congr {Ξ Ξ' : Fam} {α : Type} (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat)
    (hexc : Agree Ξ Ξ' n)
    (h : ∀ a, Agree (X a) (Y a) n) (hP : ∀ a, Agree (P a) (Q a) n) (m : Sig α) (v : Val) :
    Agree (onHost Ξ v (Member.of X P m)) (onHost Ξ' v (Member.of Y Q m)) n := by
  intro j hj W u
  have hX : ∀ a, Agree (X a) (Y a) j := fun a k hk W v => h a k (by omega) W v
  have hQ : ∀ a, Agree (P a) (Q a) j := fun a k hk W v => hP a k (by omega) W v
  have hE : Agree Ξ Ξ' j := fun k hk W v => hexc k (by omega) W v
  simp only [onHost, Member.of, List.map_map, interT, Function.comp_def]
  have hR : Agree (hostIn v (m.receivers.map X)) (hostIn v (m.receivers.map Y)) j := by
    intro k hk W r
    simp only [hostIn, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact and_congr_right fun _ => forall_congr' fun a => imp_congr_right fun _ => hX a k hk W r
  exact and_congr
    (CallEffects.callsT_congr m.calls
      (fun p => Contract.withReceiver (hostIn v (m.receivers.map X)) (MethodArrow.map X p))
      (fun p => Contract.withReceiver (hostIn v (m.receivers.map Y)) (MethodArrow.map Y p)) hE (fun _ _ => rfl)
      (fun p _ => ⟨hR, argsAgree_map hX p.arguments, hX p.result⟩) W u)
    (and_congr
      (CallEffects.restsT_congr m.rests
        (fun p => Contract.withReceiver (hostIn v (m.receivers.map X)) (MethodRestArrow.mapWith X P p))
        (fun p => Contract.withReceiver (hostIn v (m.receivers.map Y)) (MethodRestArrow.mapWith Y Q p)) hE (fun _ _ => rfl)
        (fun s _ => ⟨hR, argsAgree_map hX s.arguments.1,
          hQ s.arguments.2, hX s.result⟩) W u)
      (by simp only [boundOn, List.mem_map, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          exact forall_congr' fun _ => forall_congr' fun a => imp_congr_right fun _ => h a j hj W _))

/-- Members agreeing below the budget, read at their hosts, are the same
members. -/
theorem methodT_congr {Ξ Ξ' : Fam} {α : Type} (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat)
    (hexc : Agree Ξ Ξ' n)
    (h : ∀ a, Agree (X a) (Y a) n) (hP : ∀ a, Agree (P a) (Q a) n) (ms : List (Sig α))
    (W : WorldT n) (v : Val) :
    methodT Ξ (ms.map (Member.of X P)) n W v ↔ methodT Ξ' (ms.map (Member.of Y Q)) n W v := by
  constructor
  · intro hv m hmem
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    exact memberT_mono (m := Member.of X P s) (m' := Member.of Y Q s) rfl
      (fun v j hj U u => (onHost_congr X Y P Q n hexc h hP s v j hj U u).mp)
      (hv (Member.of X P s) (List.mem_map_of_mem hs))
  · intro hv m hmem
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    exact memberT_mono (m := Member.of Y Q s) (m' := Member.of X P s) rfl
      (fun v j hj U u => (onHost_congr X Y P Q n hexc h hP s v j hj U u).mpr)
      (hv (Member.of Y Q s) (List.mem_map_of_mem hs))

/-- Rename a member signature's operands. -/
def Sig.map {α β : Type} (f : α → β) (m : Sig α) : Sig β :=
  ⟨m.key, m.calls.map (MethodArrow.map f), m.rests.map (MethodRestArrow.map f), m.schemes.map f,
    m.receivers.map f⟩

/-- Every operand of a member signature. -/
def Sig.operands {α : Type} (m : Sig α) : List α :=
  m.calls.flatMap MethodArrow.operands ++ m.rests.flatMap MethodRestArrow.operands ++
    m.schemes ++ m.receivers

/-- Renaming a signature's operands is reading them through the renaming. -/
theorem Member.of_map {α β : Type} (X : β → Fam) (P : β → ArgFam) (f : α → β) (m : Sig α) :
    Member.of X P (m.map f) = Member.of (fun a => X (f a)) (fun a => P (f a)) m := by
  simp [Member.of, Sig.map, MethodArrow.map, MethodRestArrow.map, MethodRestArrow.mapWith,
    Contract.map, Function.comp_def]

end Verification.MethodMembers
