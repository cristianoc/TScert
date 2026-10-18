import Verification.Semantics.CallArguments
import Verification.Semantics.Heaps
/-!
# Safety and function types

`Safe T n W h t` says that running `t` for `n` steps never gets stuck, and that
if it reaches a value with budget left, that value is in `T`. Throwing is an
outcome beside a value (`Thrown`): a term that throws a closed value is safe at
every type, as ML-style type soundness with exceptions has it. A type promises
what a *value* is, never that no exception is raised. Each step spends a
level and the world drops with it; the world reached after a step must extend the
truncation of the one before, and must itself be admissible.

A function type requires an object with closed invocation code whose substituted body is safe in
every *future* world and every heap satisfying
it, at every strictly smaller budget. Requiring admissibility here is what lets a
function allocate: without it, a world carrying a contract that allocation can
falsify could be supplied, and no allocating function would be safe anywhere.

The level a call spends is the level at which the argument's own guarantees are
available. That correspondence is what makes ordinary typing derivations go
through, and it is why the arrow is stated over `Safe` rather than over an
abstract relation from arguments to results.

Since safety consults a type only at the budgets it can still reach, an arrow
reads **both** of its operands strictly below the current budget. So a function
type is a guard in its result as well as its argument, and a recursion may run
through either position.
-/
namespace Verification

/-- `t` throws a closed value of the exception family `Ξ`: the outcome that
is neither a value nor a step. A graph's exception family is its builtins's
`unknown` (`PositiveGraphs.builtinExc`), so a handler binds a thrown value
there. -/
def Thrown (Ξ : Fam) (k : Nat) (W : WorldT k) (t : Tm) : Prop :=
  ∃ v, Raises t v ∧ Scoped 0 v ∧ Ξ k W v

theorem Thrown.no_step {Ξ : Fam} {k W} {t : Tm} (h : Thrown Ξ k W t) {hp hp' t'} :
    ¬ Step hp t hp' t' := by
  obtain ⟨_, hr, _⟩ := h; exact raises_no_step hr

theorem Thrown.not_val {Ξ : Fam} {k W} {t : Tm} (h : Thrown Ξ k W t) : isVal t = false := by
  obtain ⟨_, hr, _⟩ := h; exact raises_not_val hr

/-- A throw leaves every evaluation context it is in. -/
theorem Thrown.lift {Ξ : Fam} {k W} {t : Tm} {C : Tm → Tm}
    (lift : ∀ {v}, Raises t v → Raises (C t) v) (h : Thrown Ξ k W t) : Thrown Ξ k W (C t) := by
  obtain ⟨v, hr, hs⟩ := h; exact ⟨v, lift hr, hs⟩

/-- A throw is one of every wider exception family. -/
theorem Thrown.mono {Ξ Ξ' : Fam} {k W} {t : Tm} (hΞ : ∀ v, Ξ k W v → Ξ' k W v)
    (h : Thrown Ξ k W t) : Thrown Ξ' k W t := by
  obtain ⟨v, hr, hs, he⟩ := h; exact ⟨v, hr, hs, hΞ v he⟩

/-- An exception family holds the errors the host throws: an operator that
throws (`binopThrows`) throws a fresh object owning no key. -/
def ErrorsIn (Ξ : Fam) : Prop := ∀ (k : Nat) (W : WorldT k) (oid : Nat), Ξ k W (thrownError oid)

theorem val_not_thrown {Ξ : Fam} {k W} {t : Tm} (hv : isVal t = true) : ¬ Thrown Ξ k W t := by
  intro h; rw [h.not_val] at hv; contradiction

/-- Running `t` for `n` steps never gets stuck: it is a value in `T`, it
throws a value of `Ξ`, or it steps. Each step spends a level, and the world
drops with it. -/
def Safe (Ξ T : Fam) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      ((isVal t = true ∧ T (n + 1) W t) ∨ Thrown Ξ (n + 1) W t) ∨
      (∃ (W' : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) W' ∧ WorldAdm W' ∧ Step h t h' t' ∧
          HeapOk n W' h' ∧ Safe Ξ T n W' h' t')

theorem Safe_nul {Ξ : Fam} : ∀ (n : Nat) (W : WorldT n) (h : Heap), Safe Ξ nulT n W h .nul
  | 0, _, _ => trivial
  | _ + 1, _, _ => Or.inl (Or.inl ⟨rfl, rfl⟩)

/-- Safety depends on the exception family and the type only through their
behaviour at the budgets it can still reach. -/
theorem Safe_congr' {Ξ Ξ' B C : Fam} (n : Nat) (hΞ : Agree Ξ Ξ' n) (hag : Agree B C n) :
    ∀ (j : Nat), j < n → ∀ (W : WorldT j) (h : Heap) (t : Tm),
      Safe Ξ B j W h t ↔ Safe Ξ' C j W h t := by
  intro j
  induction j with
  | zero => intro _ _ _ _; exact Iff.rfl
  | succ p ih =>
    intro hj W h t
    simp only [Safe]
    constructor <;> rintro ((⟨hv, hB⟩ | hr) | ⟨W', h', t', hx, ha, hs, hok, hsafe⟩)
    · exact Or.inl (Or.inl ⟨hv, (hag (p + 1) hj W t).mp hB⟩)
    · exact Or.inl (Or.inr (hr.mono fun v => (hΞ (p + 1) hj W v).mp))
    · exact Or.inr ⟨W', h', t', hx, ha, hs, hok, (ih (by omega) W' h' t').mp hsafe⟩
    · exact Or.inl (Or.inl ⟨hv, (hag (p + 1) hj W t).mpr hB⟩)
    · exact Or.inl (Or.inr (hr.mono fun v => (hΞ (p + 1) hj W v).mpr))
    · exact Or.inr ⟨W', h', t', hx, ha, hs, hok, (ih (by omega) W' h' t').mpr hsafe⟩

/-- Safety is monotone in the exception family and the type, at every budget
it can still reach. -/
theorem Safe_mono' {Ξ Ξ' B C : Fam} : ∀ (j : Nat),
    (∀ m, m ≤ j → ∀ (W : WorldT m) (v : Val), Ξ m W v → Ξ' m W v) →
    (∀ m, m ≤ j → ∀ (W : WorldT m) (v : Val), B m W v → C m W v) →
    ∀ (W : WorldT j) (h : Heap) (t : Tm), Safe Ξ B j W h t → Safe Ξ' C j W h t := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _ _; trivial
  | succ p ih =>
    intro hΞ hbc W h t hs
    rcases hs with (⟨hv, hB⟩ | hr) | ⟨W', h', t', hx, ha, hst, hok, hsafe⟩
    · exact Or.inl (Or.inl ⟨hv, hbc (p + 1) (Nat.le_refl _) W t hB⟩)
    · exact Or.inl (Or.inr (hr.mono (hΞ (p + 1) (Nat.le_refl _) W)))
    · exact Or.inr ⟨W', h', t', hx, ha, hst, hok,
        ih (fun m hm => hΞ m (by omega)) (fun m hm => hbc m (by omega)) W' h' t' hsafe⟩

/-- Safety is monotone in the type, at every budget it can still reach. -/
theorem Safe_mono {Ξ B C : Fam} (j : Nat)
    (hbc : ∀ m, m ≤ j → ∀ (W : WorldT m) (v : Val), B m W v → C m W v)
    (W : WorldT j) (h : Heap) (t : Tm) (hs : Safe Ξ B j W h t) : Safe Ξ C j W h t :=
  Safe_mono' j (fun _ _ _ _ h => h) hbc W h t hs

/-! ## Comparing two runs of one program

Two obligations discharged at the same world and heap are two runs of the *same*
program, so determinism makes them take the same steps. What they force about
the value it may return is then whatever both judgments force at the first
world — and no more, since the worlds diverge as soon as anything is allocated.
The subtype rules use a conservative syntactic sufficient condition for this
property. No decision procedure for exact cross-world compatibility is assumed. -/

def CrossCompatUpTo (n : Nat) (B C D : Fam) : Prop :=
  ∀ (j : Nat), j ≤ n → ∀ (W W' : WorldT j) (h : Heap), HeapOk j W h → HeapOk j W' h →
    ∀ (u : Val), B j W u → C j W' u → D j W u

/-- Ordered actual-argument contracts. The signature fixes the actual count;
the code's declared parameter count is independent. -/
def ArgsT : List Fam → (k : Nat) → WorldT k → List Tm → Prop
  | [], _, _, [] => True
  | A :: As, k, W, a :: args => A k W a ∧ ArgsT As k W args
  | _, _, _, _ => False

/-- An actual is at its position's contract. -/
theorem ArgsT_getElem? : ∀ {As : List Fam} {k : Nat} {W : WorldT k} {args : List Tm} {i : Nat}
    {A : Fam} {a : Tm}, ArgsT As k W args → As[i]? = some A → args[i]? = some a → A k W a
  | [], _, _, _, _, _, _, _, hA, _ => by simp at hA
  | _ :: _, _, _, [], _, _, _, h, _, _ => h.elim
  | _ :: _, _, _, _ :: _, 0, _, _, h, hA, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA ha
    subst hA; subst ha; exact h.1
  | _ :: _, _, _, _ :: _, i + 1, _, _, h, hA, ha => by
    simp only [List.getElem?_cons_succ] at hA ha
    exact ArgsT_getElem? h.2 hA ha

/-- Actuals at their positions' contracts, as many as the positions, are
admitted position by position. -/
theorem ArgsT_of_getElem? : ∀ {As : List Fam} {k : Nat} {W : WorldT k} {args : List Tm},
    As.length = args.length →
    (∀ (i : Nat) (A : Fam) (a : Tm), As[i]? = some A → args[i]? = some a → A k W a) →
    ArgsT As k W args
  | [], _, _, [], _, _ => trivial
  | [], _, _, _ :: _, hl, _ => by simp at hl
  | _ :: _, _, _, [], hl, _ => by simp at hl
  | A :: As, _, _, a :: args, hl, h =>
    ⟨h 0 A a rfl rfl, ArgsT_of_getElem? (by simpa using hl) fun i B b hB hb => h (i + 1) B b hB hb⟩

/-- Every position of an admitted list holds an actual: a list with an empty
position admits no list. -/
theorem ArgsT_mem : ∀ {As : List Fam} {k : Nat} {W : WorldT k} {args : List Tm} {A : Fam},
    ArgsT As k W args → A ∈ As → ∃ a, A k W a
  | [], _, _, _, _, _, hA => by simp at hA
  | _ :: _, _, _, [], _, h, _ => h.elim
  | B :: As, k, W, a :: args, A, h, hA => by
    rcases List.mem_cons.mp hA with rfl | hA
    · exact ⟨a, h.1⟩
    · exact ArgsT_mem h.2 hA

theorem ArgsT_length {As k W args} (h : ArgsT As k W args) :
    args.length = As.length := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args => exact congrArg Nat.succ (ih h.2)

theorem ArgsT_append {As Bs : List Fam} {k W args brgs}
    (h : ArgsT As k W args) (h' : ArgsT Bs k W brgs) :
    ArgsT (As ++ Bs) k W (args ++ brgs) := by
  induction As generalizing args with
  | nil => cases args with
    | nil => exact h'
    | cons a args => exact False.elim h
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args => exact ⟨h.1, ih h.2⟩

/-- Contracts that admit `undefined` are satisfied by the slots a short call
leaves for the machine to pad. -/
theorem ArgsT_undef {Us : List Fam} {k W} (h : ∀ A ∈ Us, A k W .undef) :
    ArgsT Us k W (List.replicate Us.length .undef) := by
  induction Us with
  | nil => trivial
  | cons A Us ih =>
    exact ⟨h A (by simp), ih fun B hB => h B (by simp [hB])⟩

/-- Argument membership is covariant pointwise. This is the list-shaped
premise used by callable subtyping: an implementation accepting `Bs` can be
used where callers supply the narrower `As` when every `A ≤ B`. -/
inductive ArgsLe : List Fam → List Fam → Prop where
  | nil : ArgsLe [] []
  | cons : FamLe A B → ArgsLe As Bs → ArgsLe (A :: As) (B :: Bs)

theorem ArgsT_mono {As Bs : List Fam} (h : ArgsLe As Bs) {k W args}
    (ha : ArgsT As k W args) : ArgsT Bs k W args := by
  induction h generalizing args with
  | nil =>
    cases args <;> exact ha
  | cons hab _ ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args => exact ⟨hab k W a ha.1, ih ha.2⟩

/-- Position by position, which is what an allocation needs. -/
theorem ArgsT_zip {As k W args} (h : ArgsT As k W args) :
    ∀ p ∈ As.zip args, p.1 k W p.2 := by
  induction As generalizing args with
  | nil =>
    cases args <;> simp_all [ArgsT]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args =>
      intro p hp
      rw [List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h.1
      · exact ih h.2 p hp

/-- Typed actuals are ready for binding when their domains contain only values. -/
theorem ArgsT_values {As k W args} (hA : ∀ A ∈ As, ValOnly A)
    (h : ArgsT As k W args) : CallArguments.Values args := by
  induction As generalizing args with
  | nil =>
    cases args with
    | nil => intro a ha; cases ha
    | cons a args => exact False.elim h
  | cons A As ih =>
    cases args with
    | nil => exact False.elim h
    | cons a args =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hA A (by simp) k W _ h.1
      · exact ih (fun B hb => hA B (List.mem_cons_of_mem A hb)) h.2 v hv

/-- Saved actual values retain their domains as evaluation spends budget and
extends the heap world. No argument is re-evaluated during this transfer. -/
theorem ArgsT_transfer {As n W args} (hA : ∀ A ∈ As, Adm A)
    (ha : ArgsT As n W args) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : ArgsT As j U args := by
  induction As generalizing args with
  | nil => cases args <;> exact ha
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args =>
      have hadm := hA A (by simp)
      exact ⟨hadm.mono j _ U hx a (hadm.down_le n j hj W a ha.1),
        ih (fun B hb => hA B (List.mem_cons_of_mem A hb)) ha.2⟩

inductive ArgsAgree (n : Nat) : List Fam → List Fam → Prop where
  | nil : ArgsAgree n [] []
  | cons : Agree A B n → ArgsAgree n As Bs → ArgsAgree n (A :: As) (B :: Bs)

/-- Agreement follows argument positions, including the actual-list length. -/
theorem ArgsT_congr {As Bs : List Fam} {n : Nat}
    (h : ArgsAgree n As Bs)
    {j : Nat} (hj : j < n) (W : WorldT j) (args : List Tm) :
    ArgsT As j W args ↔ ArgsT Bs j W args := by
  induction h generalizing args with
  | nil => rfl
  | cons hd ht ih =>
    cases args with
    | nil => rfl
    | cons a args => exact and_congr (hd j hj W a) (ih args)

theorem value_safe (B : Fam) (n : Nat) (U : WorldT n) (h : Heap) (v : Val)
    (hv : isVal v = true) (hb : B n U v) : Safe Ξ B n U h v := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl (Or.inl ⟨hv, hb⟩)

/-- A term that throws a closed value is safe at every type. -/
theorem thrown_safe (B : Fam) (n : Nat) (U : WorldT n) (h : Heap) {t : Tm}
    (ht : Thrown Ξ n U t) : Safe Ξ B n U h t := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl (Or.inr ht)

theorem safe_value_mem {B : Fam} {n : Nat} {U : WorldT (n+1)} {h : Heap} {v : Val}
    (hv : isVal v = true) (hs : Safe Ξ B (n+1) U h v) : B (n+1) U v := by
  rcases hs with (⟨_, hb⟩ | hr) | ⟨_, _, _, _, _, hs, _, _⟩
  · exact hb
  · rw [hr.not_val] at hv; contradiction
  · exact False.elim (value_no_step hv hs)

/-! ## Call contracts

A function type says which actual lists a caller may write and what the call
then guarantees; it does not say how the callee binds them. Padding an omitted
parameter, collecting a rest array or dropping an extra actual is the code's
business, proved once where the code is created (`ProgramTyping.callsT_of_graph`,
`restsT_of_graph` and `restsT_of_graphRest`). So a variadic value can
meet a fixed signature, and one value can carry fixed and variadic signatures
at once. -/

/-- Values with invocation code: closed objects whose descriptor is not absent. -/
def Invocable (v : Val) : Prop :=
  ∃ fs code oid, v = .objAt fs code oid ∧ code.callable = true ∧ Scoped 0 v

theorem Invocable.val {v : Val} (h : Invocable v) : isVal v = true := by
  obtain ⟨fs, code, oid, rfl, -, -⟩ := h; rfl

theorem Invocable.scoped {v : Val} (h : Invocable v) : Scoped 0 v := by
  obtain ⟨fs, code, oid, rfl, -, hs⟩ := h; exact hs

/-- The actual lists a fixed signature admits: a prefix of its positions, each
written at its contract, every omitted position admitting `undefined`. -/
def ArgsShort (Ps : List Fam) (j : Nat) (W : WorldT j) (args : List Tm) : Prop :=
  args.length ≤ Ps.length ∧ ArgsT (Ps.take args.length) j W args ∧
    ∀ A ∈ Ps.drop args.length, A j W .undef

/-- The actual lists a variadic signature admits: its fixed parameters admit
the first actuals, as a fixed signature's do, and the actuals past them, as
one argument list, are at the rest contract. -/
def ArgsRest (Ps : List Fam) (E : ArgFam) (j : Nat) (W : WorldT j) (args : List Tm) : Prop :=
  ArgsShort Ps j W (args.take Ps.length) ∧ E j W (args.drop Ps.length)

/-- A promise: every receiver value at `Rc` with every admitted list of values
invokes the value, at every future world and satisfying heap below the budget,
safely at `R`. The receiver is not an actual: `Acc` never sees it. -/
def Promise (Ξ : Fam) (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc R : Fam)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → ∀ r, isVal r = true → Rc j U r →
      ∀ args, CallArguments.Values args →
      Acc j U args → ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧ Safe Ξ R j U heap result

theorem Promise.down {Acc Rc R n W v} (h : Promise Ξ Acc Rc R (n + 1) W v) :
    Promise Ξ Acc Rc R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hrv hr args hv ha

theorem Promise.mono {Acc Rc R n W W' v} (hx : WExt W W') (h : Promise Ξ Acc Rc R n W v) :
    Promise Ξ Acc Rc R n W' v := by
  intro j hj U hy hu heap hh r hrv hr args hv ha
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hrv hr args hv ha

/-- Values meeting every fixed signature `(receiver, parameters, result)`:
each receiver at its contract with each admitted actual list, including one
omitting trailing positions that admit `undefined`. -/
def callsT (Ξ : Fam) (L : List (Fam × List Fam × Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ p ∈ L, Promise Ξ (ArgsShort p.2.1) p.1 p.2.2 k W v

/-- Values meeting every variadic signature `(receiver, fixed parameters,
element, result)`: the contract of each further actual is the element's. -/
def restsT (Ξ : Fam) (S : List (Fam × List Fam × ArgFam × Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ S, Promise Ξ (ArgsRest s.2.1 s.2.2.1) s.1 s.2.2.2 k W v

/-! ### Construct signatures -/

/-- A class value: a closed object whose code is construct-only. Every
function value is one of these or `Invocable`, which is what `typeof` calls a
function; a construct signature additionally needs `new` to run it
(`ConstructsTo`). -/
def Constructible (v : Val) : Prop :=
  ∃ fs n E K s caps rest oid, v = .objAt fs (.graph n E K s caps .construct rest) oid ∧ Scoped 0 v

/-- What `new v(args)` runs, in one step: a class value's body, with
`undefined` for its receiver and the actuals for its parameters. -/
def ConstructsTo (v : Val) (args : List Tm) (result : Tm) : Prop :=
  ∃ fs c enter oid, v = .objAt fs c oid ∧ CallArguments.construction v c = some enter ∧ result = enter args

/-- The actual lists a variadic construct signature admits: its fixed
parameters' actuals exactly, then, as one argument pack, the rest. -/
def CtorRest (Ps : List Fam) (P : ArgFam) (j : Nat) (W : WorldT j) (args : List Tm) : Prop :=
  Ps.length ≤ args.length ∧ ArgsT Ps j W (args.take Ps.length) ∧
    P j W (args.drop Ps.length)

/-! ### Argument packs -/

/-- Tuple shape and position membership, independent of approximation policy:
the interpretation of an element is supplied. -/
def TupleFits (member : Fam → Val → Prop) (T : TupleF) (vs : List Val) : Prop :=
  T.required.length ≤ vs.length ∧
    (T.rest = none → vs.length ≤ T.required.length + T.optional.length) ∧
    ∀ i v A, vs[i]? = some v → positionFam T i = some A → member A v

theorem TupleFits.map {P Q : Fam → Val → Prop} {T : TupleF} {vs : List Val}
    (h : TupleFits P T vs) (hm : ∀ i A, positionFam T i = some A →
      ∀ v, P A v → Q A v) : TupleFits Q T vs :=
  ⟨h.1, h.2.1, fun i v A hv hA => hm i A hA v (h.2.2 i v A hv hA)⟩

/-- Equal shapes with equivalent position predicates admit the same lists.
-/
theorem TupleFits.congr {P Q : Fam → Val → Prop} {T T' : TupleF} {vs}
    (hreq : T.required.length = T'.required.length) (hopt : T.optional.length = T'.optional.length)
    (hrest : T.rest = none ↔ T'.rest = none)
    (hpos : ∀ i, (positionFam T i = none ↔ positionFam T' i = none) ∧
      ∀ A B, positionFam T i = some A → positionFam T' i = some B → ∀ v, P A v ↔ Q B v) :
    TupleFits P T vs ↔ TupleFits Q T' vs := by
  unfold TupleFits
  rw [hreq, hopt, hrest]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h i u B hu hB => ?_,
    fun h i u A hu hA => ?_⟩)
  · cases hA : positionFam T i with
    | none => rw [(hpos i).1.mp hA] at hB; cases hB
    | some A => exact ((hpos i).2 A B hA hB u).mp (h i u A hu hA)
  · cases hB : positionFam T' i with
    | none => rw [(hpos i).1.mpr hB] at hA; cases hA
    | some B => exact ((hpos i).2 A B hA hB u).mpr (h i u B hu hB)

theorem callsT_adm (L : List (Fam × List Fam × Fam)) : Adm (callsT Ξ L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

theorem restsT_adm (S : List (Fam × List Fam × ArgFam × Fam)) : Adm (restsT Ξ S) :=
  ⟨fun _ _ _ h => ⟨h.1, fun p hp => (h.2 p hp).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun p hp => (h.2 p hp).mono hx⟩⟩

/-! ### Admitted lists -/

theorem ArgsT_take_drop {Ps : List Fam} {j W} : ∀ {args : List Tm} (m : Nat),
    ArgsT Ps j W args → ArgsT (Ps.take m) j W (args.take m) ∧ ArgsT (Ps.drop m) j W (args.drop m) := by
  induction Ps with
  | nil => intro args m h; cases args <;> cases m <;> simp_all [ArgsT]
  | cons A Ps ih =>
    intro args m h
    cases args with
    | nil => exact False.elim h
    | cons a args =>
      cases m with
      | zero => exact ⟨trivial, h⟩
      | succ m => exact ⟨⟨h.1, (ih m h.2).1⟩, (ih m h.2).2⟩

theorem ArgsT_all_undef {As : List Fam} {j W} : ∀ {pad : List Tm}, (∀ a ∈ pad, a = .undef) →
    ArgsT As j W pad → ∀ A ∈ As, A j W .undef := by
  induction As with
  | nil => intro _ _ _ A hA; cases hA
  | cons B As ih =>
    intro pad hp h A hA
    cases pad with
    | nil => exact False.elim h
    | cons a pad =>
      rcases List.mem_cons.mp hA with rfl | hA
      · have : a = .undef := hp a (by simp)
        subst this; exact h.1
      · exact ih (fun x hx => hp x (by simp [hx])) h.2 A hA

/-- Every member of a list typed position by position is in any family all
the positions are within. -/
theorem ArgsT_all_le {As : List Fam} {E : Fam} {j W}
    (hle : ∀ A ∈ As, ∀ u, A j W u → E j W u) :
    ∀ {xs : List Tm}, ArgsT As j W xs → ∀ e ∈ xs, E j W e := by
  induction As with
  | nil => intro xs h e he; cases xs <;> simp_all [ArgsT]
  | cons A As ih =>
    intro xs h e he
    cases xs with
    | nil => cases he
    | cons x xs =>
      rcases List.mem_cons.mp he with rfl | he
      · exact hle A (by simp) e h.1
      · exact ih (fun B hB => hle B (by simp [hB])) h.2 e he

/-- An exact list is admitted. -/
theorem ArgsShort_of_exact {Ps j W args} (h : ArgsT Ps j W args) : ArgsShort Ps j W args := by
  have hl := ArgsT_length h
  refine ⟨by omega, by rw [hl, List.take_length]; exact h, ?_⟩
  rw [hl, List.drop_length]; simp

/-- A list padded with `undefined` to a signature's length admits the prefix. -/
theorem ArgsShort_of_pad {Ps j W args pad} (hp : ∀ a ∈ pad, a = .undef)
    (h : ArgsT Ps j W (args ++ pad)) : ArgsShort Ps j W args := by
  have hl := ArgsT_length h
  obtain ⟨ht, hd⟩ := ArgsT_take_drop args.length h
  simp only [List.take_left, List.drop_left] at ht hd
  exact ⟨by simp at hl; omega, ht, ArgsT_all_undef hp hd⟩

/-- An admitted list, padded with `undefined`, is an exact list. -/
theorem ArgsShort_pad {Ps j W args} (h : ArgsShort Ps j W args) :
    ArgsT Ps j W (args ++ List.replicate (Ps.length - args.length) .undef) := by
  obtain ⟨hl, ht, hd⟩ := h
  have := ArgsT_append ht (ArgsT_undef (Us := Ps.drop args.length) hd)
  rwa [List.take_append_drop, List.length_drop] at this

theorem ArgsLe_take_drop {As Bs : List Fam} (h : ArgsLe As Bs) : ∀ m : Nat,
    ArgsLe (As.take m) (Bs.take m) ∧ ArgsLe (As.drop m) (Bs.drop m) := by
  induction h with
  | nil => intro m; simp only [List.take_nil, List.drop_nil]; exact ⟨.nil, .nil⟩
  | cons hab ht ih =>
    intro m
    cases m with
    | zero => exact ⟨.nil, .cons hab ht⟩
    | succ m => exact ⟨.cons hab (ih m).1, (ih m).2⟩

theorem ArgsLe_length {As Bs : List Fam} (h : ArgsLe As Bs) : As.length = Bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsLe_all {As Bs : List Fam} (h : ArgsLe As Bs) {j W u}
    (ha : ∀ A ∈ As, A j W u) : ∀ B ∈ Bs, B j W u := by
  induction h with
  | nil => intro B hB; cases hB
  | cons hab _ ih =>
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hab j W u (ha _ (by simp))
    · exact ih (fun A hA => ha A (by simp [hA])) B hB

/-- Pointwise wider positions admit every list the narrower ones do. -/
theorem ArgsShort_mono {Qs Ps : List Fam} (h : ArgsLe Qs Ps) {j W args}
    (ha : ArgsShort Qs j W args) : ArgsShort Ps j W args := by
  obtain ⟨hl, ht, hd⟩ := ha
  have hlen := ArgsLe_length h
  obtain ⟨htk, hdr⟩ := ArgsLe_take_drop h args.length
  exact ⟨by omega, ArgsT_mono htk ht, ArgsLe_all hdr hd⟩

theorem ArgsAgree_take_drop {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) : ∀ m : Nat,
    ArgsAgree n (As.take m) (Bs.take m) ∧ ArgsAgree n (As.drop m) (Bs.drop m) := by
  induction h with
  | nil => intro m; simp only [List.take_nil, List.drop_nil]; exact ⟨.nil, .nil⟩
  | cons hab ht ih =>
    intro m
    cases m with
    | zero => exact ⟨.nil, .cons hab ht⟩
    | succ m => exact ⟨.cons hab (ih m).1, (ih m).2⟩

theorem ArgsAgree_length {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) :
    As.length = Bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsAgree_all {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) {j : Nat} (hj : j < n)
    {W u} : (∀ A ∈ As, A j W u) ↔ ∀ B ∈ Bs, B j W u := by
  induction h with
  | nil => simp
  | cons hab _ ih => simp only [List.mem_cons, forall_eq_or_imp]; exact and_congr (hab j hj W u) ih

theorem ArgsShort_congr {n : Nat} {As Bs : List Fam} (h : ArgsAgree n As Bs) {j : Nat} (hj : j < n)
    (W : WorldT j) (args : List Tm) : ArgsShort As j W args ↔ ArgsShort Bs j W args := by
  have hlen := ArgsAgree_length h
  obtain ⟨htk, hdr⟩ := ArgsAgree_take_drop h args.length
  unfold ArgsShort
  rw [hlen, ArgsT_congr htk hj W args, ArgsAgree_all hdr hj]

/-! ### Admitted lists, position by position -/

theorem ArgsShort_nil_args {Ps : List Fam} {j W} :
    ArgsShort Ps j W [] ↔ ∀ A ∈ Ps, A j W .undef := by
  simp [ArgsShort, ArgsT]

theorem ArgsShort_nil_params {j W} {args : List Tm} : ArgsShort [] j W args ↔ args = [] := by
  cases args <;> simp [ArgsShort, ArgsT]

theorem ArgsShort_cons {P : Fam} {Ps : List Fam} {j W a args} :
    ArgsShort (P :: Ps) j W (a :: args) ↔ P j W a ∧ ArgsShort Ps j W args := by
  simp only [ArgsShort, List.length_cons, List.take_succ_cons, List.drop_succ_cons, ArgsT]
  constructor
  · rintro ⟨hl, ⟨ha, ht⟩, hd⟩; exact ⟨ha, by omega, ht, hd⟩
  · rintro ⟨ha, hl, ht, hd⟩; exact ⟨by omega, ⟨ha, ht⟩, hd⟩

theorem ArgsRest_nil_args {Ps : List Fam} {E : ArgFam} {j W} :
    ArgsRest Ps E j W [] ↔ (∀ A ∈ Ps, A j W .undef) ∧ E j W [] := by
  simp only [ArgsRest, List.take_nil, List.drop_nil, ArgsShort_nil_args]

theorem ArgsRest_nil_params {E : ArgFam} {j W} {args : List Tm} :
    ArgsRest [] E j W args ↔ E j W args := by
  simp [ArgsRest, ArgsShort_nil_params]

theorem ArgsRest_cons {P : Fam} {Ps : List Fam} {E : ArgFam} {j W a args} :
    ArgsRest (P :: Ps) E j W (a :: args) ↔ P j W a ∧ ArgsRest Ps E j W args := by
  simp only [ArgsRest, List.length_cons, List.take_succ_cons, List.drop_succ_cons, ArgsShort_cons,
    and_assoc]

theorem ArgsRest_of_exact_extra {Ps : List Fam} {E : ArgFam} {j W args extra}
    (ha : ArgsT Ps j W args) (he : E j W extra) : ArgsRest Ps E j W (args ++ extra) := by
  have hl := ArgsT_length ha
  refine ⟨?_, ?_⟩
  · rw [← hl, List.take_left]; exact ArgsShort_of_exact ha
  · rw [← hl, List.drop_left]; exact he

/-! ### Bound functions

`.bind` allocates a forwarding descriptor. Its promise is the target's, with
the prefix taken off the front of the parameters and any receiver admitted:
invocation drops the receiver it is given and supplies the saved one. -/

/-- A saved exact prefix followed by an admitted list is admitted by the
target's parameters. -/
theorem ArgsShort_prefix {Ps Ds : List Fam} {j W pre args}
    (hp : ArgsT Ps j W pre) (ha : ArgsShort Ds j W args) :
    ArgsShort (Ps ++ Ds) j W (pre ++ args) := by
  obtain ⟨hlen, htake, hdrop⟩ := ha
  have hpl := ArgsT_length hp
  refine ⟨by simp; omega, ?_, ?_⟩
  · have ht : (Ps ++ Ds).take (pre ++ args).length = Ps ++ Ds.take args.length := by
      rw [List.length_append, hpl, List.take_append, List.take_of_length_le (by omega)]
      congr 2
      omega
    rw [ht]
    exact ArgsT_append hp htake
  · intro A hA
    have hd : (Ps ++ Ds).drop (pre ++ args).length = Ds.drop args.length := by
      rw [List.length_append, hpl, List.drop_append, List.drop_of_length_le (by omega)]
      simp
    rw [hd] at hA
    exact hdrop A hA

/-- An admitted list stays admitted as the budget drops and the world grows. -/
theorem ArgsShort_transfer {Ps : List Fam} (hA : ∀ A ∈ Ps, Adm A) {n W args}
    (ha : ArgsShort Ps n W args) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : ArgsShort Ps j U args := by
  obtain ⟨hlen, htake, hdrop⟩ := ha
  refine ⟨hlen, ArgsT_transfer (fun A hm => hA A (List.mem_of_mem_take hm)) htake j hj U hx, ?_⟩
  intro A hm
  have hadm := hA A (List.mem_of_mem_drop hm)
  exact hadm.mono j _ U hx _ (hadm.down_le n j hj W _ (hdrop A hm))

/-- Every actual typed position by position at one element contract is in it. -/
theorem ArgsT_replicate_all {E : Fam} {j W} : ∀ {m : Nat} {xs : List Tm},
    ArgsT (List.replicate m E) j W xs → ∀ x ∈ xs, E j W x
  | 0, [], _, x, hx => by cases hx
  | 0, _ :: _, h, _, _ => by cases h
  | m + 1, [], h, _, _ => by cases h
  | m + 1, y :: ys, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ArgsT_replicate_all h.2 x hx

/-- A saved prefix covering the first positions of a variadic signature,
followed by a list the rest of the signature admits, is admitted by the whole
signature, when the rest contract admits the prefix's values past the fixed
positions in front of any pack it admits. -/
theorem ArgsRest_prefix {Ps : List Fam} {E : ArgFam} {j W pre args}
    (hp : ArgsT (Ps.take pre.length) j W (pre.take Ps.length))
    (hext : ∀ ys, E j W ys → E j W (pre.drop Ps.length ++ ys))
    (ha : ArgsRest (Ps.drop pre.length) E j W args) : ArgsRest Ps E j W (pre ++ args) := by
  by_cases hk : pre.length ≤ Ps.length
  · rw [List.take_of_length_le hk] at hp
    obtain ⟨hs, he⟩ := ha
    have hdl : (Ps.drop pre.length).length = Ps.length - pre.length := by simp
    refine ⟨?_, ?_⟩
    · have htk : (pre ++ args).take Ps.length = pre ++ args.take (Ps.drop pre.length).length := by
        rw [List.take_append, List.take_of_length_le hk, hdl]
      rw [htk]
      have h := ArgsShort_prefix hp hs
      rwa [List.take_append_drop] at h
    · have hdr : (pre ++ args).drop Ps.length = args.drop (Ps.drop pre.length).length := by
        rw [List.drop_append, List.drop_of_length_le hk, hdl]
        simp
      rw [hdr]; exact he
  · have hdrop : Ps.drop pre.length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, ArgsRest_nil_params] at ha
    rw [List.take_of_length_le (show Ps.length ≤ pre.length by omega)] at hp
    refine ⟨?_, ?_⟩
    · have : (pre ++ args).take Ps.length = pre.take Ps.length := by
        rw [List.take_append]; simp [show Ps.length - pre.length = 0 by omega]
      rw [this]; exact ArgsShort_of_exact hp
    · have hd : (pre ++ args).drop Ps.length = pre.drop Ps.length ++ args := by
        rw [List.drop_append]; simp [show Ps.length - pre.length = 0 by omega]
      rw [hd]; exact hext args ha

/-- An admitted variadic list stays admitted as the budget drops and the world
grows. -/
theorem ArgsRest_transfer {Ps : List Fam} {E : ArgFam} (hA : ∀ A ∈ Ps, Adm A) (hE : Adm E)
    {n W args} (ha : ArgsRest Ps E n W args) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : ArgsRest Ps E j U args :=
  ⟨ArgsShort_transfer hA ha.1 j hj U hx, hE.mono j _ U hx _ (hE.down_le n j hj W _ ha.2)⟩

end Verification
