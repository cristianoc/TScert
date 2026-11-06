import Verification.Programs.OperatorTyping

/-! ## Variadic functions

A variadic body finds the actuals past its fixed parameters in a fresh array in
slot 0. The array's type is an object whose one field holds a store of any
length at the element type; a spread reads a store whose every position's type
is among the element type's labels, and `undefined` must be among them when the
store may have a hole. -/
namespace Verification.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower
open CallEffects (Arrow RestArrow MethodArrow MethodRestArrow Contract Effect PromiseWith ctorsT ctorsT_adm
  ctorRestsT ctorRestsT_adm)
open HeapObservations (SafePost)

variable {ι : Type}

/-- The variadic signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def restSigs (G : NormalGraph ι) (F : Ty ι) : List (RestArrow (Ty ι)) :=
  match expand G F with
  | [.arrs _ S] | [.callable _ _ _ S _] => S
  | _ => []

theorem restsT_of_restSigs {G : NormalGraph ι} {F : Ty ι} {s} (hs : s ∈ restSigs G F) {n W v}
    (hv : meaning G F n W v) :
    CallEffects.restsT (excOf G) [s.mapWith (meaning G) (argMeaning G)] n W v := by
  unfold restSigs at hs
  split at hs
  · rename_i L S hF
    have hv' := ((represents_raw hF n W v) hv).2
    exact CallEffects.restsT_select hv' (List.mem_map_of_mem hs)
  · rename_i P Ps L S ms hF
    have hv' := ((represents_raw hF n W v) hv).1.2
    exact CallEffects.restsT_select hv' (List.mem_map_of_mem hs)
  · cases hs

/-- The clauses a type's values are members of: the clause it is
represented by, or the clauses of a meet row (`N & C`, a binder within `C`),
whose values are what the assignment gives the binder, within `C`. -/
def objectClauses (G : NormalGraph ι) (O : Ty ι) : List (Clause (Ty ι)) :=
  match expand G O with
  | [c] => [c]
  | _ => match O with
    | [i] => if G.meetRow i then meetClauses G i else []
    | _ => []

/-- A value of a type is a member of one of its object clauses, where it has
any. -/
theorem objectClauses_sem {G : NormalGraph ι} {O : Ty ι}
    (hne : objectClauses G O ≠ []) {n W v} (hv : meaning G O n W v) :
    ∃ c ∈ objectClauses G O, semWithArgs (excOf G) (meaning G) (argMeaning G) c n W v := by
  unfold objectClauses at hne ⊢
  split
  · rename_i c' hO
    exact ⟨c', List.mem_singleton_self _, represents_raw (show Represents G O c' from hO) n W v hv⟩
  · rename_i hnot
    split
    · rename_i i
      split
      · rename_i hmeet
        obtain ⟨l, hl, hlv⟩ := hv
        have hli : l = i := List.mem_singleton.mp hl
        subst hli
        obtain ⟨c, hc, hv'⟩ := meet_clause_of (η := G.env) hmeet hlv
        exact ⟨c, hc, hv'.1⟩
      · rename_i hm
        simp [hm] at hne
    · exfalso
      apply hne
      split
      · simp_all
      · split <;> simp_all

/-- The member a clause names by a key, where it is an object clause. -/
def clauseMember (c : Clause (Ty ι)) (k : PropKey) : Option (MethodMembers.Sig (Ty ι)) :=
  match c with
  | .refs _ _ _ _ ms _ _ | .dict _ _ _ _ _ ms _ _ _ | .callable _ _ _ _ ms => ms.find? (·.key == k)
  | _ => none

/-- A member of a clause's value holds of that value. -/
theorem clauseMember_at {G : NormalGraph ι} {c : Clause (Ty ι)} {k : PropKey} {m : MethodMembers.Sig (Ty ι)}
    (hm : clauseMember c k = some m) {n W v}
    (hs : semWithArgs (excOf G) (meaning G) (argMeaning G) c n W v) :
    m.key = k ∧ MethodMembers.memberT (excOf G) (MethodMembers.Member.of (meaning G) (argMeaning G) m) n W v := by
  unfold clauseMember at hm
  split at hm
  all_goals try contradiction
  all_goals
    rename_i ms
    have hmem := List.mem_of_find?_eq_some hm
    have hkey : m.key = k := by simpa using List.find?_some hm
    exact ⟨hkey, MethodMembers.methodT_at (List.mem_map_of_mem hmem)
      (by first | exact hs.2.2.2.1 | exact hs.2.2.2.2.1 | exact hs.2)⟩

/-- The member a type's object clauses name by a key, the same in each: a
host-relative method, whose contract holds when it is invoked on the object it
is read from. -/
def memberOf [DecidableEq ι] (G : NormalGraph ι) (O : Ty ι) (k : PropKey) : Option (MethodMembers.Sig (Ty ι)) :=
  match objectClauses G O with
  | [] => none
  | c :: cs => (clauseMember c k).bind fun m =>
    if cs.all (fun d => clauseMember d k == some m) then some m else none

/-- The quantified signatures of the member of key `k` of `O`: the schemes a
generic method's member bound to its host meets (`bindScheme`). -/
def memberSchemes [DecidableEq ι] (G : NormalGraph ι) (O : Ty ι) (k : PropKey) : List (Ty ι) :=
  ((memberOf G O k).map (·.schemes)).getD []

/-- A fixed signature covered by one of a member's: each claimed parameter
within the member's, and the member's result within the claimed one, by
checked proofs. The claimed types may be other rows for the same types, such as
a producer's copy of a declared array type. -/
def CoveredCallUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : Arrow (Ty ι))
    (c : MethodArrow (Ty ι)) : Prop :=
  q.arguments.length = c.arguments.length ∧
    (∀ x ∈ q.arguments.zip c.arguments, ∃ p, PositiveCertificates.checkUsing G images x.1 x.2 p = true) ∧
    (∃ p, PositiveCertificates.checkUsing G images c.result q.result p = true) ∧ c.effect.bindCovers 0 q.effect = true

/-- Parameters each within the member's, as families. -/
theorem CoveredCallUsing.params [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} :
    ∀ {Ds Cs : List (Ty ι)}, Ds.length = Cs.length →
      (∀ x ∈ Ds.zip Cs, ∃ p, PositiveCertificates.checkUsing G images x.1 x.2 p = true) →
      ArgsLe (Ds.map (meaning G)) (Cs.map (meaning G))
  | [], [], _, _ => .nil
  | D :: Ds, C :: Cs, hl, h => by
    obtain ⟨p, hp⟩ := h (D, C) (by simp)
    exact .cons (PositiveCertificates.acceptedUsing hp)
      (CoveredCallUsing.params (by simpa using hl) fun x hx => h x (by simp [hx]))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A variadic signature covered by one of a member's with as many fixed
parameters: each claimed fixed parameter within the member's, the claimed
rest within the member's, and the member's result within the claimed one, by
checked proofs. As for `CoveredCallUsing`, the claimed types may be other
rows for the same types, such as a producer's copy of a declared array type
at the rest. -/
def CoveredRestUsing [DecidableEq ι] (G : NormalGraph ι)
    (images : PositiveCertificates.InstanceImageCheck G) (q : RestArrow (Ty ι))
    (c : MethodRestArrow (Ty ι)) : Prop :=
  q.arguments.1.length = c.arguments.1.length ∧
    (∀ x ∈ q.arguments.1.zip c.arguments.1, ∃ p, PositiveCertificates.checkUsing G images x.1 x.2 p = true) ∧
    (∃ p, PositiveCertificates.checkUsing G images q.arguments.2 c.arguments.2 p = true) ∧
    (∃ p, PositiveCertificates.checkUsing G images c.result q.result p = true) ∧ c.effect.bindCovers 0 q.effect = true

/-- A checked proof is an inclusion of argument lists too: the argument
component of the two types' meanings. -/
theorem argsAcceptedUsing [DecidableEq ι] {G : NormalGraph ι}
    {images : PositiveCertificates.InstanceImageCheck G} {S T proof}
    (h : PositiveCertificates.checkUsing G images S T proof = true) (n W vs)
    (hv : argMeaning G S n W vs) : argMeaning G T n W vs :=
  PositiveCertificates.checkUsing_sound h G.env n W (.inr vs) hv

/-- A member of a host's type is found by the member's key on the host, whose
contract implies the member's signatures invoked on that host. -/
theorem memberOf_at [DecidableEq ι] {G : NormalGraph ι} {O : Ty ι} {k : PropKey} {m : MethodMembers.Sig (Ty ι)}
    (hm : memberOf G O k = some m) {n W v} (hv : meaning G O n W v) :
    m.key = k ∧ MethodMembers.memberT (excOf G) (MethodMembers.Member.of (meaning G) (argMeaning G) m) n W v := by
  unfold memberOf at hm
  split at hm
  · cases hm
  · rename_i c cs hcs
    obtain ⟨m0, hm0, hrest⟩ := Option.bind_eq_some_iff.mp hm
    split at hrest
    · rename_i hall
      cases hrest
      obtain ⟨d, hd, hs⟩ := objectClauses_sem (by simp [hcs]) hv
      rw [hcs] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact clauseMember_at hm0 hs
      · have := List.all_eq_true.mp hall d hd
        exact clauseMember_at (by simpa using this) hs
    · cases hrest

/-- **Reading along the chain.** A key held `d` prototypes up is read in `d`
delegation steps, each one level down, then from its location, whose contract
implies `A`. -/
theorem along_read_safe {A : Fam} (hval : ValOnly A) (key : PropKey) :
    ∀ (d : Nat) {n : Nat} {W : WorldT n} {h : Heap} {v : Val}, WorldAdm W → HeapOk n W h →
      MethodMembers.along key A d n W v → Safe Ξ A n W h (.readAt key v)
  | 0, n, W, h, _, hw, hh, ⟨flds, l, c, oid, code, rfl, hf, hl, hag⟩ => read_view_rule_ext hval n W h l hw hh hf hl hag
  | d + 1, n, W, h, _, hw, hh, ⟨flds, oid, code, rfl, hmiss, hp⟩ => by
    obtain ⟨pf, lp, cp, oid', code', hρ, hpf, hlp, hpag⟩ := hp
    cases hρ
    cases n with
    | zero => trivial
    | succ q =>
      obtain ⟨pv, hpv, hmem⟩ := hh.2 lp cp hlp
      have hU := WorldAdm_trunc (Nat.le_succ q) hw
      have hH := HeapOk_trunc q W h hh
      exact Or.inr ⟨trunc q (Nat.le_succ q) W, h, .readAt key pv, WExt_refl _,
        hU, .readProto hmiss hpf hpv, hH,
        along_read_safe hval key d hU hH (hpag q (by omega) _ (WExt_refl _) pv (hmem q (by omega)))⟩

/-- **Reading a member.** The read finds the key on the host, or, some steps
later, on an object along the host's prototype chain; either way the value
read meets the member's signatures invoked on the host. -/
theorem member_read_safe {m : MethodMembers.Member} {n : Nat} {W : WorldT n} {h : Heap} {v : Val}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hm : MethodMembers.memberT Ξ m n W v) :
    Safe Ξ (MethodMembers.onHost Ξ v m) n W h (.readAt m.key v) := by
  have hval : ValOnly (MethodMembers.onHost Ξ v m) := fun _ _ _ hv => hv.1.1.val
  obtain ⟨d, hd⟩ := hm
  exact along_read_safe hval m.key d hw hh hd

/-- The fixed signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def callSigs (G : NormalGraph ι) (F : Ty ι) : List (Arrow (Ty ι)) :=
  match expand G F with
  | [.arrs L _] | [.callable _ _ L _ _] => L
  | _ => []

theorem callsT_of_callSigs {G : NormalGraph ι} {F : Ty ι} {p} (hp : p ∈ callSigs G F) {n W v}
    (hv : meaning G F n W v) :
    CallEffects.callsT (excOf G) [p.map (meaning G)] n W v := by
  unfold callSigs at hp
  split at hp
  · rename_i L S hF
    have hv' := ((represents_raw hF n W v) hv).1
    exact CallEffects.callsT_select hv' (List.mem_map_of_mem hp)
  · rename_i P Ps L S ms hF
    have hv' := ((represents_raw hF n W v) hv).1.1.2
    exact CallEffects.callsT_select hv' (List.mem_map_of_mem hp)
  · cases hp

/-- Saved slots, in order, at the contracts the environment gives them. -/
theorem ArgsT_slots {G : NormalGraph ι} {Γ ρ n W} (he : EnvOk G Γ ρ n W) :
    ∀ {slots : List Nat} {Ps : List (Ty ι)}, slots.map (Γ[·]?) = Ps.map some →
      ArgsT (Ps.map (meaning G)) n W (slots.map ρ)
  | [], [], _ => trivial
  | i :: slots, P :: Ps, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨he.2 _ _ h.1, ArgsT_slots he h.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The type of the store a variadic body receives for a rest type: the rest's
one tuple contract, as a writable store, since the store is fresh. -/
def RestStore (G : NormalGraph ι) (S P : Ty ι) : Prop :=
  match expand G P, expand G S with
  | [.pack T []], [.list U []] => U = { T with readonly := false, presence := U.presence }
  | _, _ => False

/-- A store type whose elements a spread passes at `E`. -/
def SpreadsInto (G : NormalGraph ι) (S E : Ty ι) : Prop :=
  match expand G S with
  | [.list T []] =>
      (∀ A ∈ T.required ++ T.optional ++ T.rest.toList, ∀ i ∈ A, i ∈ E) ∧
      (T.presence ≠ .sparse ∨ ∃ i ∈ E, Represents G [i] .undef)
  | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (S P : Ty ι) : Decidable (RestStore G S P) := by
  unfold RestStore; split <;> (try dsimp only [Represents]) <;> infer_instance

instance [DecidableEq ι] (G : NormalGraph ι) (S E : Ty ι) : Decidable (SpreadsInto G S E) := by
  unfold SpreadsInto; split <;> (try dsimp only [Represents]) <;> infer_instance

/-- An actual as a call writes it: itself, or a spread of it. -/
def spreadTerm (p : Bool × Tm) : Tm := if p.1 then .spread p.2 else p.2

theorem instantiate_spreadTerm (d : Nat) (ρ : Env) (p : Bool × Tm) :
    instantiate d ρ (spreadTerm p) = spreadTerm (p.1, instantiate d ρ p.2) := by
  rcases p with ⟨_ | _, t⟩ <;> simp [spreadTerm, instantiate]

theorem positionTy_eq (T : Tuple (Ty ι)) (i : Nat) :
    positionTy T i = PositiveNormalization.Tuple.position T i := by
  rcases hr : T.required[i]? with _ | A <;>
    rcases ho : T.optional[i - T.required.length]? with _ | B <;>
    simp [positionTy, PositiveNormalization.Tuple.position, hr, ho]

theorem positionTy_mem {T : Tuple (Ty ι)} {i : Nat} {A : Ty ι} (h : positionTy T i = some A) :
    A ∈ T.required ++ T.optional ++ T.rest.toList := by
  unfold positionTy at h
  split at h
  · rename_i B hB; cases h; simp [List.mem_of_getElem? hB]
  · split at h
    · rename_i B hB; cases h; simp [List.mem_of_getElem? hB]
    · split at h
      · simp [h]
      · cases h

theorem undef_of_label {G : NormalGraph ι} {E : Ty ι} {i : ι} (hi : i ∈ E)
    (hr : Represents G [i] .undef) (j : Nat) (U : WorldT j) : meaning G E j U .undef := by
  obtain ⟨i', hi', hv⟩ := (represents_back hr j U .undef) rfl
  simp only [List.mem_singleton] at hi'
  rw [hi'] at hv
  exact ⟨i, hi, hv⟩

theorem spreadsInto_sound {G : NormalGraph ι} {S E : Ty ι} (h : SpreadsInto G S E) :
    RestCalls.Spreads (meaning G S) (meaning G E) := by
  unfold SpreadsInto at h
  split at h
  · rename_i T hS
    have hl := RestCalls.listT_spreads (T := tupleFams (meaning G) T) (E := meaning G E)
      (by
        intro i A hA
        rw [positionFam_tupleFams] at hA
        obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp hA
        rintro n W v ⟨k, hk, hv⟩
        exact ⟨k, h.1 A' (positionTy_mem hA') k hk, hv⟩)
      (by
        intro hs j U
        rcases h.2 with hd | ⟨i, hi, hr⟩
        · simp [tupleFams] at hs; simp [hs] at hd
        · exact undef_of_label hi hr j U)
    intro n W heap v hh hv
    exact hl n W heap v hh ((represents_raw hS n W v) hv).1
  · exact h.elim

/-- A prefix covering a signature's first fixed positions, then its element
past them: its first positions are the signature's, the rest the element. -/
theorem prefix_take_drop {α : Type} (Ps : List α) (k : Nat) (E : α) :
    (Ps.take k ++ List.replicate (k - Ps.length) E).take Ps.length = Ps.take k ∧
    (Ps.take k ++ List.replicate (k - Ps.length) E).drop Ps.length =
      List.replicate (k - Ps.length) E := by
  by_cases hk : k ≤ Ps.length
  · have h0 : k - Ps.length = 0 := by omega
    rw [h0, List.replicate_zero, List.append_nil]
    refine ⟨List.take_of_length_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega)⟩
  · rw [List.take_of_length_le (show Ps.length ≤ k by omega)]
    simp

/-- **Allocating the rest store.** A store of the actuals past the fixed ones
meets a rest-store type when the actuals as one pack meet the rest type. -/
theorem restStore_safe {G : NormalGraph ι} {S P : Ty ι} (hS : RestStore G S P)
    {n : Nat} {W : WorldT n} {h : Heap} {extra : List Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (he : argMeaning G P n W extra) (hvals : CallArguments.Values extra) :
    Safe (excOf G) (meaning G S) n W h (.arrLit extra) := by
  unfold RestStore at hS
  split at hS
  · rename_i T U hP hR
    let T' := { T with presence := U.presence }
    have hpos : ∀ i B, positionFam (tupleFams (meaning G) T') i = some B → Adm B := by
      intro i B hB
      rw [PositiveNormalization.positionFam_tupleFams] at hB
      obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hB
      exact meaning_adm G b
    have hposv : ∀ i B, positionFam (tupleFams (meaning G) T') i = some B → ValOnly B := by
      intro i B hB
      rw [PositiveNormalization.positionFam_tupleFams] at hB
      obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hB
      exact meaning_valOnly G b
    have hfit : ArgumentContracts.Fits (tupleFams (meaning G) T') n W extra := by
      exact (mixed_pack_args hP).mp he
    have := RestCalls.argument_alloc_safe (Ξ := excOf G) hpos hposv hw hh (builtinExc_errors G _) hfit hvals
    apply Safe_mono n _ W h _ this
    intro k _ V v hv
    apply (represents_back hR k V v)
    refine ⟨?_, by simp⟩
    have heq : tupleFams (meaning G) U = {tupleFams (meaning G) T' with readonly := false} := by
      rw [hS]; rfl
    rw [heq]
    exact hv
  · exact hS.elim


/-- A literal of more values than a store holds throws its fresh
`RangeError` in one step, a throw meeting `R` where `R` holds of the heap with
the error object allocated. -/
theorem alloc_throw_exc {Ξ T : Fam} {Q : HeapObservations.Post} {R : Heap → Prop} {n : Nat} {W : WorldT n}
    {h : Heap} {vs : List Tm} (hvals : ∀ v ∈ vs, isVal v = true) (hlen : maxArrayLength < vs.length)
    (hw : WorldAdm W) (hh : HeapOk n W h) (hΞ : ErrorsIn Ξ) (hR : R (h ++ [.nul])) :
    HeapObservations.SafePostExc Ξ T Q R n W h (.arrLit vs) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : CtrAdm (res nulT : Ctr p) :=
      ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => by rw [show _ = Tm.nul from h]; rfl⟩
    refine .inr ⟨appendW (trunc p (Nat.le_succ p) W) (res nulT), h ++ [.nul], _,
      WExt_appendW _ _, WorldAdm_append (WorldAdm_trunc _ hw) hcadm, .arrAllocThrow hvals hlen,
      heap_alloc p _ h (res nulT) .nul (HeapOk_trunc p W h hh) (WorldAdm_trunc _ hw)
        (fun _ _ => rfl), ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact .inl (.inr ⟨⟨thrownError h.length, .throwV rfl rfl, by simp [thrownError, Scoped], hΞ _ _ _⟩, hR⟩)

/-- **Invoking graph code with a rest.** A call at a variadic signature
whose fixed parameters are the code's first collects the actuals past them
into a fresh store, which meets the rest's store type, and runs the code from
the frame the signature describes with that store in slot 0. -/
theorem graphRest_invoke {G : NormalGraph ι} {arity E K start Cs A vs n W}
    {s : RestArrow (Ty ι)}
    (hs : GraphCodeSpec G arity E K start Cs s.fixed (some A))
    (hk : s.arguments.1.length = arity) (harr : RestStore G A s.arguments.2)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (_hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs)
    {j : Nat} (hj : j < n) {U : WorldT j} (hx : WExt (trunc j (Nat.le_of_lt hj) W) U)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G s.receiver j U r)
    {args : List Tm} (hvals : CallArguments.Values args)
    (ha : ArgsRest (s.arguments.1.map (meaning G)) (argMeaning G s.arguments.2) j U args) :
    HeapObservations.SafePostExc (excOf G) (s.effect.result (meaning G s.result) (s.effect.promised args))
      (s.effect.post r heap) (s.effect.excPost r heap) j U heap
      (.letE (.arrLit (args.drop arity))
        (.goto E K start (.var 0 :: r :: CallArguments.parameters arity args ++ vs) .nul)) := by
  obtain ⟨hshort, hpack⟩ := ha
  simp only [List.length_map, hk] at hshort hpack
  have hle : arity ≤ s.fixed.arguments.length := by simp [RestArrow.fixed, hk]
  have hframe := frame_envOk (row := s.fixed) hle hvs (Nat.le_of_lt hj) hx
    hr (args := args.take arity) (by simpa [RestArrow.fixed] using hshort)
  rw [CallArguments.parameters_take] at hframe
  have hclosed : ∀ v ∈ r :: CallArguments.parameters arity args ++ vs, Scoped 0 v := by
    intro v hm
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
    have := hframe.1 i
    unfold envOf at this
    rw [List.getD_eq_getElem?_getD, hi] at this
    exact this
  have hstore : HeapObservations.SafePostExc (excOf G) (meaning G A) (fun heap' _ => heap.IsPrefix heap')
      (s.effect.excPost r heap) j U heap (.arrLit (args.drop arity)) := by
    by_cases hmax : (args.drop arity).length ≤ maxArrayLength
    · apply HeapObservations.SafePostExc.one_step rfl rfl
        (.arrAlloc (fun a hm => hvals a (List.mem_of_mem_drop hm)) hmax)
        ⟨args.drop arity, rfl⟩ (restStore_safe harr hu hh hpack (fun a hm => hvals a (List.mem_of_mem_drop hm)))
    · exact alloc_throw_exc (fun a hm => hvals a (List.mem_of_mem_drop hm)) (by omega) hu hh
        (builtinExc_errors G _) (fun _ => Effect.within_of_holds
          (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) (Footprints.Closed.holds_empty.mpr ⟨[.nul], rfl⟩)))
  apply HeapObservations.SafePostExc.bind (.letE · _) .letC .letC j U heap _ hu hh hstore
  intro i hi V hy hv heap' a hh' hval harr' hprefix
  cases i with
  | zero => trivial
  | succ p =>
    apply HeapObservations.SafePostExc.bind_value hval hv hh'
    have hsub : subst 0 a (.goto E K start (.var 0 :: r :: CallArguments.parameters arity args ++ vs)
        .nul) = .goto E K start (a :: r :: CallArguments.parameters arity args ++ vs) .nul := by
      have hmap : (r :: CallArguments.parameters arity args ++ vs).map (subst 0 a) =
          r :: CallArguments.parameters arity args ++ vs := by
        rw [List.map_congr_left (g := id) (fun v hm => subst_above (hclosed v hm) (Nat.le_refl 0) a),
          List.map_id]
      show Tm.goto E K start (substArgs 0 a (.var 0 :: (r :: CallArguments.parameters arity args ++ vs)))
        (subst 0 a .nul) = _
      rw [substArgs_eq_map, List.map_cons, hmap]
      rfl
    rw [hsub]
    have hUV : WExt (trunc (p + 1) hi U) V := hy
    have henv := (hframe.transfer (p + 1) hi V hUV).push harr'
    have henv' : EnvOk G (codeFrame arity s.fixed Cs (some A))
        (envOf (a :: r :: CallArguments.parameters arity args ++ vs) .nul) (p + 1) V := by
      have he : push a (envOf (r :: CallArguments.parameters arity args ++ vs) .nul) =
          envOf (a :: r :: CallArguments.parameters arity args ++ vs) .nul := by
        funext i; cases i <;> rfl
      rw [← he]; exact henv
    apply HeapObservations.SafePostExc.weaken (Q := fun heap'' v => ∀ r', s.fixed.effect.post r' heap' heap'' v)
      (R := fun heap'' => ∀ r', s.fixed.effect.excPost r' heap' heap'')
      (fun heap'' v hp => s.effect.post_prefix hprefix (hp r))
      (fun heap'' hp => s.effect.excPost_prefix hprefix (hp r))
    have hpromised := framePromised_params (e := s.fixed.effect) hs.2.1 [a, r] args vs
    simp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] at hpromised
    rw [← show framePromised s.effect (frameOffset (some A)) (a :: r :: CallArguments.parameters arity args ++ vs) =
      s.effect.promised args from hpromised]
    exact hs.2.2 p _ heap' _ (henv'.transfer p (Nat.le_succ p) _ (WExt_refl _))
      (WorldAdm_trunc _ hv) (HeapOk_trunc p V heap' hh') (by
        intro v hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hval
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact (meaning_value hr).1
          · rcases List.mem_append.mp hm with hm | hm
            · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl hvals v hm
            · exact hvalues v hm)

/-- **Graph code with a rest meets its variadic signatures**: the actuals past
its fixed parameters are collected, not discarded (`restsT_of_graph` is the
fixed-arity case, which discards them). -/
theorem restsT_of_graphRest {G : NormalGraph ι} {arity E K start Cs vs n W} {kind : Invoke}
    {S : List (RestArrow (Ty ι))} {As : List (Ty ι)} (fs : List (PropKey × Nat)) (hkind : kind ≠ .construct)
    (hb : ∀ s ∈ S, KindBinds G kind s.receiver)
    (hs : ∀ q ∈ S.zip As, q.1.arguments.1.length = arity ∧ RestStore G q.2 q.1.arguments.2 ∧
      GraphCodeSpec G arity E K start Cs q.1.fixed (some q.2))
    (hlen : S.length = As.length)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hcs : Cs.length ≤ vs.length)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W (.objAt fs (.graph arity E K start vs kind true) oid) := by
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind true) oid) := by simpa [Scoped] using hsc
  refine ⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩
  intro q hq j hj U hx hu heap hh r hrv hr args hvals ha _
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  have hbind := hb s hsm j U r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsm
  have hiA : i < As.length := hlen ▸ hi
  have hz : (S[i], As[i]) ∈ S.zip As :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
      ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiA⟩)
  obtain ⟨hk, harr, hspec⟩ := hs _ hz
  have hsc' : ∀ v ∈ vs ++ [Tm.objAt fs (.graph arity E K start vs kind true) oid], Scoped 0 v := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hsc v hv
    · rw [List.mem_singleton.mp hv]; exact hself
  exact ⟨_, .graph hrv hvals hbind,
    graphRest_invoke hspec hk harr (hvs.withSelf hcs hself) hsc' (Values.withSelf hvalues rfl) hj hx hu hh hr hvals ha⟩

/-- **The signatures graph code offers.** Code without a rest meets each
fixed signature and, discarding the actuals past its parameters, each
variadic one, all at their rows (`offerRows`); code with a rest offers no
fixed signature, and meets each variadic one from the frame with the store of
the further actuals, whose type `As` lists in the signatures' order. -/
def CodeOffers (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (rest : Bool) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) (As : List (Ty ι)) : Prop :=
  match rest with
  | false => ∀ p ∈ offerRows L S, GraphCodeSpec G arity E K start Cs p
  | true => L = [] ∧ S.length = As.length ∧ ∀ q ∈ S.zip As, q.1.arguments.1.length = arity ∧
      RestStore G q.2 q.1.arguments.2 ∧
      GraphCodeSpec G arity E K start Cs q.1.fixed (some q.2)

/-- The arity and rest-store requirements of a code offer. -/
def CodeOffersShape (G : NormalGraph ι) (arity : Nat) (rest : Bool)
    (L : List (Arrow (Ty ι))) (S : List (RestArrow (Ty ι))) (As : List (Ty ι)) : Prop :=
  match rest with
  | false => True
  | true => L = [] ∧ S.length = As.length ∧ ∀ q ∈ S.zip As,
      q.1.arguments.1.length = arity ∧ RestStore G q.2 q.1.arguments.2

/-- Whether code of kind `kind` may offer a signature whose receiver is `R`:
`call` code any; `sloppy` code one whose type is of clause rows, each an
object clause, so that it admits objects only (`kindOffers_binds`); construct
code no call signature. -/
@[nospecialize] def kindOffers (G : NormalGraph ι) (kind : Invoke) (R : Ty ι) : Bool :=
  match kind with
  | .call => true
  | .sloppy => G.plainTy R && (expand G R).all objectClause
  | .construct => false

/-- A receiver type `kindOffers` admits for a kind is one the kind binds. -/
theorem kindOffers_binds {G : NormalGraph ι} {kind : Invoke} {R : Ty ι}
    (h : kindOffers G kind R = true) : KindBinds G kind R := by
  intro j U r hr
  cases kind with
  | call => rfl
  | construct => simp [kindOffers] at h
  | sloppy =>
    simp only [kindOffers, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨c, hc, hv, -⟩ := (expand_sem G R h.1 j U r).mp hr
    obtain ⟨fs, code, oid, rfl⟩ := objectClause_member (h.2 c hc) hv
    rfl

/-- The signatures code of kind `kind` offers: it has `[[Call]]`, and binds
every receiver of each (`kindOffers`). -/
def KindOffers (G : NormalGraph ι) (kind : Invoke) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) : Prop :=
  kind ≠ .construct ∧ ∀ p ∈ offerRows L S, kindOffers G kind p.receiver = true

instance [DecidableEq ι] (G : NormalGraph ι) (kind : Invoke) (L : List (Arrow (Ty ι)))
    (S : List (RestArrow (Ty ι))) : Decidable (KindOffers G kind L S) := by
  unfold KindOffers; infer_instance

/-- Graph code with captured values meets the signatures it offers. -/
theorem offers_sem {G : NormalGraph ι} {arity E K start Cs rest vs n W} {kind : Invoke}
    {L : List (Arrow (Ty ι))} {S : List (RestArrow (Ty ι))}
    {As : List (Ty ι)} (fs : List (PropKey × Nat))
    (hk : KindOffers G kind L S)
    (ho : CodeOffers G arity E K start Cs rest L S As)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hcs : Cs.length ≤ vs.length)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    CallEffects.callsT (excOf G) (L.map (Arrow.map (meaning G))) n W
        (.objAt fs (.graph arity E K start vs kind rest) oid) ∧
      CallEffects.restsT (excOf G) (S.map (RestArrow.mapWith (meaning G) (argMeaning G))) n W (.objAt fs (.graph arity E K start vs kind rest) oid) := by
  obtain ⟨hkind, hrows⟩ := hk
  have hbL : ∀ p ∈ L, KindBinds G kind p.receiver :=
    fun p hp => kindOffers_binds (hrows p (List.mem_append_left _ hp))
  have hbS : ∀ s ∈ S, KindBinds G kind s.receiver :=
    fun s hs => kindOffers_binds (hrows _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)))
  cases rest with
  | false =>
    exact ⟨callsT_of_graph _ hkind hbL (fun p hp => ho p (List.mem_append_left _ hp)) hvs hcs hsc hvalues,
      restsT_of_graph _ hkind hbS (fun s hs => ho _
        (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩))) hvs hcs hsc hvalues⟩
  | true =>
    obtain ⟨rfl, hlen, hs⟩ := ho
    exact ⟨⟨⟨fs, _, _, rfl, callable_of_kind hkind, by simpa [Scoped] using hsc⟩, by simp⟩,
      restsT_of_graphRest fs hkind hbS hs hlen hvs hcs hsc hvalues⟩

/-- **A recursive closure meets its type.** Graph code of fixed arity checked
from the frame whose last slot, after its captures, is its self entry at the
closure's own type `F`, meets `F` wherever its captures meet theirs: by
induction on the level, an invocation runs below it, where the self entry,
the invoked object, meets `F` by the induction hypothesis. The type and its
effects are what the code's checks establish, the self entry's included. -/
theorem offers_self {G : NormalGraph ι} {arity E K start Cs vs} {kind : Invoke}
    {F : Ty ι} {L : List (Arrow (Ty ι))} {S : List (RestArrow (Ty ι))} (fs : List (PropKey × Nat)) {oid : Nat}
    (hr : Represents G F (.arrs L S)) (hk : KindOffers G kind L S)
    (ho : CodeOffers G arity E K start (Cs ++ [F]) false L S [])
    (hlen : Cs.length = vs.length) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    ∀ n W, EnvOk G Cs (envOf vs .nul) n W →
      meaning G F n W (.objAt fs (.graph arity E K start vs kind false) oid) := by
  obtain ⟨hkind, hrows⟩ := hk
  have hbL : ∀ p ∈ L, KindBinds G kind p.receiver :=
    fun p hp => kindOffers_binds (hrows p (List.mem_append_left _ hp))
  have hbS : ∀ s ∈ S, KindBinds G kind s.receiver :=
    fun s hs => kindOffers_binds (hrows _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)))
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind false) oid) := by simpa [Scoped] using hsc
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro W hvs
  apply (represents_back hr n W _)
  refine ⟨⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩, ⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩⟩
  · intro q hq j hj U hx hu heap hh r hrv hrr args hvals ha _
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have henv := hvs.transfer j (Nat.le_of_lt hj) U hx
    have hF := ih j hj U henv
    exact ⟨_, .graph hrv hvals (hbL p hp j U r hrr),
      graph_invoke_at (ho p (List.mem_append_left _ hp)) (henv.withSelfAt hlen hself hF)
        (Values.withSelf hvalues rfl) hu hh hrr ha⟩
  · intro q hq j hj U hx hu heap hh r hrv hrr args hvals ha _
    obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
    have hspec := ho _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hsm, rfl⟩))
    have hle : arity ≤ s.arguments.1.length := hspec.1
    have hbelow : s.fixed.effect.below arity = true := hspec.2.1
    have henv := hvs.transfer j (Nat.le_of_lt hj) U hx
    have hF := ih j hj U henv
    have hsafe := graph_invoke_at hspec (henv.withSelfAt hlen hself hF) (Values.withSelf hvalues rfl) hu hh
      (args := args.take s.arguments.1.length) hrr
      (by simpa [RestArrow.mapWith, Contract.map, RestArrow.fixed] using ha.1)
    have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
        CallArguments.parameters arity args := by
      rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
        Nat.min_eq_left hle, CallArguments.parameters_take]
    rw [hp, CallEffects.Effect.promised_take (e := s.fixed.effect) hbelow hle] at hsafe
    exact ⟨_, .graph hrv hvals (hbS s hsm j U r hrr), hsafe⟩

/-- **A class value's graph code** meets each construct signature it was
checked at, with its effect, with `undefined` for its receiver: `new` enters it
so. -/
theorem ctorsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {U : Ty ι}
    {L : List (MethodArrow (Ty ι))} (fs : List (PropKey × Nat))
    (hs : ∀ p ∈ L, GraphCodeSpec G arity E K start Cs ⟨U, p.arguments, p.result, p.effect⟩)
    (hu : Represents G U .undef)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hcs : Cs.length ≤ vs.length)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    ctorsT (excOf G) (L.map (MethodArrow.map (meaning G))) n W
      (.objAt fs (.graph arity E K start vs .construct) oid) := by
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs .construct) oid) := by simpa [Scoped] using hsc
  refine ⟨⟨fs, _, _, _, _, _, _, _, rfl, hself⟩, ?_⟩
  intro q hq j hj V hx hv heap hh args _ ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  refine ⟨_, ⟨fs, _, _, _, rfl, rfl, rfl⟩, ?_⟩
  exact graph_invoke (row := ⟨U, p.arguments, p.result, p.effect⟩) (hs p hp) (hvs.withSelf hcs hself)
    (Values.withSelf hvalues rfl) hj hx hv hh
    ((represents_back hu j V _) rfl) (ArgsShort_of_exact ha)

/-- The row a class's graph code is checked at for a variadic construct
signature with fixed parameters `Qs` and element rest `El`: the fixed
parameters, then each further position the code binds at `El` or `undefined`,
which construction binds where the list is shorter. -/
def ctorRestParams (arity : Nat) (Qs : List (Ty ι)) (El U : Ty ι) : List (Ty ι) :=
  Qs ++ List.replicate (arity - Qs.length) (El ++ U)

/-- A list of members of `D`, cut to `r` positions, is admitted by `r`
positions at `D` when `D` admits `undefined`. -/
theorem ArgsShort_replicate {D : Fam} {j : Nat} {W : WorldT j} {r : Nat} {xs : List Tm}
    (hx : ∀ x ∈ xs, D j W x) (hu : D j W .undef) :
    ArgsShort (List.replicate r D) j W (xs.take r) := by
  refine ⟨by simp; omega, ?_, ?_⟩
  · apply ArgsT_of_getElem? (by simp)
    intro i A a hA ha
    simp only [List.take_replicate, List.getElem?_replicate] at hA
    split at hA
    · cases hA; exact hx a (List.mem_of_mem_take (List.mem_of_getElem? ha))
    · cases hA
  · intro A hA
    rw [List.drop_replicate] at hA
    rw [List.eq_of_mem_replicate hA]; exact hu

/-- Graph code of a class meets a variadic construct signature with an
element rest when it meets the row `ctorRestParams` gives: construction binds
the fixed actuals, then further ones up to its arity, padding with `undefined`,
and discards the rest. The signature's effect is plain, so its result
operand is the result's type whichever actuals the body binds. -/
theorem ctorRestsT_of_graph {G : NormalGraph ι} {arity E K start Cs vs n W} {U : Ty ι}
    {S : List (MethodRestArrow (Ty ι))} (fs : List (PropKey × Nat))
    (hs : ∀ s ∈ S, s.effect.plain = true ∧ ∃ El, restElem G s.arguments.2 = some El ∧
      GraphCodeSpec G arity E K start Cs ⟨U, ctorRestParams arity s.arguments.1 El U, s.result, s.effect⟩)
    (hu : Represents G U .undef)
    (hvs : EnvOk G Cs (envOf vs .nul) n W) (hcs : Cs.length ≤ vs.length)
    (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs) :
    ctorRestsT (excOf G) (S.map (MethodRestArrow.mapWith (meaning G) (argMeaning G))) n W
      (.objAt fs (.graph arity E K start vs .construct) oid) := by
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs .construct) oid) := by simpa [Scoped] using hsc
  refine ⟨⟨fs, _, _, _, _, _, _, _, rfl, hself⟩, ?_⟩
  intro q hq j hj V hx hv heap hh args _ ha
  obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hplain, El, hel, hspec⟩ := hs s hsm
  obtain ⟨hlen, hfix, hext⟩ := ha
  simp only [MethodRestArrow.mapWith, Contract.map, List.length_map] at hlen hfix hext ⊢
  have hel' := (restElem_args hel).mp hext
  let D : Ty ι := El ++ U
  have hD : ∀ x ∈ args.drop s.arguments.1.length, meaning G D j V x :=
    fun x hx => (meaning_append G El U j V x).mpr (Or.inl (hel' x hx))
  have hDu : meaning G D j V .undef :=
    (meaning_append G El U j V _).mpr (Or.inr ((represents_back hu j V _) rfl))
  have hshort := ArgsShort_prefix hfix
    (ArgsShort_replicate (r := arity - s.arguments.1.length) hD hDu)
  have hle : arity ≤ (ctorRestParams arity s.arguments.1 El U).length := hspec.1
  have hm : (ctorRestParams arity s.arguments.1 El U).length = s.arguments.1.length + (arity - s.arguments.1.length) := by
    simp [ctorRestParams]
  have hargs' : args.take s.arguments.1.length ++ (args.drop s.arguments.1.length).take (arity - s.arguments.1.length) =
      args.take (s.arguments.1.length + (arity - s.arguments.1.length)) := by
    rw [List.take_add]
  rw [hargs'] at hshort
  have hsafe := graph_invoke (row := ⟨U, ctorRestParams arity s.arguments.1 El U, s.result, s.effect⟩) hspec
    (hvs.withSelf hcs hself) (Values.withSelf hvalues rfl) hj hx hv hh ((represents_back hu j V _) rfl)
    (args := args.take (s.arguments.1.length + (arity - s.arguments.1.length)))
    (by simpa [ctorRestParams, List.map_append, List.map_replicate] using hshort)
  have hp : CallArguments.parameters arity (args.take (s.arguments.1.length + (arity - s.arguments.1.length))) =
      CallArguments.parameters arity args := by
    rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
      Nat.min_eq_left (by omega), CallArguments.parameters_take]
  rw [hp] at hsafe
  rw [Effect.result_plain hplain] at hsafe ⊢
  exact ⟨_, ⟨fs, _, _, _, rfl, rfl, rfl⟩, hsafe⟩

/-- The parts a variadic call writes past its fixed actuals fit its rest. With
a spread among them, the rest is an element rest, each plain part at its
element and each spread spreading into it. Without one, the rest is a pack of
one tuple contract, and the parts are at its positions, within its bounds. -/
def RestParts (G : NormalGraph ι) (P : Ty ι) (parts : List (Bool × Ty ι)) : Prop :=
  if parts.any (·.1) then
    match restElem G P with
    | some E => ∀ p ∈ parts, if p.1 then SpreadsInto G p.2 E else p.2 = E
    | none => False
  else
    match expand G P with
    | [.pack T []] => T.required.length ≤ parts.length ∧
        (T.rest = none → parts.length ≤ T.required.length + T.optional.length) ∧
        ∀ i ∈ List.range parts.length, positionTy T i = (parts[i]?).map (·.2)
    | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (P : Ty ι) (parts : List (Bool × Ty ι)) :
    Decidable (RestParts G P parts) := by
  unfold RestParts
  split
  · split <;> infer_instance
  · split <;> infer_instance

/-- Plain actuals at the positions of a rest's one tuple contract, within its
bounds, form a pack of the rest. -/
theorem restParts_pack {G : NormalGraph ι} {P : Ty ι} {T : Tuple (Ty ι)}
    (hP : expand G P = [.pack T []]) {Qs : List (Ty ι)}
    (hreq : T.required.length ≤ Qs.length)
    (hbound : T.rest = none → Qs.length ≤ T.required.length + T.optional.length)
    (hpos : ∀ i ∈ List.range Qs.length, positionTy T i = Qs[i]?)
    {k : Nat} {W : WorldT k} {extra : List Tm} (ha : ArgsT (Qs.map (meaning G)) k W extra) :
    argMeaning G P k W extra := by
  have hlen : extra.length = Qs.length := by simpa using ArgsT_length ha
  refine (mixed_pack_args hP).mpr ⟨by simpa [tupleFams, hlen] using hreq,
    by simpa [tupleFams, hlen] using hbound, ?_⟩
  intro i u B hu hB
  have hi : i < Qs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hu).1
  rw [PositiveNormalization.positionFam_tupleFams] at hB
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hB
  have hq : Qs[i]? = some b := by
    rw [← hpos i (List.mem_range.mpr hi), positionTy_eq]
    exact hb
  exact ArgsT_getElem? (A := meaning G b) ha (by simp [List.getElem?_map, hq]) hu

theorem ArgStep_append {h h' : Heap} {args args' : List Tm} (rest : List Tm)
    (s : CallArguments.ArgStep h args h' args') :
    CallArguments.ArgStep h (args ++ rest) h' (args' ++ rest) := by
  induction s with
  | head hs => exact .head hs
  | tail hv _ ih => exact .tail hv ih

/-- **A variadic call with a spread.** The callee, the receiver, the fixed
actuals, then the further parts run left to right; the call meets the
signature's result. Each further actual is at the element contract `E`, and
actuals at `E` form a pack of the rest `P`. -/
theorem rest_call_safe {Rc : Fam} {Ps : List Fam} {E R : Fam} {P : ArgFam}
    (hRc : Adm Rc)
    (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A) (hE : Adm E) (hEv : ValOnly E)
    (hP : Adm P) (hEP : ∀ k W xs, (∀ e ∈ xs, E k W e) → P k W xs)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps) (parts : List (Option Fam × Tm))
    (hS : ∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (restsT Ξ [(Rc, Ps, P, R)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r)
    (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) (hp : ∀ p ∈ parts, FutureSafe Ξ (p.1.getD E) n W p.2) :
    Safe Ξ R n W heap (.invoke f r (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) := by
  apply Safe_bind (fun f => .invoke f r (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) Step.callL Raises.callL
    n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply Safe_bind (fun r => .invoke v r (xs.map Prod.snd ++ parts.map RestCalls.partTerm))
    (Step.callRecv hv) (Raises.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv (args ++ parts.map RestCalls.partTerm))
    (fun hs => (CallArguments.Prepare.args hv hrv (ArgStep_append _ hs)).step)
    (fun hr => (hr.append _).invoke hv hrv) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  apply RestCalls.spread_parts_safe hE hEv hv hrv parts k V heap'' args hS hv' hok'
    (ArgsT_values hAv hargs) (fun p hm => ((hp p hm).transfer hj hxU).transfer hk hy)
  intro i hi X hz hX heap3 extra hh3 hext
  have hUX : WExt (trunc i (Nat.le_trans hi hk) U) X := by
    apply WExt_trans _ hz
    simpa only [trunc_trunc] using WExt_trunc hi hy
  have hfX := (restsT_adm _).mono i _ X hUX v
    ((restsT_adm _).down_le j i (Nat.le_trans hi hk) U v hfun)
  have hrX := hRc.mono i _ X hUX rv (hRc.down_le j i (Nat.le_trans hi hk) U rv hrm)
  exact RestCalls.call_elim_rest (s := (Rc, Ps, P, R)) (by simp) hRc hA hAv hP hrv hrX hfX
    (ArgsT_transfer hA hargs i hi X hz) (hEP i X extra hext) (fun e he => hEv i X e (hext e he))
    hX hh3

/-- Every label of `A` is the packed binder `t`, or a meet row of it: each
value of `A` is one of `t`'s. -/
def PackedBy (G : NormalGraph ι) (A : Ty ι) (t : ι) : Prop :=
  G.parameterKinds t = some .packed ∧
    ∀ l ∈ A, l = t ∨ (G.params l = false ∧ G.schemes l = none ∧ (G.meets l).map Prod.fst = some t)

instance [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (t : ι) : Decidable (PackedBy G A t) := by
  unfold PackedBy; infer_instance

/-- A value of a packed binder, or of a meet row of it, is packable by the
binder's argument lists. -/
theorem packedBy_sound {G : NormalGraph ι} {A : Ty ι} {t : ι} (hp : PackedBy G A t)
    {n W v} (hv : meaning G A n W v) : Packable (argMeaning G [t]) n W v := by
  obtain ⟨hk, hA⟩ := hp
  have hparam : G.params t = true := by simp [NormalGraph.params, hk]
  have hpart : ∀ {m U u}, (mixedParameters G).value t (G.env.1 t) m U u →
      Packable (argMeaning G [t]) m U u := by
    intro m U u h
    simp only [mixedParameters, hk, selectParameter] at h
    rcases h with ⟨h, _⟩ | ⟨_, _, h⟩
    · cases h
    · refine Packable_mono ?_ h
      intro j U' vs hvs
      exact ⟨t, List.mem_singleton_self t, by simpa [NormalGraph.listParam, hk] using hvs⟩
  obtain ⟨l, hl, hv⟩ := hv
  rcases hA l hl with rfl | ⟨hlp, hls, hm'⟩
  · change qDenoteWithArgs G (mixedParameters G) (G.env, l) n W v at hv
    rw [qDenoteWithArgs_unfold] at hv
    simp only [qLayerWithArgs, hparam, ite_true] at hv
    exact hpart hv
  obtain ⟨⟨t', cs⟩, hm, ht⟩ := Option.map_eq_some_iff.mp hm'
  cases ht
  change qDenoteWithArgs G (mixedParameters G) (G.env, l) n W v at hv
  rw [qDenoteWithArgs_unfold] at hv
  simp only [qLayerWithArgs, hlp, hls, hm, Bool.false_eq_true, ite_false] at hv
  rw [partSemWithArgs_param hparam] at hv
  exact hpart hv.1.1

/-- **A spread of a packed value.** The callee, the receiver and the fixed
actuals run, then the operand; its store is read and spread, a step each, and
the elements form a list of the rest `P`, which the operand's values are
packable by (`Packable`). -/
theorem packed_call_safe {Rc : Fam} {Ps : List Fam} {R V : Fam} {P : ArgFam}
    (hRc : Adm Rc) (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A)
    (hP : Adm P) (hPv : ∀ n W vs, P n W vs → CallArguments.Values vs)
    (hVP : ∀ n W v, V n W v → Packable P n W v)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps)
    {n W heap f r a} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (restsT Ξ [(Rc, Ps, P, R)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r) (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) (ha : FutureSafe Ξ V n W a) :
    Safe Ξ R n W heap (.invoke f r (xs.map Prod.snd ++
      [.spread (.readAt CallArguments.arrayStoreField a)])) := by
  let tail := fun (t : Tm) => [Tm.spread (.readAt CallArguments.arrayStoreField t)]
  apply Safe_bind (fun f => .invoke f r (xs.map Prod.snd ++ tail a)) Step.callL Raises.callL
    n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply Safe_bind (fun r => .invoke v r (xs.map Prod.snd ++ tail a))
    (Step.callRecv hv) (Raises.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv (args ++ tail a))
    (fun hs => (CallArguments.Prepare.args hv hrv (ArgStep_append _ hs)).step)
    (fun hr => (hr.append _).invoke hv hrv) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V' hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  have hvals := ArgsT_values hAv hargs
  have hkU : WExt (trunc k (Nat.le_trans hk hj) W) V' := by
    apply WExt_trans _ hy
    simpa only [trunc_trunc] using WExt_trunc hk hxU
  apply Safe_bind (A := V) (fun t => .invoke v rv (args ++ tail t))
    (fun s => RestCalls.call_lift hv hrv hvals (.spreadC (.readC s)))
    (fun s => RestCalls.call_raise hv hrv hvals (.spreadC (.readC s))) k V' heap'' a hv' hok'
    ((ha.transfer (Nat.le_trans hk hj) hkU) k (Nat.le_refl _) V'
      (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
  intro i hi X hz hX heap3 av hok3 hav hva
  have hfX := (restsT_adm _).mono i _ X hz v ((restsT_adm _).down_le k i hi V' v
    ((restsT_adm _).mono k _ V' hy v ((restsT_adm _).down_le j k hk U v hfun)))
  have hrX := hRc.mono i _ X hz rv (hRc.down_le k i hi V' rv
    (hRc.mono k _ V' hy rv (hRc.down_le j k hk U rv hrm)))
  have hargsX := ArgsT_transfer hA hargs i hi X hz
  cases i with
  | zero => trivial
  | succ i =>
    obtain ⟨fs, c, oid, l, ls, vs, rfl, hl, hls, hrd, hvs⟩ :=
      hVP (i + 1) X av hva i (Nat.le_refl _) X (by rw [trunc_id]; exact WExt_refl _) heap3 hok3
    cases i with
    | zero =>
      refine Or.inr ⟨trunc 0 (Nat.le_succ 0) X, heap3, _, WExt_refl _, WorldAdm_trunc _ hX,
        RestCalls.call_lift hv hrv hvals (.spreadC (.readField hl hls)), HeapOk_trunc 0 X heap3 hok3, trivial⟩
    | succ m =>
      let X1 := trunc (m + 1) (Nat.le_succ (m + 1)) X
      refine Or.inr ⟨X1, heap3, _, WExt_refl _, WorldAdm_trunc _ hX,
        RestCalls.call_lift (rest := []) hv hrv hvals (.spreadC (.readField hl hls)),
        HeapOk_trunc (m + 1) X heap3 hok3, ?_⟩
      have hvsv := hPv _ _ _ (hvs m (by omega))
      let X2 := trunc m (Nat.le_succ m) X1
      refine Or.inr ⟨X2, heap3, .invoke v rv (args ++ vs), WExt_refl _,
        WorldAdm_trunc _ (WorldAdm_trunc _ hX),
        by simpa using Step.callSpread (pre := args) (post := []) hv hrv rfl hvals hrd,
        HeapOk_trunc m X1 heap3 (HeapOk_trunc (m + 1) X heap3 hok3), ?_⟩
      have hle : ∀ {F : Fam}, Adm F → ∀ u, F (m + 2) X u → F m X2 u := fun hF u h =>
        hF.down m X1 u (hF.down (m + 1) X u h)
      have hPm : P m X2 vs := by
        have := hvs m (by omega)
        simpa only [X2, X1, trunc_trunc] using this
      exact RestCalls.call_elim_rest (s := (Rc, Ps, P, R)) (by simp) hRc hA hAv hP hrv
        (hle hRc rv hrX) (hle (restsT_adm _) v hfX)
        (ArgsT_transfer hA hargsX m (by omega) X2 (by simp only [X2, X1, trunc_trunc]; exact WExt_refl _))
        hPm hvsv (WorldAdm_trunc _ (WorldAdm_trunc _ hX))
        (HeapOk_trunc m X1 heap3 (HeapOk_trunc (m + 1) X heap3 hok3))

/-- **A variadic call writing no spread.** The callee, the receiver and every
actual run left to right; the fixed ones meet the signature's parameters, less
trailing ones `Us` the call omits, each admitting `undefined`, and the further
ones, at `Qs`, form a pack of the rest `P`. A call that omits a fixed position
writes no further actual. -/
theorem pack_call_safe {Rc : Fam} {Ps Us Qs : List Fam} {R : Fam} {P : ArgFam}
    (hRc : Adm Rc) (hA : ∀ A ∈ Ps ++ Qs, Adm A) (hAv : ∀ A ∈ Ps ++ Qs, ValOnly A)
    (hUA : ∀ A ∈ Us, Adm A)
    (hpack : ∀ k W extra, ArgsT Qs k W extra → P k W extra)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps ++ Qs) (hshort : Us = [] ∨ Qs = [])
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (restsT Ξ [(Rc, Ps ++ Us, P, R)]) n W heap f)
    (hr : FutureSafe Ξ Rc n W r) (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe Ξ A n W .undef) :
    Safe Ξ R n W heap (.invoke f r (xs.map Prod.snd)) := by
  apply Safe_bind (fun f => .invoke f r (xs.map Prod.snd)) Step.callL Raises.callL n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply Safe_bind (fun r => .invoke v r (xs.map Prod.snd)) (Step.callRecv hv) (Raises.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv args)
    (fun hs => (CallArguments.Prepare.args hv hrv hs).step) (fun hr => hr.invoke hv hrv) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  cases k with
  | zero => trivial
  | succ k =>
    let X := trunc k (Nat.le_succ k) V
    have hX : WorldAdm X := WorldAdm_trunc _ hv'
    have hhX : HeapOk k X heap'' := HeapOk_trunc k V heap'' hok'
    have hfV := (restsT_adm _).mono (k + 1) _ V hy v
      ((restsT_adm _).down_le j (k + 1) hk U v hfun)
    have hrV := hRc.down k V rv (hRc.mono (k + 1) _ V hy rv (hRc.down_le j (k + 1) hk U rv hrm))
    have hargsX := ArgsT_transfer hA hargs k (Nat.le_succ k) X (WExt_refl _)
    have hsplit := ArgsT_take_drop Ps.length hargsX
    simp only [List.take_append_of_le_length (Nat.le_refl _),
      List.take_length, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
      List.nil_append] at hsplit
    have hacc : ArgsRest (Ps ++ Us) P k X args := by
      rcases hshort with rfl | rfl
      · have := ArgsRest_of_exact_extra (Ps := Ps) hsplit.1 (hpack k X _ hsplit.2)
        simpa only [List.append_nil, List.take_append_drop] using this
      · have hundef : ∀ A ∈ Us, A k X .undef := by
          intro A hA'
          have := safe_value_mem rfl
            (((hu A hA').transfer hj hxU).transfer hk hy (k + 1) (Nat.le_refl _) V
              (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
          exact (hUA A hA').down k V _ this
        simp only [List.append_nil] at hargsX
        have hshortX : ArgsShort (Ps ++ Us) k X args :=
          ArgsShort_of_pad (pad := List.replicate Us.length .undef)
            (fun a hm => List.eq_of_mem_replicate hm)
            (ArgsT_append hargsX (ArgsT_undef hundef))
        have hl : args.length ≤ (Ps ++ Us).length := hshortX.1
        refine ⟨by rwa [List.take_of_length_le hl], ?_⟩
        rw [List.drop_eq_nil_of_le hl]
        exact hpack k X [] trivial
    obtain ⟨body, hi, hsafe⟩ := hfV.2 (Rc, Ps ++ Us, P, R) (by simp) k (Nat.lt_succ_self k) X
      (WExt_refl _) hX heap'' hhX rv hrv hrV args (ArgsT_values hAv hargsX) hacc
    exact Or.inr ⟨X, heap'', body, WExt_refl _, hX, hi.step heap'', hhX, hsafe⟩

/-- **Eliminating a variadic construct signature.** A ready construction whose
fixed actuals meet the parameters and whose further ones form a pack of the
rest takes one step to the class's body, safe at the result. -/
theorem ctor_elim_rest {Ps : List Fam} {P : ArgFam} {R : Fam} {e : Effect} (hpl : e.plain = true)
    (hA : ∀ A ∈ Ps, Adm A) (hP : Adm P)
    {n W v args extra heap} (hf : ctorRestsT Ξ [⟨(), (Ps, P), R, e⟩] n W v)
    (ha : ArgsT Ps n W args) (he : P n W extra) (hvals : CallArguments.Values (args ++ extra))
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe Ξ R n W heap (.construct v (args ++ extra)) := by
  cases n with
  | zero => trivial
  | succ k =>
    have hl := ArgsT_length ha
    have hrest : CtorRest Ps P k (trunc k (Nat.le_succ k) W) (args ++ extra) := by
      refine ⟨by simp; omega, ?_, ?_⟩
      · rw [List.take_left' hl]
        exact ArgsT_transfer hA ha k (Nat.le_succ k) _ (WExt_refl _)
      · rw [List.drop_left' hl]
        exact hP.down k W extra he
    obtain ⟨result, ⟨fs, c, enter, oid, rfl, hc', rfl⟩, hsafe⟩ :=
      (hf.2 _ (List.mem_singleton_self _)).erase hpl k (Nat.lt_succ_self k) (trunc k (Nat.le_succ k) W)
        (WExt_refl _) (WorldAdm_trunc _ hw) heap (HeapOk_trunc k W heap hh) _ hvals hrest
    exact Or.inr ⟨trunc k (Nat.le_succ k) W, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
      CallArguments.construction_step hc' hvals heap, HeapOk_trunc k W heap hh, hsafe⟩

/-- **A variadic construction with a spread.** The constructor, the fixed
actuals, then the further parts run left to right, each spread read where it
is written; each further actual is at the element contract `E`, and actuals at
`E` form a pack of the rest `P`. -/
theorem construct_rest_safe {Ps : List Fam} {E R : Fam} {P : ArgFam} {e : Effect} (hpl : e.plain = true)
    (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A) (hE : Adm E) (hEv : ValOnly E)
    (hP : Adm P) (hEP : ∀ k W xs, (∀ e ∈ xs, E k W e) → P k W xs)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps) (parts : List (Option Fam × Tm))
    (hS : ∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (ctorRestsT Ξ [⟨(), (Ps, P), R, e⟩]) n W heap f)
    (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) (hp : ∀ p ∈ parts, FutureSafe Ξ (p.1.getD E) n W p.2) :
    Safe Ξ R n W heap (.construct f (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) := by
  apply Safe_bind (fun f => .construct f (xs.map Prod.snd ++ parts.map RestCalls.partTerm))
    Step.constructL Raises.constructL n W heap f hw hh hf
  intro j hj U hxU hu heap' v hok hv hfun
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .construct v (args ++ parts.map RestCalls.partTerm))
    (fun hs => CallArguments.Step.constructArgs hv (ArgStep_append _ hs))
    (fun hr => (hr.append _).construct hv) hu hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  apply RestCalls.parts_safe hE hEv (Tm.construct v)
    (fun hp s => CallArguments.Step.constructArgs hv (CallArguments.keep_prefix hp (.head s)))
    (fun hp s => .constructArg hv (prefix_position hp).1 (prefix_position hp).2 s)
    (fun hp hr => .constructSpread hv rfl hp hr)
    parts k V heap'' args hS hv' hok' (ArgsT_values hAv hargs)
    (fun p hm => ((hp p hm).transfer hj hxU).transfer hk hy)
  intro i hi X hz hX heap3 extra hh3 hext
  have hUX : WExt (trunc i (Nat.le_trans hi hk) U) X := by
    apply WExt_trans _ hz
    simpa only [trunc_trunc] using WExt_trunc hi hy
  have hfX := (ctorRestsT_adm _).mono i _ X hUX v
    ((ctorRestsT_adm _).down_le j i (Nat.le_trans hi hk) U v hfun)
  exact ctor_elim_rest hpl hA hP hfX (ArgsT_transfer hA hargs i hi X hz) (hEP i X extra hext)
    (by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact ArgsT_values hAv hargs a ha
      · exact hEv i X a (hext a ha)) hX hh3

/-- **A variadic construction writing no spread.** The constructor and every
actual run left to right; the fixed ones meet the signature's parameters and
the further ones, at `Qs`, form a pack of the rest `P`. -/
theorem construct_pack_safe {Ps Qs : List Fam} {R : Fam} {P : ArgFam} {e : Effect} (hpl : e.plain = true)
    (hA : ∀ A ∈ Ps ++ Qs, Adm A) (hAv : ∀ A ∈ Ps ++ Qs, ValOnly A) (hP : Adm P)
    (hpack : ∀ k W extra, ArgsT Qs k W extra → P k W extra)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps ++ Qs)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe Ξ (ctorRestsT Ξ [⟨(), (Ps, P), R, e⟩]) n W heap f)
    (hx : ∀ p ∈ xs, FutureSafe Ξ p.1 n W p.2) :
    Safe Ξ R n W heap (.construct f (xs.map Prod.snd)) := by
  apply Safe_bind (fun f => .construct f (xs.map Prod.snd)) Step.constructL Raises.constructL n W heap f hw hh hf
  intro j hj U hxU hu heap' v hok hv hfun
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (Tm.construct v) (fun hs => CallArguments.Step.constructArgs hv hs) (fun hr => hr.construct hv) hu hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  obtain ⟨h1, h2⟩ := ArgsT_take_drop Ps.length hargs
  simp only [List.take_append_of_le_length (Nat.le_refl _), List.take_length,
    List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append] at h1 h2
  have hfV := (ctorRestsT_adm _).mono k _ V hy v ((ctorRestsT_adm _).down_le j k hk U v hfun)
  have := ctor_elim_rest hpl (fun A h => hA A (List.mem_append_left _ h)) hP hfV h1 (hpack k V _ h2)
    (by rw [List.take_append_drop]; exact ArgsT_values hAv hargs) hv' hok'
  rwa [List.take_append_drop] at this

/-- **A fresh store of values at `E`.** Allocated, the values meet the
contract `E` at every position, under any readonly flag and presence mode:
every position holds a location of its own. -/
theorem fresh_store_safe {E : Fam} (ro : Bool) (presence : ArrayPresence) (hE : Adm E) (hEv : ValOnly E)
    {n : Nat} {W : WorldT n} {h : Heap} {vs : List Tm} (hw : WorldAdm W) (hh : HeapOk n W h) (hΞ : ErrorsIn Ξ)
    (hvs : ∀ e ∈ vs, E n W e) :
    Safe Ξ (listT ⟨[], [], some E, ro, presence⟩) n W h (.arrLit vs) := by
  apply arr_alloc_rule (As := List.replicate vs.length E)
    (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact hE)
    (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact hEv)
    n W h vs (by simp) (fun v hm => hEv n W v (hvs v hm)) hw hh hΞ
    (by
      intro q hq
      rw [List.eq_of_mem_replicate (List.of_mem_zip hq).1]
      exact hvs q.2 (List.of_mem_zip hq).2)
  intro k hk X hy hl hmax
  have := listT_alloc (n := k) (W := X) (T := ⟨[], [], some E, ro, presence⟩)
    (As := List.replicate vs.length E) (base := h.length)
    (by simp) (by simpa using hmax) (by simp)
    (by
      intro i A hA
      have := (List.getElem?_eq_some_iff.mp hA)
      simp only [List.getElem_replicate] at this
      rw [← this.2]
      simp [positionFam])
    hl
  simpa using this

/-- The named fields and readonly views of an object of one record operand:
a record's, or a dictionary's, whose named members hold beside its index. -/
def namedMembers : Clause α → Option (List (PropKey × α) × List (PropKey × α))
  | .refs fs [] vs _ _ _ _ => some (fs, vs)
  | .dict fs [] vs _ _ _ _ _ _ => some (fs, vs)
  | _ => none

/-- A value of a type with named members holds each named field as a cell of
its contract and each view as a location whose contents meet its bound. -/
theorem namedMembers_sem {G : NormalGraph ι} {A : Ty ι} {c : Clause (Ty ι)}
    {fs vs : List (PropKey × Ty ι)} (hr : Represents G A c)
    (hc : namedMembers c = some (fs, vs)) {n W v} (h : meaning G A n W v) :
    recT (ReferenceConjunctions.famsOf (meaning G) fs) n W v ∧
      viewsT (ReferenceConjunctions.famsOf (meaning G) vs) n W v := by
  have hs := (represents_raw hr n W v) h
  match c, hc with
  | .refs _ [] _ _ _ _ _, rfl => exact ⟨hs.1.1, hs.2.1⟩
  | .dict _ [] _ _ _ _ _ _ _, rfl => exact ⟨hs.1.1, hs.2.1⟩

/-- A clause with named members is a record's or a dictionary's, which the
builtins's invariant applies to. -/
theorem namedMembers_carriesInvariant {c : Clause α} {fs vs : List (PropKey × α)}
    (hc : namedMembers c = some (fs, vs)) : c.carriesInvariant = true := by
  match c, hc with
  | .refs _ [] _ _ _ _ _, rfl => rfl
  | .dict _ [] _ _ _ _ _ _ _, rfl => rfl

/-- **`length`, read where the object may be an array**: an array's is its
store's length, any other object's its own property's. -/
def lengthRead (i : Nat) : Tm :=
  .ite (.test .isArray (.var i)) (.lenOf (.readAt CallArguments.arrayStoreField (.var i)))
    (.readAt lengthKey (.var i))

/-- Whether a clause's members exclude the number `w`. -/
def rejectsNum (w : UInt64) (c : Clause α) : Bool :=
  match c with
  | .numLit b => b != w
  | .numIn bs => !bs.contains w
  | c => tagClause .isNum c == some false

theorem rejectsNum_sound {Ξ : Fam} {S : α → Fam} {P : α → ArgFam} {w : UInt64} {c : Clause α}
    (h : rejectsNum w c = true) {n W} : ¬ semWithArgs Ξ S P c n W (.num w) := by
  intro hv
  unfold rejectsNum at h
  split at h
  · simp only [bne_iff_ne, ne_eq] at h
    simp only [semWithArgs, Tm.num.injEq] at hv
    exact h hv.symm
  · obtain ⟨b, hb, he⟩ := hv
    cases he
    simp [hb] at h
  · have := tagClause_sound (beq_iff_eq.mp h) hv
    simp [tagHolds] at this

/-- A number no value of the type is, where one is found among the first
few: one more than its numeric singletons, a tag set's elements counted. -/
@[nospecialize] def numWitness (G : NormalGraph ι) (A : Ty ι) : Option UInt64 :=
  if G.plainTy A then
    ((List.range ((splitSets (expand G A)).length + 1)).map Nat.toUInt64).find? fun w =>
      (expand G A).all (rejectsNum w)
  else none

theorem numWitness_sound {G : NormalGraph ι} {A : Ty ι} {w : UInt64} (h : numWitness G A = some w)
    {n W} : ¬ meaning G A n W (.num w) := by
  intro hv
  unfold numWitness at h
  split at h
  · rename_i hp
    have hall := List.find?_some h
    simp only [List.all_eq_true] at hall
    obtain ⟨c, hc, hcv, -⟩ := (expand_sem G A hp n W _).mp hv
    exact rejectsNum_sound (hall c hc) hcv
  · cases h

/-- **A `length` view met at its own location**: its type excludes a number,
so the view's array alternative (`arrayLenT`, which needs every number) does
not hold, and the view is at the object's own location. -/
@[nospecialize] def lengthExcluded (G : NormalGraph ι) (A : Ty ι) : Bool := (numWitness G A).isSome

/-- Whether a type's `length` is a view an array may meet (`lenView` reads
it): its one record or dictionary clause names `length` among its views, not
among its fields, at a type excluding no number found. -/
@[nospecialize] def lengthViewed (G : NormalGraph ι) (B : Ty ι) : Bool :=
  match expand G B with
  | [c] => match namedMembers c with
    | some (fs, vs) => (fs.lookup lengthKey).isNone &&
        match vs.lookup lengthKey with
        | some A => !lengthExcluded G A
        | none => false
    | none => false
  | _ => false

end Verification.ProgramTyping
