import Verification.Types.LoopingSchemes
import Verification.Semantics.KindsAllocation

/-! # Inhabited types

**The inhabitance check** (`typeWitnessB`): a decision, on a type of a
normal graph, that it has a value in an extension of any admissible world
whose heap meets it, the extension allocating the value's objects, and that
the value meets the type there and, by admissibility, at every budget
below and every world extending it (`typeWitness_sound`). It reads the
type's labels: a label of call schemes (`callSchemeB`), met by the looping
closure (`LoopingSchemes.loop_meaning`); and a clause row one of whose
clauses has a witness (`clauseWitnessB`), by an exhaustive case analysis on
the clause: a literal or a primitive class, its value; call signatures, the
looping closure; a record of methods, an object whose every member key
holds the looping closure at a location admitting it alone, its generic
members met bound to it (`LoopingSchemes.boundLoop_meaning`). Every other
clause has no witness the check builds, a stated precision limit: the check
then answers `false`.

It is the inhabitance of the types of a framed plan's outside slots, which
its initial premise reads (the framed acceptance draft, "The
initialization as a premise"). -/
namespace Verification.InhabitedTypes
open Verification PositiveGraphs PositiveRules PositiveNormalization LoopingClosures LoopingSchemes Kinds

variable {ι : Type}

/-! ## The looping closure, allocated -/

/-- The world one identity location past `W`. -/
def withIdentity {n : Nat} (W : WorldT n) : WorldT n := appendWs W [(.identity, idCtr)]

/-- **The looping closure, allocated** (proved): one identity location
appended to an admissible world whose heap meets it gives an admissible
world, a heap meeting it, and the looping closure at that identity with
valid references. -/
theorem loop_alloc {n : Nat} {W : WorldT n} {heap : Heap} (hA : WorldAdm W) (hh : HeapOk n W heap)
    (fn : Nat) (c : ComponentTag) :
    WorldAdm (withIdentity W) ∧ HeapOk n (withIdentity W) (heap ++ [.nul]) ∧
      RefsOk (withIdentity W) (loopFn fn c heap.length) := by
  have hlen : heap.length = (entries W).length := by simpa using hh.1.1
  refine ⟨WorldAdm_appendWs_plain hA (by simpa using idCtr_adm) (by simp), ?_, ?_⟩
  · refine HeapOk_appendWs hh hA (by simpa using idCtr_adm) rfl ?_ ?_
    · intro i c' v hc hv j hj
      have hi : i = 0 := by have := (List.getElem?_eq_some_iff.mp hc).1; simp at this; omega
      subst hi
      simp at hc hv; subst hc hv; rfl
    · intro i r v hr hv
      have hi : i = 0 := by have := (List.getElem?_eq_some_iff.mp hr).1; simp at this; omega
      subst hi
      simp at hr hv; subst hr hv
      exact ⟨rfl, fun _ hr => by simp [refs] at hr⟩
  · intro r hr
    simp [loopFn, refs, objRefs, loopE] at hr
    subst hr
    show roleAt _ _ = _
    rw [hlen, show (entries W).length = (entries W).length + 0 from rfl, withIdentity, roleAt_appendWs']
    rfl

/-! ## A record of methods, allocated -/

/-- The contract admitting `u` alone. -/
def oneCtr {n : Nat} (u : Val) : Ctr n := fun _ _ _ x => x = u

theorem oneCtr_adm {n : Nat} {u : Val} (hu : isVal u = true) : CtrAdm (oneCtr (n := n) u) :=
  ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => by rw [show _ = u from h]; exact hu⟩

/-- The entries of an object whose fields `ns` each hold `u`. -/
def recordEntries {n : Nat} (ns : List PropKey) (u : Val) : List (Role × Ctr n) :=
  objectEntries (ns.map .field) (ns.map fun _ => oneCtr u)

/-- The world of such an object allocated past `W`. -/
def recordWorld {n : Nat} (W : WorldT n) (ns : List PropKey) (u : Val) : WorldT n :=
  appendWs W (recordEntries ns u)

/-- The object whose fields `ns` are allocated from `base`, its identity past them. -/
def recordVal (base : Nat) (ns : List PropKey) : Val := .objAt (slots base ns) .absent (base + ns.length)

/-- A key of `ns` is found at the location of its first occurrence. -/
theorem slots_lookup_mem {key : PropKey} : ∀ {ns : List PropKey} (base : Nat), key ∈ ns →
    ∃ i, i < ns.length ∧ (slots base ns).lookup key = some (base + i)
  | [], _, h => by simp at h
  | k :: ns, base, h => by
    by_cases hk : key = k
    · subst hk; exact ⟨0, by simp, by simp [slots]⟩
    · have hm : key ∈ ns := (List.mem_cons.mp h).resolve_left hk
      obtain ⟨i, hi, hl⟩ := slots_lookup_mem (base + 1) hm
      have hk' : (key == k) = false := by simpa using hk
      exact ⟨i + 1, by simp; omega, by simp [slots, List.lookup, hk', hl]; omega⟩

/-- A key outside `ns` is found nowhere. -/
theorem slots_lookup_not_mem {key : PropKey} : ∀ {ns : List PropKey} (base : Nat), key ∉ ns →
    (slots base ns).lookup key = none
  | [], _, _ => rfl
  | k :: ns, base, h => by
    have hk0 : key ≠ k := fun e => h (by rw [e]; exact List.mem_cons_self)
    have hk : (key == k) = false := by simpa using hk0
    simp [slots, List.lookup, hk, slots_lookup_not_mem (base + 1) (fun hm => h (List.mem_cons_of_mem _ hm))]

/-- **A record of fields holding `u`, allocated** (proved): its world is
admissible, its heap meets it, the object's references are valid, and each
field's location admits `u` alone. -/
theorem record_alloc {n : Nat} {W : WorldT n} {heap : Heap} (hA : WorldAdm W) (hh : HeapOk n W heap)
    {u : Val} (hu : isSourceVal u = true) (hur : RefsOk W u) {ns : List PropKey}
    (hkeys : ∀ f ∈ ns, f ≠ arraySpineKey) :
    WorldAdm (recordWorld W ns u) ∧ HeapOk n (recordWorld W ns u) (heap ++ (ns.map fun _ => u) ++ [.nul]) ∧
      RefsOk (recordWorld W ns u) (recordVal heap.length ns) ∧
      ∀ i, i < ns.length → lookup (recordWorld W ns u) (heap.length + i) = some (oneCtr u) := by
  have hlen : heap.length = (entries W).length := by simpa using hh.1.1
  have hv := sourceVal_isVal hu
  have hcadm : ∀ e ∈ recordEntries (n := n) ns u, CtrAdm e.2 := by
    intro e he
    rcases List.mem_append.mp (List.of_mem_zip he).2 with h | h
    · obtain ⟨_, _, he'⟩ := List.mem_map.mp h; rw [← he']; exact oneCtr_adm hv
    · simp only [List.mem_singleton] at h; rw [h]; exact idCtr_adm
  have hplain := objectEntries_plain (k := n) (rs := ns.map .field) (cs := ns.map fun _ => oneCtr u)
    (by intro r hr f N; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr; exact fun h => by cases h)
  have hrefs : RefsOk W (Tm.makeAt .absent ns (ns.map fun _ => u)) := by
    intro r hr
    rw [refs_makeAt] at hr
    simp only [codeRefs, List.nil_append, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨_, ⟨_, _, rfl⟩, hr⟩ := hr
    exact hur r hr
  obtain ⟨hsh, href⟩ := objectLiteral_shaped (c := .absent) (ns := ns) (vs := ns.map fun _ => u)
    (ns.map fun _ => oneCtr u) hlen hh.2 (by simp) (by simp) hrefs hkeys
    (by intro v hv'; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv'; exact hu)
  have hes : (recordEntries (n := n) ns u).length = ((ns.map fun _ => u) ++ [Tm.nul]).length := by
    simp [recordEntries, objectEntries_length]
  have hmeets := HeapMeets_appendWs (es := recordEntries (n := n) ns u) (vs := (ns.map fun _ => u) ++ [.nul])
    hh.1 hA hcadm hes (by
      intro i c v hc hv' j hj
      simp only [recordEntries, objectEntries, List.map_snd_zip (by simp : (ns.map Role.field ++ [Role.identity]).length ≥
        ((ns.map fun _ => oneCtr (n := n) u) ++ [idCtr]).length)] at hc
      by_cases hi : i < ns.length
      · rw [List.getElem?_append_left (by simpa using hi)] at hc hv'
        simp [hi] at hc hv'; subst hc hv'; rfl
      · rw [List.getElem?_append_right (by simp; omega)] at hc hv'
        have hi' : i - ns.length = 0 := by have := (List.getElem?_eq_some_iff.mp hc).1; simp at this; omega
        simp [hi'] at hc hv'; subst hc hv'; rfl)
  refine ⟨WorldAdm_appendWs_plain hA hcadm hplain, ⟨by simpa [recordWorld, List.append_assoc] using hmeets,
    by simpa [recordWorld, recordEntries] using hsh⟩, ?_, ?_⟩
  · simpa [recordVal, recordWorld, recordEntries] using href
  · intro i hi
    rw [hlen, recordWorld, lookup_appendWs_ge]
    simp only [recordEntries, objectEntries, List.map_snd_zip (by simp : (ns.map Role.field ++ [Role.identity]).length ≥
        ((ns.map fun _ => oneCtr (n := n) u) ++ [idCtr]).length)]
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hi]

/-! ## The check -/

/-- **A label of call schemes**, decided (`CallScheme`). -/
def callSchemeB (G : NormalGraph ι) (l : ι) : Bool :=
  !G.params l && match G.schemes l with
    | some s => !s.construct
    | none => false

theorem callSchemeB_sound {G : NormalGraph ι} {l : ι} (h : callSchemeB G l = true) : CallScheme G l := by
  unfold callSchemeB at h
  cases hs : G.schemes l with
  | none => simp [hs] at h
  | some s => simp only [hs, Bool.and_eq_true, Bool.not_eq_true'] at h; exact ⟨h.1, s, hs, h.2⟩

/-- **A type the looping closure meets**, decided: one of its labels is of
call schemes, or a clause row with a clause of call signatures. -/
def loopTypeB (G : NormalGraph ι) (S : List ι) : Bool :=
  S.any fun l => callSchemeB G l || (G.plain l && (G l).any fun c => match c with
    | .arrs _ _ => true
    | _ => false)

/-- **The looping closure meets a type `loopTypeB` passes** (proved), at
every level and world. -/
theorem loopType_meaning {G : NormalGraph ι} {S : List ι} (h : loopTypeB G S = true) (n : Nat) (W : WorldT n)
    (fn : Nat) (tag : ComponentTag) (oid : Nat) : meaning G S n W (loopFn fn tag oid) := by
  obtain ⟨l, hl, hb⟩ := List.any_eq_true.mp h
  rcases Bool.or_eq_true_iff.mp hb with hcs | hp
  · exact loop_meaning ⟨l, hl, callSchemeB_sound hcs⟩ n W fn tag oid
  · obtain ⟨hpl, hany⟩ := Bool.and_eq_true_iff.mp hp
    obtain ⟨c, hc, ha⟩ := List.any_eq_true.mp hany
    cases c with
    | arrs L Sg =>
      exact ⟨l, hl, (mixed_unfold_plain G.env hpl n W _).mpr ⟨_, hc,
        ⟨loop_callsT _ fn tag oid, loop_restsT _ fn tag oid⟩, builtinInvariant_of_withoutInvariant rfl n W _⟩⟩
    | _ => simp at ha

/-- **A member the looping closure meets**: each of its generic signatures
a type with a label of call schemes; its fixed and variadic signatures are
met whatever they state. -/
def memberB (G : NormalGraph ι) (m : MethodMembers.Sig (List ι)) : Bool :=
  m.schemes.all fun S => S.any (callSchemeB G)

/-- The keys of a record of readonly views and methods. -/
def recordKeys (vs : List (PropKey × List ι)) (ms : List (MethodMembers.Sig (List ι))) : List PropKey :=
  vs.map (·.1) ++ ms.map (·.key)

/-- **The keys of a record of views and methods**: none is the array spine
or the prototype, and no optional field shares one. -/
def recordKeysB (os : List (OptionalField (List ι))) (vs : List (PropKey × List ι))
    (ms : List (MethodMembers.Sig (List ι))) : Bool :=
  (recordKeys vs ms).all (fun k => k != CallArguments.arraySpineField && k != CallArguments.protoField) &&
    os.all fun o => decide (o.key ∉ recordKeys vs ms)

/-- **A clause with a witness the check builds**, by cases on the clause: a
literal or a primitive class; call signatures; a record of readonly views of
types the looping closure meets and of methods. Every other clause has none the check builds. -/
def clauseWitnessB (G : NormalGraph ι) : Clause (List ι) → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _ | .bigintLit _ | .symbolLit _ => true
  | .arrs _ _ => true
  | .refs a bs vs os ms ks st =>
    a.isEmpty && bs.isEmpty && ks.isEmpty && st.isEmpty && recordKeysB os vs ms &&
      vs.all (fun v => loopTypeB G v.2) && ms.all (memberB G)
  | .dict .. | .callable .. | .top | .source | .list .. | .bigint | .symbol | .ctors .. | .pack .. | .numIn _
  | .strIn _ | .view .. | .int => false

/-- **The inhabitance check of a type**: one of its labels is of call
schemes, or a clause row one of whose clauses has a witness. -/
def typeWitnessB (G : NormalGraph ι) (S : List ι) : Bool :=
  S.any fun l => callSchemeB G l || (G.plain l && (G l).any (clauseWitnessB G))

/-! ## Soundness -/

/-- The conclusion of the check at a family `T`: an extension of the world
whose heap meets it, holding a closed value with valid references in `T`. -/
def Witnessed (T : Fam) {n : Nat} (W : WorldT n) : Prop :=
  ∃ (W' : WorldT n) (heap' : Heap) (v : Val), WExt W W' ∧ WorldAdm W' ∧ HeapOk n W' heap' ∧
    isVal v = true ∧ Scoped 0 v ∧ RefsOk W' v ∧ T n W' v

/-- A value that is its own witness, at the same world. -/
theorem witnessed_here {T : Fam} {n : Nat} {W : WorldT n} {heap : Heap} (hA : WorldAdm W) (hh : HeapOk n W heap)
    {v : Val} (hv : isVal v = true) (hs : Scoped 0 v) (hr : RefsOk W v) (hT : T n W v) : Witnessed T W :=
  ⟨W, heap, v, WExt_refl _, hA, hh, hv, hs, hr, hT⟩

/-- **A clause the check passes has a witness** (proved), by cases on the
clause. -/
theorem clause_witness {G : NormalGraph ι} {c : Clause (List ι)} (hc : clauseWitnessB G c = true) (tag : ComponentTag)
    {n : Nat} {W : WorldT n} {heap : Heap} (hA : WorldAdm W) (hh : HeapOk n W heap) :
    Witnessed (mixedSem G G.env c) W := by
  have prim : ∀ {v : Val}, isVal v = true → Scoped 0 v → refs v = [] → c.carriesInvariant = false →
      semWithArgs (builtinExc G (builtinValues G)) (mixedValues G G.env) (mixedArgs G G.env) c n W v →
      Witnessed (mixedSem G G.env c) W := fun hv hs hr hci hsem =>
    witnessed_here hA hh hv hs (fun x hx => by rw [hr] at hx; cases hx)
      ⟨hsem, builtinInvariant_of_withoutInvariant hci n W _⟩
  cases c with
  | nul => exact prim (v := .nul) rfl (by simp [Scoped]) rfl rfl rfl
  | undef => exact prim (v := .undef) rfl (by simp [Scoped]) rfl rfl rfl
  | bool => exact prim (v := .tru) rfl (by simp [Scoped]) rfl rfl (.inl rfl)
  | boolLit b =>
    cases b
    · exact prim (v := .fls) rfl (by simp [Scoped]) rfl rfl rfl
    · exact prim (v := .tru) rfl (by simp [Scoped]) rfl rfl rfl
  | num => exact prim (v := .num 0) rfl (by simp [Scoped]) rfl rfl ⟨0, rfl⟩
  | numLit b => exact prim (v := .num b) rfl (by simp [Scoped]) rfl rfl rfl
  | str => exact prim (v := .str "") rfl (by simp [Scoped]) rfl rfl ⟨"", rfl⟩
  | strLit t => exact prim (v := .str t) rfl (by simp [Scoped]) rfl rfl rfl
  | bigintLit i => exact prim (v := .bigint i) rfl (by simp [Scoped]) rfl rfl rfl
  | symbolLit i => exact prim (v := .sym i) rfl (by simp [Scoped]) rfl rfl rfl
  | arrs L Sg =>
    obtain ⟨hA', hh', hr⟩ := loop_alloc hA hh 0 tag
    exact ⟨_, _, _, WExt_appendWs _ _, hA', hh', rfl, (loop_invocable 0 tag heap.length).scoped, hr,
      ⟨⟨loop_callsT _ 0 tag heap.length, loop_restsT _ 0 tag heap.length⟩,
        builtinInvariant_of_withoutInvariant rfl n _ _⟩⟩
  | refs a bs vs os ms ks st =>
    simp only [clauseWitnessB, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hkeys⟩, hvs⟩, hms⟩ := hc
    obtain ⟨hA₁, hh₁, hr₁⟩ := loop_alloc hA hh 0 tag
    have hlen : heap.length = (entries W).length := by simpa using hh.1.1
    let u := loopFn 0 tag heap.length
    let ns := recordKeys vs ms
    simp only [recordKeysB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hkeys
    obtain ⟨hk, hos⟩ := hkeys
    obtain ⟨hA₂, hh₂, hr₂, hl₂⟩ := record_alloc hA₁ hh₁ (u := u) rfl hr₁ (ns := ns)
      (fun f hf => (hk f hf).1)
    let W₂ := recordWorld (withIdentity W) ns u
    let v := recordVal (heap ++ [Tm.nul]).length ns
    have hval : isVal v = true := rfl
    have hsc : Scoped 0 v := by simp [v, recordVal, Scoped]
    have hnot : ∀ key, key ∉ ns → (slots (heap ++ [Tm.nul]).length ns).lookup key = none :=
      fun key h => slots_lookup_not_mem _ h
    refine ⟨W₂, _, v, WExt_trans (WExt_appendWs _ _) (WExt_appendWs _ _), hA₂, hh₂, hval, hsc, hr₂, ?_, ?_⟩
    · simp only [semWithArgs]
      refine ⟨⟨⟨_, _, rfl, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro f s T hm; simp [ReferenceConjunctions.famsOf, mapStored] at hm
      · intro f s T hm; simp [ReferenceConjunctions.famsOf, mapStored] at hm
      · intro B hB; simp at hB
      · intro hne; simp [ReferenceConjunctions.famsOf, mapStored] at hne
      · intro f T hm
        obtain ⟨⟨f', S⟩, hfS, he⟩ := List.mem_map.mp hm
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨i, hi, hli⟩ := slots_lookup_mem (heap ++ [Tm.nul]).length (key := f')
          (show f' ∈ recordKeys vs ms from List.mem_append_left _ (List.mem_map_of_mem (f := fun p : PropKey × List ι => p.1) hfS))
        refine .inl (viewT_single ⟨_, _, oneCtr u, _, rfl, hli, hl₂ i hi, fun j hj U u' hu' => ?_⟩)
        have hu'' : u' = u := hu'
        subst hu''
        exact loopType_meaning (hvs _ hfS) j U 0 tag heap.length
      · refine ⟨_, _, rfl, ?_, ?_, ?_⟩
        · intro o ho _ l hl
          obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
          exact absurd (hl.symm.trans (hnot o'.key (hos o' ho'))) (by simp)
        · intro _ _ _
          exact hnot _ (fun h => (hk _ h).2 rfl)
        · intro o ho l hl
          obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
          exact absurd (hl.symm.trans (hnot o'.key (hos o' ho'))) (by simp)
      · intro m hm
        obtain ⟨sig, hsig, rfl⟩ := List.mem_map.mp hm
        obtain ⟨i, hi, hli⟩ := slots_lookup_mem (heap ++ [Tm.nul]).length (key := sig.key)
          (show sig.key ∈ recordKeys vs ms from List.mem_append_right _
            (List.mem_map_of_mem (f := fun m : MethodMembers.Sig (List ι) => m.key) hsig))
        refine ⟨0, _, _, oneCtr u, _, .absent, rfl, hli, hl₂ i hi, fun j hj U _ u' hu' => ?_⟩
        have hu'' : u' = u := hu'
        subst hu''
        refine ⟨loop_callsT _ 0 tag heap.length, loop_restsT _ 0 tag heap.length, fun oid F hF => ?_⟩
        obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hF
        have hmem := hms sig hsig
        simp only [memberB, List.all_eq_true, List.any_eq_true] at hmem
        obtain ⟨l, hl, hcs⟩ := hmem S hS
        exact boundLoop_meaning ⟨l, hl, callSchemeB_sound hcs⟩ j U 0 tag heap.length hval hsc oid
      · intro K hK; simp at hK
      · intro key hK; simp at hK
    · unfold builtinInvariant
      have hsp : (slots (heap ++ [Tm.nul]).length ns).lookup CallArguments.arraySpineField = none :=
        hnot _ (fun h => (hk _ h).1 rfl)
      cases G.builtins with
      | none =>
        intro flds oid he hs
        simp only [v, recordVal, Tm.objAt.injEq] at he
        obtain ⟨rfl, -, -⟩ := he
        rw [hsp] at hs; cases hs
      | some r =>
        intro flds oid he hs
        simp only [v, recordVal, Tm.objAt.injEq] at he
        obtain ⟨rfl, -, -⟩ := he
        rw [hsp] at hs; cases hs
  | dict => simp [clauseWitnessB] at hc
  | callable => simp [clauseWitnessB] at hc
  | top => simp [clauseWitnessB] at hc
  | source => simp [clauseWitnessB] at hc
  | list => simp [clauseWitnessB] at hc
  | bigint => simp [clauseWitnessB] at hc
  | symbol => simp [clauseWitnessB] at hc
  | ctors => simp [clauseWitnessB] at hc
  | pack => simp [clauseWitnessB] at hc
  | numIn => simp [clauseWitnessB] at hc
  | strIn => simp [clauseWitnessB] at hc
  | view => simp [clauseWitnessB] at hc
  | int => simp [clauseWitnessB] at hc

/-- **The inhabitance check is sound** (proved): a type it passes has, in
an extension of any admissible world whose heap meets it, a closed value
with valid references meeting it at that world's level, and so, the
meaning being admissible, at every budget below and every world extending
the extension's truncation. -/
theorem typeWitness_sound {G : NormalGraph ι} {S : List ι} (h : typeWitnessB G S = true) (tag : ComponentTag)
    {n : Nat} {W : WorldT n} {heap : Heap} (hA : WorldAdm W) (hh : HeapOk n W heap) :
    ∃ (W' : WorldT n) (heap' : Heap) (v : Val), WExt W W' ∧ WorldAdm W' ∧ HeapOk n W' heap' ∧
      isVal v = true ∧ Scoped 0 v ∧ RefsOk W' v ∧
      ∀ j (hj : j ≤ n) (V : WorldT j), WExt (trunc j hj W') V → meaning G S j V v := by
  have hadm : Adm (meaning G S) := Tower.setSem_adm (fun i => normalDenote_adm G i) S
  have lift : ∀ {W' : WorldT n} {v : Val}, meaning G S n W' v →
      ∀ j (hj : j ≤ n) (V : WorldT j), WExt (trunc j hj W') V → meaning G S j V v :=
    fun hm j hj V hx => hadm.mono j _ V hx _ (hadm.down_le n j hj _ _ hm)
  obtain ⟨l, hl, hb⟩ := List.any_eq_true.mp h
  rcases Bool.or_eq_true_iff.mp hb with hcs | hp
  · obtain ⟨hA', hh', hr⟩ := loop_alloc hA hh 0 tag
    exact ⟨_, _, _, WExt_appendWs _ _, hA', hh', rfl, (loop_invocable 0 tag heap.length).scoped, hr,
      fun j _ V _ => loop_meaning ⟨l, hl, callSchemeB_sound hcs⟩ j V 0 tag heap.length⟩
  · obtain ⟨hpl, hany⟩ := Bool.and_eq_true_iff.mp hp
    obtain ⟨c, hc, hw⟩ := List.any_eq_true.mp hany
    obtain ⟨W', heap', v, hx, hA', hh', hv, hs, hr, hm⟩ := clause_witness hw tag hA hh
    exact ⟨W', heap', v, hx, hA', hh', hv, hs, hr,
      lift ⟨l, hl, (mixed_unfold_plain G.env hpl n W' v).mpr ⟨c, hc, hm⟩⟩⟩

end Verification.InhabitedTypes
