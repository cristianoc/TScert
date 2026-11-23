import Verification.Semantics.Confinement
import Verification.Programs.PromiseCalls
import Verification.Programs.Parametricity
import Verification.Programs.GraphCode
import Verification.Programs.CertificateProducer

/-! # Checked local-object confinement

An untrusted per-node confinement table (`Table`) assigns each graph label `l`
four slot lists (`NodeConf`) over its claim context `0 .. width - 1`:
- `owned`: slots whose own non-spine field locations lie in `Priv`;
- `ownedArr`: slots whose spine location and element cells lie in `Priv`;
- `ownedSpines`: slots holding a fresh `.arr` spine whose cells lie in `Priv`;
- `holders`: a superset of all slots `< width` whose value may directly reach
  `Priv`.

`Table.framedNodes` lists labels whose expression mentions no slot in `holders`
(`freeSlotsNotIn width 0 pre.holders node.expression = true`); at each such
node, `Table.framed` supplies `Confinement.confinedFootprint pre.owned pre.ownedArr`
so the single pass keeps every index fact, cell fact and read link over those
confined objects across arbitrary-effect calls (including `top`).

`checkNode` checks each visited node's transition against its checked step
derivation (`derivChecked`) and outgoing edges (`edgeOk`). `checkNode_sound`
proves `ConfinedAt` preservation on normal and exceptional exits and discharges
`Footprints.Supported` at every framed node via
`Confinement.steps_confined_unreachable`, `Confinement.closedOut_of_keep_outside`,
and `PromiseCalls.callerFrame_post`, with zero client trust. -/
namespace Verification.LocalConfinement

open Verification Footprints HeapObservations ControlFlow PointClaims
open ProgramTyping PositiveGraphs PositiveRules PositiveCertificates ProgramCertificates CertificateProducer
open Verification.TolerantFrames.Reach
open Verification.Confinement

/-- Per-node confinement state over the node's entry slots `0 .. width - 1`. -/
structure NodeConf where
  owned : List Nat := []
  ownedArr : List Nat := []
  ownedSpines : List Nat := []
  holders : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- Untrusted confinement proposal for a function's graph. -/
structure Table where
  nodes : Array NodeConf
  framedNodes : List Nat := []
  allocPriv : List Nat := []
  deriving DecidableEq, Repr

def Table.at (t : Table) (l : Nat) : NodeConf :=
  t.nodes.getD l {}

/-- The `SinglePass.framed` list induced by `t`: for each framed node with at
least one owned slot, its `confinedFootprint`. -/
def Table.framed (t : Table) : List (Nat × List Footprint) :=
  t.framedNodes.filterMap fun l =>
    let nc := t.at l
    if nc.owned.isEmpty && nc.ownedArr.isEmpty then none
    else some (l, [confinedFootprint nc.owned nc.ownedArr])

def NodeConf.shift (nc : NodeConf) : NodeConf :=
  { owned := nc.owned.map (· + 1)
    ownedArr := nc.ownedArr.map (· + 1)
    ownedSpines := nc.ownedSpines.map (· + 1)
    holders := nc.holders.map (· + 1) }

/-! ## Inert types (values with no heap references or code) -/

/-- Whether a normalized clause admits only primitive (`Reach.Inert`) values. -/
def inertClause {α : Type} : PositiveNormalization.Clause α → Bool
  | .nul | .bool | .boolLit _ | .num | .numLit _ | .undef
  | .str | .strLit _ | .bigint | .symbol | .bigintLit _ | .symbolLit _
  | .numIn _ | .strIn _ | .int => true
  | _ => false

/-- Whether every value of type `A` in `G` is `Reach.Inert`. -/
def inertTy [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all inertClause

theorem inertClause_sound {G : NormalGraph ι} {c : PositiveNormalization.Clause (List ι)} {n W v}
    (hc : inertClause c = true) (hv : clauseSem G c n W v) : Inert allC v := by
  replace hv := hv.1
  cases c <;> simp only [inertClause, reduceCtorEq] at hc
  case nul =>
    have : v = .nul := by simpa [PositiveNormalization.semWithArgs, nulT] using hv
    subst this; exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case bool =>
    have : v = .tru ∨ v = .fls := by simpa [PositiveNormalization.semWithArgs, boolT] using hv
    rcases this with rfl | rfl <;> exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case boolLit b =>
    have : v = if b then .tru else .fls := by simpa [PositiveNormalization.semWithArgs] using hv
    subst this; cases b <;> exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case num =>
    obtain ⟨b, rfl⟩ : ∃ b, v = .num b := by simpa [PositiveNormalization.semWithArgs, numT] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case numLit b =>
    have : v = .num b := by simpa [PositiveNormalization.semWithArgs] using hv
    subst this; exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case undef =>
    have : v = .undef := by simpa [PositiveNormalization.semWithArgs, undefT] using hv
    subst this; exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case str =>
    obtain ⟨s, rfl⟩ : ∃ s, v = .str s := by simpa [PositiveNormalization.semWithArgs, strT] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case strLit s =>
    have : v = .str s := by simpa [PositiveNormalization.semWithArgs] using hv
    subst this; exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case bigint =>
    obtain ⟨i, rfl⟩ : ∃ i, v = .bigint i := by simpa [PositiveNormalization.semWithArgs, bigintT] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case symbol =>
    obtain ⟨i, rfl⟩ : ∃ i, v = .sym i := by simpa [PositiveNormalization.semWithArgs, symbolT] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case bigintLit i =>
    have : v = .bigint i := by simpa [PositiveNormalization.semWithArgs] using hv
    subst this; exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case symbolLit i =>
    have : v = .sym i := by simpa [PositiveNormalization.semWithArgs] using hv
    subst this; exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case numIn S =>
    obtain ⟨b, -, rfl⟩ : ∃ b ∈ S, v = .num b := by simpa [PositiveNormalization.semWithArgs] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case strIn S =>
    obtain ⟨s, -, rfl⟩ : ∃ s ∈ S, v = .str s := by simpa [PositiveNormalization.semWithArgs] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩
  case int =>
    obtain ⟨b, rfl, -⟩ : ∃ b, v = .num b ∧ SafeIntegers.safeIntOfBits b ≠ none := by
      simpa [PositiveNormalization.semWithArgs, PositiveNormalization.intT] using hv
    exact ⟨fun a => by cases a <;> rfl, rfl⟩

theorem inertTy_sound [DecidableEq ι] {G : NormalGraph ι} {A : Ty ι} {n W v}
    (hi : inertTy G A = true) (hv : meaning G A n W v) : Inert allC v := by
  simp only [inertTy, Bool.and_eq_true, List.all_eq_true] at hi
  obtain ⟨hplain, hall⟩ := hi
  obtain ⟨c, hcm, hsem⟩ := (expand_sem G A hplain n W v).mp hv
  exact inertClause_sound (hall c hcm) hsem

theorem inertTy_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι) (A : Ty ι) :
    inertTy (reassign G η) A = inertTy G A := rfl

/-! ## Bounded `HoldersCover` and free-slot checks -/

/-- Every slot `< width` outside `holders` holds a value with `NoPriv Priv`. -/
def HoldersCoverB (width : Nat) (ρ : Env) (holders : List Nat) (Priv : Nat → Prop) : Prop :=
  ∀ y, y < width → y ∉ holders → NoPriv Priv (ρ y)

mutual
/-- Executable check that every free slot of `t` at depth `d` is `< width` and
lies outside `holders`. -/
def freeSlotsNotIn (width d : Nat) (holders : List Nat) : Tm → Bool
  | .var i => i < d || (i - d < width && !holders.contains (i - d))
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | .objAt _ .absent _ => true
  | .makeAt .absent _ args => freeSlotsNotInAll width d holders args
  | .objAt _ (.bound t r pre) _ =>
      freeSlotsNotIn width d holders t && freeSlotsNotIn width d holders r && freeSlotsNotInAll width d holders pre
  | .makeAt (.bound t r pre) _ args =>
      freeSlotsNotIn width d holders t && freeSlotsNotIn width d holders r &&
      freeSlotsNotInAll width d holders pre && freeSlotsNotInAll width d holders args
  | .objAt _ (.graph _ _ _ _ caps _ _ _) _ => freeSlotsNotInAll width d holders caps
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ args =>
      freeSlotsNotInAll width d holders caps && freeSlotsNotInAll width d holders args
  | .letE a b => freeSlotsNotIn width d holders a && freeSlotsNotIn width (d + 1) holders b
  | .invoke f r args =>
      freeSlotsNotIn width d holders f && freeSlotsNotIn width d holders r && freeSlotsNotInAll width d holders args
  | .construct f args => freeSlotsNotIn width d holders f && freeSlotsNotInAll width d holders args
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b | .merge _ a b | .makeKey a b =>
      freeSlotsNotIn width d holders a && freeSlotsNotIn width d holders b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => freeSlotsNotIn width d holders a
  | .setElem a b c =>
      freeSlotsNotIn width d holders a && freeSlotsNotIn width d holders b && freeSlotsNotIn width d holders c
  | .arrLit args => freeSlotsNotInAll width d holders args
  | .ite c a b =>
      freeSlotsNotIn width d holders c && freeSlotsNotIn width d holders a && freeSlotsNotIn width d holders b
  | _ => false

def freeSlotsNotInAll (width d : Nat) (holders : List Nat) : List Tm → Bool
  | [] => true
  | a :: as => freeSlotsNotIn width d holders a && freeSlotsNotInAll width d holders as
end

private theorem freeSlotsNotInAll_iff (width d : Nat) (holders : List Nat) :
    ∀ xs, freeSlotsNotInAll width d holders xs = true ↔ ∀ a ∈ xs, freeSlotsNotIn width d holders a = true
  | [] => by simp [freeSlotsNotInAll]
  | a :: as => by
    simp only [freeSlotsNotInAll, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [freeSlotsNotInAll_iff width d holders as]

theorem freeSlotsNotIn_sound {width : Nat} {holders : List Nat}
    {P : Nat → Prop} (hh : ∀ y, y < width → y ∉ holders → P y) :
    ∀ (t : Tm) (d : Nat), freeSlotsNotIn width d holders t = true → FreeSlotsOk d P t := by
  intro t
  induction t using Tm.induct
  case var i =>
    intro d h
    simp only [FreeSlotsOk]
    intro hge
    simp only [freeSlotsNotIn, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with hlt | ⟨hltw, hnm⟩
    · omega
    · exact hh (i - d) hltw (fun hm => by rw [List.contains_iff_mem.mpr hm] at hnm; cases hnm)
  case invoke f r args ihf ihr iha =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true, freeSlotsNotInAll_iff] at h
    exact ⟨ihf d h.1.1, ihr d h.1.2, fun a ha => iha a ha d (h.2 a ha)⟩
  case construct f args ihf iha =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true, freeSlotsNotInAll_iff] at h
    exact ⟨ihf d h.1, fun a ha => iha a ha d (h.2 a ha)⟩
  case letE a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb (d + 1) h.2⟩
  case objBound fs oid t r pre iht ihr ihp =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true, freeSlotsNotInAll_iff] at h
    exact ⟨iht d h.1.1, ihr d h.1.2, fun a ha => ihp a ha d (h.2 a ha)⟩
  case makeBound t r pre ns args iht ihr ihp iha =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true, freeSlotsNotInAll_iff] at h
    exact ⟨iht d h.1.1.1, ihr d h.1.1.2, fun a ha => ihp a ha d (h.1.2 a ha), fun a ha => iha a ha d (h.2 a ha)⟩
  case alloc ns args iha =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, freeSlotsNotInAll_iff] at h
    exact fun a ha => iha a ha d (h a ha)
  case objGraph fs oid n E K st caps k r comp _ ihc =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, freeSlotsNotInAll_iff] at h
    exact fun a ha => ihc a ha d (h a ha)
  case makeGraph n E K st caps k r comp ns args _ ihc iha =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true, freeSlotsNotInAll_iff] at h
    exact ⟨fun a ha => ihc a ha d (h.1 a ha), fun a ha => iha a ha d (h.2 a ha)⟩
  case arrLit args iha =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, freeSlotsNotInAll_iff] at h
    exact fun a ha => iha a ha d (h a ha)
  case setElem a b c iha ihb ihc =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1.1, ihb d h.1.2, ihc d h.2⟩
  case ite c a b ihc iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨ihc d h.1.1, iha d h.1.2, ihb d h.2⟩
  case write f a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb d h.2⟩
  case arith op a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb d h.2⟩
  case elemAt a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb d h.2⟩
  case index a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb d h.2⟩
  case merge dr a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb d h.2⟩
  case makeKey a b iha ihb =>
    intro d h; simp only [FreeSlotsOk]
    simp only [freeSlotsNotIn, Bool.and_eq_true] at h
    exact ⟨iha d h.1, ihb d h.2⟩
  case read f a iha =>
    intro d h; simp only [FreeSlotsOk]; exact iha d h
  case test k a iha =>
    intro d h; simp only [FreeSlotsOk]; exact iha d h
  case lenOf a iha =>
    intro d h; simp only [FreeSlotsOk]; exact iha d h
  case spread a iha =>
    intro d h; simp only [FreeSlotsOk]; exact iha d h
  case throw a iha =>
    intro d h; simp only [FreeSlotsOk]; exact iha d h
  all_goals
    intro d h
    simp [freeSlotsNotIn, FreeSlotsOk] at h ⊢

/-! ## Confined-effect footprints -/

/-- Whether a footprint modifies only locations inside `owned` (non-spine fields)
or `ownedArr` (cells, or spines at `≤ .grow`). Every other location is strictly
`.keep` (necessary because `InitStep` and `ScalarStep` admit object values). -/
def frameConfined (owned ownedArr : List Nat) (Φ : Footprint) : Bool :=
  Φ.all fun (R, δ) =>
    δ == .keep ||
    owned.any (fun x => regionSub R (.fields x)) ||
    ownedArr.any (fun x => regionSub R (.cells x)) ||
    (δ != .any && ownedArr.any (fun x => regionSub R (.spine x [])))

private theorem spineCells_role_elem {n : Nat} {W : WorldT n} {h : Heap} {v : Val} {c : Nat}
    (hok : HeapOk n W h) (hv : RefsOk W v) (hc : some c ∈ spineCells h v) :
    roleAt W c = some .elem := by
  have from_spine : ∀ {s : Nat}, (∃ sf, roleAt W s = some (.spine sf)) →
      some c ∈ entriesAt h (some s) → roleAt W c = some .elem := by
    intro s ⟨sf, hrs⟩ hm
    obtain ⟨u, hu, hcat, hoku⟩ := hok.2 s (.spine sf) hrs
    simp only [entriesAt, hu, Option.bind_some] at hm
    cases sf with
    | array =>
      obtain ⟨ls, rfl⟩ := hcat
      simp only [spineEntries, Option.getD_some] at hm
      have hr : Ref.elem c ∈ refs (.arr ls) := by
        simp only [refs, spineRefs, List.mem_filterMap]; exact ⟨some c, hm, rfl⟩
      exact hoku _ hr
    | view fmt len =>
      obtain ⟨cs, rfl, -⟩ := hcat
      simp only [spineEntries, Option.getD_some, List.mem_map, Option.some.injEq] at hm
      obtain ⟨c', hc', hcc⟩ := hm
      subst hcc
      have hr : Ref.elem c' ∈ refs (.viewSpine fmt cs) := by
        simp only [refs, List.mem_map]; exact ⟨c', hc', rfl⟩
      exact hoku _ hr
  simp only [spineCells, List.mem_append] at hc
  rcases hc with hc | hc
  · cases ho : (fieldsOf v).lookup arraySpineKey with
    | none => simp [ho, entriesAt] at hc
    | some s =>
      rw [ho] at hc
      cases v with
      | objAt fs cc oid =>
        simp only [fieldsOf] at ho
        have hsr : SlotRole arraySpineKey (roleAt W s) :=
          hv _ (TolerantFrames.Reach.slot_mem_refs (c := cc) (i := oid) (lookup_mem_pair ho))
        cases hrs : roleAt W s with
        | none => rw [hrs] at hsr; exact hsr.elim
        | some r =>
          cases r with
          | spine sf => exact from_spine ⟨sf, hrs⟩ hc
          | field _ => rw [hrs] at hsr; exact (hsr.2 rfl).elim
          | cell _ => rw [hrs] at hsr; exact (hsr.2 rfl).elim
          | elem | identity => rw [hrs] at hsr; exact hsr.elim
      | _ => simp [fieldsOf] at ho
  · cases hd : HeapKnowledge.descriptorSpine v with
    | none => simp [hd, entriesAt] at hc
    | some s =>
      rw [hd] at hc
      cases v with
      | objAt fs cc oid =>
        cases cc with
        | view s' fmt len =>
          simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hd
          subst hd
          have hsr := hv _ (by simp [refs] :
            Ref.view s' fmt len (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view s' fmt len) oid))
          exact from_spine ⟨.view fmt len, hsr.2⟩ hc
        | _ => simp [HeapKnowledge.descriptorSpine] at hd
      | _ => simp [HeapKnowledge.descriptorSpine] at hd

private theorem spineCells_lt {n : Nat} {W : WorldT n} {h : Heap} {v : Val} {c : Nat}
    (hok : HeapOk n W h) (hv : RefsOk W v) (hc : some c ∈ spineCells h v) : c < h.length := by
  have hlenW : (entries W).length = h.length := by
    have := hok.1.1; simp only [toList, List.length_map] at this; exact this.symm
  have := roleAt_lt (spineCells_role_elem hok hv hc)
  omega

/-- A `Post Φ` transition whose footprint is `frameConfined` leaves every
allocated location outside `Priv` unchanged, and keeps `OwnedArrays` under the
extended private set `Priv ∪ [h.length, h'.length)`. -/
theorem frameConfined_sound {n n' : Nat} {W : WorldT n} {W' : WorldT n'} {Φ : Footprint}
    {ρ : Env} {h h' : Heap} {owned ownedArr : List Nat} {Priv : Nat → Prop}
    (hc : frameConfined owned ownedArr Φ = true)
    (hpost : Post Φ ρ h h')
    (hok : HeapOk n W h) (hok' : HeapOk n' W' h')
    (hof : OwnedFields ρ owned Priv) (hoa : OwnedArrays h ρ ownedArr Priv)
    (hρ : ∀ i, RefsOk W (ρ i)) (hρ' : ∀ i, RefsOk W' (ρ i)) :
    (∀ m, m < h.length → ¬ Priv m → h'[m]? = h[m]?) ∧
    OwnedArrays h' ρ ownedArr (fun loc => Priv loc ∨ (h.length ≤ loc ∧ loc < h'.length)) := by
  have hall := List.all_eq_true.mp hc
  have hlenW : (entries W).length = h.length := by
    have := hok.1.1; simp only [toList, List.length_map] at this; exact this.symm
  have hkeep : ∀ m, m < h.length → ¬ Priv m → h'[m]? = h[m]? := by
    intro m hm hnp
    obtain ⟨v, hv⟩ : ∃ v, h[m]? = some v := ⟨h[m], List.getElem?_eq_getElem hm⟩
    obtain ⟨v', hv', hal⟩ := hpost.2 m v hv
    rcases hal with rfl | ⟨⟨R, δ⟩, hmem, hrm, hch⟩
    · rw [hv', hv]
    · have h1 := hall (R, δ) hmem
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, List.any_eq_true] at h1
      rcases h1 with ((rfl | ⟨x, hx, hsub⟩) | ⟨x, hx, hsub⟩) | ⟨_, x, hx, hsub⟩
      · simp only [Change.Holds] at hch; rw [hch] at hv'; rw [hv', hv]
      · have hm' := regionSub_mem hsub hrm
        simp only [Region.mem, List.contains_iff_mem] at hm'
        exact absurd (hof x hx m hm') hnp
      · have hm' := regionSub_mem hsub hrm
        simp only [Region.mem, List.contains_iff_mem] at hm'
        exact absurd ((hoa x hx).2 m hm') hnp
      · have hm' := regionSub_mem hsub hrm
        simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hm'
        exact absurd ((hoa x hx).1 m hm') hnp
  refine ⟨hkeep, fun x hx => ⟨fun loc hl => .inl ((hoa x hx).1 loc hl), fun loc hl => ?_⟩⟩
  have hloc_lt : loc < h'.length := spineCells_lt hok' (hρ' x) hl
  have spine_kept : ∀ {s : Nat} {sf}, roleAt W s = some (.spine sf) →
      (∀ c, some c ∈ entriesAt h (some s) → Priv c) →
      some loc ∈ entriesAt h' (some s) → Priv loc ∨ (h.length ≤ loc ∧ loc < h'.length) := by
    intro s sf hrs hold hc'
    have hslt : s < h.length := by have := roleAt_lt hrs; omega
    obtain ⟨v, hv⟩ : ∃ v, h[s]? = some v := ⟨h[s], List.getElem?_eq_getElem hslt⟩
    obtain ⟨v', hv', hal⟩ := hpost.2 s v hv
    have hsame_or_grow : v' = v ∨ Change.grow.Holds h.length v v' := by
      rcases hal with rfl | ⟨⟨R, δ⟩, hmem, hrm, hch⟩
      · exact .inl rfl
      · have h1 := hall (R, δ) hmem
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, List.any_eq_true] at h1
        rcases h1 with ((rfl | ⟨y, _, hsub⟩) | ⟨y, _, hsub⟩) | ⟨hne, _, _, _⟩
        · exact .inl hch
        · have hm' := regionSub_mem hsub hrm
          simp only [Region.mem, List.contains_iff_mem, fieldLocs, List.mem_map, List.mem_filter,
            bne_iff_ne] at hm'
          obtain ⟨⟨k, s'⟩, ⟨hpair, hk⟩, hs'⟩ := hm'
          subst hs'
          cases hy : ρ y
          case objAt fs cc oid =>
            rw [hy] at hpair; simp only [fieldsOf] at hpair
            have hsr : SlotRole k (roleAt W s') :=
              (hρ y) (.slot k s') (by rw [hy]; exact TolerantFrames.Reach.slot_mem_refs (c := cc) (i := oid) hpair)
            rw [hrs] at hsr
            cases sf <;> simp only [SlotRole] at hsr
            exact absurd hsr hk
          all_goals (rw [hy] at hpair; simp [fieldsOf] at hpair)
        · have hm' := regionSub_mem hsub hrm
          simp only [Region.mem, List.contains_iff_mem] at hm'
          have hel := spineCells_role_elem hok (hρ y) hm'
          rw [hrs] at hel; cases hel
        · have hle : δ.le .grow = true := by cases δ <;> simp_all [Change.le, Change.rank]
          exact .inr (Change.Holds.mono hle hch)
    simp only [entriesAt, hv', Option.bind_some] at hc'
    rcases hsame_or_grow with rfl | hgrow
    · exact .inl (hold loc (by simp only [entriesAt, hv, Option.bind_some]; exact hc'))
    · rcases hgrow with rfl | ⟨ls, ls', rfl, rfl, -, hnew, -⟩ | ⟨_, _, ha'⟩ | ⟨f, cs, cs', rfl, rfl, -, hnew⟩
      · exact .inl (hold loc (by simp only [entriesAt, hv, Option.bind_some]; exact hc'))
      · simp only [spineEntries, Option.getD_some] at hc'
        rcases hnew loc hc' with hold' | hge
        · exact .inl (hold loc (by simp [entriesAt, hv, spineEntries, hold']))
        · exact .inr ⟨hge, hloc_lt⟩
      · cases v' <;> simp_all [isArr, spineEntries]
      · simp only [spineEntries, Option.getD_some, List.mem_map, Option.some.injEq] at hc'
        obtain ⟨c₀, hc₀, hce⟩ := hc'
        rw [← hce] at hloc_lt ⊢
        rcases hnew c₀ hc₀ with hold' | hge
        · exact .inl (hold c₀ (by simp [entriesAt, hv, spineEntries, hold']))
        · exact .inr ⟨hge, hloc_lt⟩
  simp only [spineCells, List.mem_append] at hl
  rcases hl with hl | hl
  · cases ho : (fieldsOf (ρ x)).lookup arraySpineKey with
    | none => simp [ho, entriesAt] at hl
    | some s =>
      rw [ho] at hl
      cases hvx : ρ x
      case objAt fs cc oid =>
        rw [hvx] at ho; simp only [fieldsOf] at ho
        have hsr : SlotRole arraySpineKey (roleAt W s) :=
          (hρ x) (.slot arraySpineKey s) (by rw [hvx]; exact TolerantFrames.Reach.slot_mem_refs (c := cc) (i := oid) (lookup_mem_pair ho))
        cases hrs : roleAt W s with
        | none => rw [hrs] at hsr; exact hsr.elim
        | some r =>
          cases r with
          | spine sf =>
            exact spine_kept hrs (fun c hc => (hoa x hx).2 c (by
              simp only [spineCells, hvx, fieldsOf, ho, List.mem_append]; exact .inl hc)) hl
          | field _ => rw [hrs] at hsr; exact (hsr.2 rfl).elim
          | cell _ => rw [hrs] at hsr; exact (hsr.2 rfl).elim
          | elem | identity => rw [hrs] at hsr; exact hsr.elim
      all_goals (rw [hvx] at ho; simp [fieldsOf] at ho)
  · cases hd : HeapKnowledge.descriptorSpine (ρ x) with
    | none => simp [hd, entriesAt] at hl
    | some s =>
      rw [hd] at hl
      cases hvx : ρ x
      case objAt fs cc oid =>
        rw [hvx] at hd
        cases cc with
        | view s' fmt len =>
          simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hd
          subst hd
          have hsr := (hρ x) _ (by rw [hvx]; simp [refs] :
            Ref.view s' fmt len (fs.lookup arraySpineKey).isNone ∈ refs (ρ x))
          exact spine_kept hsr.2 (fun c hc => (hoa x hx).2 c (by
            simp only [spineCells, hvx, HeapKnowledge.descriptorSpine, List.mem_append]; exact .inr hc)) hl
        | _ => simp [HeapKnowledge.descriptorSpine] at hd
      all_goals (rw [hvx] at hd; simp [HeapKnowledge.descriptorSpine] at hd)

/-! ## Checked per-node confinement transition -/

section Check
variable {ι : Type} [DecidableEq ι]

/-- Check a step's derivation at the node's claim and step knowledge. -/
def derivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : HeapKnowledge.Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (ProgramCertificates.claim deriv).term == node.expression &&
    PromiseCalls.intRefines G c.context (ProgramCertificates.claim deriv).context stepK.indices &&
    (ProgramCertificates.checkTreeUsing G images deriv codes sums ||
      PromiseCalls.requiresTree G images stepK codes sums deriv)

theorem derivChecked_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node)
    (stepK : HeapKnowledge.Knowledge) (deriv : ProgramCertificates.Evidence ι) :
    derivChecked (reassign G η) (images.reassign η) codes sums c node stepK deriv =
      derivChecked G images codes sums c node stepK deriv := by
  simp only [derivChecked, Parametricity.checkTree_reassign, Parametricity.requiresTree_reassign,
    Parametricity.intRefines_reassign]

/-- Whether `t` is an object-literal allocation (not an array-object wrapper). -/
def isFreshObjectTerm : Tm → Bool
  | .makeAt .absent ns _ => !ns.contains arraySpineKey
  | .merge _ _ _ => true
  | .makeKey _ _ => true
  | _ => false

/-- Whether `t` is the lowered array-object wrapper `.makeAt .absent [arraySpineKey, proto] [.var si, .var pi]`
whose spine slot `si` is in `ownedSpines`. -/
def isFreshArrObjTerm (width : Nat) (ownedSpines : List Nat) : Tm → Bool
  | .makeAt .absent [k1, k2] [.var si, .var pi] =>
      k1 == arraySpineKey && k2 == CallArguments.protoField && ownedSpines.contains si && pi < width
  | .letE (.arrLit _) (.makeAt .absent [k1, k2] [.var 0, .var pi]) =>
      k1 == arraySpineKey && k2 == CallArguments.protoField && 0 < pi && pi - 1 < width
  | _ => false

/-- Whether a step derivation establishes a confined normal frame. -/
def confinedCallNormal (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : HeapKnowledge.Knowledge)
    (deriv : Option (ProgramCertificates.Evidence ι)) (pre : NodeConf) : Bool :=
  match deriv with
  | some d =>
      derivChecked G images codes sums c node stepK d &&
      ExpressionEffects.selectedOperands d &&
      match ExpressionEffects.selectedEffect d with
      | some eff => frameConfined pre.owned pre.ownedArr (PromiseCalls.callerFrame eff node.expression)
      | none => false
  | none => false

theorem confinedCallNormal_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node)
    (stepK : HeapKnowledge.Knowledge) (deriv : Option (ProgramCertificates.Evidence ι)) (pre : NodeConf) :
    confinedCallNormal (reassign G η) (images.reassign η) codes sums c node stepK deriv pre =
      confinedCallNormal G images codes sums c node stepK deriv pre := by
  cases deriv with
  | none => rfl
  | some d => simp only [confinedCallNormal, derivChecked_reassign]

/-- Graph-independent core of `nodePostN`, factored over `isInert` and `isConfCall`. -/
def nodePostNCore (width : Nat) (expr : Tm) (isInert isConfCall : Bool)
    (pre : NodeConf) (allocIntoPriv : Bool) : NodeConf :=
  let sh := pre.shift
  let unreach := freeSlotsNotIn width 0 pre.holders expr
  if Purity.inspectTerm expr && checkScope width expr then
    if isFreshArrObjTerm width pre.ownedSpines expr then
      if allocIntoPriv then
        { sh with owned := 0 :: sh.owned, ownedArr := 0 :: sh.ownedArr, holders := 0 :: sh.holders }
      else if unreach then sh
      else {}
    else if isFreshObjectTerm expr then
      if allocIntoPriv then
        { sh with owned := 0 :: sh.owned, holders := 0 :: sh.holders }
      else if unreach then sh
      else {}
    else if expr matches .arrLit _ then
      if allocIntoPriv then
        { sh with ownedSpines := 0 :: sh.ownedSpines, holders := 0 :: sh.holders }
      else if unreach then sh
      else {}
    else if unreach then sh
    else if isInert then sh
    else match expr with
      | .var i =>
          if i < width then
            { owned := if pre.owned.contains i then 0 :: sh.owned else sh.owned
              ownedArr := if pre.ownedArr.contains i then 0 :: sh.ownedArr else sh.ownedArr
              ownedSpines := if pre.ownedSpines.contains i then 0 :: sh.ownedSpines else sh.ownedSpines
              holders := if pre.holders.contains i then 0 :: sh.holders else sh.holders }
          else {}
      | _ => { sh with holders := 0 :: sh.holders }
  else if unreach then
    sh
  else
    match expr with
    | .writeAt f (.var x) (.var y) =>
        if f != arraySpineKey && x < width && y < width &&
            (!pre.holders.contains y || pre.owned.contains x) then
          sh
        else {}
    | _ =>
        if isConfCall then
          if isInert then sh else { sh with holders := 0 :: sh.holders }
        else {}

/-- The post-step normal `NodeConf` (over `push v ρ`, width `c.context.length + 1`)
determined by the checked rule at node `l`. -/
def nodePostN (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (node : Node) (c : PointClaim ι)
    (stepK : HeapKnowledge.Knowledge) (deriv : Option (ProgramCertificates.Evidence ι))
    (pre : NodeConf) (allocIntoPriv : Bool) : NodeConf :=
  nodePostNCore c.context.length node.expression (inertTy G c.type)
    (confinedCallNormal G images codes sums c node stepK deriv pre) pre allocIntoPriv

/-- The post-step exceptional `NodeConf`: resets `Priv` to empty on handler
edges, matching the single pass's `dropHeap`. -/
def nodePostE : NodeConf := {}

/-- Whether an edge from `post` (width `srcWidth + 1`, with result at slot `0`)
with `pushed` and `mapping` delivers `dst` (at width `dstWidth`). -/
def edgeOk (post : NodeConf) (srcWidth : Nat) (pushed : Bool) (mapping : Mapping)
    (dstWidth : Nat) (dst : NodeConf) : Bool :=
  let idx := fun i => if pushed then i else i + 1
  dst.owned.all (fun j => j < dstWidth && post.owned.contains (idx (slot mapping j))) &&
  dst.ownedArr.all (fun j => j < dstWidth && post.ownedArr.contains (idx (slot mapping j))) &&
  dst.ownedSpines.all (fun j => j < dstWidth && post.ownedSpines.contains (idx (slot mapping j))) &&
  (List.range dstWidth).all fun j =>
    dst.holders.contains j || (idx (slot mapping j) < srcWidth + 1 && !post.holders.contains (idx (slot mapping j)))

/-- Normal exits of a node, matching `SinglePass.Exit.ofNode`. -/
def normalExits (node : Node) : List (Target × Bool) :=
  match node.continuation with
  | .ret => []
  | .bind t => [(t, true)]
  | .effect t => [(t, false)]
  | .branch y m => [(y, false), (m, false)]
  | .branchBind y m => [(y, true), (m, true)]
  | .tagBind _ y m => [(y, true), (m, true)]

/-- Check one visited node `l` of `conf`. -/
def checkNode (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (claims : List (PointClaim ι)) (conf : Table) (l : Nat)
    (node : Node) (c : PointClaim ι) (stepK : HeapKnowledge.Knowledge)
    (deriv : Option (ProgramCertificates.Evidence ι)) : Bool :=
  let pre := conf.at l
  let width := c.context.length
  let framedOk := !conf.framedNodes.contains l || freeSlotsNotIn width 0 pre.holders node.expression
  let postN := nodePostN G images codes sums node c stepK deriv pre (conf.allocPriv.contains l)
  let dstW := fun lbl => ((claims[lbl]?).map (·.context.length)).getD 0
  let normOk := (normalExits node).all fun (t, pushed) =>
    edgeOk postN width pushed t.mapping (dstW t.label) (conf.at t.label)
  let handOk := match node.handler with
    | none => true
    | some t =>
        let dst := conf.at t.label
        dst.owned.isEmpty && dst.ownedArr.isEmpty && dst.ownedSpines.isEmpty
  framedOk && normOk && handOk

theorem nodePostN_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (node : Node) (c : PointClaim ι)
    (stepK : HeapKnowledge.Knowledge) (deriv : Option (ProgramCertificates.Evidence ι))
    (pre : NodeConf) (allocIntoPriv : Bool) :
    nodePostN (reassign G η) (images.reassign η) codes sums node c stepK deriv pre allocIntoPriv =
      nodePostN G images codes sums node c stepK deriv pre allocIntoPriv := by
  simp only [nodePostN, inertTy_reassign, confinedCallNormal_reassign]

theorem checkNode_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ReadSummary ι)) (claims : List (PointClaim ι))
    (conf : Table) (l : Nat) (node : Node) (c : PointClaim ι) (stepK : HeapKnowledge.Knowledge)
    (deriv : Option (ProgramCertificates.Evidence ι)) :
    checkNode (reassign G η) (images.reassign η) codes sums claims conf l node c stepK deriv =
      checkNode G images codes sums claims conf l node c stepK deriv := by
  simp only [checkNode, nodePostN_reassign]

/-! ## Soundness of `checkNode` -/

/-- The semantic confinement invariant at `(l, ρ, h)` relative to entry heap
length `m₀`: there exists a set of private locations `Priv ⊆ [m₀, h.length)`
closed from outside (`ClosedOut h Priv`) containing all owned fields, arrays
and spines of `conf.at l`, and disjoint from every slot `< width` outside
`(conf.at l).holders`. -/
def ConfinedAt (conf : Table) (width : Nat → Nat) (l : Nat) (ρ : Env) (m₀ : Nat) (h : Heap) : Prop :=
  let nc := conf.at l
  ∃ Priv : Nat → Prop,
    (∀ loc, Priv loc → m₀ ≤ loc ∧ loc < h.length) ∧
    ClosedOut h Priv ∧
    OwnedFields ρ nc.owned Priv ∧
    OwnedArrays h ρ nc.ownedArr Priv ∧
    OwnedSpines ρ nc.ownedSpines Priv ∧
    HoldersCoverB (width l) ρ nc.holders Priv

/-- Empty confinement holds at every heap and environment (`Priv = ∅`). -/
theorem confinedAt_empty {conf : Table} {width : Nat → Nat} {l : Nat} {ρ : Env} {m₀ : Nat} {h : Heap}
    (he : conf.at l = {}) : ConfinedAt conf width l ρ m₀ h := by
  refine ⟨fun _ => False, fun _ hf => False.elim hf, ClosedOut.empty h, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [he] at hx; cases hx
  · intro x hx; rw [he] at hx; cases hx
  · intro x hx; rw [he] at hx; cases hx
  · intro y _ _ _ _ hf; exact hf

/-- `ConfinedAt` is preserved by an edge passing `edgeOk`. -/
theorem confinedAt_edge {conf : Table} {width : Nat → Nat} {post : NodeConf} {srcWidth : Nat}
    {pushed : Bool} {mapping : Mapping} {t : Nat} {ρ : Env} {v : Val} {m₀ : Nat} {h : Heap}
    {Priv : Nat → Prop}
    (he : edgeOk post srcWidth pushed mapping (width t) (conf.at t) = true)
    (hbd : ∀ loc, Priv loc → m₀ ≤ loc ∧ loc < h.length)
    (hcl : ClosedOut h Priv)
    (hof : OwnedFields (push v ρ) post.owned Priv)
    (hoa : OwnedArrays h (push v ρ) post.ownedArr Priv)
    (hos : OwnedSpines (push v ρ) post.ownedSpines Priv)
    (hhl : HoldersCoverB (srcWidth + 1) (push v ρ) post.holders Priv) :
    ConfinedAt conf width t (mapEnv mapping (if pushed then push v ρ else ρ)) m₀ h := by
  simp only [edgeOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.contains_iff_mem, decide_eq_true_eq] at he
  obtain ⟨⟨⟨hO, hA⟩, hS⟩, hH⟩ := he
  have hpush : ∀ k, (if pushed then push v ρ else ρ) k = push v ρ (if pushed then k else k + 1) := by
    intro k; cases pushed <;> rfl
  refine ⟨Priv, hbd, hcl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h1 := (hO x hx).2
    simp only [mapEnv, hpush]
    exact hof _ h1
  · intro x hx
    have h1 := (hA x hx).2
    simp only [mapEnv, hpush]
    exact hoa _ h1
  · intro x hx
    have h1 := (hS x hx).2
    simp only [mapEnv, hpush]
    exact hos _ h1
  · intro y hy hnm
    rcases hH y hy with hm | ⟨hlt, hnp⟩
    · exact absurd hm hnm
    · simp only [mapEnv, hpush]
      exact hhl _ hlt (fun hm => by rw [List.contains_iff_mem.mpr hm] at hnp; cases hnp)

/-- Shifting `OwnedFields` / `OwnedArrays` / `OwnedSpines` / `HoldersCoverB` across `push v ρ`. -/
private theorem shift_ownedFields {ρ : Env} {v : Val} {xs : List Nat} {Priv : Nat → Prop}
    (h : OwnedFields ρ xs Priv) : OwnedFields (push v ρ) (xs.map (· + 1)) Priv := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  simpa [push] using h y hy

private theorem shift_ownedArrays {hp : Heap} {ρ : Env} {v : Val} {xs : List Nat} {Priv : Nat → Prop}
    (h : OwnedArrays hp ρ xs Priv) : OwnedArrays hp (push v ρ) (xs.map (· + 1)) Priv := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  simpa [push] using h y hy

private theorem shift_ownedSpines {ρ : Env} {v : Val} {xs : List Nat} {Priv : Nat → Prop}
    (h : OwnedSpines ρ xs Priv) : OwnedSpines (push v ρ) (xs.map (· + 1)) Priv := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  simpa [push] using h y hy

private theorem shift_holdersCoverB {width : Nat} {ρ : Env} {v : Val} {hs : List Nat} {Priv : Nat → Prop}
    (hv : NoPriv Priv v) (h : HoldersCoverB width ρ hs Priv) :
    HoldersCoverB (width + 1) (push v ρ) (hs.map (· + 1)) Priv := by
  intro y hy hnm
  cases y with
  | zero => simpa [push] using hv
  | succ k =>
    have hk : k ∉ hs := fun hkm => hnm (List.mem_map.mpr ⟨k, hkm, rfl⟩)
    simpa [push] using h k (by omega) hk

private theorem shift_holdersCoverB_add0 {width : Nat} {ρ : Env} {v : Val} {hs : List Nat} {Priv : Nat → Prop}
    (h : HoldersCoverB width ρ hs Priv) :
    HoldersCoverB (width + 1) (push v ρ) (0 :: hs.map (· + 1)) Priv := by
  intro y hy hnm
  cases y with
  | zero => exact absurd (List.mem_cons_self) hnm
  | succ k =>
    have hk : k ∉ hs := fun hkm => hnm (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, hkm, rfl⟩))
    simpa [push] using h k (by omega) hk

private theorem noPriv_ext {n : Nat} {W : WorldT n} {h h' : Heap} {Priv : Nat → Prop} {v : Val}
    (hok : HeapOk n W h) (hv : RefsOk W v) (hno : NoPriv Priv v) :
    NoPriv (fun loc => Priv loc ∨ (h.length ≤ loc ∧ loc < h'.length)) v := by
  have hlenW : (entries W).length = h.length := by
    have := hok.1.1; simp only [toList, List.length_map] at this; exact this.symm
  intro l hl hp'
  rcases hp' with hp | ⟨hge, _⟩
  · exact hno l hl hp
  · have hlt : l < h.length := by
      have htb := refsOk_tmRefsBelow hok hv
      -- Directly from `leaves_lt_of_refsOkN` through `RefsOk` on a value:
      by_cases hi : Inert allC v
      · exact False.elim ((NoPriv.of_inert hi (Priv := fun _ => True)) l hl trivial)
      · exact htb v (vals_all allC _ .empty true false (mem_vals_self hi)) l hl
    omega

/-- Multi-step heap prefix for `Purity.inspectTerm`. -/
private theorem inspect_steps_prefix : ∀ {k : Nat} {h h' : Heap} {t t' : Tm},
    Steps k h t h' t' → Purity.inspectTerm t = true → HeapVals h → h.IsPrefix h' := by
  intro k
  induction k with
  | zero =>
    intro h h' t t' hst _ _
    cases hst; exact List.prefix_refl _
  | succ k ih =>
    intro h h' t t' hst hp hh
    cases hst with
    | next hs hrest =>
      obtain ⟨hpref, hp'⟩ := Purity.inspect_step hs hp hh
      exact hpref.trans (ih hrest hp' (step_heapVals hs hh))

private theorem prefix_keep {h h' : Heap} (hp : h.IsPrefix h') :
    h.length ≤ h'.length ∧ ∀ m, m < h.length → h'[m]? = h[m]? := by
  obtain ⟨xs, rfl⟩ := hp
  exact ⟨by simp, fun m hm => List.getElem?_append_left hm⟩



/-- When every location of `Priv` keeps its exact contents from `h` to `h'`,
`OwnedArrays` is preserved. -/
private theorem ownedArrays_of_same {n : Nat} {W : WorldT n} {h h' : Heap} {ρ : Env} {ownedArr : List Nat}
    {Priv : Nat → Prop} (hoa : OwnedArrays h ρ ownedArr Priv) (hρ : ∀ i, RefsOk W (ρ i))
    (hsame : ∀ loc, Priv loc → h'[loc]? = h[loc]?) :
    OwnedArrays h' ρ ownedArr Priv := by
  intro y hy
  refine ⟨(hoa y hy).1, fun loc hl => ?_⟩
  have hsc_eq : spineCells h' (ρ y) = spineCells h (ρ y) := by
    unfold spineCells; congr 1
    · cases ho : (fieldsOf (ρ y)).lookup arraySpineKey with
      | none => rfl
      | some sp =>
        have hsp : Priv sp := (hoa y hy).1 sp (by
          cases hvx : ρ y
          case objAt fs cc oid => rw [hvx] at ho; simp only [fieldsOf] at ho; simp [HeapKnowledge.elementsOf, ho]
          all_goals (rw [hvx] at ho; simp [fieldsOf] at ho))
        simp [entriesAt, hsame sp hsp]
    · cases hd : HeapKnowledge.descriptorSpine (ρ y) with
      | none => rfl
      | some sp =>
        have hsp : Priv sp := (hoa y hy).1 sp (by
          cases hvx : ρ y
          case objAt fs cc oid =>
            rw [hvx] at hd
            cases cc with
            | view s' fmt len =>
              simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hd
              subst hd
              have hsr := (hρ y) _ (by rw [hvx]; simp [refs] :
                Ref.view s' fmt len (fs.lookup arraySpineKey).isNone ∈ refs (ρ y))
              have hnone : fs.lookup arraySpineKey = none := Option.isNone_iff_eq_none.mp hsr.1
              simp [HeapKnowledge.elementsOf, hnone]
            | _ => simp [HeapKnowledge.descriptorSpine] at hd
          all_goals (rw [hvx] at hd; simp [HeapKnowledge.descriptorSpine] at hd))
        simp [entriesAt, hsame sp hsp]
  exact (hoa y hy).2 loc (by rw [← hsc_eq]; exact hl)

/-- **Single-node soundness of `checkNode`** (normal exits and framed return):
given `ConfinedAt` on entry of node `l`, `checkNode = true`, `TmRefsBelow m₀ node.expression`,
and a normal run `Steps k s.h (instantiate 0 ρ node.expression) s'.h v`:
1. If `l ∈ conf.framedNodes`, then `Supported (confinedFootprint pre.owned pre.ownedArr) ρ s.h s'.h`.
2. For every normal exit `(t, pushed) ∈ normalExits node`, `ConfinedAt` holds at `t.label`! -/
theorem checkNode_sound_normal {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {claims : List (PointClaim ι)} {conf : Table} {l : Nat}
    {node : Node} {c : PointClaim ι} {stepK : HeapKnowledge.Knowledge}
    {deriv : Option (ProgramCertificates.Evidence ι)} {ε : HeapKnowledge.EntryState}
    {ρ : Env} {m₀ : Nat} {s s' : TolerantFrames.IndexedHeap} {k : Nat} {v : Val}
    (hchk : checkNode G images codes sums claims conf l node c stepK deriv = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    (hwl : ((claims[l]?).map (·.context.length)).getD 0 = c.context.length)
    (he : EnvOk G c.context ρ s.n s.W) (he' : EnvOk G (c.type :: c.context) (push v ρ) s'.n s'.W)
    (hρ_ok : ∀ i, RefsOk s.W (ρ i)) (hρ'_ok : ∀ i, RefsOk s'.W (ρ i))
    (hkS : HeapKnowledge.Holds stepK ε ρ s.h)
    (hm₀ : m₀ ≤ s.h.length)
    (htb : TmRefsBelow m₀ node.expression)
    (hconf : ConfinedAt conf (fun lbl => ((claims[lbl]?).map (·.context.length)).getD 0) l ρ m₀ s.h)
    (hval : isVal v = true)
    (href : RefsOk s.W (instantiate 0 ρ node.expression))
    (hsteps : Steps k s.h (instantiate 0 ρ node.expression) s'.h v) (hkn : k < s.n) :
    (l ∈ conf.framedNodes →
      Supported (confinedFootprint (conf.at l).owned (conf.at l).ownedArr) ρ s.h s'.h) ∧
    ∀ t pushed, (t, pushed) ∈ normalExits node →
      ConfinedAt conf (fun lbl => ((claims[lbl]?).map (·.context.length)).getD 0)
        t.label (mapEnv t.mapping (if pushed then push v ρ else ρ)) m₀ s'.h := by
  let widthFn : Nat → Nat := fun (lbl : Nat) => ((claims[lbl]?).map fun (pc : PointClaim ι) => pc.context.length).getD 0
  let pre := conf.at l
  have hval_lt : ∀ i, i < c.context.length → isVal (ρ i) = true := fun i hi =>
    (meaning_value (he.2 i (c.context[i]'hi) (List.getElem?_eq_getElem hi))).1
  simp only [checkNode, Bool.and_eq_true] at hchk
  obtain ⟨⟨hfrOk, hnormOk⟩, _⟩ := hchk
  obtain ⟨Priv, hbd, hcl, hof, hoa, hos, hhl⟩ := hconf
  dsimp only at hhl; rw [hwl] at hhl
  have hge : ∀ loc, Priv loc → m₀ ≤ loc := fun loc hp => (hbd loc hp).1
  have hlt : ∀ loc, Priv loc → loc < s.h.length := fun loc hp => (hbd loc hp).2
  have hlen : s.h.length ≤ s'.h.length := by
    have key : ∀ {j h₁ h₂ t₁ t₂}, Steps j h₁ t₁ h₂ t₂ → h₁.length ≤ h₂.length := by
      intro j h₁ h₂ t₁ t₂ hst
      induction hst with
      | refl => exact Nat.le_refl _
      | next hs _ ih => exact Nat.le_trans (Footprints.step_length_le hs) ih
    exact key hsteps

  have unreach_run : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true →
      (∀ loc, Priv loc → s'.h[loc]? = s.h[loc]?) ∧ ClosedOut s'.h Priv ∧ NoPriv Priv v := by
    intro hun
    have hhlv : ∀ y, y < c.context.length → y ∉ pre.holders → isVal (ρ y) = true ∧ NoPriv Priv (ρ y) :=
      fun y hy hnm => ⟨hval_lt y hy, hhl y hy hnm⟩
    have hf := freeSlotsNotIn_sound hhlv node.expression 0 hun
    have hroots := instantiate_noPriv_empty hge htb hf
    obtain ⟨hsame, hcl', hr'⟩ := steps_confined_unreachable (heapVals_of_indexed s) hsteps hlt hcl hroots
    exact ⟨hsame, hcl', noPriv_of_val hr'⟩
  have hframed : l ∈ conf.framedNodes →
      Supported (confinedFootprint pre.owned pre.ownedArr) ρ s.h s'.h := by
    intro hmem
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hfrOk
    rcases hfrOk with hnm | hun
    · rw [List.contains_iff_mem.mpr hmem] at hnm; cases hnm
    · exact confinedFootprint_supported hof hoa (unreach_run hun).1
  refine ⟨hframed, fun t pushed hmem => ?_⟩
  have hedge := List.all_eq_true.mp hnormOk (t, pushed) hmem
  let postN := nodePostN G images codes sums node c stepK deriv pre (conf.allocPriv.contains l)
  suffices hpost : ∃ Priv' : Nat → Prop,
      (∀ loc, Priv' loc → m₀ ≤ loc ∧ loc < s'.h.length) ∧
      ClosedOut s'.h Priv' ∧
      OwnedFields (push v ρ) postN.owned Priv' ∧
      OwnedArrays s'.h (push v ρ) postN.ownedArr Priv' ∧
      OwnedSpines (push v ρ) postN.ownedSpines Priv' ∧
      HoldersCoverB (c.context.length + 1) (push v ρ) postN.holders Priv' by
    obtain ⟨Priv', h1, h2, h3, h4, h5, h6⟩ := hpost
    exact confinedAt_edge (width := widthFn) hedge h1 h2 h3 h4 h5 h6
  let PrivExt : Nat → Prop := fun loc => Priv loc ∨ (s.h.length ≤ loc ∧ loc < s'.h.length)
  have hbd_ext : ∀ loc, PrivExt loc → m₀ ≤ loc ∧ loc < s'.h.length := by
    intro loc hp
    rcases hp with hp | ⟨h1, h2⟩
    · exact ⟨(hbd loc hp).1, Nat.lt_of_lt_of_le (hbd loc hp).2 hlen⟩
    · exact ⟨Nat.le_trans hm₀ h1, h2⟩
  have hof_ext : OwnedFields (push v ρ) pre.shift.owned PrivExt :=
    fun x hx loc hl => .inl (shift_ownedFields hof x hx loc hl)
  have hos_ext : OwnedSpines (push v ρ) pre.shift.ownedSpines PrivExt := by
    intro x hx
    obtain ⟨ls, hls, hall⟩ := shift_ownedSpines hos x hx
    exact ⟨ls, hls, fun loc hl => .inl (hall loc hl)⟩
  have hhl_ext : HoldersCoverB c.context.length ρ pre.holders PrivExt :=
    fun y hy hnm => noPriv_ext s.ok (hρ_ok y) (hhl y hy hnm)
  have hEmpty : ∃ Priv' : Nat → Prop,
      (∀ loc, Priv' loc → m₀ ≤ loc ∧ loc < s'.h.length) ∧
      ClosedOut s'.h Priv' ∧
      OwnedFields (push v ρ) ({} : NodeConf).owned Priv' ∧
      OwnedArrays s'.h (push v ρ) ({} : NodeConf).ownedArr Priv' ∧
      OwnedSpines (push v ρ) ({} : NodeConf).ownedSpines Priv' ∧
      HoldersCoverB (c.context.length + 1) (push v ρ) ({} : NodeConf).holders Priv' :=
    ⟨fun _ => False, fun _ h => False.elim h, ClosedOut.empty _,
      (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h), (fun _ _ _ _ _ h => h)⟩
  have hShiftUnreach : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true →
      ∃ Priv' : Nat → Prop,
        (∀ loc, Priv' loc → m₀ ≤ loc ∧ loc < s'.h.length) ∧
        ClosedOut s'.h Priv' ∧
        OwnedFields (push v ρ) pre.shift.owned Priv' ∧
        OwnedArrays s'.h (push v ρ) pre.shift.ownedArr Priv' ∧
        OwnedSpines (push v ρ) pre.shift.ownedSpines Priv' ∧
        HoldersCoverB (c.context.length + 1) (push v ρ) pre.shift.holders Priv' := by
    intro hun
    obtain ⟨hsame, hcl', hnov⟩ := unreach_run hun
    exact ⟨Priv, fun loc hp => ⟨(hbd loc hp).1, Nat.lt_of_lt_of_le (hbd loc hp).2 hlen⟩, hcl',
      shift_ownedFields hof, shift_ownedArrays (ownedArrays_of_same hoa hρ_ok hsame),
      shift_ownedSpines hos, shift_holdersCoverB hnov hhl⟩
  dsimp only [postN, nodePostN, nodePostNCore]
  by_cases hinsp : (Purity.inspectTerm node.expression && checkScope c.context.length node.expression) = true
  · simp only [hinsp, ↓reduceIte]
    simp only [Bool.and_eq_true] at hinsp
    have hinst : Purity.inspectTerm (instantiate 0 ρ node.expression) = true :=
      HeapExpressionRules.inspect_instantiate (d := 0) hinsp.1 (by simpa using hinsp.2) he
    have hpref := inspect_steps_prefix hsteps hinst (heapVals_of_indexed s)
    obtain ⟨_, hkeep⟩ := prefix_keep hpref
    have hcl_ext : ClosedOut s'.h PrivExt := closedOut_of_keep_outside s.ok hcl (fun m hm _ => hkeep m hm)
    have hoa_ext : OwnedArrays s'.h (push v ρ) pre.shift.ownedArr PrivExt := by
      have hoa' := ownedArrays_of_same hoa hρ_ok (fun loc hp => hkeep loc (hlt loc hp))
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨fun loc hl => .inl ((hoa' y hy).1 loc (by simpa [push] using hl)),
             fun loc hl => .inl ((hoa' y hy).2 loc (by simpa [push] using hl))⟩
    by_cases hfarr : isFreshArrObjTerm c.context.length pre.ownedSpines node.expression = true
    · simp only [hfarr, ↓reduceIte]
      by_cases halloc : conf.allocPriv.contains l = true
      · simp only [halloc, ↓reduceIte]
        cases hex : node.expression with
        | makeAt cc ns args =>
          rw [hex] at hfarr
          cases cc with
          | bound _ _ _ => simp [isFreshArrObjTerm] at hfarr
          | graph _ _ _ _ _ _ _ _ => simp [isFreshArrObjTerm] at hfarr
          | view _ _ _ => simp [isFreshArrObjTerm] at hfarr
          | absent =>
          cases ns with
          | nil => simp [isFreshArrObjTerm] at hfarr
          | cons k1 ns' =>
            cases ns' with
            | nil => simp [isFreshArrObjTerm] at hfarr
            | cons k2 ns'' =>
              cases ns'' with
              | cons _ _ => simp [isFreshArrObjTerm] at hfarr
              | nil =>
                cases args with
                | nil => simp [isFreshArrObjTerm] at hfarr
                | cons a1 args' =>
                  cases args' with
                  | nil => simp [isFreshArrObjTerm] at hfarr
                  | cons a2 args'' =>
                    cases args'' with
                    | cons _ _ => simp [isFreshArrObjTerm] at hfarr
                    | nil =>
                      cases a1 with
                      | var si =>
                        cases a2 with
                        | var pi =>
                      simp only [isFreshArrObjTerm, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
                        decide_eq_true_eq] at hfarr
                      obtain ⟨⟨⟨rfl, rfl⟩, hsi⟩, hpi⟩ := hfarr
                      obtain ⟨ls, hls, hls_priv⟩ := hos si hsi
                      rw [hex] at hsteps
                      simp only [instantiate, instantiateArgs, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, hls] at hsteps
                      obtain ⟨hff, hfe, hfc⟩ := steps_makeArrObj_fresh (hval_lt pi hpi) hval hsteps
                      refine ⟨PrivExt, hbd_ext, hcl_ext, ?_, ?_, hos_ext, shift_holdersCoverB_add0 hhl_ext⟩
                      · intro x hx
                        rcases List.mem_cons.mp hx with rfl | hx
                        · intro loc hl; exact .inr (hff loc (by simpa [push] using hl))
                        · exact hof_ext x hx
                      · intro x hx
                        rcases List.mem_cons.mp hx with rfl | hx
                        · refine ⟨fun loc hl => .inr (hfe loc (by simpa [push] using hl)),
                            fun loc hl => .inl (hls_priv loc (hfc loc (by simpa [push] using hl)))⟩
                        · exact hoa_ext x hx
                        | _ => simp [isFreshArrObjTerm] at hfarr
                      | _ => simp [isFreshArrObjTerm] at hfarr
        | letE a b =>
          rw [hex] at hfarr hsteps
          cases a with
          | arrLit args =>
            cases b with
            | makeAt cc ns bargs =>
              cases cc with
              | absent =>
                cases ns with
                | nil => simp [isFreshArrObjTerm] at hfarr
                | cons k1 ns' =>
                  cases ns' with
                  | nil => simp [isFreshArrObjTerm] at hfarr
                  | cons k2 ns'' =>
                    cases ns'' with
                    | cons _ _ => simp [isFreshArrObjTerm] at hfarr
                    | nil =>
                      cases bargs with
                      | nil => simp [isFreshArrObjTerm] at hfarr
                      | cons a1 bargs' =>
                        cases bargs' with
                        | nil => simp [isFreshArrObjTerm] at hfarr
                        | cons a2 bargs'' =>
                          cases bargs'' with
                          | cons _ _ => simp [isFreshArrObjTerm] at hfarr
                          | nil =>
                            cases a1 with
                            | var z =>
                              cases z with
                              | succ _ => simp [isFreshArrObjTerm] at hfarr
                              | zero =>
                                cases a2 with
                                | var pi =>
                                  simp only [isFreshArrObjTerm, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfarr
                                  obtain ⟨⟨⟨rfl, rfl⟩, hpos⟩, hpi⟩ := hfarr
                                  have hpi_not_lt : ¬(pi < 1) := by omega
                                  simp only [instantiate, instantiateArgs, ↓reduceIte,
                                    show (0 : Nat) < 1 by omega, hpi_not_lt] at hsteps
                                  obtain ⟨hff, hfe, hfc⟩ := steps_letArrObj_fresh (hval_lt (pi - 1) hpi)
                                    (he.1 (pi - 1)) hval hsteps
                                  refine ⟨PrivExt, hbd_ext, hcl_ext, ?_, ?_, hos_ext, shift_holdersCoverB_add0 hhl_ext⟩
                                  · intro x hx
                                    rcases List.mem_cons.mp hx with rfl | hx
                                    · intro loc hl; exact .inr (hff loc (by simpa [push] using hl))
                                    · exact hof_ext x hx
                                  · intro x hx
                                    rcases List.mem_cons.mp hx with rfl | hx
                                    · refine ⟨fun loc hl => .inr (hfe loc (by simpa [push] using hl)),
                                        fun loc hl => .inr (hfc loc (by simpa [push] using hl))⟩
                                    · exact hoa_ext x hx
                                | _ => simp [isFreshArrObjTerm] at hfarr
                            | _ => simp [isFreshArrObjTerm] at hfarr
              | _ => simp [isFreshArrObjTerm] at hfarr
            | _ => simp [isFreshArrObjTerm] at hfarr
          | _ => simp [isFreshArrObjTerm] at hfarr
        | _ => rw [hex] at hfarr; simp [isFreshArrObjTerm] at hfarr
      · simp only [halloc, Bool.false_eq_true, ↓reduceIte]
        by_cases hun : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true
        · simp only [hun, ↓reduceIte]; exact hShiftUnreach hun
        · simp only [hun, Bool.false_eq_true, ↓reduceIte]; exact hEmpty
    · simp only [hfarr, Bool.false_eq_true, ↓reduceIte]
      by_cases hfobj : isFreshObjectTerm node.expression = true
      · simp only [hfobj, ↓reduceIte]
        by_cases halloc : conf.allocPriv.contains l = true
        · simp only [halloc, ↓reduceIte]
          have hff : ∀ loc ∈ fieldLocs v, s.h.length ≤ loc ∧ loc < s'.h.length := by
            cases hex : node.expression with
            | makeAt cc ns args =>
              rw [hex] at hfobj hsteps
              cases cc <;> try simp [isFreshObjectTerm] at hfobj
              simp only [instantiate] at hsteps
              exact steps_makeAt_fresh hsteps hval
            | merge d a b =>
              rw [hex] at hsteps; simp only [instantiate] at hsteps
              exact steps_merge_fresh hsteps hval
            | makeKey a b =>
              rw [hex] at hsteps; simp only [instantiate] at hsteps
              exact steps_makeKey_fresh hsteps hval
            | _ => rw [hex] at hfobj; simp [isFreshObjectTerm] at hfobj
          refine ⟨PrivExt, hbd_ext, hcl_ext, ?_, hoa_ext, hos_ext, shift_holdersCoverB_add0 hhl_ext⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · intro loc hl; exact .inr (hff loc (by simpa [push] using hl))
          · exact hof_ext x hx
        · simp only [halloc, Bool.false_eq_true, ↓reduceIte]
          by_cases hun : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true
          · simp only [hun, ↓reduceIte]; exact hShiftUnreach hun
          · simp only [hun, Bool.false_eq_true, ↓reduceIte]; exact hEmpty
      · simp only [hfobj, Bool.false_eq_true, ↓reduceIte]
        by_cases harr : (node.expression matches .arrLit _) = true
        · simp only [harr, ↓reduceIte]
          by_cases halloc : conf.allocPriv.contains l = true
          · simp only [halloc, ↓reduceIte]
            cases hex : node.expression with
            | arrLit args =>
              rw [hex] at hsteps; simp only [instantiate] at hsteps
              obtain ⟨ls, rfl, hls⟩ := steps_arrLit_fresh hsteps hval
              refine ⟨PrivExt, hbd_ext, hcl_ext, hof_ext, hoa_ext, ?_, shift_holdersCoverB_add0 hhl_ext⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨ls, rfl, fun loc hl => .inr (hls loc hl)⟩
              · exact hos_ext x hx
            | _ => rw [hex] at harr; simp at harr
          · simp only [halloc, Bool.false_eq_true, ↓reduceIte]
            by_cases hun : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true
            · simp only [hun, ↓reduceIte]; exact hShiftUnreach hun
            · simp only [hun, Bool.false_eq_true, ↓reduceIte]; exact hEmpty
        · simp only [harr, Bool.false_eq_true, ↓reduceIte]
          by_cases hun : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true
          · simp only [hun, ↓reduceIte]; exact hShiftUnreach hun
          · simp only [hun, Bool.false_eq_true, ↓reduceIte]
            by_cases hinert : inertTy G c.type = true
            · simp only [hinert, ↓reduceIte]
              have hni : Inert allC v := inertTy_sound hinert (he'.2 0 c.type rfl)
              exact ⟨PrivExt, hbd_ext, hcl_ext, hof_ext, hoa_ext, hos_ext,
                shift_holdersCoverB (NoPriv.of_inert hni) hhl_ext⟩
            · simp only [hinert, Bool.false_eq_true, ↓reduceIte]
              cases hex : node.expression with
              | var i =>
                by_cases hilt : i < c.context.length
                · simp only [hilt, ↓reduceIte]
                  rw [hex] at hsteps; simp only [instantiate] at hsteps
                  have hveq : v = ρ i := PromiseCalls.steps_value (hval_lt i hilt) hsteps
                  subst hveq
                  refine ⟨PrivExt, hbd_ext, hcl_ext, ?_, ?_, ?_, ?_⟩
                  · intro x hx
                    by_cases hi : pre.owned.contains i = true
                    · simp only [hi, ↓reduceIte] at hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · intro loc hl; exact .inl (hof i (List.contains_iff_mem.mp hi) loc (by simpa [push] using hl))
                      · exact hof_ext x hx
                    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hx; exact hof_ext x hx
                  · intro x hx
                    by_cases hi : pre.ownedArr.contains i = true
                    · simp only [hi, ↓reduceIte] at hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · have h0 := hoa_ext (i + 1) (List.mem_map.mpr ⟨i, List.contains_iff_mem.mp hi, rfl⟩)
                        simpa [push] using h0
                      · exact hoa_ext x hx
                    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hx; exact hoa_ext x hx
                  · intro x hx
                    by_cases hi : pre.ownedSpines.contains i = true
                    · simp only [hi, ↓reduceIte] at hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · have h0 := hos_ext (i + 1) (List.mem_map.mpr ⟨i, List.contains_iff_mem.mp hi, rfl⟩)
                        simpa [push] using h0
                      · exact hos_ext x hx
                    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hx; exact hos_ext x hx
                  · by_cases hi : pre.holders.contains i = true
                    · simp only [hi, ↓reduceIte]; exact shift_holdersCoverB_add0 hhl_ext
                    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
                      exact shift_holdersCoverB (hhl_ext i hilt (fun hm => hi (List.contains_iff_mem.mpr hm))) hhl_ext
                · simp only [hilt, ↓reduceIte]; exact hEmpty
              | _ =>
                exact ⟨PrivExt, hbd_ext, hcl_ext, hof_ext, hoa_ext, hos_ext, shift_holdersCoverB_add0 hhl_ext⟩
  · simp only [hinsp, Bool.false_eq_true, ↓reduceIte]
    by_cases hun : freeSlotsNotIn c.context.length 0 pre.holders node.expression = true
    · simp only [hun, ↓reduceIte]; exact hShiftUnreach hun
    · simp only [hun, Bool.false_eq_true, ↓reduceIte]
      have hCallCase : confinedCallNormal G images codes sums c node stepK deriv pre = true →
          ∃ Priv' : Nat → Prop,
            (∀ loc, Priv' loc → m₀ ≤ loc ∧ loc < s'.h.length) ∧
            ClosedOut s'.h Priv' ∧
            OwnedFields (push v ρ) (if inertTy G c.type then pre.shift else { pre.shift with holders := 0 :: pre.shift.holders }).owned Priv' ∧
            OwnedArrays s'.h (push v ρ) (if inertTy G c.type then pre.shift else { pre.shift with holders := 0 :: pre.shift.holders }).ownedArr Priv' ∧
            OwnedSpines (push v ρ) (if inertTy G c.type then pre.shift else { pre.shift with holders := 0 :: pre.shift.holders }).ownedSpines Priv' ∧
            HoldersCoverB (c.context.length + 1) (push v ρ) (if inertTy G c.type then pre.shift else { pre.shift with holders := 0 :: pre.shift.holders }).holders Priv' := by
        intro hcc
        unfold confinedCallNormal at hcc
        cases hd : deriv with
        | none => rw [hd] at hcc; cases hcc
        | some d =>
          rw [hd] at hcc
          simp only [Bool.and_eq_true] at hcc
          obtain ⟨⟨hdc, hops⟩, hfc⟩ := hcc
          cases heff : ExpressionEffects.selectedEffect d with
          | none => rw [heff] at hfc; cases hfc
          | some eff =>
            rw [heff] at hfc
            simp only [derivChecked, Bool.and_eq_true, beq_iff_eq] at hdc
            obtain ⟨⟨hterm, hctx⟩, htree⟩ := hdc
            have hsafe : SafePost (excOf G) (meaning G (claim d).type)
                (eff.callPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim d).term))
                  (ExpressionEffects.actualsOf (instantiate 0 ρ (claim d).term)) s.h) s.n s.W s.h
                (instantiate 0 ρ (claim d).term) := by
              rcases Bool.or_eq_true_iff.mp htree with htree | hreq
              · exact ExpressionEffects.selected_sound d htree hops heff hcodes hsums
                  (PromiseCalls.envOk_intRefines hctx he hkS.2.2.2.2.2) s.adm s.ok (by rw [hterm]; exact href)
              · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums d hreq
                rw [heff] at heff'; cases heff'
                exact hs (PromiseCalls.envOk_intRefines hctx he hkS.2.2.2.2.2) hkS s.adm s.ok (by rw [hterm]; exact href)
            rw [hterm] at hsafe
            have hcp := GraphCode.returnsPost_of_safePost hsafe k s'.h v hkn hsteps hval
            have hpf : Post (PromiseCalls.callerFrame eff node.expression) ρ s.h s'.h :=
              PromiseCalls.callerFrame_post (CallEffects.Effect.callPost_within hcp)
            obtain ⟨hkeep_out, hoa_c⟩ := frameConfined_sound hfc hpf s.ok s'.ok hof hoa hρ_ok hρ'_ok
            have hcl_c : ClosedOut s'.h PrivExt := closedOut_of_keep_outside s.ok hcl hkeep_out
            have hoa_sh : OwnedArrays s'.h (push v ρ) pre.shift.ownedArr PrivExt := shift_ownedArrays hoa_c
            by_cases hinert : inertTy G c.type = true
            · simp only [hinert, ↓reduceIte]
              have hni : Inert allC v := inertTy_sound hinert (he'.2 0 c.type rfl)
              exact ⟨PrivExt, hbd_ext, hcl_c, hof_ext, hoa_sh, hos_ext,
                shift_holdersCoverB (NoPriv.of_inert hni) hhl_ext⟩
            · simp only [hinert, Bool.false_eq_true, ↓reduceIte]
              exact ⟨PrivExt, hbd_ext, hcl_c, hof_ext, hoa_sh, hos_ext, shift_holdersCoverB_add0 hhl_ext⟩
      cases hex : node.expression with
      | writeAt f a b =>
        cases a with
        | var x =>
          cases b with
          | var y =>
            by_cases hwc : (f != arraySpineKey && x < c.context.length && y < c.context.length &&
                (!pre.holders.contains y || pre.owned.contains x)) = true
            · simp only [hwc, ↓reduceIte]
              simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq,
                Bool.not_eq_true', List.contains_iff_mem] at hwc
              obtain ⟨⟨⟨hfne, hxlt⟩, hylt⟩, hy_or_x⟩ := hwc
              rw [hex] at hsteps; simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hsteps
              have hcond : NoPriv Priv (ρ y) ∨ ∀ loc ∈ fieldLocs (ρ x), Priv loc :=
                hy_or_x.imp (fun hnm => hhl y hylt (fun hm => by rw [List.contains_iff_mem.mpr hm] at hnm; cases hnm)) (hof x)
              obtain ⟨hlenw, hcl', -, hsp⟩ := steps_writeAt_val_confined (hval_lt x hxlt) (hval_lt y hylt) hval hfne (hρ_ok x) hcl hcond hsteps
              have hbd' : ∀ loc, Priv loc → m₀ ≤ loc ∧ loc < s'.h.length := by
                intro loc hp; rw [hlenw]; exact hbd loc hp
              have hoa' : OwnedArrays s'.h (push v ρ) pre.shift.ownedArr Priv := by
                intro z hz
                obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
                refine ⟨fun loc hl => (hoa z₀ hz₀).1 loc (by simpa [push] using hl), fun loc hl => ?_⟩
                have := hsp (ρ z₀) (hρ_ok z₀)
                exact (hoa z₀ hz₀).2 loc (by simpa [push, this] using hl)
              have hvnul : v = .nul := by
                have hvx := hval_lt x hxlt
                have hvy := hval_lt y hylt
                generalize hh' : s'.h = h' at hsteps
                generalize hx : ρ x = rx at hsteps hvx
                generalize hy : ρ y = ry at hsteps hvy
                cases hsteps with
                | refl => simp [isVal] at hval
                | next hs hr =>
                  cases hs with
                  | writeC1 hs' => exact absurd hs' (value_no_step hvx)
                  | writeC2 _ hs' => exact absurd hs' (value_no_step hvy)
                  | writeField _ _ _ =>
                    cases hr with
                    | refl => rfl
                    | next hs2 _ => exact absurd hs2 (value_no_step (by rfl : isVal .nul = true))
              subst hvnul
              exact ⟨Priv, hbd', hcl', shift_ownedFields hof, hoa', shift_ownedSpines hos,
                shift_holdersCoverB (NoPriv.of_inert inert_nul) hhl⟩
            · simp only [hwc, Bool.false_eq_true, ↓reduceIte]; exact hEmpty
          | _ =>
            by_cases hcc : confinedCallNormal G images codes sums c node stepK deriv pre = true
            · simpa only [hex, hcc, ↓reduceIte] using hCallCase hcc
            · simpa only [hex, hcc, Bool.false_eq_true, ↓reduceIte] using hEmpty
        | _ =>
          by_cases hcc : confinedCallNormal G images codes sums c node stepK deriv pre = true
          · simpa only [hex, hcc, ↓reduceIte] using hCallCase hcc
          · simpa only [hex, hcc, Bool.false_eq_true, ↓reduceIte] using hEmpty
      | _ =>
        by_cases hcc : confinedCallNormal G images codes sums c node stepK deriv pre = true
        · simpa only [hex, hcc, ↓reduceIte] using hCallCase hcc
        · simpa only [hex, hcc, Bool.false_eq_true, ↓reduceIte] using hEmpty

/-- **Single-node soundness of `checkNode` on the handler edge**: the handler
target's `owned`, `ownedArr`, `ownedSpines` are empty, so `ConfinedAt` holds
at `Priv = ∅` for every heap and environment. -/
theorem checkNode_sound_handler {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {claims : List (PointClaim ι)} {conf : Table} {l : Nat}
    {node : Node} {c : PointClaim ι} {stepK : HeapKnowledge.Knowledge}
    {deriv : Option (ProgramCertificates.Evidence ι)} {t : Target} {ρ : Env} {m₀ : Nat} {h : Heap}
    (hchk : checkNode G images codes sums claims conf l node c stepK deriv = true)
    (hh : node.handler = some t) :
    ConfinedAt conf (fun lbl => ((claims[lbl]?).map (·.context.length)).getD 0) t.label ρ m₀ h := by
  simp only [checkNode, hh, Bool.and_eq_true, List.isEmpty_iff] at hchk
  obtain ⟨⟨_, _⟩, ⟨⟨ho, ha⟩, hs⟩⟩ := hchk
  refine ⟨fun _ => False, fun _ hf => False.elim hf, ClosedOut.empty h, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [ho] at hx; cases hx
  · intro x hx; rw [ha] at hx; cases hx
  · intro x hx; rw [hs] at hx; cases hx
  · intro _ _ _ _ _ hf; exact hf

end Check

/-! ## Untrusted confinement proposer -/

section Propose
variable {ι : Type} [DecidableEq ι]

private def listInter (a b : List Nat) : List Nat :=
  a.filter b.contains

private def listUnion (a b : List Nat) : List Nat :=
  b.foldl (fun acc x => if acc.contains x then acc else x :: acc) a

private def mapOut (post : NodeConf) (srcWidth : Nat) (pushed : Bool) (mapping : Mapping) (dstWidth : Nat) : NodeConf :=
  let idx := fun i => if pushed then i else i + 1
  let slots := List.range dstWidth
  { owned := slots.filter fun j => post.owned.contains (idx (slot mapping j))
    ownedArr := slots.filter fun j => post.ownedArr.contains (idx (slot mapping j))
    ownedSpines := slots.filter fun j => post.ownedSpines.contains (idx (slot mapping j))
    holders := slots.filter fun j =>
      let src := idx (slot mapping j)
      src >= srcWidth + 1 || post.holders.contains src }

private def mergeConf (a b : NodeConf) : NodeConf :=
  { owned := listInter a.owned b.owned
    ownedArr := listInter a.ownedArr b.ownedArr
    ownedSpines := listInter a.ownedSpines b.ownedSpines
    holders := listUnion a.holders b.holders }

/-- Untrusted heuristic for whether a call at `node.expression` is likely to
have a confined normal frame, read from the callee's signature type in `c.context`. -/
private def callLikelyConfined (G : NormalGraph ι) (c : PointClaim ι) (node : Node) (pre : NodeConf) : Bool :=
  match node.expression with
  | .invoke (.var fi) _ _ =>
      match c.context[fi]? with
      | some F =>
          (expand G F).any fun cl => match cl with
            | .arrs arrs rest =>
                arrs.any (fun a => frameConfined pre.owned pre.ownedArr (PromiseCalls.callerFrame a.effect node.expression)) ||
                rest.any (fun a => frameConfined pre.owned pre.ownedArr (PromiseCalls.callerFrame a.effect node.expression))
            | .callable _ _ arrs rest _ =>
                arrs.any (fun a => frameConfined pre.owned pre.ownedArr (PromiseCalls.callerFrame a.effect node.expression)) ||
                rest.any (fun a => frameConfined pre.owned pre.ownedArr (PromiseCalls.callerFrame a.effect node.expression))
            | _ => false
      | none => false
  | _ => false

/-- Untrusted per-node post-state mirror of `nodePostN` for fixed-point proposal. -/
private def proposePostN (G : NormalGraph ι) (node : Node) (c : PointClaim ι)
    (pre : NodeConf) (allocIntoPriv : Bool) : NodeConf × Bool :=
  let width := c.context.length
  let sh := pre.shift
  let unreach := freeSlotsNotIn width 0 pre.holders node.expression
  if Purity.inspectTerm node.expression && checkScope width node.expression then
    if isFreshArrObjTerm width pre.ownedSpines node.expression then
      if allocIntoPriv then
        ({ sh with owned := 0 :: sh.owned, ownedArr := 0 :: sh.ownedArr, holders := 0 :: sh.holders }, false)
      else if unreach then (sh, false)
      else ({}, true)
    else if isFreshObjectTerm node.expression then
      if allocIntoPriv then
        ({ sh with owned := 0 :: sh.owned, holders := 0 :: sh.holders }, false)
      else if unreach then (sh, false)
      else ({}, true)
    else if node.expression matches .arrLit _ then
      if allocIntoPriv then
        ({ sh with ownedSpines := 0 :: sh.ownedSpines, holders := 0 :: sh.holders }, false)
      else if unreach then (sh, false)
      else ({}, true)
    else if unreach then (sh, false)
    else if inertTy G c.type then (sh, false)
    else match node.expression with
      | .var i =>
          if i < width then
            ({ owned := if pre.owned.contains i then 0 :: sh.owned else sh.owned
               ownedArr := if pre.ownedArr.contains i then 0 :: sh.ownedArr else sh.ownedArr
               ownedSpines := if pre.ownedSpines.contains i then 0 :: sh.ownedSpines else sh.ownedSpines
               holders := if pre.holders.contains i then 0 :: sh.holders else sh.holders }, false)
          else ({}, true)
      | _ => ({ sh with holders := 0 :: sh.holders }, false)
  else if unreach then
    (sh, false)
  else
    match node.expression with
    | .writeAt f (.var x) (.var y) =>
        if f != arraySpineKey && x < width && y < width &&
            (!pre.holders.contains y || pre.owned.contains x) then
          (sh, false)
        else ({}, !(pre.owned.isEmpty && pre.ownedArr.isEmpty && pre.ownedSpines.isEmpty))
    | _ =>
        if callLikelyConfined G c node pre then
          (if inertTy G c.type then sh else { sh with holders := 0 :: sh.holders }, false)
        else ({}, !(pre.owned.isEmpty && pre.ownedArr.isEmpty && pre.ownedSpines.isEmpty))

/-- Run one fixed-point pass for a chosen `allocPriv` set; returns the converged
node table and whether any non-empty confined set escaped. -/
private def runFixedPoint (G : NormalGraph ι) (P : Program) (claims : List (PointClaim ι))
    (start : Nat) (allocPriv : List Nat) : Array NodeConf × Bool := Id.run do
  let n := P.length
  let mut reached := Array.replicate n false
  let mut tbl : Array NodeConf := Array.replicate n {}
  if start < n then
    reached := reached.set! start true
  let mut changed := true
  let mut escaped := false
  let mut iter := 0
  let maxIter := n * 4 + 16
  while changed && iter < maxIter do
    changed := false
    escaped := false
    iter := iter + 1
    for l in List.range n do
      if reached[l]! then
        let some node := P[l]? | continue
        let c : PointClaim ι := (claims[l]?).getD ⟨[], []⟩
        let pre := tbl.getD l {}
        let (postN, esc) := proposePostN G node c pre (allocPriv.contains l)
        if esc then escaped := true
        for (t, pushed) in normalExits node do
          if t.label < n then
            let dstW := ((claims[t.label]?).map (·.context.length)).getD 0
            let out := mapOut postN c.context.length pushed t.mapping dstW
            if !reached[t.label]! then
              reached := reached.set! t.label true
              tbl := tbl.set! t.label out
              changed := true
            else
              let merged := mergeConf (tbl.getD t.label {}) out
              if merged != tbl.getD t.label {} then
                tbl := tbl.set! t.label merged
                changed := true
        if let some t := node.handler then
          if t.label < n then
            let emptyH : NodeConf := { holders := (tbl.getD t.label {}).holders }
            if !reached[t.label]! then
              reached := reached.set! t.label true
              tbl := tbl.set! t.label {}
              changed := true
            else
              let merged := mergeConf (tbl.getD t.label {}) emptyH
              if merged != tbl.getD t.label {} then
                tbl := tbl.set! t.label merged
                changed := true
  return (tbl, escaped)

/-- **Untrusted confinement proposer**: finds locally allocated objects/arrays
that never escape and marks unreachable writing calls as framed. If the graph
has no unreachable writing call over a confined object, returns an empty table
(`framed = []`), keeping zero overhead for ordinary functions. -/
def propose (G : NormalGraph ι) (P : Program) (claims : List (PointClaim ι)) (start : Nat) : Table := Id.run do
  let n := P.length
  let hasCall := P.any fun node => match node.expression with
    | .invoke .. | .construct .. => true
    | _ => false
  if !hasCall then return ⟨#[], [], []⟩
  let mut allocs : List Nat := []
  for l in List.range n do
    let some nd := P[l]? | continue
    let e := nd.expression
    if Purity.inspectTerm e then
      if isFreshObjectTerm e || (e matches .arrLit _) ||
          (match e with
           | .makeAt .absent [k1, k2] [.var _, .var _] => k1 == arraySpineKey && k2 == CallArguments.protoField
           | .letE (.arrLit _) (.makeAt .absent [k1, k2] [.var 0, .var pi]) =>
               k1 == arraySpineKey && k2 == CallArguments.protoField && 0 < pi
           | _ => false) then
        allocs := allocs ++ [l]
  if allocs.isEmpty then return ⟨#[], [], []⟩
  let (tbl0, esc0) := runFixedPoint G P claims start allocs
  let mut chosen := allocs
  let mut tbl := tbl0
  if esc0 && allocs.length ≤ 16 then
    chosen := []
    for a in allocs do
      let tryList := chosen ++ [a]
      let (t', e') := runFixedPoint G P claims start tryList
      if !e' then
        chosen := tryList
        tbl := t'
    if chosen.isEmpty then
      return ⟨#[], [], []⟩
    else
      let (tFinal, _) := runFixedPoint G P claims start chosen
      tbl := tFinal
  let mut framed : List Nat := []
  for l in List.range n do
    let some node := P[l]? | continue
    let nc := tbl.getD l {}
    let width := ((claims[l]?).map (·.context.length)).getD 0
    if !(nc.owned.isEmpty && nc.ownedArr.isEmpty) &&
        !Purity.inspectTerm node.expression &&
        freeSlotsNotIn width 0 nc.holders node.expression then
      framed := framed ++ [l]
  if framed.isEmpty then return ⟨#[], [], []⟩
  return ⟨tbl, framed, chosen⟩

end Propose

end Verification.LocalConfinement
