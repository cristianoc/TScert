import Verification.Paper.TolerantFrames.ReadOnlyFitsSubst

/-! # Read-only handles: the fit of a node expression, read from its code

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
checks of a code"). A proposal meets a code
(`CodeOk`) when each node expression, instantiated at every environment
meeting the node's slots and their signatures, fits the node's value set.
That condition quantifies over every environment; this module states it
on the node expression itself (proof scope: the lemmas below):

- **An open term fits** (`OFits τ φ d Γ a o S e`): the rules of `Fits` over
  a term whose variables below `d` are bound inside it (`Γ`), and whose
  variable `d + i` is the slot `i` of the node's environment, of the sites
  `τ i` and, where `φ i` names one, holding a closure of that signature.
  A call whose callee is such a slot is a call of a closure of `C`'s code
  of a known signature (`invokeC`); a capture or a bound part is a
  primitive or a variable (`OVOr`).
- **Instantiation keeps it** (`ofits_sound`): at an environment meeting
  the slots' sites (`VJ`) and signatures (`FnIs`), the instantiated term
  fits (`Fits`).
- **The checks of an edge** (`ContChk`, `HandlerChk`): each slot of a
  continuation's or a handler's target holds the sites of the slot it
  reads (`mapIdx`, `Carries`), the value bound at the node's value set, a
  test's boolean at none, a thrown value at `O`, and names a signature
  only where that slot names it (`CarriesFn`); they give the edge's
  conditions (`contOk_of_chk`, `handlerOk_of_chk`).
- **The checks of a code** (`CodeChk`): each node expression fits openly,
  a node value naming a signature is a slot naming it, and each edge is
  checked; they give `CodeOk` (`codeOk_of_chk`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} (Fl : Flow P) (τ : Nat → Sites P) (φ : Nat → Option FnSig)

/-- **A part of a closure's code, open**: a primitive, a variable bound
inside the term to a smaller set, or a slot of a smaller set. -/
def OVOr (d : Nat) (Γ : Nat → Option (Sites P)) (S : Sites P) (u : Tm) : Prop :=
  primVal u = true ∨ (∃ j S', u = .var j ∧ j < d ∧ Γ j = some S' ∧ Sub S' S) ∨
    ∃ j, u = .var j ∧ d ≤ j ∧ Sub (τ (j - d)) S

/-- **An open term fits a set of sites** (the module's header). -/
inductive OFits : Nat → (Nat → Option (Sites P)) → Alloc P → Bool → Sites P → Tm → Prop where
  | prim {d Γ a o S v} : primVal v = true → (o = true → Sub S Fl.O) → OFits d Γ a o S v
  | arr {d Γ a o S ls} : (∀ x ∈ ls, x = none) → (o = true → Sub S Fl.O) → OFits d Γ a o S (.arr ls)
  | bvar {d Γ a o S S' i} : i < d → Γ i = some S' → Sub S' S → (o = true → Sub S Fl.O) → OFits d Γ a o S (.var i)
  | fvar {d Γ a o S i} : d ≤ i → Sub (τ (i - d)) S → (o = true → Sub S Fl.O) → OFits d Γ a o S (.var i)
  | invoke {d Γ a o S f r args} : OFits d Γ a o Fl.O f → OFits d Γ a o Fl.O r →
      (∀ x ∈ args, OFits d Γ a o Fl.O x) → Sub Fl.O S → a.arr ∈ Fl.O → (o = true → Sub S Fl.O) →
      OFits d Γ a o S (.invoke f r args)
  | invokeC {d Γ a o S j r args} (σ : FnSig) (π : CodeFlow P) (Sa : Nat → Sites P) (Sr : Sites P) :
      o = false → d ≤ j → φ (j - d) = some σ → Fl.code σ.code = some π →
      Sub (τ (j - d)) (π.env σ.s (capSlot σ.ar σ.rest σ.ncaps)) →
      OFits d Γ a o (π.env σ.s (recvSlot σ.rest)) r → (∀ i x, args[i]? = some x → OFits d Γ a o (Sa i) x) →
      (∀ x ∈ args, primVal x = true ∨ ∃ k, x = .var k) →
      (∀ i, i < σ.ar → Sub (Sa i) (π.env σ.s (paramSlot σ.rest i))) →
      (σ.rest = true → a.arr ∈ π.env σ.s 0 ∧ Stores Fl a.arr Sr ∧ ∀ i, σ.ar ≤ i → Sub (Sa i) Sr) →
      Sub π.ret S → (o = true → Sub S Fl.O) → OFits d Γ a o S (.invoke (.var j) r args)
  | construct {d Γ a o S f args} : OFits d Γ a o Fl.O f → (∀ x ∈ args, OFits d Γ a o Fl.O x) → Sub Fl.O S →
      a.arr ∈ Fl.O → (o = true → Sub S Fl.O) → OFits d Γ a o S (.construct f args)
  | letE {d Γ a o S Sx x b} : OFits d Γ a o Sx x → OFits (d + 1) (consSites Sx Γ) a o S b →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.letE x b)
  | spread {d Γ a o S Sx x} : OFits d Γ a o Sx x → (∀ s ∈ Sx, Sub (Fl.H.contents s) S) →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.spread x)
  | makeAbsent {d Γ a o S ns inits} (Ss : Tm → Sites P) : (∀ x ∈ inits, Stores Fl a.obj (Ss x)) →
      (∀ x ∈ inits, OFits d Γ a o (Ss x) x) → a.obj ∈ S → (o = true → Sub S Fl.O) →
      OFits d Γ a o S (.makeAt .absent ns inits)
  | makeBound {d Γ a o S t r pre ns inits} (Ss : Tm → Sites P) : (∀ x ∈ inits, Stores Fl a.obj (Ss x)) →
      (∀ x ∈ inits, OFits d Γ a o (Ss x) x) → a.obj ∈ S → (∀ x ∈ t :: r :: pre, OVOr τ d Γ S x) →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.makeAt (.bound t r pre) ns inits)
  | makeGraphC {d Γ a o S ar E K s caps k rest comp ns inits} (π : CodeFlow P) (Ss : Tm → Sites P) :
      (∀ x ∈ inits, Stores Fl a.obj (Ss x)) → (∀ x ∈ inits, OFits d Γ a o (Ss x) x) → a.obj ∈ S →
      P.ofC comp = true → Fl.code (E, K) = some π →
      (∀ i u, caps[i]? = some u → OVOr τ d Γ (π.env s (capSlot ar rest i)) u) →
      SelfFn π ar E K s rest caps.length → OpenAt Fl π ar s rest caps.length → (∀ e ∈ E, Lowered Fl e) →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.makeAt (.graph ar E K s caps k rest comp) ns inits)
  | makeGraphOut {d Γ a o S ar E K s caps k rest comp ns inits} (Ss : Tm → Sites P) :
      (∀ x ∈ inits, Stores Fl a.obj (Ss x)) → (∀ x ∈ inits, OFits d Γ a o (Ss x) x) → a.obj ∈ S →
      P.ofC comp = false → (∀ e ∈ E, Lowered Fl e) → (∀ u ∈ caps, OVOr τ d Γ S u) →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.makeAt (.graph ar E K s caps k rest comp) ns inits)
  | readAt {d Γ a o S Sx Q f x} : OFits d Γ a o Sx x → Sub Sx Q → (∀ s ∈ Q, Sub (Fl.H.contents s) Q) →
      (∀ s ∈ Q, Sub (Fl.H.contents s) S) → (o = true → Sub S Fl.O) → OFits d Γ a o S (.readAt f x)
  | indexAt {d Γ a o S Sx Q Sk x key} : OFits d Γ a o Sx x → OFits d Γ a o Sk key → Sub Sx Q →
      (∀ s ∈ Q, Sub (Fl.H.contents s) Q) → (∀ s ∈ Q, Sub (Fl.H.contents s) S) →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.indexAt x key)
  | writeAt {d Γ a o S Sx Sy f x y} : OFits d Γ a o Sx x → OFits d Γ a o Sy y → (∀ s ∈ Sx, Stores Fl s Sy) →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.writeAt f x y)
  | test {d Γ a o S Sx k x} : OFits d Γ a o Sx x → (o = true → Sub S Fl.O) → OFits d Γ a o S (.test k x)
  | ite {d Γ a o S Sc c x y} : OFits d Γ a o Sc c → OFits d Γ a o S x → OFits d Γ a o S y →
      (o = true → Sub S Fl.O) → OFits d Γ a o S (.ite c x y)
  | arith {d Γ a o S Sx Sy op x y} : OFits d Γ a o Sx x → OFits d Γ a o Sy y → (o = true → Sub S Fl.O) →
      OFits d Γ a o S (.arith op x y)
  | arrLit {d Γ a o S inits} (Ss : Tm → Sites P) : (∀ x ∈ inits, Stores Fl a.arr (Ss x)) →
      (∀ x ∈ inits, OFits d Γ a o (Ss x) x) → a.arr ∈ S → (o = true → Sub S Fl.O) →
      OFits d Γ a o S (.arrLit inits)
  | elemAt {d Γ a o S Sx Si x i} : OFits d Γ a o Sx x → OFits d Γ a o Si i →
      (∀ s ∈ Sx, Sub (Fl.H.contents s) S) → (o = true → Sub S Fl.O) → OFits d Γ a o S (.elemAt x i)
  | setElem {d Γ a o S Sx Si Sv x i v} : OFits d Γ a o Sx x → OFits d Γ a o Si i → OFits d Γ a o Sv v →
      (∀ s ∈ a.arr :: Sx, Stores Fl s Sv) → Sub Sx S → a.arr ∈ S → (o = true → Sub S Fl.O) →
      OFits d Γ a o S (.setElem x i v)
  | lenOf {d Γ a o S Sx x} : OFits d Γ a o Sx x → (o = true → Sub S Fl.O) → OFits d Γ a o S (.lenOf x)
  | throw {d Γ a o S x} : OFits d Γ a o Fl.O x → (o = true → Sub S Fl.O) → OFits d Γ a o S (.throw x)
  | merge {d Γ a o S Sx Sy Q dr x y} : OFits d Γ a o Sx x → OFits d Γ a o Sy y → Sub (Sx ++ Sy) Q →
      (∀ s ∈ Q, Sub (Fl.H.contents s) Q) → (∀ s ∈ Q, Stores Fl a.obj (Fl.H.contents s)) → a.obj ∈ S →
      (o = true → Sub Q Fl.O) → (o = true → Sub S Fl.O) → OFits d Γ a o S (.merge dr x y)
  | makeKey {d Γ a o S Sk Sx k x} : OFits d Γ a o Sk k → Stores Fl a.obj Sx → OFits d Γ a o Sx x →
      a.obj ∈ S → (o = true → Sub S Fl.O) → OFits d Γ a o S (.makeKey k x)

/-! ## Instantiation keeps a term fitting -/

variable {Fl τ φ} {g : Ghost P} {n : Nat}

/-- **An open part, instantiated** (proved). -/
theorem OVOr.inst {ρ : Env} (hρ : ∀ i, VJ Fl g n (τ i) (ρ i)) {d : Nat} {Γ : Nat → Option (Sites P)}
    {S : Sites P} {u : Tm} (h : OVOr τ d Γ S u) : VOr (VJ Fl g n) Γ S (instantiate d ρ u) := by
  rcases h with hp | ⟨j, S', rfl, hj, hΓ, hs⟩ | ⟨j, rfl, hj, hs⟩
  · rw [instantiate_prim hp]; exact .inl (VJ.prim hp)
  · simp only [instantiate, if_pos hj]; exact .inr ⟨j, S', rfl, hΓ, hs⟩
  · simp only [instantiate, if_neg (by omega : ¬ j < d)]; exact .inl ((hρ _).sub hs)

/-- An instantiated argument list. -/
theorem mem_inst {d : Nat} {ρ : Env} {args : List Tm} {x : Tm} (hx : x ∈ args.map (instantiate d ρ)) :
    ∃ y ∈ args, x = instantiate d ρ y := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ⟨y, hy, rfl⟩

/-- **Instantiation keeps an open term fitting** (proved): at an
environment whose slot `i` meets `τ i` and holds a closure of `φ i`'s
signature where it names one, the instantiated term fits. -/
theorem ofits_sound {ρ : Env} (hρ : ∀ i, VJ Fl g n (τ i) (ρ i)) (hφ : ∀ i σ, φ i = some σ → FnIs P σ (ρ i)) :
    ∀ {d Γ a o S e}, OFits Fl τ φ d Γ a o S e → Fits Fl (VJ Fl g n) Γ a o S (instantiate d ρ e) := by
  intro d Γ a o S e h
  induction h with
  | prim hp ho => rw [instantiate_prim hp]; exact .val (by cases ‹Tm› <;> simp_all [primVal, isVal]) (VJ.prim hp) ho
  | @arr d _ _ _ _ ls hl ho =>
    have he : instantiate d ρ (.arr ls) = .arr ls := by simp [instantiate]
    rw [he]; exact .val rfl (VJ.arr fun l hl' => by have := hl _ hl'; simp at this) ho
  | bvar hi hΓ hs ho => simp only [instantiate, if_pos hi]; exact .var hΓ hs ho
  | @fvar d _ _ _ _ i hi hs ho =>
    simp only [instantiate, if_neg (by omega : ¬ i < d)]; exact .val (hρ _).val ((hρ _).sub hs) ho
  | invoke _ _ _ hO ha ho ihf ihr iha =>
    simp only [instantiate, instantiateArgs_eq_map]
    exact .invoke ihf ihr (fun x hx => by obtain ⟨y, hy, rfl⟩ := mem_inst hx; exact iha y hy) hO ha ho
  | @invokeC d _ _ _ _ j _ args σ π Sa Sr hof hj hφj hcode hself _ _ hat hpar hrest hO ho ihr iha =>
    simp only [instantiate, instantiateArgs_eq_map, if_neg (by omega : ¬ j < d)]
    refine .invokeC σ π Sa Sr hof (hφ _ σ hφj) hcode ((hρ _).sub hself) ihr (fun i x hx => ?_) (fun x hx => ?_)
      hpar hrest hO ho
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx; exact iha i y hy
    · obtain ⟨y, hy, rfl⟩ := mem_inst hx
      rcases hat y hy with hp | ⟨k, rfl⟩
      · rw [instantiate_prim hp]; exact .inl (by cases y <;> simp_all [primVal, isVal])
      · simp only [instantiate]
        split
        · exact .inr ⟨k, rfl⟩
        · exact .inl (hρ _).val
  | construct _ _ hO ha ho ihf iha =>
    simp only [instantiate, instantiateArgs_eq_map]
    exact .construct ihf (fun x hx => by obtain ⟨y, hy, rfl⟩ := mem_inst hx; exact iha y hy) hO ha ho
  | letE _ _ ho ihx ihb => simp only [instantiate]; exact .letE ihx ihb ho
  | spread _ hc ho ih => simp only [instantiate]; exact .spread ih hc ho
  | @makeAbsent d _ _ _ _ _ _ Ss hst _ hs ho ih =>
    simp only [instantiate, instantiateArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) _ _ _) (instantiate d ρ) hst ih
    exact .makeAbsent Ss' h₁ h₂ hs ho
  | @makeBound d _ _ _ _ _ _ _ _ _ Ss hst _ hs hp ho ih =>
    simp only [instantiate, instantiateArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) _ _ _) (instantiate d ρ) hst ih
    refine .makeBound Ss' h₁ h₂ hs (fun x hx => ?_) ho
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | rfl | ⟨y, hy, rfl⟩
    · exact (hp _ (by simp)).inst hρ
    · exact (hp _ (by simp)).inst hρ
    · exact (hp y (by simp [hy])).inst hρ
  | @makeGraphC d _ _ _ _ ar E K s caps k rest comp _ _ π Ss hst _ hs hc hcode hcaps hself hop hE ho ih =>
    simp only [instantiate, instantiateArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) _ _ _) (instantiate d ρ) hst ih
    have hself' : SelfFn π ar E K s rest (caps.map (instantiate d ρ)).length := by rwa [List.length_map]
    refine .makeGraphC π Ss' h₁ h₂ hs hc hcode (fun i u hu => ?_) hself'.capFn (by rwa [List.length_map]) hE ho
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact (hcaps i x hx).inst hρ
  | @makeGraphOut d _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ss hst _ hs hc hE hcaps ho ih =>
    simp only [instantiate, instantiateArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) _ _ _) (instantiate d ρ) hst ih
    refine .makeGraphOut Ss' h₁ h₂ hs hc hE (fun u hu => ?_) ho
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
    exact (hcaps y hy).inst hρ
  | readAt _ hq hcl hr ho ih => simp only [instantiate]; exact .readAt ih hq hcl hr ho
  | indexAt _ _ hq hcl hr ho ihx ihk => simp only [instantiate]; exact .indexAt ihx ihk hq hcl hr ho
  | writeAt _ _ hst ho ihx ihy => simp only [instantiate]; exact .writeAt ihx ihy hst ho
  | test _ ho ih => simp only [instantiate]; exact .test ih ho
  | ite _ _ _ ho ihc ihx ihy => simp only [instantiate]; exact .ite ihc ihx ihy ho
  | arith _ _ ho ihx ihy => simp only [instantiate]; exact .arith ihx ihy ho
  | @arrLit d _ _ _ _ _ Ss hst _ hs ho ih =>
    simp only [instantiate, instantiateArgs_eq_map]
    obtain ⟨Ss', h₁, h₂⟩ := sites_map (Fi := Fits Fl (VJ Fl g n) _ _ _) (instantiate d ρ) hst ih
    exact .arrLit Ss' h₁ h₂ hs ho
  | elemAt _ _ hc ho ihx ihi => simp only [instantiate]; exact .elemAt ihx ihi hc ho
  | setElem _ _ _ hst hS ha ho ihx ihi ihv => simp only [instantiate]; exact .setElem ihx ihi ihv hst hS ha ho
  | lenOf _ ho ih => simp only [instantiate]; exact .lenOf ih ho
  | throw _ ho ih => simp only [instantiate]; exact .throw ih ho
  | merge _ _ hq hcl hst hs hQ ho ihx ihy => simp only [instantiate]; exact .merge ihx ihy hq hcl hst hs hQ ho
  | makeKey _ hst _ hs ho ihk ihx => simp only [instantiate]; exact .makeKey ihk hst ihx hs ho

/-! ## The edges of a code -/

/-- **The slot of a node's environment the slot `i` of an edge's target
reads**: the mapping's entry, or the default, slot `0`, past it. -/
def mapIdx : Option (List Nat) → Nat → Nat
  | none, i => i
  | some slots, i => slots.getD i 0

/-- A mapped environment reads its source at `mapIdx` (proved). -/
theorem envOf_envMap_idx (m : Option (List Nat)) (L : List Tm) (d : Tm) (i : Nat) :
    envOf (envMap m L d).1 (envMap m L d).2 i = envOf L d (mapIdx m i) := by
  cases m with
  | none => rfl
  | some slots =>
    simp only [envMap, mapIdx, envOf, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : slots[i]? <;> simp

/-- The sites of a node's slots with a value pushed at slot `0`. -/
def pushSites (Sv : Sites P) (τ : Nat → Sites P) : Nat → Sites P
  | 0 => Sv
  | i + 1 => τ i

/-- The signatures of a node's slots with a value pushed at slot `0`. -/
def pushFn (vf : Option FnSig) (φ : Nat → Option FnSig) : Nat → Option FnSig
  | 0 => vf
  | i + 1 => φ i

/-- **An edge carries the slots `τ` into `τ'`**: each slot of the target
holds the sites of the slot it reads. -/
def Carries (τ τ' : Nat → Sites P) (m : Option (List Nat)) : Prop := ∀ i, Sub (τ (mapIdx m i)) (τ' i)

/-- **An edge carries the signatures `φ` into `φ'`**: each slot of the
target naming a signature reads a slot naming it. -/
def CarriesFn (φ φ' : Nat → Option FnSig) (m : Option (List Nat)) : Prop :=
  ∀ i σ, φ' i = some σ → φ (mapIdx m i) = some σ

/-- **The checks of a continuation**: a return's value meets the code's
return set; each
edge carries the node's slots, the value it binds at the node's value set
(a test's boolean at none), into its target's, and their signatures. -/
def ContChk (π : CodeFlow P) (l : Nat) : Continuation → Prop
  | .ret => Sub (π.val l) π.ret
  | .bind y => Carries (pushSites (π.val l) (π.env l)) (π.env y.label) y.mapping ∧
      CarriesFn (pushFn (π.vfn l) (π.fn l)) (π.fn y.label) y.mapping
  | .effect y => Carries (π.env l) (π.env y.label) y.mapping ∧ CarriesFn (π.fn l) (π.fn y.label) y.mapping
  | .branch y n => (Carries (π.env l) (π.env y.label) y.mapping ∧ CarriesFn (π.fn l) (π.fn y.label) y.mapping) ∧
      (Carries (π.env l) (π.env n.label) n.mapping ∧ CarriesFn (π.fn l) (π.fn n.label) n.mapping)
  | .branchBind y n =>
      (Carries (pushSites [] (π.env l)) (π.env y.label) y.mapping ∧
        CarriesFn (pushFn none (π.fn l)) (π.fn y.label) y.mapping) ∧
      (Carries (pushSites [] (π.env l)) (π.env n.label) n.mapping ∧
        CarriesFn (pushFn none (π.fn l)) (π.fn n.label) n.mapping)
  | .tagBind _ y n =>
      (Carries (pushSites (π.val l) (π.env l)) (π.env y.label) y.mapping ∧
        CarriesFn (pushFn (π.vfn l) (π.fn l)) (π.fn y.label) y.mapping) ∧
      (Carries (pushSites (π.val l) (π.env l)) (π.env n.label) n.mapping ∧
        CarriesFn (pushFn (π.vfn l) (π.fn l)) (π.fn n.label) n.mapping)

variable (Fl) in
/-- **The checks of a handler**: its edge carries the node's slots, the
thrown value at `O`, into its target's, and their signatures, a thrown
value naming none. -/
def HandlerChk (π : CodeFlow P) (l : Nat) : Option Target → Prop
  | none => True
  | some y => Carries (pushSites Fl.O (π.env l)) (π.env y.label) y.mapping ∧
      CarriesFn (pushFn none (π.fn l)) (π.fn y.label) y.mapping

/-- A carried environment meets the target's slots (proved). -/
theorem carries_env {τ τ' : Nat → Sites P} {m : Option (List Nat)} (hc : Carries τ τ' m) {L : List Tm} {d : Tm}
    (henv : ∀ i, VJ Fl g n (τ i) (envOf L d i)) : EnvIn (VJ Fl g n) τ' (envMap m L d).1 (envMap m L d).2 :=
  fun i => by rw [envOf_envMap_idx]; exact (henv _).sub (hc i)

/-- A carried environment meets the target's signatures (proved). -/
theorem carries_fn {φ φ' : Nat → Option FnSig} {m : Option (List Nat)} (hc : CarriesFn φ φ' m) {L : List Tm}
    {d : Tm} (hfn : ∀ i σ, φ i = some σ → FnIs P σ (envOf L d i)) :
    ∀ i σ, φ' i = some σ → FnIs P σ (envOf (envMap m L d).1 (envMap m L d).2 i) :=
  fun i σ hi => by rw [envOf_envMap_idx]; exact hfn _ σ (hc i σ hi)

/-- A pushed environment meets the pushed slots (proved). -/
theorem push_env {Sv : Sites P} {τ : Nat → Sites P} {L : List Tm} {d v : Tm}
    (henv : ∀ i, VJ Fl g n (τ i) (envOf L d i)) (hv : VJ Fl g n Sv v) :
    ∀ i, VJ Fl g n (pushSites Sv τ i) (envOf (v :: L) d i)
  | 0 => by simpa [envOf, pushSites] using hv
  | i + 1 => by simpa [envOf, pushSites] using henv i

/-- A pushed environment meets the pushed signatures (proved). -/
theorem push_fn {vf : Option FnSig} {φ : Nat → Option FnSig} {L : List Tm} {d v : Tm}
    (hfn : ∀ i σ, φ i = some σ → FnIs P σ (envOf L d i)) (hv : ∀ σ, vf = some σ → FnIs P σ v) :
    ∀ i σ, pushFn vf φ i = some σ → FnIs P σ (envOf (v :: L) d i)
  | 0, σ, h => by simpa [envOf] using hv σ h
  | i + 1, σ, h => by simpa [envOf] using hfn i σ h

/-- **The checks of a continuation give its conditions** (proved). -/
theorem contOk_of_chk {π : CodeFlow P} {l : Nat} {k : Continuation} (h : ContChk π l k) :
    ContOk Fl π l k ∧ ContFn π l k := by
  cases k with
  | ret => exact ⟨h, trivial⟩
  | bind y =>
    exact ⟨fun _ _ _ _ _ henv hv => carries_env h.1 (push_env henv hv),
      fun _ _ _ hfn hv => carries_fn h.2 (push_fn hfn hv)⟩
  | effect y => exact ⟨fun _ _ _ _ henv => carries_env h.1 henv, fun _ _ hfn => carries_fn h.2 hfn⟩
  | branch y n =>
    exact ⟨fun _ _ _ _ henv => ⟨carries_env h.1.1 henv, carries_env h.2.1 henv⟩,
      fun _ _ hfn => ⟨carries_fn h.1.2 hfn, carries_fn h.2.2 hfn⟩⟩
  | branchBind y n =>
    exact ⟨fun _ _ _ _ henv => ⟨carries_env h.1.1 (push_env henv (VJ.prim rfl)),
        carries_env h.2.1 (push_env henv (VJ.prim rfl))⟩,
      fun _ _ hfn => ⟨carries_fn h.1.2 (push_fn hfn (by simp)), carries_fn h.2.2 (push_fn hfn (by simp))⟩⟩
  | tagBind _ y n =>
    exact ⟨fun _ _ _ _ _ henv hv => ⟨carries_env h.1.1 (push_env henv hv), carries_env h.2.1 (push_env henv hv)⟩,
      fun _ _ _ hfn hv => ⟨carries_fn h.1.2 (push_fn hfn hv), carries_fn h.2.2 (push_fn hfn hv)⟩⟩

/-- **The checks of a handler give its conditions** (proved). -/
theorem handlerOk_of_chk {π : CodeFlow P} {l : Nat} {x : Option Target} (h : HandlerChk Fl π l x) :
    HandlerOk Fl π l x ∧ HandlerFn π l x := by
  cases x with
  | none => exact ⟨trivial, trivial⟩
  | some y =>
    exact ⟨fun _ _ _ _ _ henv hv => carries_env h.1 (push_env henv hv),
      fun _ _ _ hfn => carries_fn h.2 (push_fn hfn (by simp))⟩

/-! ## The checks of a code -/

variable (Fl) in
/-- **The checks of a code**: each node expression fits the node's value
set openly at the node's slots and signatures; a node value naming a
signature is a slot naming it; each continuation and handler carries the
node into its targets. -/
def CodeChk (m : Code) (π : CodeFlow P) : Prop :=
  ∀ l e k x, m.1[l]? = some e → m.2[l]? = some (k, x) →
    OFits Fl (π.env l) (π.fn l) 0 (fun _ => none) π.alloc false (π.val l) e ∧
    (∀ σ, π.vfn l = some σ → ∃ j, e = .var j ∧ π.fn l j = some σ) ∧
    ContChk π l k ∧ HandlerChk Fl π l x

/-- **The checks of a code give `CodeOk`** (proved, `ofits_sound`,
`contOk_of_chk`, `handlerOk_of_chk`). -/
theorem codeOk_of_chk {m : Code} {π : CodeFlow P} (h : CodeChk Fl m π) : CodeOk Fl m π := by
  intro l e k x he hk
  obtain ⟨hf, hv, hc, hh⟩ := h l e k x he hk
  have hc' := contOk_of_chk (Fl := Fl) hc
  have hh' := handlerOk_of_chk hh
  refine ⟨fun g n L d henv hfn => ⟨ofits_sound henv hfn hf, fun σ hσ => ?_⟩, hc'.1, hh'.1, hc'.2, hh'.2⟩
  obtain ⟨j, rfl, hj⟩ := hv σ hσ
  simpa [instantiate] using hfn j σ hj

end Verification.TolerantFrames.ReadOnly
