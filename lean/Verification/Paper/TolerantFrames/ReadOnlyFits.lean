import Verification.Paper.TolerantFrames.ReadOnlySites

/-! # Read-only handles: the sites a term's values may reach

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
sites of a term"). The flow of `C`'s code (`ClientFrame.SitesSound`) gives,
at each step, the heap meeting a heap of sites and the roots of outside
code meeting a set `O`. Both are read from a typing of whole terms by sets
of sites (proof scope: the definitions and the lemmas below; preservation
by every step is not proved here):

- **A flow** (`Flow`): the set `O` of the sites outside code may see, a
  heap of sites `H`, and for each code of `C` its proposal (`CodeFlow`):
  at each node, the sites of each slot of the environment and of the node
  expression's value, and the sites its frames allocate at, objects and
  arrays apart (`Alloc`).
- **A term fits a set of sites** (`Fits Γ a S t`, `Γ` the sites of the
  variables a `letE` binds, `a` the sites the running frame allocates at),
  the rules by which its value, once computed, meets `S`. Every callee, receiver, actual and thrown value meets
  `O` (the callee is not known); a read's result meets the contents of
  the sites of the locations it may read, closed under prototypes; a
  write's value meets the contents of each site the written location may
  have; an allocation's initial values the contents of its site. A
  nested run of graph code fits when its environment meets the node's
  proposal (a code of `C`) or `O` (outside code), and its result meets `O`.
- **The proposal's conditions** (`CodeOk`): each node expression fits the
  node's value set from every environment meeting the node's slots; each
  continuation maps an environment meeting the node, with the node's value,
  to one meeting the target node; a returning node's value meets `O`; a
  handler's target accepts every value of `O`. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package}

/-- **A finite set of sites**, `none` for outside storage. -/
abbrev Sites (P : Package) := List (Option P.Site)

/-- **Inclusion of sets of sites.** -/
def Sub (S S' : Sites P) : Prop := ∀ s ∈ S, s ∈ S'

theorem Sub.refl (S : Sites P) : Sub S S := fun _ h => h

theorem Sub.trans {S₁ S₂ S₃ : Sites P} (h₁ : Sub S₁ S₂) (h₂ : Sub S₂ S₃) : Sub S₁ S₃ :=
  fun s hs => h₂ s (h₁ s hs)

/-- **The sites a frame allocates at**: an object's fields and identity
(`obj`), an array's cells, a grown cell among them (`arr`). -/
structure Alloc (P : Package) where
  obj : Option P.Site
  arr : Option P.Site

/-- The allocation sites of outside code: outside storage. -/
def Alloc.outside : Alloc P := ⟨none, none⟩

/-- **The proposal for one code of `C`**: at each node, the sites of each
slot of the environment (`env l i`) and of the node expression's value
(`val l`); the sites its frames allocate at. -/
structure CodeFlow (P : Package) where
  env : Nat → Nat → Sites P
  val : Nat → Sites P
  alloc : Alloc P

/-- **A flow**: the sites outside code may see, the heap of sites, and the
proposal for each code of `C`. -/
structure Flow (P : Package) where
  O : Sites P
  H : SiteHeap P
  code : Code → Option (CodeFlow P)

variable (Fl : Flow P)

/-- **What storage of a site may hold**: values meeting `S`, and the values
a closure there binds meeting them too. -/
def Stores (s : Option P.Site) (S : Sites P) : Prop := Sub S (Fl.H.contents s) ∧ Sub S (Fl.H.bindings s)

/-- **An environment meets the sites of a node's slots**, at a value
judgment `V`. -/
def EnvIn (V : Sites P → Val → Prop) (τ : Nat → Sites P) (L : List Tm) (d : Tm) : Prop :=
  ∀ i, V (τ i) (envOf L d i)

/-- The slot of a capture `i` of graph code of arity `n`: past the receiver
and the parameters, and the rest's spine when the code collects one. -/
def capSlot (n : Nat) (rest : Bool) (i : Nat) : Nat := (if rest then 1 else 0) + 1 + n + i

/-- **The values a value holds in its code**: itself, a capture of graph
code, a value of a graph code's node expressions, a part of a bound
function, and so on. -/
inductive Within (P : Package) : Val → Val → Prop where
  | refl (v : Val) : Within P v v
  | cap {fs n E K s caps k rest comp oid u w} : u ∈ caps → Within P u w →
      Within P (.objAt fs (.graph n E K s caps k rest comp) oid) w
  | code {fs n E K s caps k rest comp oid u w} : u ∈ valsArgs P.ofC true E → Within P u w →
      Within P (.objAt fs (.graph n E K s caps k rest comp) oid) w
  | bound {fs t r pre oid u w} : u ∈ t :: r :: pre → Within P u w → Within P (.objAt fs (.bound t r pre) oid) w

/-! ## Lowered code -/

/-- A primitive value: no location, no code. -/
def primVal : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | _ => false

/-- **A part of a closure's code in lowered code**: a variable, or a value
with no location. -/
def CodePart (t : Tm) : Prop := (∃ i, t = .var i) ∨ primVal t = true

mutual
/-- **A term of lowered code**: it holds no located value (an object, a
spine with a cell, a view spine, a typed array's allocation) and no run,
and every closure of `C`'s code it creates
has a proposal. The lowering emits no object and no run, so every node
expression of a lowered graph is one; outside code is lowered source, a
premise of the entries. -/
def Lowered : Tm → Prop
  | .objAt .. => False
  | .arr ls => ∀ x ∈ ls, x = none
  | .viewSpine .. => False
  | .goto .. => False
  | .frame .. => False
  | .invoke f r args => Lowered f ∧ Lowered r ∧ LoweredArgs args
  | .construct f args => Lowered f ∧ LoweredArgs args
  | .letE a b => Lowered a ∧ Lowered b
  | .makeAt .absent _ xs => LoweredArgs xs
  | .makeAt (.view _ _ _) _ _ => False
  | .makeAt (.bound t r pre) _ xs => CodePart t ∧ CodePart r ∧ (∀ x ∈ pre, CodePart x) ∧ LoweredArgs xs
  | .makeAt (.graph _ E K _ caps _ _ comp) _ xs =>
    (P.ofC comp = true → ∃ π, Fl.code (E, K) = some π) ∧ LoweredArgs E ∧ (∀ x ∈ caps, CodePart x) ∧ LoweredArgs xs
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => Lowered a
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    Lowered a ∧ Lowered b
  | .ite a b c | .setElem a b c => Lowered a ∧ Lowered b ∧ Lowered c
  | .arrLit xs => LoweredArgs xs
  | _ => True
termination_by structural t => t

def LoweredArgs : List Tm → Prop
  | [] => True
  | x :: xs => Lowered x ∧ LoweredArgs xs
termination_by structural xs => xs
end

theorem loweredArgs_iff : ∀ {xs : List Tm}, LoweredArgs Fl xs ↔ ∀ x ∈ xs, Lowered Fl x
  | [] => by simp [LoweredArgs]
  | x :: xs => by simp [LoweredArgs, loweredArgs_iff]

/-- **A closure of outside code has lowered code.** -/
def OutLowered (v : Val) : Prop :=
  ∀ fs ar E K s caps k rest comp oid, v = .objAt fs (.graph ar E K s caps k rest comp) oid →
    P.ofC comp = false → ∀ e ∈ E, Lowered Fl e

variable (g : Ghost P) (n : Nat)

/-- **A closure of `C`'s code meets its code's proposal**: each capture
meets the sites of its slot at the code's entry and references allocated
locations. -/
def CapsOk (v : Val) : Prop :=
  ∀ fs ar E K s caps k rest comp oid, v = .objAt fs (.graph ar E K s caps k rest comp) oid →
    P.ofC comp = true → ∃ π, Fl.code (E, K) = some π ∧ ∀ i u, caps[i]? = some u →
      SitesOf g (π.env s (capSlot ar rest i)) u ∧ ∀ l, Leaves P.ofC u l → l < n

/-- **A value meets a set of sites at a ghost and a heap length**: it is a
closed value, references allocated locations only, meets the sites; every
value it holds in its code is a value, every closure of `C`'s code among
them meets its proposal and every closure of outside code has lowered
code. Closed under allocation
(`VJ.alloc`). -/
structure VJ (S : Sites P) (v : Val) : Prop where
  val : isVal v = true
  closed : Verification.Closed v
  below : ∀ l, Leaves P.ofC v l → l < n
  sites : SitesOf g S v
  inner : ∀ w, Within P v w → isVal w = true ∧ CapsOk Fl g n w ∧ OutLowered Fl w

/-- The variables' sites under one more binder; `none` for a variable no
binder binds. -/
def consSites (S : Sites P) (Γ : Nat → Option (Sites P)) : Nat → Option (Sites P)
  | 0 => some S
  | i + 1 => Γ i

variable {g n}

/-- **A value meeting a set, or a variable a binder binds to a smaller
set**: a position of a closure's code or a run's environment, filled with
a value when the binder's value is substituted. -/
def VOr (V : Sites P → Val → Prop) (Γ : Nat → Option (Sites P)) (S : Sites P) (u : Tm) : Prop :=
  V S u ∨ ∃ j S', u = .var j ∧ Γ j = some S' ∧ Sub S' S

theorem VOr.imp {V V' : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {S : Sites P} {u : Tm}
    (hV : ∀ S v, V S v → V' S v) (h : VOr V Γ S u) : VOr V' Γ S u := h.imp_left (hV _ _)

/-- **A term fits a set of sites** at a value judgment `V` (the module's
header). -/
inductive Fits (V : Sites P → Val → Prop) : (Nat → Option (Sites P)) → Alloc P → Sites P → Tm → Prop where
  | val {Γ a S v} : isVal v = true → V S v → Fits V Γ a S v
  | var {Γ a S S' i} : Γ i = some S' → Sub S' S → Fits V Γ a S (.var i)
  | invoke {Γ a S f r args} : Fits V Γ a Fl.O f → Fits V Γ a Fl.O r → (∀ x ∈ args, Fits V Γ a Fl.O x) →
      Sub Fl.O S → a.arr ∈ Fl.O → Fits V Γ a S (.invoke f r args)
  | construct {Γ a S f args} : Fits V Γ a Fl.O f → (∀ x ∈ args, Fits V Γ a Fl.O x) → Sub Fl.O S →
      a.arr ∈ Fl.O → Fits V Γ a S (.construct f args)
  | letE {Γ a S Sx x b} : Fits V Γ a Sx x → Fits V (consSites Sx Γ) a S b → Fits V Γ a S (.letE x b)
  | spread {Γ a S Sx x} : Fits V Γ a Sx x → (∀ s ∈ Sx, Sub (Fl.H.contents s) S) → Fits V Γ a S (.spread x)
  | makeAbsent {Γ a S ns inits} : (Ss : Tm → Sites P) → (∀ x ∈ inits, Stores Fl a.obj (Ss x)) → (∀ x ∈ inits, Fits V Γ a (Ss x) x) → a.obj ∈ S →
      Fits V Γ a S (.makeAt .absent ns inits)
  | makeView {Γ a S sp fm len ns inits} : (Ss : Tm → Sites P) → (∀ x ∈ inits, Stores Fl a.obj (Ss x)) → (∀ x ∈ inits, Fits V Γ a (Ss x) x) →
      a.obj ∈ S → V S (.objAt [] (.view sp fm len) 0) → Fits V Γ a S (.makeAt (.view sp fm len) ns inits)
  | makeBound {Γ a S t r pre ns inits} : (Ss : Tm → Sites P) → (∀ x ∈ inits, Stores Fl a.obj (Ss x)) →
      (∀ x ∈ inits, Fits V Γ a (Ss x) x) → a.obj ∈ S → (∀ x ∈ t :: r :: pre, VOr V Γ S x) →
      Fits V Γ a S (.makeAt (.bound t r pre) ns inits)
  | makeGraphC {Γ a S ar E K s caps k rest comp ns inits} (π : CodeFlow P) :
      (Ss : Tm → Sites P) → (∀ x ∈ inits, Stores Fl a.obj (Ss x)) → (∀ x ∈ inits, Fits V Γ a (Ss x) x) →
      a.obj ∈ S → P.ofC comp = true → Fl.code (E, K) = some π →
      (∀ i u, caps[i]? = some u → VOr V Γ (π.env s (capSlot ar rest i)) u) → (∀ e ∈ E, Lowered Fl e) →
      Fits V Γ a S (.makeAt (.graph ar E K s caps k rest comp) ns inits)
  | makeGraphOut {Γ a S ar E K s caps k rest comp ns inits} :
      (Ss : Tm → Sites P) → (∀ x ∈ inits, Stores Fl a.obj (Ss x)) → (∀ x ∈ inits, Fits V Γ a (Ss x) x) →
      a.obj ∈ S → P.ofC comp = false → (∀ e ∈ E, Lowered Fl e) → (∀ u ∈ caps, VOr V Γ S u) →
      Fits V Γ a S (.makeAt (.graph ar E K s caps k rest comp) ns inits)
  | readAt {Γ a S Sx Q f x} : Fits V Γ a Sx x → Sub Sx Q → (∀ s ∈ Q, Sub (Fl.H.contents s) Q) →
      (∀ s ∈ Q, Sub (Fl.H.contents s) S) → Fits V Γ a S (.readAt f x)
  | indexAt {Γ a S Sx Q Sk x key} : Fits V Γ a Sx x → Fits V Γ a Sk key → Sub Sx Q →
      (∀ s ∈ Q, Sub (Fl.H.contents s) Q) → (∀ s ∈ Q, Sub (Fl.H.contents s) S) →
      Fits V Γ a S (.indexAt x key)
  | writeAt {Γ a S Sx Sy f x y} : Fits V Γ a Sx x → Fits V Γ a Sy y → (∀ s ∈ Sx, Stores Fl s Sy) →
      Fits V Γ a S (.writeAt f x y)
  | test {Γ a S Sx k x} : Fits V Γ a Sx x → Fits V Γ a S (.test k x)
  | ite {Γ a S Sc c x y} : Fits V Γ a Sc c → Fits V Γ a S x → Fits V Γ a S y → Fits V Γ a S (.ite c x y)
  | arith {Γ a S Sx Sy op x y} : Fits V Γ a Sx x → Fits V Γ a Sy y → Fits V Γ a S (.arith op x y)
  | arrLit {Γ a S inits} : (Ss : Tm → Sites P) → (∀ x ∈ inits, Stores Fl a.arr (Ss x)) → (∀ x ∈ inits, Fits V Γ a (Ss x) x) → a.arr ∈ S →
      Fits V Γ a S (.arrLit inits)
  | elemAt {Γ a S Sx Si x i} : Fits V Γ a Sx x → Fits V Γ a Si i → (∀ s ∈ Sx, Sub (Fl.H.contents s) S) →
      Fits V Γ a S (.elemAt x i)
  | setElem {Γ a S Sx Si Sv x i v} : Fits V Γ a Sx x → Fits V Γ a Si i → Fits V Γ a Sv v →
      (∀ s ∈ a.arr :: Sx, Stores Fl s Sv) → Sub Sx S → a.arr ∈ S → Fits V Γ a S (.setElem x i v)
  | lenOf {Γ a S Sx x} : Fits V Γ a Sx x → Fits V Γ a S (.lenOf x)
  | throw {Γ a S x} : Fits V Γ a Fl.O x → Fits V Γ a S (.throw x)
  | merge {Γ a S Sx Sy d x y} : Fits V Γ a Sx x → Fits V Γ a Sy y →
      (∀ s ∈ Sx ++ Sy, Stores Fl a.obj (Fl.H.contents s)) → a.obj ∈ S → Fits V Γ a S (.merge d x y)
  | makeKey {Γ a S Sk Sx k x} : Fits V Γ a Sk k → Stores Fl a.obj Sx → Fits V Γ a Sx x → a.obj ∈ S →
      Fits V Γ a S (.makeKey k x)
  | gotoC {Γ a S E K l L d comp} (π : CodeFlow P) : P.ofC comp = true → Fl.code (E, K) = some π →
      (∀ i, VOr V Γ (π.env l i) (envOf L d i)) → Sub Fl.O S → Fits V Γ a S (.goto E K l L d comp)
  | gotoOut {Γ a S E K l L d comp} : P.ofC comp = false → (∀ e ∈ E, Lowered Fl e) →
      (∀ i, VOr V Γ Fl.O (envOf L d i)) → Sub Fl.O S → Fits V Γ a S (.goto E K l L d comp)
  | frameC {Γ a S E K t L d k x comp} (π : CodeFlow P) (l : Nat) : P.ofC comp = true →
      Fl.code (E, K) = some π → NodeOf (E, K) l k x → (∀ i, V (π.env l i) (envOf L d i)) →
      Fits V Γ π.alloc (π.val l) t → Sub Fl.O S → Fits V Γ a S (.frame E K t L d k x comp)
  | frameOut {Γ a S E K t L d k x comp} : P.ofC comp = false → (∀ e ∈ E, Lowered Fl e) →
      (∀ i, V Fl.O (envOf L d i)) →
      Fits V Γ Alloc.outside Fl.O t → Sub Fl.O S → Fits V Γ a S (.frame E K t L d k x comp)

/-- **A value judgment monotone in its set of sites.** -/
def Mono (V : Sites P → Val → Prop) : Prop := ∀ S S' v, Sub S S' → V S v → V S' v

variable {Fl}

/-- **A term fits at a weaker value judgment** (proved): `Fits` reads values
only through `V`. -/
theorem Fits.mono {V V' : Sites P → Val → Prop} (hV : ∀ S v, V S v → V' S v) :
    ∀ {Γ a S t}, Fits Fl V Γ a S t → Fits Fl V' Γ a S t := by
  intro Γ a S t h
  induction h with
  | val hv h₀ => exact .val hv (hV _ _ h₀)
  | var h₁ h₂ => exact .var h₁ h₂
  | invoke _ _ _ hS ha ihf ihr iha => exact .invoke ihf ihr iha hS ha
  | construct _ _ hS ha ihf iha => exact .construct ihf iha hS ha
  | letE _ _ ihx ihb => exact .letE ihx ihb
  | spread _ hc ih => exact .spread ih hc
  | makeAbsent Ss hst _ hs ih => exact .makeAbsent Ss hst ih hs
  | makeView Ss hst _ hs hv ih => exact .makeView Ss hst ih hs (hV _ _ hv)
  | makeBound Ss hst _ hs hp ih => exact .makeBound Ss hst ih hs (fun x hx => (hp x hx).imp hV)
  | makeGraphC π Ss hst _ hs hc hcode hcaps hE ih =>
    exact .makeGraphC π Ss hst ih hs hc hcode (fun i u hu => (hcaps i u hu).imp hV) hE
  | makeGraphOut Ss hst _ hs hc hE hcaps ih =>
    exact .makeGraphOut Ss hst ih hs hc hE (fun u hu => (hcaps u hu).imp hV)
  | readAt _ hq hcl hr ih => exact .readAt ih hq hcl hr
  | indexAt _ _ hq hcl hr ihx ihk => exact .indexAt ihx ihk hq hcl hr
  | writeAt _ _ hst ihx ihy => exact .writeAt ihx ihy hst
  | test _ ih => exact .test ih
  | ite _ _ _ ihc ihx ihy => exact .ite ihc ihx ihy
  | arith _ _ ihx ihy => exact .arith ihx ihy
  | arrLit Ss hst _ hs ih => exact .arrLit Ss hst ih hs
  | elemAt _ _ hc ihx ihi => exact .elemAt ihx ihi hc
  | setElem _ _ _ hst hS ha ihx ihi ihv => exact .setElem ihx ihi ihv hst hS ha
  | lenOf _ ih => exact .lenOf ih
  | throw _ ih => exact .throw ih
  | merge _ _ hst hs ihx ihy => exact .merge ihx ihy hst hs
  | makeKey _ hst _ hs ihk ihx => exact .makeKey ihk hst ihx hs
  | gotoC π hc hcode henv hS => exact .gotoC π hc hcode (fun i => (henv i).imp hV) hS
  | gotoOut hc hE henv hS => exact .gotoOut hc hE (fun i => (henv i).imp hV) hS
  | frameC π l hc hcode hn henv _ hS ih => exact .frameC π l hc hcode hn (fun i => hV _ _ (henv i)) ih hS
  | frameOut hc hE henv _ hS ih => exact .frameOut hc hE (fun i => hV _ _ (henv i)) ih hS

/-- **A value fits only by its value judgment** (proved): every other rule
types a term that is not a value. -/
theorem Fits.value {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {a : Alloc P} {S : Sites P} {v : Val}
    (h : Fits Fl V Γ a S v) (hv : isVal v = true) : V S v := by
  cases h <;> first | assumption | simp [isVal] at hv

/-! ## Allocation keeps what a value meets -/

theorem VJ.sub {S S' : Sites P} {v : Val} (h : VJ Fl g n S v) (hS : Sub S S') : VJ Fl g n S' v :=
  ⟨h.val, h.closed, h.below, h.sites.mono hS, h.inner⟩

theorem VJ.mono : Mono (VJ Fl g n) := fun _ _ _ hS h => h.sub hS

theorem CapsOk.alloc {w : Val} {n' : Nat} {sf : Nat → Option P.Site} {key : Nat → Option PropKey}
    (h : CapsOk Fl g n w) (hn : n ≤ n') : CapsOk Fl (g.alloc n sf key) n' w := by
  intro fs ar E K s caps k rest comp oid hw hc
  obtain ⟨π, hπ, hcaps⟩ := h fs ar E K s caps k rest comp oid hw hc
  exact ⟨π, hπ, fun i u hu => ⟨(hcaps i u hu).1.alloc (hcaps i u hu).2,
    fun l hl => Nat.lt_of_lt_of_le ((hcaps i u hu).2 l hl) hn⟩⟩

/-- **Allocation keeps what a value meets** (proved): the allocation keeps
the site of every location the value references. -/
theorem VJ.alloc {S : Sites P} {v : Val} {n' : Nat} {sf : Nat → Option P.Site} {key : Nat → Option PropKey}
    (h : VJ Fl g n S v) (hn : n ≤ n') : VJ Fl (g.alloc n sf key) n' S v :=
  ⟨h.val, h.closed, fun l hl => Nat.lt_of_lt_of_le (h.below l hl) hn, h.sites.alloc h.below,
    fun w hw => ⟨(h.inner w hw).1, (h.inner w hw).2.1.alloc hn, (h.inner w hw).2.2⟩⟩

/-- **Allocation keeps a term fitting** (proved, `Fits.mono`). -/
theorem Fits.alloc {Γ : Nat → Option (Sites P)} {a : Alloc P} {S : Sites P} {t : Tm} {n' : Nat}
    {sf : Nat → Option P.Site} {key : Nat → Option PropKey} (h : Fits Fl (VJ Fl g n) Γ a S t) (hn : n ≤ n') :
    Fits Fl (VJ Fl (g.alloc n sf key) n') Γ a S t :=
  h.mono fun _ _ hv => hv.alloc hn

theorem VOr.alloc {Γ : Nat → Option (Sites P)} {S : Sites P} {u : Tm} {n' : Nat}
    {sf : Nat → Option P.Site} {key : Nat → Option PropKey} (h : VOr (VJ Fl g n) Γ S u) (hn : n ≤ n') :
    VOr (VJ Fl (g.alloc n sf key) n') Γ S u :=
  h.imp fun _ _ hv => hv.alloc hn

/-- **At a closed term a position is a value** (proved). -/
theorem VOr.top {V : Sites P → Val → Prop} {S : Sites P} {u : Tm} (h : VOr V (fun _ => none) S u) : V S u := by
  rcases h with h | ⟨_, _, _, h, _⟩
  · exact h
  · cases h

/-! ## The heap -/

variable (Fl g) in
/-- **A heap meets the flow**: each location holds a value, meeting the
contents of its site at the heap's length, its code's values meeting the
bindings of its site. -/
def HeapInv (h : Heap) : Prop :=
  ∀ w u, h[w]? = some u → VJ Fl g h.length (Fl.H.contents (g.site w)) u ∧
    ∀ x ∈ codeVals P.ofC u, SitesOf g (Fl.H.bindings (g.site w)) x

/-- A heap meeting the flow meets the heap of sites (proved). -/
theorem HeapInv.sites {h : Heap} (hH : HeapInv Fl g h) : HeapSites g Fl.H h :=
  fun w u hw => ⟨(hH w u hw).1.sites, (hH w u hw).2⟩

/-! ## The frame a step runs in -/

mutual
/-- **The innermost frame and the active term**: the code and tag of the
innermost frame around the term `redex` the next step reduces, following
`Step`'s congruence rules as `path` does; `cur` outside every frame. -/
def activeFrame (cur : Option (Code × ComponentTag)) : Tm → Option (Code × ComponentTag) × Tm
  | .invoke f r args =>
    if isVal f = false then activeFrame cur f
    else if isVal r = false then activeFrame cur r
    else activeArgs cur (.invoke f r args) args
  | .construct f args =>
    if isVal f = false then activeFrame cur f else activeArgs cur (.construct f args) args
  | .letE a b => if isVal a = false then activeFrame cur a else (cur, .letE a b)
  | .makeAt cc ns xs => activeArgs cur (.makeAt cc ns xs) xs
  | .readAt f a => if isVal a = false then activeFrame cur a else (cur, .readAt f a)
  | .indexAt a key =>
    if isVal a = false then activeFrame cur a
    else if isVal key = false then activeFrame cur key else (cur, .indexAt a key)
  | .writeAt f a b =>
    if isVal a = false then activeFrame cur a
    else if isVal b = false then activeFrame cur b else (cur, .writeAt f a b)
  | .test k a => if isVal a = false then activeFrame cur a else (cur, .test k a)
  | .ite x a b => if isVal x = false then activeFrame cur x else (cur, .ite x a b)
  | .arith op a b =>
    if isVal a = false then activeFrame cur a
    else if isVal b = false then activeFrame cur b else (cur, .arith op a b)
  | .arrLit xs => activeArgs cur (.arrLit xs) xs
  | .elemAt a i =>
    if isVal a = false then activeFrame cur a
    else if isVal i = false then activeFrame cur i else (cur, .elemAt a i)
  | .setElem a i v =>
    if isVal a = false then activeFrame cur a
    else if isVal i = false then activeFrame cur i
    else if isVal v = false then activeFrame cur v else (cur, .setElem a i v)
  | .lenOf a => if isVal a = false then activeFrame cur a else (cur, .lenOf a)
  | .spread a => if isVal a = false then activeFrame cur a else (cur, .spread a)
  | .throw a => if isVal a = false then activeFrame cur a else (cur, .throw a)
  | .merge d a b =>
    if isVal a = false then activeFrame cur a
    else if isVal b = false then activeFrame cur b else (cur, .merge d a b)
  | .makeKey k a =>
    if isVal k = false then activeFrame cur k
    else if isVal a = false then activeFrame cur a else (cur, .makeKey k a)
  | .frame E K t _ _ _ _ comp => activeFrame (some ((E, K), comp)) t
  | t => (cur, t)
termination_by structural t => t

/-- The active frame through a list evaluated left to right, `t` the term
when every element is a value. -/
def activeArgs (cur : Option (Code × ComponentTag)) (t : Tm) : List Tm → Option (Code × ComponentTag) × Tm
  | [] => (cur, t)
  | a :: as => if isVal a = false then activeFrame cur a else activeArgs cur t as
termination_by structural xs => xs
end

variable (Fl) in
/-- **The allocation sites of a frame**: its code's proposal for a frame of
`C`'s code, outside storage for outside code. -/
def allocOf : Option (Code × ComponentTag) → Alloc P
  | some (m, comp) => if P.ofC comp = true then ((Fl.code m).map CodeFlow.alloc).getD Alloc.outside else Alloc.outside
  | none => Alloc.outside

variable (Fl) in
/-- **The site of a step's fresh locations**: an array's cells where the
active term builds or grows an array, an object's otherwise, at the
allocation sites of the innermost frame. -/
def stepSite (cur : Option (Code × ComponentTag)) (t : Tm) : Option P.Site :=
  match activeFrame cur t with
  | (fr, .arrLit _) => (allocOf Fl fr).arr
  | (fr, .setElem _ _ _) => (allocOf Fl fr).arr
  | (fr, _) => (allocOf Fl fr).obj

/-! ## The proposal's conditions -/

variable (Fl) in
/-- **A continuation's targets accept a node's environment and value**: the
environment each edge maps to meets the target node's slots. -/
def ContOk (π : CodeFlow P) (l : Nat) : Continuation → Prop
  | .ret => Sub (π.val l) Fl.O
  | .bind y => ∀ V, Mono V → ∀ L d v, EnvIn V (π.env l) L d → V (π.val l) v →
      EnvIn V (π.env y.label) (envMap y.mapping (v :: L) d).1 (envMap y.mapping (v :: L) d).2
  | .effect y => ∀ V, Mono V → ∀ L d, EnvIn V (π.env l) L d →
      EnvIn V (π.env y.label) (envMap y.mapping L d).1 (envMap y.mapping L d).2
  | .branch y n => ∀ V, Mono V → ∀ L d, EnvIn V (π.env l) L d →
      EnvIn V (π.env y.label) (envMap y.mapping L d).1 (envMap y.mapping L d).2 ∧
      EnvIn V (π.env n.label) (envMap n.mapping L d).1 (envMap n.mapping L d).2
  | .branchBind y n => ∀ V, Mono V → ∀ L d, EnvIn V (π.env l) L d →
      EnvIn V (π.env y.label) (envMap y.mapping (.tru :: L) d).1 (envMap y.mapping (.tru :: L) d).2 ∧
      EnvIn V (π.env n.label) (envMap n.mapping (.fls :: L) d).1 (envMap n.mapping (.fls :: L) d).2
  | .tagBind _ y n => ∀ V, Mono V → ∀ L d v, EnvIn V (π.env l) L d → V (π.val l) v →
      EnvIn V (π.env y.label) (envMap y.mapping (v :: L) d).1 (envMap y.mapping (v :: L) d).2 ∧
      EnvIn V (π.env n.label) (envMap n.mapping (v :: L) d).1 (envMap n.mapping (v :: L) d).2

variable (Fl) in
/-- **A handler accepts every value of `O`.** -/
def HandlerOk (π : CodeFlow P) (l : Nat) : Option Target → Prop
  | none => True
  | some y => ∀ V, Mono V → ∀ L d v, EnvIn V (π.env l) L d → V Fl.O v →
      EnvIn V (π.env y.label) (envMap y.mapping (v :: L) d).1 (envMap y.mapping (v :: L) d).2

variable (Fl) in
/-- **A proposal meets the code's nodes**: each node expression fits its
value set from every environment meeting its slots; each continuation and
handler accepts it. -/
def CodeOk (m : Code) (π : CodeFlow P) : Prop :=
  ∀ l e k x, m.1[l]? = some e → m.2[l]? = some (k, x) →
    (∀ (g : Ghost P) n (L : List Tm) d, EnvIn (VJ Fl g n) (π.env l) L d →
      Fits Fl (VJ Fl g n) (fun _ => none) π.alloc (π.val l) (instantiate 0 (envOf L d) e)) ∧
    ContOk Fl π l k ∧ HandlerOk Fl π l x

variable (Fl) in
/-- **A flow meets every code it proposes for.** -/
def Flow.Ok : Prop := ∀ m π, Fl.code m = some π → CodeOk Fl m π

/-! ## Every step keeps a term fitting -/

variable (Fl) in
/-- **The facts of a flow every step reads**: its proposals meet their
codes; `O` holds outside storage, is closed in the heap of sites, and its
storage may hold all of `O`; every slot of every node accepts `O`. -/
structure Flow.Facts : Prop where
  ok : Fl.Ok
  none : none ∈ Fl.O
  closed : ∀ s ∈ Fl.O, Sub (Fl.H.contents s) Fl.O
  writable : ∀ s ∈ Fl.O, Stores Fl s Fl.O
  envO : ∀ m π, Fl.code m = some π → ∀ l i, Sub Fl.O (π.env l i)

/-- A heap meeting the flow keeps meeting it at a step that allocates
nothing (proved). -/
theorem HeapInv.same {h : Heap} {sf : Nat → Option P.Site} {key : Nat → Option PropKey} (hH : HeapInv Fl g h) :
    HeapInv Fl (g.alloc h.length sf key) h := by
  intro w u hw
  have hl : w < h.length := (List.getElem?_eq_some_iff.mp hw).1
  rw [(Ghost.alloc_old hl).1]
  obtain ⟨hv, hb⟩ := hH w u hw
  exact ⟨hv.alloc (Nat.le_refl _), fun x hx => (hb x hx).alloc fun l hl => hv.below l (Leaves.code hx hl)⟩

/-- A term that steps is not a value. -/
theorem notVal_of_step {h h' : Heap} {a a' : Tm} (hs : Step h a h' a') : isVal a = false := by
  cases hv : isVal a
  · rfl
  · exact absurd hs (value_no_step hv)

/-- **The active frame of a list at its first term that is not a value**
(proved). -/
theorem activeArgs_at {cur : Option (Code × ComponentTag)} {t a : Tm} :
    ∀ {args : List Tm} {i : Nat}, args[i]? = some a → (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) →
      isVal a = false → activeArgs cur t args = activeFrame cur a
  | [], _, h, _, _ => by simp at h
  | b :: bs, 0, h, _, hn => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [activeArgs, hn]
  | b :: bs, i + 1, h, hpre, hn => by
    have hb : isVal b = true := hpre 0 (Nat.zero_lt_succ _) b rfl
    simp only [activeArgs, hb, Bool.true_eq_false, if_false]
    exact activeArgs_at (by simpa using h) (fun j hj v hv => hpre (j + 1) (by omega) v (by simpa using hv)) hn

/-- The elements of a list with one replaced (proved). -/
theorem mem_set_cases {l : List Tm} {i : Nat} {b x : Tm} (hx : x ∈ l.set i b) : x ∈ l ∨ x = b :=
  List.mem_or_eq_of_mem_set hx

theorem mem_set_cases' {α : Type} {l : List α} {i : Nat} {b x : α} (hx : x ∈ l.set i b) : x ∈ l ∨ x = b :=
  List.mem_or_eq_of_mem_set hx

theorem allocOf_C {m : Code} {comp : ComponentTag} {π : CodeFlow P} (hc : P.ofC comp = true)
    (hcode : Fl.code m = some π) : allocOf Fl (some (m, comp)) = π.alloc := by
  simp [allocOf, hc, hcode]

theorem allocOf_out {m : Code} {comp : ComponentTag} (hc : P.ofC comp = false) :
    allocOf Fl (some (m, comp)) = Alloc.outside := by
  simp [allocOf, hc]

open Classical in
/-- **A list with one element stepped keeps its sites** (proved): the
stepped element takes the sites of the one it replaces. -/
theorem sites_set {St : Sites P → Prop} {Fi Fi' : Sites P → Tm → Prop} {Ss : Tm → Sites P} {inits : List Tm}
    {i : Nat} {a a' : Tm} (hai : inits[i]? = some a) (hst : ∀ x ∈ inits, St (Ss x))
    (hi : ∀ x ∈ inits, Fi (Ss x) x) (ha' : Fi' (Ss a) a') (hlift : ∀ S x, Fi S x → Fi' S x) :
    (∀ x ∈ inits.set i a', St ((fun y => if y = a' then Ss a else Ss y) x)) ∧
      ∀ x ∈ inits.set i a', Fi' ((fun y => if y = a' then Ss a else Ss y) x) x := by
  have hm := List.mem_of_getElem? hai
  constructor
  · intro x hx
    by_cases he : x = a'
    · simp only [he, if_true]; exact hst a hm
    · simp only [he, if_false]
      rcases mem_set_cases hx with hx | hx
      · exact hst x hx
      · exact absurd hx he
  · intro x hx
    by_cases he : x = a'
    · simp only [he, if_true]; exact ha'
    · simp only [he, if_false]
      rcases mem_set_cases hx with hx | hx
      · exact hlift _ _ (hi x hx)
      · exact absurd hx he

/-! ### Values that reference nothing -/

/-- **A value with no location and no code meets every set** (proved). -/
theorem VJ.atom {S : Sites P} {v : Val} (hv : isVal v = true) (hc : Verification.Closed v)
    (hcode : codeVals P.ofC v = []) (hnext : ∀ a, next v a = none)
    (hw : ∀ w, Within P v w → w = v) (hcap : ∀ fs ar E K s caps k rest comp oid,
      v ≠ .objAt fs (.graph ar E K s caps k rest comp) oid) : VJ Fl g n S v := by
  have hl : ∀ l, ¬ Leaves P.ofC v l := by
    rintro l ⟨x, hx, a, hn⟩
    cases hx with
    | refl => rw [hnext a] at hn; cases hn
    | step hm _ => rw [hcode] at hm; cases hm
  refine ⟨hv, hc, fun l h => (hl l h).elim, fun l h => (hl l h).elim, fun w hwv => ?_⟩
  rw [hw w hwv]
  exact ⟨hv, fun fs ar E K s caps k rest comp oid he => absurd he (hcap fs ar E K s caps k rest comp oid),
    fun fs ar E K s caps k rest comp oid he => absurd he (hcap fs ar E K s caps k rest comp oid)⟩

theorem VJ.prim {S : Sites P} {v : Val} (hp : primVal v = true) : VJ Fl g n S v := by
  refine VJ.atom ?_ ?_ ?_ ?_ ?_ ?_
  · cases v <;> simp [primVal] at hp <;> rfl
  · intro k a; cases v <;> simp [primVal] at hp <;> rfl
  · cases v <;> simp [primVal] at hp <;> rfl
  · intro a; cases v <;> simp [primVal] at hp <;> cases a <;> rfl
  · intro w hw; cases hw with
    | refl => rfl
    | cap => simp [primVal] at hp
    | code => simp [primVal] at hp
    | bound => simp [primVal] at hp
  · intro fs ar E K s caps k rest comp oid he; subst he; simp [primVal] at hp

/-- **A thrown error meets every set** (proved): an object with no field
and no code. -/
theorem VJ.thrown {S : Sites P} (i : Nat) : VJ Fl g n S (thrownError i) := by
  refine VJ.atom rfl (fun _ _ => rfl) rfl ?_ ?_ ?_
  · intro a; cases a <;> rfl
  · intro w hw; cases hw with
    | refl => rfl
  · intro fs ar E K s caps k rest comp oid he; cases he

/-- **The children a value holds in its code**: a capture or a node
expression's value of graph code, a part of a bound function. -/
def Child (v u : Val) : Prop :=
  (∃ fs n E K s caps k rest comp oid, v = .objAt fs (.graph n E K s caps k rest comp) oid ∧
    (u ∈ caps ∨ u ∈ valsArgs P.ofC true E)) ∨
  ∃ fs t r pre oid, v = .objAt fs (.bound t r pre) oid ∧ u ∈ t :: r :: pre

/-- **An object meets a set of sites** (proved): its field locations and
its descriptor's spine are allocated and of sites of the set, the values
its code holds meet the set, its children meet some set, and it meets its
code's proposal. -/
theorem VJ.obj {S : Sites P} {fs : List (PropKey × Nat)} {c : CallCode} {oid : Nat}
    (hc : Verification.Closed (.objAt fs c oid))
    (hfs : ∀ k l, (k, l) ∈ fs → l < n ∧ g.site l ∈ S)
    (hview : ∀ l, HeapKnowledge.descriptorSpine (.objAt fs c oid) = some l → l < n ∧ g.site l ∈ S)
    (hcode : ∀ x ∈ codeVals P.ofC (.objAt fs c oid), ∀ l, Leaves P.ofC x l → l < n ∧ g.site l ∈ S)
    (hchild : ∀ u, Child (P := P) (.objAt fs c oid) u → ∃ S', VJ Fl g n S' u)
    (hcaps : CapsOk Fl g n (.objAt fs c oid)) (hout : OutLowered Fl (.objAt fs c oid)) :
    VJ Fl g n S (.objAt fs c oid) := by
  have hl : ∀ l, Leaves P.ofC (.objAt fs c oid) l → l < n ∧ g.site l ∈ S := by
    rintro l ⟨x, hx, a, hn⟩
    cases hx with
    | refl =>
      cases a with
      | key k => exact hfs k l (lookup_mem_pair (by simpa [next, Footprints.fieldsOf] using hn))
      | view => exact hview l hn
      | cell i => simp [next, spineEntries] at hn
      | code i => cases hn
    | step hm hr => exact hcode _ hm l ⟨x, hr, a, hn⟩
  refine ⟨rfl, hc, fun l h => (hl l h).1, fun l h => (hl l h).2, fun w hw => ?_⟩
  cases hw with
  | refl => exact ⟨rfl, hcaps, hout⟩
  | cap hu hw' =>
    obtain ⟨S', hv⟩ := hchild _ (.inl ⟨_, _, _, _, _, _, _, _, _, _, rfl, .inl hu⟩)
    exact hv.inner w hw'
  | code hu hw' =>
    obtain ⟨S', hv⟩ := hchild _ (.inl ⟨_, _, _, _, _, _, _, _, _, _, rfl, .inr hu⟩)
    exact hv.inner w hw'
  | bound hu hw' =>
    obtain ⟨S', hv⟩ := hchild _ (.inr ⟨_, _, _, _, _, rfl, hu⟩)
    exact hv.inner w hw'

/-- **A value's positions reach only what the value reaches** (proved). -/
theorem leaves_of_vals {v x : Val} (hv : isVal v = true) (hx : x ∈ vals P.ofC true v) {l : Nat}
    (hl : Leaves P.ofC x l) : Leaves P.ofC v l := by
  cases v with
  | objAt fs cc i =>
    rw [vals_objAt] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl
    · exact Leaves.code hx hl
  | arr ls => simp [vals] at hx; subst hx; exact hl
  | viewSpine f cs => simp [vals] at hx; subst hx; exact hl
  | _ => simp [vals, isVal] at hx hv

theorem closed_bound {fs : List (PropKey × Nat)} {t r : Tm} {pre : List Tm} {oid : Nat}
    (ht : Verification.Closed t) (hr : Verification.Closed r) (hp : ∀ x ∈ pre, Verification.Closed x) :
    Verification.Closed (.objAt fs (.bound t r pre) oid) := by
  intro k a
  have : pre.map (subst k a) = pre := (List.map_congr_left fun x hx => hp x hx k a).trans (List.map_id _)
  simp [subst, ht k a, hr k a, this]

theorem closed_graph {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} (hc : ∀ x ∈ caps, Verification.Closed x) :
    Verification.Closed (.objAt fs (.graph ar E K s caps kd rest comp) oid) := by
  intro k a
  have : caps.map (subst k a) = caps := (List.map_congr_left fun x hx => hc x hx k a).trans (List.map_id _)
  simp [subst, this]

/-! ### The heap at a step -/

/-- **An allocation keeps the heap meeting the flow** (proved): each fresh
value meets the contents of its fresh location's site and its code's
values the bindings. -/
theorem HeapInv.append {h : Heap} {xs : List Val} {sf : Nat → Option P.Site} {key : Nat → Option PropKey}
    (hH : HeapInv Fl g h)
    (hnew : ∀ i u, xs[i]? = some u → VJ Fl (g.alloc h.length sf key) (h ++ xs).length
      (Fl.H.contents (sf (h.length + i))) u ∧
      ∀ x ∈ codeVals P.ofC u, SitesOf (g.alloc h.length sf key) (Fl.H.bindings (sf (h.length + i))) x) :
    HeapInv Fl (g.alloc h.length sf key) (h ++ xs) := by
  intro w u hw
  by_cases hlt : w < h.length
  · rw [List.getElem?_append_left hlt] at hw
    rw [(Ghost.alloc_old hlt).1]
    obtain ⟨hv, hb⟩ := hH w u hw
    exact ⟨hv.alloc (by simp), fun x hx => (hb x hx).alloc fun l hl => hv.below l (Leaves.code hx hl)⟩
  · rw [List.getElem?_append_right (by omega)] at hw
    have hs : (g.alloc h.length sf key).site w = sf (h.length + (w - h.length)) := by
      simp [Ghost.alloc, hlt, show h.length + (w - h.length) = w by omega]
    rw [hs]
    exact hnew _ u hw

/-- **A write keeps the heap meeting the flow** (proved): the written value
meets the contents of the location's site, its code's values the
bindings. -/
theorem HeapInv.set {h : Heap} {w : Nat} {u : Val} (hH : HeapInv Fl g h)
    (hu : VJ Fl g h.length (Fl.H.contents (g.site w)) u)
    (hb : ∀ x ∈ codeVals P.ofC u, SitesOf g (Fl.H.bindings (g.site w)) x) : HeapInv Fl g (h.set w u) := by
  intro x v hx
  rw [List.getElem?_set] at hx
  simp only [List.length_set]
  split at hx
  · rename_i he; subst he; split at hx
    · cases hx; exact ⟨hu, hb⟩
    · cases hx
  · exact hH x v hx

/-- **A read meets the contents of the location's site** (proved): a
location one step from a value meeting `Sx` is of a site of `Sx`, and its
contents meet that site's contents. -/
theorem HeapInv.read {h : Heap} {Sx : Sites P} {u v : Val} {a : Label} {l : Nat} (hH : HeapInv Fl g h)
    (hu : VJ Fl g h.length Sx u) (hn : next u a = some l) (hv : h[l]? = some v) :
    g.site l ∈ Sx ∧ VJ Fl g h.length (Fl.H.contents (g.site l)) v :=
  ⟨hu.sites l (Leaves.of_next hn), (hH l v hv).1⟩

/-- The location an index names in a spine is one step from it (proved). -/
theorem next_of_elemLoc {ls : List (Option Nat)} {b : UInt64} {l : Nat} (he : elemLoc ls b = some l) :
    ∃ k, next (.arr ls) (.cell k) = some l := by
  unfold elemLoc at he
  obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp he
  exact ⟨k, by simp only [next, spineEntries]; rw [← hk]; cases ls[k]? <;> rfl⟩

/-- **A spine meets the sites of its cells** (proved). -/
theorem VJ.arr {S : Sites P} {ls : List (Option Nat)}
    (hc : ∀ l, some l ∈ ls → l < n ∧ g.site l ∈ S) : VJ Fl g n S (.arr ls) := by
  have hl : ∀ l, Leaves P.ofC (.arr ls) l → some l ∈ ls := by
    rintro l ⟨x, hx, a, hn⟩
    cases hx with
    | refl =>
      cases a with
      | cell i =>
        simp only [next, spineEntries] at hn
        cases hi : ls[i]? with
        | none => rw [hi] at hn; cases hn
        | some o =>
          rw [hi] at hn
          cases o with
          | none => cases hn
          | some l' => cases hn; exact List.mem_of_getElem? hi
      | _ => cases hn
    | step hm _ => simp [codeVals] at hm
  refine ⟨rfl, fun _ _ => rfl, fun l h => (hc l (hl l h)).1, fun l h => (hc l (hl l h)).2, fun w hw => ?_⟩
  cases hw with
  | refl =>
    refine ⟨rfl, ?_, ?_⟩ <;> (intro _ _ _ _ _ _ _ _ _ _ he; cases he)

theorem mem_placeAt {ls : List (Option Nat)} {k l : Nat} {x : Option Nat} (hx : x ∈ placeAt ls k l) :
    x ∈ ls ∨ x = none ∨ x = some l := by
  unfold placeAt at hx
  rcases mem_set_cases' hx with hx | rfl
  · rcases List.mem_append.mp hx with hx | hx
    · exact .inl hx
    · exact .inr (.inl (List.eq_of_mem_replicate hx))
  · exact .inr (.inr rfl)

/-- **The cells of a spine one step from a value** (proved). -/
theorem cells_leaves {u : Val} {ls : List (Option Nat)} (hu : u = .arr ls) {l : Nat} (hl : some l ∈ ls) :
    Leaves P.ofC u l := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hl
  subst hu
  exact Leaves.of_next (a := .cell i) (by simp [next, spineEntries, hi])

/-- **A write keeps the heap meeting the flow at the step's ghost** (proved). -/
theorem HeapInv.set_same {h : Heap} {w : Nat} {u : Val} {sf : Nat → Option P.Site} {key : Nat → Option PropKey}
    (hH : HeapInv Fl g h) (hu : VJ Fl g h.length (Fl.H.contents (g.site w)) u)
    (hb : ∀ x ∈ codeVals P.ofC u, SitesOf g (Fl.H.bindings (g.site w)) x) :
    HeapInv Fl (g.alloc h.length sf key) (h.set w u) := by
  have := (hH.set hu hb).same (sf := sf) (key := key)
  rwa [List.length_set] at this

theorem stepSite_setElem {cur : Option (Code × ComponentTag)} {ls : List (Option Nat)} {b : UInt64} {v : Tm}
    (hv : isVal v = true) : stepSite Fl cur (.setElem (.arr ls) (.num b) v) = (allocOf Fl cur).arr := by
  simp only [stepSite, activeFrame, hv, show isVal (.arr ls) = true from rfl, show isVal (.num b) = true from rfl,
    Bool.true_eq_false, if_false]

theorem activeArgs_vals {cur : Option (Code × ComponentTag)} {t : Tm} :
    ∀ {xs : List Tm}, (∀ v ∈ xs, isVal v = true) → activeArgs cur t xs = (cur, t)
  | [], _ => by simp [activeArgs]
  | x :: xs, h => by
    simp only [activeArgs, h x (List.mem_cons_self ..), Bool.true_eq_false, if_false]
    exact activeArgs_vals fun v hv => h v (List.mem_cons_of_mem _ hv)

theorem stepSite_makeAt {cur : Option (Code × ComponentTag)} {c : CallCode} {ns : List PropKey} {vs : List Tm}
    (hvs : ∀ v ∈ vs, isVal v = true) : stepSite Fl cur (.makeAt c ns vs) = (allocOf Fl cur).obj := by
  simp only [stepSite, activeFrame, activeArgs_vals hvs]

theorem stepSite_arrLit {cur : Option (Code × ComponentTag)} {vs : List Tm}
    (hvs : ∀ v ∈ vs, isVal v = true) : stepSite Fl cur (.arrLit vs) = (allocOf Fl cur).arr := by
  simp only [stepSite, activeFrame, activeArgs_vals hvs]

theorem mem_slots : ∀ {base : Nat} {ns : List PropKey} {k : PropKey} {l : Nat}, (k, l) ∈ slots base ns →
    base ≤ l ∧ l < base + ns.length
  | _, [], _, _, h => by simp [slots] at h
  | base, n :: ns, k, l, h => by
    simp only [slots, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | h
    · simp
    · have := mem_slots h; simp; omega

/-- **An allocation of values each meeting the contents of one site keeps
the heap meeting the flow** (proved), a trailing identity location
included. -/
theorem HeapInv.fresh {h : Heap} {vs : List Val} {o : Option P.Site} {key : Nat → Option PropKey}
    {Ss : Tm → Sites P} (hH : HeapInv Fl g h) (hst : ∀ x ∈ vs, Stores Fl o (Ss x))
    (hv : ∀ x ∈ vs, VJ Fl g h.length (Ss x) x) (tail : List Val) (htail : ∀ x ∈ tail, primVal x = true) :
    HeapInv Fl (g.alloc h.length (fun _ => o) key) (h ++ (vs ++ tail)) := by
  refine hH.append fun i u hu => ?_
  rcases List.mem_append.mp (List.mem_of_getElem? hu) with hm | hm
  · have hv' := hv u hm
    exact ⟨(hv'.sub (hst u hm).1).alloc (by simp), fun x hx => ((hv'.sites.code hx).mono (hst u hm).2).alloc
      fun l hl => hv'.below l (Leaves.code hx hl)⟩
  · have hp := htail u hm
    refine ⟨VJ.prim hp, fun x hx => ?_⟩
    cases u <;> simp [primVal] at hp <;> simp [codeVals] at hx

theorem bound_all {V : Sites P → Val → Prop} {S : Sites P} {t r : Tm} {pre : List Tm} (ht : V S t) (hr : V S r)
    (hp : ∀ x ∈ pre, V S x) : ∀ y ∈ t :: r :: pre, V S y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact ht
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hr
  · exact hp y hy

/-- The values a bound function's code holds reach what its parts reach
(proved). -/
theorem bound_code {fs : List (PropKey × Nat)} {t r : Tm} {pre : List Tm} {oid : Nat} {S : Sites P}
    (hall : ∀ y ∈ t :: r :: pre, VJ Fl g n S y) :
    ∀ x ∈ codeVals P.ofC (.objAt fs (.bound t r pre) oid), ∀ l, Leaves P.ofC x l → l < n ∧ g.site l ∈ S := by
  intro x hx l hl
  simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap] at hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t :: r :: pre, x ∈ vals P.ofC true y := by
    rcases hx with (hx | hx) | ⟨y, hy, hx⟩
    · exact ⟨_, List.mem_cons_self .., hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hx⟩
    · exact ⟨y, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy), hx⟩
  have hyv := hall y hy
  have hle := leaves_of_vals hyv.val hxy hl
  exact ⟨hyv.below l hle, hyv.sites l hle⟩

theorem bound_child {fs : List (PropKey × Nat)} {t r : Tm} {pre : List Tm} {oid : Nat} {S : Sites P}
    (hall : ∀ y ∈ t :: r :: pre, VJ Fl g n S y) :
    ∀ u, Child (P := P) (.objAt fs (.bound t r pre) oid) u → ∃ S', VJ Fl g n S' u := by
  rintro u (⟨_, _, _, _, _, _, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, hu⟩)
  · cases he
  · cases he; exact ⟨_, hall u hu⟩

/-- **A closure of `C`'s code meets a set** (proved): its fields are of
sites of the set, its captures meet its code's proposal. -/
theorem VJ.graphC {S : Sites P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} {π : CodeFlow P} (hc : P.ofC comp = true) (hcode : Fl.code (E, K) = some π)
    (hfs : ∀ k l, (k, l) ∈ fs → l < n ∧ g.site l ∈ S)
    (hcaps : ∀ i u, caps[i]? = some u → VJ Fl g n (π.env s (capSlot ar rest i)) u)
    (hE : ∀ u ∈ valsArgs P.ofC true E, VJ Fl g n S u) :
    VJ Fl g n S (.objAt fs (.graph ar E K s caps kd rest comp) oid) := by
  have hcm : ∀ u ∈ caps, ∃ S', VJ Fl g n S' u := fun u hu =>
    let ⟨i, hi⟩ := List.getElem?_of_mem hu; ⟨_, hcaps i u hi⟩
  refine VJ.obj (closed_graph fun x hx => (hcm x hx).choose_spec.closed) hfs
    (fun l hl => by simp [HeapKnowledge.descriptorSpine] at hl) (fun x hx => by simp [codeVals, hc] at hx)
    ?_ ?_ ?_
  · rintro u (⟨_, _, _, _, _, _, _, _, _, _, he, hu⟩ | ⟨_, _, _, _, _, he, _⟩)
    · cases he
      rcases hu with hu | hu
      · exact hcm u hu
      · exact ⟨_, hE u hu⟩
    · cases he
  · intro fs' ar' E' K' s' caps' k' rest' comp' oid' he _
    cases he
    exact ⟨π, hcode, fun i u hu => ⟨(hcaps i u hu).sites, (hcaps i u hu).below⟩⟩
  · intro fs' ar' E' K' s' caps' k' rest' comp' oid' he hc'
    cases he
    rw [hc] at hc'; cases hc'

/-- **A closure of outside code meets a set** (proved): its fields, its
node expressions' values and its captures meet the set. -/
theorem VJ.graphOut {S : Sites P} {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm} {kd : Invoke} {rest : Bool}
    {comp : ComponentTag} {oid : Nat} (hc : P.ofC comp = false)
    (hfs : ∀ k l, (k, l) ∈ fs → l < n ∧ g.site l ∈ S)
    (hcaps : ∀ u ∈ caps, VJ Fl g n S u) (hE : ∀ u ∈ valsArgs P.ofC true E, VJ Fl g n S u)
    (hlow : ∀ e ∈ E, Lowered Fl e) :
    VJ Fl g n S (.objAt fs (.graph ar E K s caps kd rest comp) oid) := by
  refine VJ.obj (closed_graph fun x hx => (hcaps x hx).closed) hfs
    (fun l hl => by simp [HeapKnowledge.descriptorSpine] at hl) ?_ ?_ ?_ ?_
  · intro x hx l hl
    simp only [codeVals, hc, Bool.false_eq_true, if_false, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨(hE x hx).below l hl, (hE x hx).sites l hl⟩
    · simp only [valsArgs_eq, List.mem_flatMap] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hle := leaves_of_vals (hcaps y hy).val hxy hl
      exact ⟨(hcaps y hy).below l hle, (hcaps y hy).sites l hle⟩
  · rintro u (⟨_, _, _, _, _, _, _, _, _, _, he, hu⟩ | ⟨_, _, _, _, _, he, _⟩)
    · cases he
      rcases hu with hu | hu
      · exact ⟨_, hcaps u hu⟩
      · exact ⟨_, hE u hu⟩
    · cases he
  · intro fs' ar' E' K' s' caps' k' rest' comp' oid' he hc'
    cases he
    rw [hc] at hc'; cases hc'
  · intro fs' ar' E' K' s' caps' k' rest' comp' oid' he _
    cases he
    exact hlow

theorem vals_codePart {t : Tm} (o : Bool) (h : CodePart t) : vals P.ofC o t = [] := by
  rcases h with ⟨i, rfl⟩ | h
  · simp [vals]
  · cases t <;> simp [primVal] at h <;> simp [vals]

/-- **Lowered code holds only spines without cells as values** (proved). -/
theorem lowered_vals : ∀ (e : Tm) (o : Bool) {u : Val}, Lowered Fl e → u ∈ vals P.ofC o e →
    ∃ ls, u = .arr ls ∧ ∀ x ∈ ls, x = none := by
  intro e
  induction e using Tm.induct
  all_goals intro o u hl hu
  all_goals simp only [Lowered, loweredArgs_iff, vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hl hu
  all_goals grind [vals_codePart]

theorem lowered_vj {E : List Tm} {S : Sites P} (hE : ∀ e ∈ E, Lowered Fl e) :
    ∀ u ∈ valsArgs P.ofC true E, VJ Fl g n S u := by
  intro u hu
  simp only [valsArgs_eq, List.mem_flatMap] at hu
  obtain ⟨e, he, hu⟩ := hu
  obtain ⟨ls, rfl, hls⟩ := lowered_vals e true (hE e he) hu
  exact VJ.arr fun l hl => absurd (hls _ hl) (by simp)

/-! ### A raised value -/

/-- **A raised value meets `O`** (proved, by induction on `Raises`): every
thrown value fits `O`. -/
theorem raises_fits {V : Sites P → Val → Prop} {t v : Tm} (hr : Raises t v) :
    ∀ {Γ a S}, Fits Fl V Γ a S t → V Fl.O v := by
  induction hr with
  | throwV hv _ => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | throw hx => exact hx.value hv
  | throwC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | throw hx => exact ih hx
  | callL _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | invoke hf _ _ _ _ => exact ih hf
  | callRecv _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | invoke _ hr _ _ _ => exact ih hr
  | callArg _ _ hai _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | invoke _ _ hargs _ _ => exact ih (hargs _ (List.mem_of_getElem? hai))
  | constructL _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | construct hf _ _ _ => exact ih hf
  | constructArg _ hai _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | construct _ hargs _ _ => exact ih (hargs _ (List.mem_of_getElem? hai))
  | letC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | letE hx _ => exact ih hx
  | spreadC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | spread hx _ => exact ih hx
  | makeArg hai _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | makeAbsent _ _ hi _ => exact ih (hi _ (List.mem_of_getElem? hai))
    | makeView _ _ hi _ _ => exact ih (hi _ (List.mem_of_getElem? hai))
    | makeBound _ _ hi _ _ => exact ih (hi _ (List.mem_of_getElem? hai))
    | makeGraphC _ _ _ hi _ _ _ _ _ => exact ih (hi _ (List.mem_of_getElem? hai))
    | makeGraphOut _ _ hi _ _ _ _ => exact ih (hi _ (List.mem_of_getElem? hai))
  | readC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | readAt hx _ _ _ => exact ih hx
  | indexC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | indexAt hx _ _ _ _ => exact ih hx
  | indexC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | indexAt _ hk _ _ _ => exact ih hk
  | writeC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | writeAt hx _ _ => exact ih hx
  | writeC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | writeAt _ hy _ => exact ih hy
  | testC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | test hx => exact ih hx
  | iteC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | ite hc _ _ => exact ih hc
  | arithC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | arith hx _ => exact ih hx
  | arithC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | arith _ hy => exact ih hy
  | arrArg hai _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | arrLit _ _ hi _ => exact ih (hi _ (List.mem_of_getElem? hai))
  | elemC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | elemAt hx _ _ => exact ih hx
  | elemC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | elemAt _ hi _ => exact ih hi
  | setC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | setElem hx _ _ _ _ _ => exact ih hx
  | setC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | setElem _ hi _ _ _ _ => exact ih hi
  | setC3 _ _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | setElem _ _ hv _ _ _ => exact ih hv
  | lenC _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | lenOf hx => exact ih hx
  | mergeC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | merge hx _ _ _ => exact ih hx
  | mergeC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | merge _ hy _ _ => exact ih hy
  | makeKeyC1 _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | makeKey hk _ _ _ => exact ih hk
  | makeKeyC2 _ _ ih => intro Γ a S h; cases h with
    | val hv' => simp [isVal] at hv'
    | makeKey _ _ hx _ => exact ih hx

/-! ### Frames -/

/-- **The proposal's conditions at a node a frame runs** (proved). -/
theorem codeOk_node (hF : Fl.Facts) {E : List Tm} {K : List (Continuation × Option Target)} {π : CodeFlow P}
    {l : Nat} {k : Continuation} {x : Option Target} (hcode : Fl.code (E, K) = some π) (hn : NodeOf (E, K) l k x) :
    ContOk Fl π l k ∧ HandlerOk Fl π l x := by
  obtain ⟨hk, e, he⟩ := hn
  obtain ⟨-, hc, hh⟩ := hF.ok (E, K) π hcode l e k x he hk
  exact ⟨hc, hh⟩

/-- Every slot of a mapped environment holds a slot of the one it maps
(proved). -/
theorem envOf_envMap {m : Option (List Nat)} {L : List Tm} {d : Tm} (i : Nat) :
    ∃ j, envOf (envMap m L d).1 (envMap m L d).2 i = envOf L d j := by
  have hx : envOf (envMap m L d).1 (envMap m L d).2 i ∈ (envMap m L d).1 ∨
      envOf (envMap m L d).1 (envMap m L d).2 i = (envMap m L d).2 := getD_mem_or _ _ _
  rcases envMap_mem hx with hm | he
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
    exact ⟨j, by simp [envOf, List.getD_eq_getElem?_getD, hj]⟩
  · exact ⟨L.length, by rw [he]; simp [envOf, List.getD_eq_getElem?_getD]⟩

/-- **A mapped environment of values of `O` holds values of `O`** (proved). -/
theorem envIn_map_O {V : Sites P → Val → Prop} {m : Option (List Nat)} {L : List Tm} {d : Tm}
    (henv : ∀ i, V Fl.O (envOf L d i)) (i : Nat) : V Fl.O (envOf (envMap m L d).1 (envMap m L d).2 i) := by
  obtain ⟨j, hj⟩ := envOf_envMap (m := m) (L := L) (d := d) i
  rw [hj]; exact henv j

theorem envIn_cons {V : Sites P → Val → Prop} {S : Sites P} {L : List Tm} {d v : Tm}
    (henv : ∀ i, V S (envOf L d i)) (hv : V S v) (i : Nat) : V S (envOf (v :: L) d i) := by
  cases i with
  | zero => simpa [envOf] using hv
  | succ i => simpa [envOf] using henv i

/-- A goto to a node whose environment meets the node's slots fits (proved). -/
theorem fits_gotoC {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {a : Alloc P} {S : Sites P}
    {E : List Tm} {K : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm} {comp : ComponentTag}
    {π : CodeFlow P} (hc : P.ofC comp = true) (hcode : Fl.code (E, K) = some π) (henv : EnvIn V (π.env l) L d)
    (hS : Sub Fl.O S) : Fits Fl V Γ a S (.goto E K l L d comp) :=
  .gotoC π hc hcode (fun i => .inl (henv i)) hS

theorem fits_gotoOut {V : Sites P → Val → Prop} {Γ : Nat → Option (Sites P)} {a : Alloc P} {S : Sites P}
    {E : List Tm} {K : List (Continuation × Option Target)} {l : Nat} {L : List Tm} {d : Tm} {comp : ComponentTag}
    (hc : P.ofC comp = false) (hE : ∀ e ∈ E, Lowered Fl e) (henv : ∀ i, V Fl.O (envOf L d i))
    (hS : Sub Fl.O S) : Fits Fl V Γ a S (.goto E K l L d comp) :=
  .gotoOut hc hE (fun i => .inl (henv i)) hS

end Verification.TolerantFrames.ReadOnly
