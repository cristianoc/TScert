import Verification.Source.Claims.FramedSpec
import Verification.Paper.TolerantFrames.ReadOnlyBinding
import Verification.Source.ComponentWire

/-! # The binding checks of a framed plan, at its request

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The binding checks" and
"Realization"). The checks of `ReadOnlyBinding` read at a framed plan's
request:

- **The request's code** (`requestCode`): the tables of the request's
  program, which the claim's term runs (`gotoOf_requestCode`).
- **The realized code's proposals are the request's at body labels**
  (`realizedFlowB`, `realizedFlowB_sound`): at every context of the
  realized code, the request's code has a proposal with the same nodes at
  each label of the request's program, the same allocation sites at each
  of its nodes' continuations and handlers, and the same return set, so
  `Fits`, `Provenance` and the frame check read the same proposal in
  either code.
- **The component** (`compB`, `compB_sound`): the request's tag, which the
  lowering assigns (`componentAt` at its name), is `C`, so the claim's
  frames run `C`'s code.
- **One site per body allocation** (`bodyOf`, `allocB`, `allocB_realized`):
  a realized code's body is its request's code, every other code its own;
  the flow allocates at `some` sites (`allocSomeB`) numbered as the
  canonical sites of the body's allocation occurrences (`allocCanonB`), so
  the realized code and its request's allocate at the same sites at every
  node key of the request's program.
- **The client obligation is the source's** (`clientsB`, `clientsB_sound`):
  each `@clients` row of the component's exported types states class keys
  only (`clientsByKindB`, the restriction "@clients by kind"), and the
  plan's $`\Theta_C`$ is, at every part of every package, the join of the
  rows' changes at the part's kind (`rowsTheta`), a row read-only where it
  states none. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **The request's code**: the tables of its program. -/
def requestCode (r : SourceRequest σ ι) : Code :=
  (r.program.map (·.expression), r.program.map fun n => (n.continuation, n.handler))

/-- The claim's term runs the request's code (proved, by definition). -/
theorem gotoOf_requestCode (r : SourceRequest σ ι) (s : Nat) (L : List Tm) (d : Tm) (c : ComponentTag) :
    PassUnit.gotoOf r.program s L d c = .goto (requestCode r).1 (requestCode r).2 s L d c := rfl

/-- **The realized code's proposals are the request's at body labels**,
decided (`agreeB` at the request's program's labels and node keys). -/
def realizedFlowB {P : Package} [DecidableEq P.Site] (F : FFlow P) (r : SourceRequest σ ι) : Bool :=
  agreeB F (realizedCode r) (requestCode r) (requestCode r).2 r.program.length

/-- **The realization check is sound** (proved, `agreeB_sound`). -/
theorem realizedFlowB_sound {P : Package} [DecidableEq P.Site] {F : FFlow P} {r : SourceRequest σ ι}
    (h : realizedFlowB F r = true) {c : Nat} {π₁ : CodeFlow P} (h₁ : F.flow.code (realizedCode r) c = some π₁) :
    ∃ π₂, F.flow.code (requestCode r) c = some π₂ ∧ π₁.ret = π₂.ret ∧
      (∀ kx ∈ (requestCode r).2, π₁.alloc kx = π₂.alloc kx) ∧
      ∀ l, l < r.program.length → π₁.env l = π₂.env l ∧ π₁.val l = π₂.val l ∧ π₁.fn l = π₂.fn l ∧
        π₁.vfn l = π₂.vfn l ∧ π₁.out l = π₂.out l :=
  agreeB_sound h h₁

/-- **The component check** (`compB`): the request's tag, which the lowering
assigns from the request's place (`Components.componentAt`), is `C`. -/
def compB (C : Nat) (r : SourceRequest σ ι) : Bool := r.comp == some C

/-- **The component check is sound** (proved): the claim's frames, tagged
with the request's tag, run `C`'s code. -/
theorem compB_sound {F : TolerantFrames.ReadOnly.Family} {C : Nat} {r : SourceRequest σ ι} (h : compB C r = true) :
    (F.at C).ofC r.comp = true := by
  simp only [compB, beq_iff_eq] at h
  simp [Family.at, Family.ofC, Family.Runs, h, F.refl]

/-- **The body of a code** (the draft, "Realization"): the request's code
for its realized code, every other code itself. -/
def bodyOf (r : SourceRequest σ ι) (m : Code) : Code := if m = realizedCode r then requestCode r else m

/-- The realized code is not the request's: it has one node more. -/
theorem requestCode_ne_realized (r : SourceRequest σ ι) : requestCode r ≠ realizedCode r := by
  intro h
  have := congrArg (fun m : Code => m.1.length) h
  simp [requestCode, realizedCode] at this

theorem bodyOf_realized (r : SourceRequest σ ι) : bodyOf r (realizedCode r) = requestCode r := by
  simp [bodyOf]

theorem bodyOf_request (r : SourceRequest σ ι) : bodyOf r (requestCode r) = requestCode r := by
  simp [bodyOf, requestCode_ne_realized]

/-- **The allocation sites check** (`allocB`): sites, and the canonical
ones of the bodies by the sites' numbers `num` (for a numbered family's
component, the number a site is). -/
def allocB {P : Package} (num : P.Site → Nat) (F : FFlow P) (r : SourceRequest σ ι) (base : Nat)
    (bodies : List Code) : Bool :=
  allocSomeB F && allocCanonB num base bodies (bodyOf r) F

/-- **The realized code and its request's allocate at the same sites**
(proved, `allocCanon_same`): at every node key of the request's program,
at any contexts of the two codes. -/
theorem allocB_realized {P : Package} {num : P.Site → Nat} (hnum : ∀ a b, num a = num b → a = b) {F : FFlow P}
    {r : SourceRequest σ ι} {base : Nat} {bodies : List Code} (h : allocB num F r base bodies = true) {c₁ c₂ : Nat}
    {f₁ f₂ : FCode P}
    (h₁ : F.at (realizedCode r) c₁ = some f₁) (h₂ : F.at (requestCode r) c₂ = some f₂) {kx : NodeKey}
    (hk : kx ∈ (requestCode r).2) :
    f₁.allocAt kx = f₂.allocAt kx := by
  simp only [allocB, Bool.and_eq_true] at h
  have hk₁ : kx ∈ (realizedCode r).2 := by
    simp only [requestCode, realizedCode] at hk ⊢
    exact List.mem_append_left _ hk
  have hs := allocCanon_same h.2 ((bodyOf_realized r).trans (bodyOf_request r).symm) h₁ h₂ hk₁ hk
    (by rw [bodyOf_realized]; exact hk)
  have ho := Option.map_injective hnum hs.1
  have ha := Option.map_injective hnum hs.2
  cases e₁ : f₁.allocAt kx; cases e₂ : f₂.allocAt kx
  rw [e₁, e₂] at ho ha
  simp only at ho ha
  rw [ho, ha]

end

section clients
variable {P : Package}

/-- **The client obligation the rows state at a kind**: the join of each
stated row's change at a class region whose classes the kind has; `any`
at a region of another form, which `clientsByKindB` refuses; `keep` where
no row states one. -/
def rowsAt (rows : List ComponentWire.Clients) (k : Option Verification.Kind) : Footprints.Change :=
  rows.foldl (fun δ row => if row.stated then row.frame.foldl (fun δ e => match e.1 with
      | .cls c => if (roleKinds c.roles).contains k then δ.max e.2 else δ
      | _ => .any) δ else δ) .keep

/-- **The client obligation the rows state**: at a part, the rows'
obligation at its kind (`rowsAt`). -/
def rowsTheta (rows : List ComponentWire.Clients) : Protocol P := fun p => rowsAt rows p.kind

/-- **The rows state class keys only** (the restriction "@clients by
kind"), decided. -/
def clientsByKindB (rows : List ComponentWire.Clients) : Bool :=
  rows.all fun row => !row.stated || row.frame.all fun e => match e.1 with
    | .cls _ => true
    | _ => false

/-- **The plan's client obligation is the rows'**, decided: the rows state
class keys only, and at every kind the wire's change by kind `theta` is
the rows' (`rowsAt`). -/
def clientsB (theta : List (Option Verification.Kind × Footprints.Change)) (rows : List ComponentWire.Clients) : Bool :=
  clientsByKindB rows && allKinds.all fun k => decide (((theta.find? fun e => decide (e.1 = k)).map (·.2)).getD .keep = rowsAt rows k)

/-- **The client check is sound** (proved): the rows state class keys only,
and the wire's obligation by kind is the rows' at every part of every
package. -/
theorem clientsB_sound {theta : List (Option Verification.Kind × Footprints.Change)} {rows : List ComponentWire.Clients}
    (h : clientsB theta rows = true) :
    clientsByKindB rows = true ∧ ∀ {Q : Package} (p : Part Q), (protocolOfKinds theta : Protocol Q) p = rowsTheta rows p := by
  simp only [clientsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun p => h.2 p.kind (mem_allKinds _)⟩

end clients
end Verification.SourceClaimJson
