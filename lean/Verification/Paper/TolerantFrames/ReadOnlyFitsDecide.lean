import Verification.Paper.TolerantFrames.ReadOnlyFitsCheck
import Verification.Paper.TolerantFrames.ReadOnlyFitsEntry

/-! # Read-only handles: deciding the checks of a finite proposal

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "Deciding
the flow"). A proposal is finite (`FFlow`): `O`, the heap of sites as a
list of entries, and for each code of `C` its nodes, each node's slots as a
list with one set for every slot past it, its signatures as a list. The
checks of a code (`CodeChk`) and the facts of a flow (`Flow.Facts`) are
decided from it (proof scope: the lemmas below):

- **A term's least set** (`syn`): computed bottom-up, a read's result from
  the contents of the closure of the sites it may read under the contents
  (`closeQ`, checked closed), each allocation's initial values checked
  against its site's storage; `syn_sound` gives `OFits` at it, and
  `OFits.sub` at every larger set.
- **Lowered code** (`lowB`, `lowB_sound`).
- **The edges** (`carriesB`, `carriesFnB`): finitely many slots decide them,
  every slot past the widths reading the defaults.
- **Closures** (`graphSites`, `openB`): a closure's set holds its code's
  token; where the token lies in `O`, the code's entry holds `O` at the
  slots a caller of unknown callee fills, what outside code may supply at
  each capture's slot (`suppliedB`), and its return set lies within `O`; a
  known call's set is its callee's return set (`invokeSites`).
- **The flow** (`FFlow.check`, `FFlow.check_sound`): every code's checks and
  the facts of `O` give `Flow.Facts`; a member's entry (`FFlow.entryB`)
  gives `EntryShape`'s conditions on the flow.
- **The marks a flow gives** (`FFlow.MarksFrom`): a site of `O` released,
  every other site local; at them `O` is lent and local storage is held
  only by local storage (`FFlow.marks_of_marksFrom`), the bindings decided
  apart (`FFlow.bindingsB`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

deriving instance DecidableEq for FnSig

variable {P : Package}

/-! ## A larger set fits -/

section sub
variable {Fl : Flow P} {τ : Nat → Sites P} {φ : Nat → Option FnSig}

theorem OVOr.sub {d : Nat} {Γ : Nat → Option (Sites P)} {S S' : Sites P} {u : Tm} (h : OVOr τ d Γ S u)
    (hS : Sub S S') : OVOr τ d Γ S' u := by
  rcases h with hp | ⟨j, S'', rfl, hj, hΓ, hs⟩ | ⟨j, rfl, hj, hs⟩
  · exact .inl hp
  · exact .inr (.inl ⟨j, S'', rfl, hj, hΓ, hs.trans hS⟩)
  · exact .inr (.inr ⟨j, rfl, hj, hs.trans hS⟩)

/-- **An open term of `C`'s code fitting a set fits every larger set**
(proved). -/
theorem OFits.sub : ∀ {d Γ a o S e}, OFits Fl τ φ d Γ a o S e → o = false → ∀ {S'}, Sub S S' →
    OFits Fl τ φ d Γ a o S' e := by
  intro d Γ a o S e h
  induction h with
  | prim hp _ => intro ho _ _; exact .prim hp (by simp [ho])
  | arr hl _ => intro ho _ _; exact .arr hl (by simp [ho])
  | bvar hi hΓ hs _ => intro ho _ hS; exact .bvar hi hΓ (hs.trans hS) (by simp [ho])
  | fvar hi hs _ => intro ho _ hS; exact .fvar hi (hs.trans hS) (by simp [ho])
  | invoke hf hr ha hO harr _ hSf hout => intro ho _ hS; exact .invoke hf hr ha (hO.trans hS) harr (by simp [ho]) hSf hout
  | invokeC σ c π Sa Sr hof hj hφ hc hself hr ha hat hpar hrest hR _ =>
    intro ho _ hS; exact .invokeC σ c π Sa Sr hof hj hφ hc hself hr ha hat hpar hrest (hR.trans hS) (by simp [ho])
  | construct hf ha hO harr _ hSf hout => intro ho _ hS; exact .construct hf ha (hO.trans hS) harr (by simp [ho]) hSf hout
  | letE hx _ _ _ ihb => intro ho _ hS; exact .letE hx (ihb ho hS) (by simp [ho])
  | spread hx hc _ => intro ho _ hS; exact .spread hx (fun s hs => (hc s hs).trans hS) (by simp [ho])
  | makeAbsent Ss hst hx ha _ => intro ho _ hS; exact .makeAbsent Ss hst hx (hS _ ha) (by simp [ho])
  | makeBound Ss hst hx ha hp _ =>
    intro ho _ hS; exact .makeBound Ss hst hx (hS _ ha) (fun x hx => (hp x hx).sub hS) (by simp [ho])
  | makeGraphC π Ss hst hx ha hc hcode hcaps htok hop hE _ =>
    intro ho _ hS; exact .makeGraphC π Ss hst hx (hS _ ha) hc hcode hcaps (hS _ htok) hop hE (by simp [ho])
  | makeGraphOut Ss hst hx ha hc hE hcaps _ hn =>
    intro ho _ hS; exact .makeGraphOut Ss hst hx (hS _ ha) hc hE (fun u hu => (hcaps u hu).sub hS) (by simp [ho]) (hS _ hn)
  | readAt hx hq hcl hr _ => intro ho _ hS; exact .readAt hx hq hcl (fun s hs => (hr s hs).trans hS) (by simp [ho])
  | indexAt hx hk hq hcl hr _ =>
    intro ho _ hS; exact .indexAt hx hk hq hcl (fun s hs => (hr s hs).trans hS) (by simp [ho])
  | writeAt hx hy hst _ => intro ho _ _; exact .writeAt hx hy hst (by simp [ho])
  | test hx _ => intro ho _ _; exact .test hx (by simp [ho])
  | ite hc _ _ _ _ ihx ihy => intro ho _ hS; exact .ite hc (ihx ho hS) (ihy ho hS) (by simp [ho])
  | arith hx hy _ => intro ho _ _; exact .arith hx hy (by simp [ho])
  | arrLit Ss hst hx ha _ => intro ho _ hS; exact .arrLit Ss hst hx (hS _ ha) (by simp [ho])
  | elemAt hx hi hc _ => intro ho _ hS; exact .elemAt hx hi (fun s hs => (hc s hs).trans hS) (by simp [ho])
  | setElem hx hi hv hst hsx ha _ =>
    intro ho _ hS; exact .setElem hx hi hv hst (hsx.trans hS) (hS _ ha) (by simp [ho])
  | lenOf hx _ => intro ho _ _; exact .lenOf hx (by simp [ho])
  | throw hx _ => intro ho _ _; exact .throw hx (by simp [ho])
  | merge hx hy hq hcl hst ha hQ _ =>
    intro ho _ hS; exact .merge hx hy hq hcl hst (hS _ ha) hQ (by simp [ho])
  | makeKey hk hst hx ha _ => intro ho _ hS; exact .makeKey hk hst hx (hS _ ha) (by simp [ho])

end sub

variable [DecidableEq P.Site]

instance (S S' : Sites P) : Decidable (Sub S S') := inferInstanceAs (Decidable (∀ s ∈ S, s ∈ S'))

/-! ## A finite proposal -/

/-- **A node of a finite proposal**: its slots, the set of every slot past
them, its value set, the signatures of its slots (none past them) and of
its value, each an index into its code's table of signatures, and the
context its known calls enter their callees at. -/
structure FNode (P : Package) where
  env : Array (Sites P)
  dflt : Sites P
  val : Sites P
  fn : Array (Option Nat)
  vfn : Option Nat
  cx : Nat := entryCx
  /-- Whether a run at the node may call outside code. -/
  out : Bool := true

def FNode.envAt (x : FNode P) (i : Nat) : Sites P := x.env.getD i x.dflt

def FNode.fnAt (x : FNode P) (i : Nat) : Option Nat := x.fn.getD i none

/-- **A code's finite proposal**: its nodes, the node of every label past
them, the sites a frame allocates at (per its node's continuation and
handler, `allocs`, else `alloc`), the table of signatures its
nodes' indices name, its return set, and the site standing for its
closures. -/
structure FCode (P : Package) where
  nodes : Array (FNode P)
  dflt : FNode P
  alloc : Alloc P
  sigs : Array FnSig
  ret : Sites P
  tok : Option P.Site
  /-- The sites a frame of a node's continuation and handler allocates at,
  where they are not `alloc`. -/
  allocs : List (NodeKey × Option P.Site × Option P.Site) := []

def FCode.node (c : FCode P) (l : Nat) : FNode P := c.nodes.getD l c.dflt

/-- The sites a frame of a node's continuation and handler allocates at. -/
def FCode.allocAt (c : FCode P) (kx : NodeKey) : Alloc P :=
  match (c.allocs.find? fun e => decide (e.1 = kx)) with
  | some (_, o, a) => ⟨o, a⟩
  | none => c.alloc

/-- The signature an index names. -/
def FCode.sigAt (c : FCode P) (t : Option Nat) : Option FnSig := t.bind (c.sigs[·]?)

/-- The proposal a finite one stands for. -/
def FCode.flow (c : FCode P) : CodeFlow P where
  env l i := (c.node l).envAt i
  val l := (c.node l).val
  alloc := c.allocAt
  fn l i := c.sigAt ((c.node l).fnAt i)
  vfn l := c.sigAt (c.node l).vfn
  ret := c.ret
  tok := c.tok
  out l := (c.node l).out

/-- The first entry of a list at a key. -/
def look {α β : Type} [DecidableEq α] (a : α) (l : List (α × β)) : Option β :=
  (l.find? fun p => decide (p.1 = a)).map Prod.snd

theorem look_mem {α β : Type} [DecidableEq α] {a : α} {l : List (α × β)} {b : β} (h : look a l = some b) :
    (a, b) ∈ l := by
  simp only [look, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have he := List.find?_some hp
  simp only [decide_eq_true_eq] at he
  subst he; exact hm

/-- **A finite flow**: `O`, the heap of sites (each site's contents and
bindings, none past the entries), and each code's finite proposal at each
of its contexts. -/
structure FFlow (P : Package) where
  O : Sites P
  heap : List (Option P.Site × Sites P × Sites P)
  codes : List (Code × List (Nat × FCode P))

/-- The contexts of a code. -/
def FFlow.ctxs (F : FFlow P) (m : Code) : List (Nat × FCode P) := (look m F.codes).getD []

/-- A code's finite proposal at a context. -/
def FFlow.at (F : FFlow P) (m : Code) (c : Nat) : Option (FCode P) := look c (F.ctxs m)

def FFlow.contents (F : FFlow P) (s : Option P.Site) : Sites P := ((look s F.heap).map Prod.fst).getD []

def FFlow.bindings (F : FFlow P) (s : Option P.Site) : Sites P := ((look s F.heap).map Prod.snd).getD []

/-- The flow a finite one stands for. -/
def FFlow.flow (F : FFlow P) : Flow P where
  O := F.O
  H := ⟨F.contents, F.bindings⟩
  code m c := (F.at m c).map FCode.flow

theorem FFlow.code_at {F : FFlow P} {m : Code} {c : Nat} {π : CodeFlow P} (h : F.flow.code m c = some π) :
    ∃ fc, F.at m c = some fc ∧ π = fc.flow := by
  simp only [FFlow.flow, Option.map_eq_some_iff] at h
  obtain ⟨fc, h, rfl⟩ := h; exact ⟨fc, h, rfl⟩

omit [DecidableEq P.Site] in
theorem FFlow.at_mem {F : FFlow P} {m : Code} {c : Nat} {fc : FCode P} (h : F.at m c = some fc) :
    ∃ l, (m, l) ∈ F.codes ∧ (c, fc) ∈ l := by
  unfold FFlow.at FFlow.ctxs at h
  cases hl : look m F.codes with
  | none => rw [hl] at h; simp [look] at h
  | some l => rw [hl] at h; exact ⟨l, look_mem hl, look_mem h⟩

omit [DecidableEq P.Site] in
theorem FFlow.at_ctxs {F : FFlow P} {m : Code} {c : Nat} {fc : FCode P} (h : F.at m c = some fc) :
    (c, fc) ∈ F.ctxs m := look_mem h


/-! ## Deciding lowered code -/

section decide
variable (F : FFlow P)

/-- **What storage of a site may hold**, decided. -/
def storesB (s : Option P.Site) (S : Sites P) : Bool :=
  decide (Sub S (F.contents s)) && decide (Sub S (F.bindings s))

theorem storesB_sound {s : Option P.Site} {S : Sites P} (h : storesB F s S = true) : Stores F.flow s S := by
  simp only [storesB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h

/-- A part of a closure's code in lowered code, decided. -/
def partB : Tm → Bool
  | .var _ => true
  | t => primVal t

omit [DecidableEq P.Site] in
theorem codePart_of_partB {t : Tm} (h : partB t = true) : CodePart t := by
  unfold partB at h; split at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr h

omit [DecidableEq P.Site] in
theorem FCode.fn_lt {c : FCode P} {l i : Nat} {σ : FnSig} (h : c.flow.fn l i = some σ) :
    i < (c.node l).fn.size := by
  simp only [FCode.flow, FCode.sigAt, FNode.fnAt, Array.getD_eq_getD_getElem?] at h
  rcases Nat.lt_or_ge i (c.node l).fn.size with hi | hi
  · exact hi
  · rw [Array.getElem?_eq_none hi] at h; simp at h

/-- **A set holding what outside code may supply**, decided. -/
def suppliedB (S : Sites P) : Bool :=
  decide (none ∈ S) && F.codes.all fun e => e.2.all fun c => !decide (c.2.tok ∈ F.O) || decide (c.2.tok ∈ S)

theorem suppliedB_sound {S : Sites P} (h : suppliedB F S = true) : Supplied F.flow S := by
  simp only [suppliedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  refine ⟨h.1, fun m π hm ht => ?_⟩
  obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hm
  obtain ⟨l, hl, hc⟩ := FFlow.at_mem hfc
  rcases h.2 (m, l) hl _ hc with hn | hs
  · exact absurd ht hn
  · exact hs

/-- **A code open at an entry**, decided. -/
def openB (c : FCode P) (ar s : Nat) (rest : Bool) (n : Nat) : Bool :=
  (List.range (capSlot ar rest 0)).all (fun i => decide (Sub F.O (c.flow.env s i))) &&
    decide (Sub F.O (c.flow.env s (capSlot ar rest n))) && decide (Sub c.ret F.O) &&
    (List.range n).all fun i => suppliedB F (c.flow.env s (capSlot ar rest i))

theorem openB_sound {c : FCode P} {ar s : Nat} {rest : Bool} {n : Nat} (h : openB F c ar s rest n = true) :
    OpenAt F.flow c.flow ar s rest n := by
  simp only [openB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun i hi => suppliedB_sound F (h.2 i hi)⟩

/-- **The captures' slots of an entry hold `O`**, decided. -/
def capsOB (c : FCode P) (ar s : Nat) (rest : Bool) (n : Nat) : Bool :=
  (List.range n).all fun i => decide (Sub F.O (c.flow.env s (capSlot ar rest i)))

theorem capsOB_sound {c : FCode P} {ar s : Nat} {rest : Bool} {n : Nat} (h : capsOB F c ar s rest n = true) :
    OpenCaps F.flow c.flow ar s rest n := by
  simp only [capsOB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h

/-- **Only the closure's own slot names a signature at its entry**, decided. -/
def selfFnB (c : FCode P) (ar : Nat) (E : List Tm) (K : List (Continuation × Option Target)) (s : Nat)
    (rest : Bool) (n : Nat) : Bool :=
  (List.range (c.node s).fn.size).all fun i =>
    (c.flow.fn s i).all fun σ => decide (i = capSlot ar rest n ∧ σ = ⟨(E, K), ar, s, rest, n⟩)

omit [DecidableEq P.Site] in
theorem selfFnB_sound {c : FCode P} {ar : Nat} {E : List Tm} {K : List (Continuation × Option Target)} {s : Nat}
    {rest : Bool} {n : Nat} (h : selfFnB c ar E K s rest n = true) : SelfFn c.flow ar E K s rest n := by
  intro i σ hi
  simp only [selfFnB, List.all_eq_true, List.mem_range] at h
  have := h i (FCode.fn_lt hi)
  rw [hi] at this; simpa using this

mutual
/-- **Lowered code**, decided. -/
def lowB : Tm → Bool
  | .objAt .. => false
  | .arr ls => ls.all Option.isNone
  | .viewSpine .. => false
  | .goto .. => false
  | .frame .. => false
  | .invoke f r args => lowB f && lowB r && lowAll args
  | .construct f args => lowB f && lowAll args
  | .letE a b => lowB a && lowB b
  | .makeAt .absent _ xs => lowAll xs
  | .makeAt (.view _ _ _) _ _ => false
  | .makeAt (.bound t r pre) _ xs => partB t && partB r && pre.all partB && lowAll xs
  | .makeAt (.graph ar E K s caps _ rest comp) _ xs =>
    (!P.ofC comp || ((F.at (E, K) entryCx).any fun c => decide (c.tok ∈ F.O) && openB F c ar s rest caps.length) &&
      (F.ctxs (E, K)).all fun c => selfFnB c.2 ar E K s rest caps.length && capsOB F c.2 ar s rest caps.length) &&
      lowAll E &&
      caps.all partB && lowAll xs
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => lowB a
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
    lowB a && lowB b
  | .ite a b c | .setElem a b c => lowB a && lowB b && lowB c
  | .arrLit xs => lowAll xs
  | _ => true
termination_by structural t => t

def lowAll : List Tm → Bool
  | [] => true
  | x :: xs => lowB x && lowAll xs
termination_by structural xs => xs
end

theorem lowAll_iff : ∀ {xs : List Tm}, lowAll F xs = true ↔ ∀ x ∈ xs, lowB F x = true
  | [] => by simp [lowAll]
  | x :: xs => by simp [lowAll, lowAll_iff]

/-- **Lowered code, decided, is lowered** (proved). -/
theorem lowB_sound : ∀ {e : Tm}, lowB F e = true → Lowered F.flow e := by
  intro e
  induction e using Tm.induct
  all_goals intro h
  all_goals simp only [lowB, lowAll_iff, Lowered, loweredArgs_iff, Bool.and_eq_true, List.all_eq_true,
    Option.isNone_iff_eq_none, Bool.not_eq_true', Bool.or_eq_true] at h ⊢
  case makeBound t r pre ns args iht ihr ihp iha =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨codePart_of_partB h1, codePart_of_partB h2, fun x hx => codePart_of_partB (h3 x hx),
      fun x hx => iha x hx (h4 x hx)⟩
  case makeGraph n E K s caps k r comp ns args ihE ihc iha =>
    obtain ⟨⟨⟨hc, hE⟩, hcaps⟩, hargs⟩ := h
    refine ⟨fun hC => ?_, fun e he => ihE e he (hE e he), fun x hx => codePart_of_partB (hcaps x hx),
      fun x hx => iha x hx (hargs x hx)⟩
    rcases hc with hc | hc
    · simp [hc] at hC
    · obtain ⟨h0, hall⟩ := hc
      refine ⟨?_, fun c π hπ => ?_⟩
      · cases hl : F.at (E, K) entryCx with
        | none => simp [hl] at h0
        | some c =>
          simp only [hl, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h0
          exact ⟨c.flow, by simp [FFlow.flow, hl], h0.1, openB_sound F h0.2⟩
      · obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hπ
        have := hall _ (FFlow.at_ctxs hfc)
        exact ⟨selfFnB_sound this.1, capsOB_sound F this.2⟩
  all_goals try simp_all
  all_goals try exact h

/-! ## A term's least set -/

/-- The contents of the sites of a set. -/
def contentsOf (S : Sites P) : Sites P := S.flatMap F.contents

theorem contents_sub {S : Sites P} {s : Option P.Site} (hs : s ∈ S) : Sub (F.contents s) (contentsOf F S) :=
  fun _ hx => List.mem_flatMap.mpr ⟨s, hs, hx⟩

/-- A set grown by its contents, `n` times at most. -/
def grow : Nat → Sites P → Sites P
  | 0, S => S
  | n + 1, S => if decide (Sub (contentsOf F S) S) then S else grow n (S ++ contentsOf F S)

theorem sub_grow : ∀ (n : Nat) (S : Sites P), Sub S (grow F n S)
  | 0, _ => Sub.refl _
  | n + 1, S => by
    unfold grow; split
    · exact Sub.refl _
    · exact Sub.trans (fun _ hx => List.mem_append_left _ hx : Sub S (S ++ contentsOf F S)) (sub_grow n _)

/-- **The closure of a set under the contents**: grown as many times as the
heap of sites has entries' contents, then checked closed. -/
def closeQ (S : Sites P) : Option (Sites P) :=
  let Q := grow F (S.length + (F.heap.map fun e => e.2.1.length).sum + 1) S
  if decide (∀ s ∈ Q, Sub (F.contents s) Q) then some Q else none

theorem closeQ_sound {S Q : Sites P} (h : closeQ F S = some Q) : Sub S Q ∧ ∀ s ∈ Q, Sub (F.contents s) Q := by
  simp only [closeQ] at h
  split at h
  · cases h; exact ⟨sub_grow F _ _, of_decide_eq_true ‹_›⟩
  · cases h

variable (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P) (κ : Nat)

/-- The sites of a part of a closure's code, open. -/
def partSites (d : Nat) (Γ : Nat → Option (Sites P)) : Tm → Option (Sites P)
  | .var j => if j < d then Γ j else some (τ (j - d))
  | u => if primVal u then some [] else none

omit [DecidableEq P.Site] in
theorem partSites_sound {d : Nat} {Γ : Nat → Option (Sites P)} {u : Tm} {S' S : Sites P}
    (h : partSites τ d Γ u = some S') (hS : Sub S' S) : OVOr τ d Γ S u := by
  unfold partSites at h
  split at h
  · rename_i j
    split at h
    · exact .inr (.inl ⟨j, S', rfl, by omega, h, hS⟩)
    · cases h; exact .inr (.inr ⟨j, rfl, by omega, hS⟩)
  · split at h
    · exact .inl ‹_›
    · cases h

/-- The sites of the parts of a closure's code, open. -/
def partsSites (d : Nat) (Γ : Nat → Option (Sites P)) : List Tm → Option (Sites P)
  | [] => some []
  | u :: us => match partSites τ d Γ u, partsSites d Γ us with
    | some S, some T => some (S ++ T)
    | _, _ => none

omit [DecidableEq P.Site] in
theorem partsSites_sound {d : Nat} {Γ : Nat → Option (Sites P)} :
    ∀ {us : List Tm} {Sp : Sites P}, partsSites τ d Γ us = some Sp → ∀ u ∈ us, OVOr τ d Γ Sp u
  | [], _, _, _, hu => by simp at hu
  | u :: us, Sp, h, x, hx => by
    simp only [partsSites] at h
    split at h
    · rename_i S T hS hT
      cases h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact partSites_sound τ hS fun y hy => List.mem_append_left _ hy
      · exact (partsSites_sound hT x hx).sub fun y hy => List.mem_append_right _ hy
    · cases h

/-- **A callee's set holds outside storage only at a frame that may call
outside code**, decided. -/
def outB (Sf : Sites P) : Bool := !decide (none ∈ Sf) || a.out

theorem outB_sound {Sf : Sites P} (h : outB a Sf = true) : none ∈ Sf → a.out = true := by
  intro hn; simp only [outB, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.resolve_left (fun h' => h' hn)

/-- **A call of a closure of a known signature**, decided from the sets of
its receiver and actuals. -/
def invCB (d j : Nat) (σ : FnSig) (c : FCode P) (Sr : Sites P) (Ls : List (Sites P)) (args : List Tm) : Bool :=
  decide (Sub (τ (j - d)) (c.flow.env σ.s (capSlot σ.ar σ.rest σ.ncaps))) &&
    decide (Sub Sr (c.flow.env σ.s (recvSlot σ.rest))) && args.all partB &&
    (List.range σ.ar).all (fun i => decide (Sub (Ls.getD i []) (c.flow.env σ.s (paramSlot σ.rest i)))) &&
    (!σ.rest || (decide (a.arr ∈ c.flow.env σ.s 0) && storesB F a.arr (Ls.drop σ.ar).flatten))

/-- **The set of a call**, from the sets of its callee, receiver and
actuals: the callee's return set at the node's context `κ` where the
callee is a slot naming a signature whose entry there accepts them, or `O`
where all of them lie within `O`, the callee's set holding outside storage
only where the frame may call outside code (`outB`). -/
def invokeSites (d : Nat) (f : Tm) (Sf Sr : Sites P) (Ls : List (Sites P)) (args : List Tm) : Option (Sites P) :=
  let viaO : Option (Sites P) :=
    if decide (Sub Sf F.O) && outB a Sf && decide (Sub Sr F.O) && Ls.all (fun S => decide (Sub S F.O)) &&
        decide (a.arr ∈ F.O) then
      some F.O
    else none
  match f with
  | .var j => if d ≤ j then
      match φ (j - d) with
      | some σ => match F.at σ.code κ with
        | some c => if invCB F τ a d j σ c Sr Ls args then some c.ret else viaO
        | none => viaO
      | none => viaO
    else viaO
  | _ => viaO

/-- The sets of a closure's allocation of graph code, decided. -/
def graphSites (d : Nat) (Γ : Nat → Option (Sites P)) (ar : Nat) (E : List Tm)
    (K : List (Continuation × Option Target)) (s : Nat) (caps : List Tm) (rest : Bool) (comp : ComponentTag) :
    Option (Sites P) :=
  if P.ofC comp then
    match F.at (E, K) entryCx with
    | some c =>
      if (F.ctxs (E, K)).all (fun c' => (List.range caps.length).all (fun i => (caps[i]?).all fun u =>
          (partSites τ d Γ u).any fun S' => decide (Sub S' (c'.2.flow.env s (capSlot ar rest i)))) &&
          selfFnB c'.2 ar E K s rest caps.length) &&
        (!decide (c.tok ∈ F.O) || openB F c ar s rest caps.length) then
        some [a.obj, c.tok] else none
    | none => none
  else (partsSites τ d Γ caps).map (fun S => none :: a.obj :: S)

mutual
/-- **A term's least set** at the node's slots `τ`, signatures `φ` and
allocation sites `a`, `Γ` the sets of the variables bound inside it. -/
def syn (d : Nat) (Γ : Nat → Option (Sites P)) : Tm → Option (Sites P)
  | .var i => if i < d then Γ i else some (τ (i - d))
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => some []
  | .arr ls => if ls.all Option.isNone then some [] else none
  | .invoke f r args => match syn d Γ f, syn d Γ r, synAll d Γ args with
    | some Sf, some Sr, some Ls => invokeSites F τ φ a κ d f Sf Sr Ls args
    | _, _, _ => none
  | .construct f args => match syn d Γ f, synAll d Γ args with
    | some Sf, some Ls =>
      if decide (Sub Sf F.O) && outB a Sf && Ls.all (fun S => decide (Sub S F.O)) && decide (a.arr ∈ F.O) then some F.O
      else none
    | _, _ => none
  | .letE x b => match syn d Γ x with
    | some Sx => syn (d + 1) (consSites Sx Γ) b
    | none => none
  | .spread x => match syn d Γ x with
    | some Sx => some (contentsOf F Sx)
    | none => none
  | .makeAt .absent _ inits => match synAll d Γ inits with
    | some Ls => if Ls.all (storesB F a.obj) then some [a.obj] else none
    | none => none
  | .makeAt (.bound t r pre) _ inits => match synAll d Γ inits, partsSites τ d Γ (t :: r :: pre) with
    | some Ls, some Sp => if Ls.all (storesB F a.obj) then some (a.obj :: Sp) else none
    | _, _ => none
  | .makeAt (.graph ar E K s caps _ rest comp) _ inits => match synAll d Γ inits with
    | some Ls => if Ls.all (storesB F a.obj) && E.all (lowB F) then graphSites F τ a d Γ ar E K s caps rest comp
      else none
    | none => none
  | .readAt _ x => match syn d Γ x with
    | some Sx => (closeQ F Sx).map (contentsOf F)
    | none => none
  | .indexAt x key => match syn d Γ x, syn d Γ key with
    | some Sx, some _ => (closeQ F Sx).map (contentsOf F)
    | _, _ => none
  | .writeAt _ x y => match syn d Γ x, syn d Γ y with
    | some Sx, some Sy => if Sx.all (fun s => storesB F s Sy) then some [] else none
    | _, _ => none
  | .test _ x => match syn d Γ x with
    | some _ => some []
    | none => none
  | .ite c x y => match syn d Γ c, syn d Γ x, syn d Γ y with
    | some _, some Sx, some Sy => some (Sx ++ Sy)
    | _, _, _ => none
  | .arith _ x y => match syn d Γ x, syn d Γ y with
    | some _, some _ => some []
    | _, _ => none
  | .arrLit inits => match synAll d Γ inits with
    | some Ls => if Ls.all (storesB F a.arr) then some [a.arr] else none
    | none => none
  | .elemAt x i => match syn d Γ x, syn d Γ i with
    | some Sx, some _ => some (contentsOf F Sx)
    | _, _ => none
  | .setElem x i v => match syn d Γ x, syn d Γ i, syn d Γ v with
    | some Sx, some _, some Sv => if (a.arr :: Sx).all (fun s => storesB F s Sv) then some (a.arr :: Sx) else none
    | _, _, _ => none
  | .lenOf x => match syn d Γ x with
    | some _ => some []
    | none => none
  | .throw x => match syn d Γ x with
    | some Sx => if decide (Sub Sx F.O) then some [] else none
    | none => none
  | .merge _ x y => match syn d Γ x, syn d Γ y with
    | some Sx, some Sy => match closeQ F (Sx ++ Sy) with
      | some Q => if Q.all (fun s => storesB F a.obj (F.contents s)) then some [a.obj] else none
      | none => none
    | _, _ => none
  | .makeKey k x => match syn d Γ k, syn d Γ x with
    | some _, some Sx => if storesB F a.obj Sx then some [a.obj] else none
    | _, _ => none
  | _ => none
termination_by structural e => e

/-- The least sets of a list of terms. -/
def synAll (d : Nat) (Γ : Nat → Option (Sites P)) : List Tm → Option (List (Sites P))
  | [] => some []
  | x :: xs => match syn d Γ x, synAll d Γ xs with
    | some S, some Ls => some (S :: Ls)
    | _, _ => none
termination_by structural xs => xs
end

end decide

/-! ## The least set fits -/

section sound
variable (F : FFlow P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P) (κ : Nat)

/-- A term's least set, where computed, fits it. -/
def SynOk (e : Tm) : Prop :=
  ∀ d Γ S, syn F τ φ a κ d Γ e = some S → OFits F.flow τ φ d Γ a false S e

variable {F τ φ a κ}

theorem synAll_ok {d : Nat} {Γ : Nat → Option (Sites P)} : ∀ {xs : List Tm} {Ls : List (Sites P)},
    (∀ x ∈ xs, SynOk F τ φ a κ x) → synAll F τ φ a κ d Γ xs = some Ls →
    ∀ (i : Nat) (x : Tm), xs[i]? = some x → ∃ S, Ls[i]? = some S ∧ syn F τ φ a κ d Γ x = some S ∧
      OFits F.flow τ φ d Γ a false S x
  | [], _, _, _, i, x, hx => by simp at hx
  | y :: ys, Ls, ih, h, i, x, hx => by
    simp only [synAll] at h
    split at h
    · rename_i S Ls' hS hLs
      cases h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
        exact ⟨S, rfl, hS, ih _ (by simp) d Γ S hS⟩
      | succ i =>
        simpa using synAll_ok (fun x hx => ih x (by simp [hx])) hLs i x (by simpa using hx)
    · cases h

theorem synAll_mem {d : Nat} {Γ : Nat → Option (Sites P)} {xs : List Tm} {Ls : List (Sites P)}
    (ih : ∀ x ∈ xs, SynOk F τ φ a κ x) (h : synAll F τ φ a κ d Γ xs = some Ls) {x : Tm} (hx : x ∈ xs) :
    ∃ S ∈ Ls, syn F τ φ a κ d Γ x = some S ∧ OFits F.flow τ φ d Γ a false S x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨S, hS, hs, hf⟩ := synAll_ok ih h i x hi
  exact ⟨S, List.mem_of_getElem? hS, hs, hf⟩

/-- The initial values of an allocation, at their least sets, meet its
site's storage. -/
theorem synAll_stores {d : Nat} {Γ : Nat → Option (Sites P)} {xs : List Tm} {Ls : List (Sites P)}
    {s : Option P.Site} (ih : ∀ x ∈ xs, SynOk F τ φ a κ x) (h : synAll F τ φ a κ d Γ xs = some Ls)
    (hs : Ls.all (storesB F s) = true) :
    (∀ x ∈ xs, Stores F.flow s ((syn F τ φ a κ d Γ x).getD [])) ∧
      ∀ x ∈ xs, OFits F.flow τ φ d Γ a false ((syn F τ φ a κ d Γ x).getD []) x := by
  constructor
  · intro x hx
    obtain ⟨S, hS, he, _⟩ := synAll_mem ih h hx
    rw [he]; exact storesB_sound F (List.all_eq_true.mp hs S hS)
  · intro x hx
    obtain ⟨S, _, he, hf⟩ := synAll_mem ih h hx
    rw [he]; exact hf

omit [DecidableEq P.Site] in
theorem getD_drop_sub {Ls : List (Sites P)} {n i : Nat} (hi : n ≤ i) : Sub (Ls.getD i []) (Ls.drop n).flatten := by
  intro s hs
  rw [List.getD_eq_getElem?_getD] at hs
  cases hL : Ls[i]? with
  | none => simp [hL] at hs
  | some S =>
    simp only [hL, Option.getD_some] at hs
    have : (Ls.drop n)[i - n]? = some S := by rw [List.getElem?_drop]; rwa [Nat.add_sub_cancel' hi]
    exact List.mem_flatten.mpr ⟨S, List.mem_of_getElem? this, hs⟩

theorem invokeSites_sound {d : Nat} {Γ : Nat → Option (Sites P)} {f r : Tm} {args : List Tm} {Sf Sr S : Sites P}
    {Ls : List (Sites P)} (hf : OFits F.flow τ φ d Γ a false Sf f) (hr : OFits F.flow τ φ d Γ a false Sr r)
    (hL : ∀ (i : Nat) (x : Tm), args[i]? = some x → ∃ S', Ls[i]? = some S' ∧ OFits F.flow τ φ d Γ a false S' x)
    (h : invokeSites F τ φ a κ d f Sf Sr Ls args = some S) : OFits F.flow τ φ d Γ a false S (.invoke f r args) := by
  have hO : ∀ {S : Sites P}, (if decide (Sub Sf F.O) && outB a Sf && decide (Sub Sr F.O) &&
      Ls.all (fun S => decide (Sub S F.O)) && decide (a.arr ∈ F.O) then some F.O else none) = some S →
      OFits F.flow τ φ d Γ a false S (.invoke f r args) := by
    intro S h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
      obtain ⟨⟨⟨⟨hfO, hout⟩, hrO⟩, hLO⟩, harr⟩ := hc
      refine .invoke hf (hr.sub rfl hrO) (fun x hx => ?_) (Sub.refl _) harr (by simp) hfO (outB_sound a hout)
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      obtain ⟨S', hS', hx'⟩ := hL i x hi
      exact hx'.sub rfl (hLO S' (List.mem_of_getElem? hS'))
    · cases h
  unfold invokeSites at h
  cases f
  case var j =>
    simp only at h
    split at h
    · rename_i hj
      split at h
      · rename_i σ hσ
        split at h
        · rename_i c hc
          split at h
          · rename_i hb
            cases h
            simp only [invCB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
              Bool.or_eq_true, Bool.not_eq_true'] at hb
            obtain ⟨⟨⟨⟨hself, hrecv⟩, hat⟩, hpar⟩, hrest⟩ := hb
            refine .invokeC σ κ c.flow (fun i => Ls.getD i []) (Ls.drop σ.ar).flatten rfl hj hσ
              (by simp [FFlow.flow, hc]) hself (hr.sub rfl hrecv) (fun i x hx => ?_) (fun x hx => ?_)
              (fun i hi => hpar i hi) (fun hR => ?_) (Sub.refl _) (by simp)
            · obtain ⟨S', hS', hx'⟩ := hL i x hx
              simpa [List.getD_eq_getElem?_getD, hS'] using hx'
            · rcases codePart_of_partB (hat x hx) with ⟨k, rfl⟩ | hp
              · exact .inr ⟨k, rfl⟩
              · exact .inl hp
            · rcases hrest with hR' | ⟨hA, hS⟩
              · simp [hR] at hR'
              · exact ⟨hA, storesB_sound F hS, fun i hi => getD_drop_sub hi⟩
          · exact hO h
        · exact hO h
      · exact hO h
    · exact hO h
  all_goals exact hO h

/-- **A term's least set fits it** (proved). -/
theorem syn_sound : ∀ e, SynOk F τ φ a κ e := by
  intro e
  induction e using Tm.induct
  all_goals intro d Γ S h
  all_goals simp only [syn] at h
  case var i =>
    split at h
    · exact .bvar ‹_› h (Sub.refl _) (by simp)
    · cases h; exact .fvar (by omega) (Sub.refl _) (by simp)
  case invoke f r args ihf ihr iha =>
    split at h
    · rename_i Sf Sr Ls hf hr hL
      exact invokeSites_sound (ihf d Γ Sf hf) (ihr d Γ Sr hr)
        (fun i x hx => by obtain ⟨S', h1, _, h3⟩ := synAll_ok iha hL i x hx; exact ⟨S', h1, h3⟩) h
    · cases h
  case construct f args ihf iha =>
    split at h
    · rename_i Sf Ls hf hL
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
        obtain ⟨⟨⟨hfO, hout⟩, hLO⟩, harr⟩ := hc
        refine .construct (ihf d Γ Sf hf) (fun x hx => ?_) (Sub.refl _) harr (by simp) hfO (outB_sound a hout)
        obtain ⟨S', hS', _, hx'⟩ := synAll_mem iha hL hx
        exact hx'.sub rfl (hLO S' hS')
      · cases h
    · cases h
  case letE x b ihx ihb =>
    split at h
    · rename_i Sx hx
      exact .letE (ihx d Γ Sx hx) (ihb _ _ S h) (by simp)
    · cases h
  case nul => cases h; exact .prim rfl (by simp)
  case undef => cases h; exact .prim rfl (by simp)
  case tru => cases h; exact .prim rfl (by simp)
  case fls => cases h; exact .prim rfl (by simp)
  case num => cases h; exact .prim rfl (by simp)
  case str => cases h; exact .prim rfl (by simp)
  case bigint => cases h; exact .prim rfl (by simp)
  case sym => cases h; exact .prim rfl (by simp)
  case makeBound t r pre ns args _ _ _ iha =>
    split at h
    · rename_i Ls Sp hL hp
      split at h
      · rename_i hs
        cases h
        obtain ⟨hst, hx⟩ := synAll_stores iha hL hs
        exact .makeBound _ hst hx (List.mem_cons_self ..)
          (fun u hu => (partsSites_sound τ hp u hu).sub fun _ hy => List.mem_cons_of_mem _ hy) (by simp)
      · cases h
    · cases h
  case alloc ns args iha =>
    split at h
    · rename_i Ls hL
      split at h
      · rename_i hs
        cases h
        obtain ⟨hst, hx⟩ := synAll_stores iha hL hs
        exact .makeAbsent _ hst hx (List.mem_cons_self ..) (by simp)
      · cases h
    · cases h
  case read f x ihx =>
    split at h
    · rename_i Sx hx
      cases hq : closeQ F Sx with
      | none => simp [hq] at h
      | some Q =>
        simp only [hq, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨hs, hc⟩ := closeQ_sound F hq
        exact .readAt (ihx d Γ Sx hx) hs hc (fun s hs => contents_sub F hs) (by simp)
    · cases h
  case index x key ihx ihk =>
    split at h
    · rename_i Sx Sk hx hk
      cases hq : closeQ F Sx with
      | none => simp [hq] at h
      | some Q =>
        simp only [hq, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨hs, hc⟩ := closeQ_sound F hq
        exact .indexAt (ihx d Γ Sx hx) (ihk d Γ Sk hk) hs hc (fun s hs => contents_sub F hs) (by simp)
    · cases h
  case write f x y ihx ihy =>
    split at h
    · rename_i Sx Sy hx hy
      split at h
      · rename_i hs
        cases h
        exact .writeAt (ihx d Γ Sx hx) (ihy d Γ Sy hy)
          (fun s hs' => storesB_sound F (List.all_eq_true.mp hs s hs')) (by simp)
      · cases h
    · cases h
  case test k x ihx =>
    split at h
    · rename_i Sx hx; cases h; exact .test (ihx d Γ Sx hx) (by simp)
    · cases h
  case ite c x y ihc ihx ihy =>
    split at h
    · rename_i Sc Sx Sy hc hx hy
      cases h
      exact .ite (ihc d Γ Sc hc) ((ihx d Γ Sx hx).sub rfl fun _ h => List.mem_append_left _ h)
        ((ihy d Γ Sy hy).sub rfl fun _ h => List.mem_append_right _ h) (by simp)
    · cases h
  case arith op x y ihx ihy =>
    split at h
    · rename_i Sx Sy hx hy; cases h; exact .arith (ihx d Γ Sx hx) (ihy d Γ Sy hy) (by simp)
    · cases h
  case arr ls =>
    split at h
    · rename_i hl
      cases h
      exact .arr (fun x hx => by simpa using List.all_eq_true.mp hl x hx) (by simp)
    · cases h
  case arrLit inits iha =>
    split at h
    · rename_i Ls hL
      split at h
      · rename_i hs
        cases h
        obtain ⟨hst, hx⟩ := synAll_stores iha hL hs
        exact .arrLit _ hst hx (List.mem_cons_self ..) (by simp)
      · cases h
    · cases h
  case elemAt x i ihx ihi =>
    split at h
    · rename_i Sx Si hx hi
      cases h
      exact .elemAt (ihx d Γ Sx hx) (ihi d Γ Si hi) (fun s hs => contents_sub F hs) (by simp)
    · cases h
  case setElem x i v ihx ihi ihv =>
    split at h
    · rename_i Sx Si Sv hx hi hv
      split at h
      · rename_i hs
        cases h
        exact .setElem (ihx d Γ Sx hx) (ihi d Γ Si hi) (ihv d Γ Sv hv)
          (fun s hs' => storesB_sound F (List.all_eq_true.mp hs s hs')) (fun _ h => List.mem_cons_of_mem _ h)
          (List.mem_cons_self ..) (by simp)
      · cases h
    · cases h
  case lenOf x ihx =>
    split at h
    · rename_i Sx hx; cases h; exact .lenOf (ihx d Γ Sx hx) (by simp)
    · cases h
  case spread x ihx =>
    split at h
    · rename_i Sx hx; cases h; exact .spread (ihx d Γ Sx hx) (fun s hs => contents_sub F hs) (by simp)
    · cases h
  case throw x ihx =>
    split at h
    · rename_i Sx hx
      split at h
      · rename_i hO
        cases h
        exact .throw ((ihx d Γ Sx hx).sub rfl (of_decide_eq_true hO)) (by simp)
      · cases h
    · cases h
  case merge dr x y ihx ihy =>
    split at h
    · rename_i Sx Sy hx hy
      split at h
      · rename_i Q hq
        split at h
        · rename_i hs
          cases h
          obtain ⟨hsub, hc⟩ := closeQ_sound F hq
          exact .merge (ihx d Γ Sx hx) (ihy d Γ Sy hy) hsub hc
            (fun s hs' => storesB_sound F (List.all_eq_true.mp hs s hs')) (List.mem_cons_self ..) (by simp) (by simp)
        · cases h
      · cases h
    · cases h
  case makeKey k x ihk ihx =>
    split at h
    · rename_i Sk Sx hk hx
      split at h
      · rename_i hs
        cases h
        exact .makeKey (ihk d Γ Sk hk) (storesB_sound F hs) (ihx d Γ Sx hx) (List.mem_cons_self ..) (by simp)
      · cases h
    · cases h
  case makeGraph ar E K s caps k rest comp ns args _ _ iha =>
    split at h
    · rename_i Ls hL
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true] at hs
        obtain ⟨hs, hE⟩ := hs
        obtain ⟨hst, hx⟩ := synAll_stores iha hL hs
        have hE' : ∀ e ∈ E, Lowered F.flow e := fun e he => lowB_sound F (List.all_eq_true.mp hE e he)
        unfold graphSites at h
        split at h
        · rename_i hC
          split at h
          · rename_i c hc
            split at h
            · rename_i hb
              cases h
              simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb
              obtain ⟨hall, hop⟩ := hb
              refine .makeGraphC c.flow _ hst hx (List.mem_cons_self ..) hC (by simp [FFlow.flow, hc])
                (fun c' π' h' => ?_) (by simp [FCode.flow]) (fun ht => ?op) hE' (by simp)
              case op =>
                simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hop
                rcases hop with hn | hop
                · exact absurd ht hn
                · exact openB_sound F hop
              obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at h'
              obtain ⟨hcaps, hself⟩ := hall _ (FFlow.at_ctxs hfc)
              refine ⟨fun i u hu => ?_, selfFnB_sound hself⟩
              have hi : i < caps.length := (List.getElem?_eq_some_iff.mp hu).1
              have := hcaps i hi
              rw [hu] at this
              simp only [Option.all_some] at this
              cases hp : partSites τ d Γ u with
              | none => simp [hp] at this
              | some S' =>
                simp only [hp, Option.any_some, decide_eq_true_eq] at this
                exact partSites_sound τ hp this
            · cases h
          · cases h
        · rename_i hC
          cases hp : partsSites τ d Γ caps with
          | none => simp [hp] at h
          | some Sp =>
            simp only [hp, Option.map_some, Option.some.injEq] at h; subst h
            exact .makeGraphOut _ hst hx (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simpa using hC) hE'
              (fun u hu => (partsSites_sound τ hp u hu).sub fun _ hy =>
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)) (by simp) (List.mem_cons_self ..)
      · cases h
    · cases h
  all_goals cases h

end sound

/-! ## The edges of a finite proposal -/

/-- **Slots constant past a width.** -/
def Stable {α : Type} (τ : Nat → α) (N : Nat) : Prop := ∀ i, N ≤ i → τ i = τ N

theorem Stable.mono {α : Type} {τ : Nat → α} {N N' : Nat} (h : Stable τ N) (hN : N ≤ N') : Stable τ N' :=
  fun i hi => (h i (by omega)).trans (h N' hN).symm

omit [DecidableEq P.Site] in
theorem FNode.envAt_stable (x : FNode P) : Stable x.envAt x.env.size := by
  intro i hi
  simp only [FNode.envAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi,
    Array.getElem?_eq_none (Nat.le_refl x.env.size)]

omit [DecidableEq P.Site] in
theorem pushSites_stable {τ : Nat → Sites P} {N : Nat} (Sv : Sites P) (h : Stable τ N) :
    Stable (pushSites Sv τ) (N + 1) := by
  intro i hi
  cases i with
  | zero => omega
  | succ i => simp only [pushSites]; exact h i (by omega)

/-- The length of an edge's mapping. -/
def mlen : Option (List Nat) → Nat
  | none => 0
  | some slots => slots.length

omit [DecidableEq P.Site] in
theorem mapIdx_stable {τ : Nat → Sites P} {m : Option (List Nat)} {N i : Nat} (hτ : Stable τ N)
    (hm : mlen m ≤ N) (hi : N ≤ i) : τ (mapIdx m i) = τ (mapIdx m N) := by
  cases m with
  | none => exact hτ i hi
  | some slots =>
    simp only [mlen] at hm
    simp only [mapIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : slots.length ≤ i),
      List.getElem?_eq_none hm]

omit [DecidableEq P.Site] in
/-- A carriage holds of every smaller source. -/
theorem Carries.of_sub {τ τ₁ τ' : Nat → Sites P} {m : Option (List Nat)} (h : Carries τ₁ τ' m)
    (hs : ∀ i, Sub (τ i) (τ₁ i)) : Carries τ τ' m :=
  fun i => (hs (mapIdx m i)).trans (h i)

/-- **An edge carries the slots**, decided at the slots below a width past
which both sides and the mapping are constant. -/
def carriesB (τ τ' : Nat → Sites P) (m : Option (List Nat)) (N : Nat) : Bool :=
  (List.range (N + 1)).all fun i => decide (Sub (τ (mapIdx m i)) (τ' i))

theorem carriesB_sound {τ τ' : Nat → Sites P} {m : Option (List Nat)} {N : Nat} (hτ : Stable τ N)
    (hτ' : Stable τ' N) (hm : mlen m ≤ N) (h : carriesB τ τ' m N = true) : Carries τ τ' m := by
  simp only [carriesB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro i
  rcases Nat.lt_or_ge i (N + 1) with hi | hi
  · exact h i hi
  · rw [hτ' i (by omega), mapIdx_stable hτ hm (by omega)]
    exact h N (by omega)

/-- **An edge carries the signatures**, decided at the target's named
slots, as indices into one table: a named index at the target is the
index the source's slot holds. -/
def carriesFnB (ι ι' : Nat → Option Nat) (m : Option (List Nat)) (n : Nat) : Bool :=
  (List.range n).all fun i => (ι' i).all fun t => decide (ι (mapIdx m i) = some t)

theorem carriesFnB_sound {sigAt : Option Nat → Option FnSig} (hsig : sigAt none = none) {ι ι' : Nat → Option Nat}
    {m : Option (List Nat)} {n : Nat} (hι' : ∀ i σ, sigAt (ι' i) = some σ → i < n)
    (h : carriesFnB ι ι' m n = true) : CarriesFn (fun i => sigAt (ι i)) (fun i => sigAt (ι' i)) m := by
  intro i σ hi
  simp only at hi ⊢
  simp only [carriesFnB, List.all_eq_true, List.mem_range] at h
  have := h i (hι' i σ hi)
  cases ht : ι' i with
  | none => rw [ht, hsig] at hi; cases hi
  | some t =>
    rw [ht] at this hi
    simp only [Option.all_some, decide_eq_true_eq] at this
    rw [this, hi]

/-- The indices of a node's slots with a value pushed at slot `0`. -/
def pushIx (v : Option Nat) (ι : Nat → Option Nat) : Nat → Option Nat
  | 0 => v
  | i + 1 => ι i

omit [DecidableEq P.Site] in
theorem pushFn_sigAt (c : FCode P) (v : Option Nat) (ι : Nat → Option Nat) :
    pushFn (c.sigAt v) (fun i => c.sigAt (ι i)) = fun i => c.sigAt (pushIx v ι i) := by
  funext i; cases i <;> rfl

section edges
variable (F : FFlow P) (c : FCode P)

/-- **An edge to a target**, decided: the slots `ρ`, constant past `Nρ`,
and its signatures' indices `ι`. The target's node is read once. -/
def edgeB (ρ : Nat → Sites P) (Nρ : Nat) (ι : Nat → Option Nat) (y : Target) : Bool :=
  let x := c.node y.label
  carriesB ρ x.envAt y.mapping (max Nρ (max x.env.size (mlen y.mapping))) &&
    carriesFnB ι x.fnAt y.mapping x.fn.size

theorem edgeB_sound {ρ : Nat → Sites P} {Nρ : Nat} {ι : Nat → Option Nat} {y : Target} (hρ : Stable ρ Nρ)
    (h : edgeB c ρ Nρ ι y = true) :
    Carries ρ (c.flow.env y.label) y.mapping ∧
      CarriesFn (fun i => c.sigAt (ι i)) (c.flow.fn y.label) y.mapping := by
  simp only [edgeB, Bool.and_eq_true] at h
  exact ⟨carriesB_sound (hρ.mono (by omega)) (((c.node y.label).envAt_stable).mono (by omega)) (by omega) h.1,
    carriesFnB_sound (sigAt := c.sigAt) rfl (fun _ _ hi => FCode.fn_lt hi) h.2⟩

/-- **The checks of a continuation** of a node `x`, decided. -/
def contChkB (x : FNode P) : Continuation → Bool
  | .ret => decide (Sub x.val c.ret)
  | .bind y => edgeB c (pushSites x.val x.envAt) (x.env.size + 1) (pushIx x.vfn x.fnAt) y
  | .effect y => edgeB c x.envAt x.env.size x.fnAt y
  | .branch y n => edgeB c x.envAt x.env.size x.fnAt y && edgeB c x.envAt x.env.size x.fnAt n
  | .branchBind y n =>
      edgeB c (pushSites [] x.envAt) (x.env.size + 1) (pushIx none x.fnAt) y &&
      edgeB c (pushSites [] x.envAt) (x.env.size + 1) (pushIx none x.fnAt) n
  | .tagBind _ y n =>
      edgeB c (pushSites x.val x.envAt) (x.env.size + 1) (pushIx x.vfn x.fnAt) y &&
      edgeB c (pushSites x.val x.envAt) (x.env.size + 1) (pushIx x.vfn x.fnAt) n

/-- **The checks of a handler** of a node `x`, decided. -/
def handlerChkB (x : FNode P) : Option Target → Bool
  | none => true
  | some y => edgeB c (pushSites F.O x.envAt) (x.env.size + 1) (pushIx none x.fnAt) y

theorem contChkB_sound {l : Nat} {k : Continuation} (h : contChkB c (c.node l) k = true) :
    ContChk c.flow l k := by
  have hs : Stable (c.node l).envAt (c.node l).env.size := (c.node l).envAt_stable
  have hv : pushFn (c.flow.vfn l) (c.flow.fn l) = fun i => c.sigAt (pushIx (c.node l).vfn (c.node l).fnAt i) :=
    pushFn_sigAt c _ _
  have hn : pushFn none (c.flow.fn l) = fun i => c.sigAt (pushIx none (c.node l).fnAt i) :=
    pushFn_sigAt c none _
  cases k with
  | ret => simp only [contChkB, decide_eq_true_eq] at h; exact h
  | bind y =>
    simp only [ContChk, hv]
    exact edgeB_sound c (pushSites_stable _ hs) h
  | effect y => exact edgeB_sound c hs h
  | branch y n =>
    simp only [contChkB, Bool.and_eq_true] at h
    exact ⟨edgeB_sound c hs h.1, edgeB_sound c hs h.2⟩
  | branchBind y n =>
    simp only [contChkB, Bool.and_eq_true] at h
    simp only [ContChk, hn]
    exact ⟨edgeB_sound c (pushSites_stable _ hs) h.1, edgeB_sound c (pushSites_stable _ hs) h.2⟩
  | tagBind _ y n =>
    simp only [contChkB, Bool.and_eq_true] at h
    simp only [ContChk, hv]
    exact ⟨edgeB_sound c (pushSites_stable _ hs) h.1, edgeB_sound c (pushSites_stable _ hs) h.2⟩

theorem handlerChkB_sound {l : Nat} {x : Option Target} (h : handlerChkB F c (c.node l) x = true) :
    HandlerChk F.flow c.flow l x := by
  cases x with
  | none => trivial
  | some y =>
    simp only [HandlerChk]
    rw [show pushFn none (c.flow.fn l) = fun i => c.sigAt (pushIx none (c.node l).fnAt i) from pushFn_sigAt c none _]
    exact edgeB_sound c (pushSites_stable _ (c.node l).envAt_stable) h

/-! ## The checks of a code and of a flow -/

/-- A node value naming a signature is a slot naming it, decided by
index. -/
def vfnB (x : FNode P) (e : Tm) : Bool :=
  match x.vfn, e with
  | none, _ => true
  | some t, .var j => decide (x.fnAt j = some t)
  | some _, _ => false

omit [DecidableEq P.Site] in
theorem vfnB_sound {l : Nat} {e : Tm} (h : vfnB (c.node l) e = true) :
    ∀ σ, c.flow.vfn l = some σ → ∃ j, e = .var j ∧ c.flow.fn l j = some σ := by
  intro σ hσ
  simp only [FCode.flow] at hσ ⊢
  unfold vfnB at h
  cases hx : (c.node l).vfn with
  | none => rw [hx] at hσ; cases hσ
  | some t =>
    rw [hx] at h hσ
    cases e <;> simp_all

/-- **The checks of a node** `l`, of expression `e`, continuation `k` and
handler `x`, decided. -/
def nodeAtB (l : Nat) (e : Tm) (k : Continuation) (x : Option Target) : Bool :=
  let nd := c.node l
  (syn F nd.envAt (fun i => c.sigAt (nd.fnAt i)) ⟨c.allocAt (k, x), nd.out⟩ nd.cx 0 (fun _ => none) e).any
    (fun S => decide (Sub S nd.val)) &&
    vfnB nd e && contChkB c nd k && handlerChkB F c nd x

/-- **The checks of a node**, decided. -/
def nodeB (m : Code) (l : Nat) : Bool :=
  match m.1[l]?, m.2[l]? with
  | some e, some (k, x) => nodeAtB F c l e k x
  | _, _ => true

/-- **The checks of a code**, decided: each node with its continuation and
handler, read in one pass. -/
def codeChkB (m : Code) : Bool := (m.1.zip m.2).zipIdx.all fun ((e, k, x), l) => nodeAtB F c l e k x

/-- **The checks of a code, decided, hold** (proved). -/
theorem codeChkB_sound {m : Code} (h : codeChkB F c m = true) : CodeChk F.flow m c.flow := by
  intro l e k x he hk
  have hm : ((e, k, x), l) ∈ (m.1.zip m.2).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some]
    exact ⟨he, hk⟩
  have := List.all_eq_true.mp h _ hm
  simp only [nodeAtB, Bool.and_eq_true] at this
  obtain ⟨⟨⟨hs, hv⟩, hc⟩, hh⟩ := this
  refine ⟨?_, vfnB_sound c hv, contChkB_sound c hc, handlerChkB_sound F c hh⟩
  change (syn F (c.flow.env l) (c.flow.fn l) (c.flow.at l (k, x)) (c.node l).cx 0 (fun _ => none) e).any _ = true at hs
  cases hS : syn F (c.flow.env l) (c.flow.fn l) (c.flow.at l (k, x)) (c.node l).cx 0 (fun _ => none) e with
  | none => simp [hS] at hs
  | some S =>
    simp only [hS, Option.any_some, decide_eq_true_eq] at hs
    exact (syn_sound e 0 _ S hS).sub rfl hs

end edges

/-- **The checks of a finite flow**: each code's checks, `O` holding
outside storage, closed in the heap of sites, its storage able to hold all
of `O`. -/
def FFlow.check (F : FFlow P) : Bool :=
  decide (none ∈ F.O) && F.O.all (fun s => decide (Sub (F.contents s) F.O)) && F.O.all (fun s => storesB F s F.O) &&
    F.codes.all fun mc => mc.2.all fun cc =>
      codeChkB F cc.2 mc.1 && (F.at mc.1 entryCx).any fun c₀ =>
        decide (c₀.alloc.obj = cc.2.alloc.obj ∧ c₀.alloc.arr = cc.2.alloc.arr ∧ c₀.allocs = cc.2.allocs ∧
          c₀.tok = cc.2.tok)

/-- **The checks of a finite flow give its facts** (proved). -/
theorem FFlow.check_sound {F : FFlow P} (h : F.check = true) : F.flow.Facts := by
  simp only [FFlow.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hn, hcl⟩, hw⟩, hc⟩ := h
  refine ⟨fun m c π hm => ?_, fun m c π hm => ?_, hn, fun s hs => hcl s hs, fun s hs => storesB_sound F (hw s hs)⟩
  · obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hm
    obtain ⟨l, hl, hcl'⟩ := FFlow.at_mem hfc
    exact codeOk_of_chk (codeChkB_sound F fc (hc _ hl _ hcl').1)
  · obtain ⟨fc, hfc, rfl⟩ := FFlow.code_at hm
    obtain ⟨l, hl, hcl'⟩ := FFlow.at_mem hfc
    have h2 := (hc _ hl _ hcl').2
    cases h0 : F.at m entryCx with
    | none => rw [h0] at h2; simp at h2
    | some c₀ =>
      rw [h0] at h2
      simp only [Option.any_some, decide_eq_true_eq] at h2
      refine ⟨c₀.flow, by simp [FFlow.flow, h0], ?_, h2.2.2.2⟩
      show c₀.allocAt = fc.allocAt
      have hA : c₀.alloc = fc.alloc := by
        cases h₁ : c₀.alloc; cases h₂ : fc.alloc
        rw [h₁, h₂] at h2; simp only at h2; rw [h2.1, h2.2.1]
      funext kx
      simp only [FCode.allocAt, hA, h2.2.2.1]

/-! ## The marks and the entry -/

/-- No local site in a set, decided. -/
def noLocalB (S : Sites P) : Bool := S.all fun s => s.all fun s' => decide (P.mark s' ≠ .local)

omit [DecidableEq P.Site] in
theorem noLocalB_sound {S : Sites P} (h : noLocalB S = true) : NoLocal S := by
  intro s hs s' he
  have := List.all_eq_true.mp h s hs
  subst he; simpa using this

theorem FFlow.lookup_cases (F : FFlow P) (s : Option P.Site) :
    (F.contents s = [] ∧ F.bindings s = []) ∨ ∃ e ∈ F.heap, e.1 = s ∧ F.contents s = e.2.1 ∧ F.bindings s = e.2.2 := by
  cases hl : look s F.heap with
  | none => exact .inl ⟨by simp [FFlow.contents, hl], by simp [FFlow.bindings, hl]⟩
  | some e => exact .inr ⟨(s, e), look_mem hl, rfl, by simp [FFlow.contents, hl], by simp [FFlow.bindings, hl]⟩

/-- **The marks a frame's checks read of a flow**, decided: `O`'s sites
released (`Lendable`), storage of a site that is not local referencing no
local site (`LocalHeld`), no binding reaching a local site. -/
def FFlow.marksB (F : FFlow P) : Bool :=
  F.O.all (fun s => s.all fun s' => decide (P.mark s' = .released)) &&
    F.heap.all fun e => (!(e.1.all fun s' => decide (P.mark s' ≠ .local)) || noLocalB e.2.1) && noLocalB e.2.2

theorem FFlow.marksB_sound {F : FFlow P} (h : F.marksB = true) :
    Lendable F.flow.O ∧ LocalHeld F.flow.H ∧ ∀ s, NoLocal (F.flow.H.bindings s) := by
  simp only [FFlow.marksB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hO, hH⟩ := h
  refine ⟨fun s hs s' he => ?_, fun s hs => ?_, fun s => ?_⟩
  · have := hO s hs; subst he; simpa using this
  · rcases F.lookup_cases s with ⟨hc, -⟩ | ⟨e, he, rfl, hc, -⟩
    · show NoLocal (F.contents s); rw [hc]; simp [NoLocal]
    · show NoLocal (F.contents e.1); rw [hc]
      have := (hH e he).1
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
      rcases this with hn | hn
      · exfalso
        cases h1 : e.1 with
        | none => simp [h1] at hn
        | some s' => simp only [h1, Option.all_some, decide_eq_false_iff_not] at hn; exact hn (hs s' h1)
      · exact noLocalB_sound hn
  · rcases F.lookup_cases s with ⟨-, hb⟩ | ⟨e, he, rfl, -, hb⟩
    · show NoLocal (F.bindings s); rw [hb]; simp [NoLocal]
    · show NoLocal (F.bindings e.1); rw [hb]; exact noLocalB_sound (hH e he).2

/-- **The marks a flow gives**: a site of `O` released, every other site
local. -/
def FFlow.MarksFrom (F : FFlow P) : Prop := ∀ s, P.mark s = if some s ∈ F.O then .released else .local

theorem FFlow.mark_of_marksFrom {F : FFlow P} (hm : F.MarksFrom) {s : P.Site} (h : P.mark s ≠ .local) :
    some s ∈ F.O := by
  rw [hm s] at h
  split at h
  · assumption
  · exact absurd rfl h

/-- **At the marks a flow gives, `O` is lent** (proved). -/
theorem FFlow.lendable_of_marksFrom {F : FFlow P} (hm : F.MarksFrom) : Lendable F.flow.O := by
  intro s hs s' he
  subst he
  rw [hm s']
  simp [show some s' ∈ F.O from hs]

/-- **At the marks a flow gives, local storage is held only by local
storage** (proved): storage of a site that is not local is of `O`, whose
contents `O` holds, and `O` has no local site. -/
theorem FFlow.localHeld_of_marksFrom {F : FFlow P} (hm : F.MarksFrom) (hF : F.flow.Facts) :
    LocalHeld F.flow.H := by
  have hO : ∀ s, (∀ s', s = some s' → P.mark s' ≠ .local) → s ∈ F.O := by
    intro s hs
    cases s with
    | none => exact hF.none
    | some s' => exact F.mark_of_marksFrom hm (hs s' rfl)
  intro s hs t ht t' he
  subst he
  have ht' : some t' ∈ F.O := hF.closed s (hO s hs) _ ht
  rw [hm t']
  simp [ht']

/-- **No binding reaches a local site**, decided: the condition on the
values the code of a closure of outside code or of a bound function holds,
which the closure of `O` does not give. -/
def FFlow.bindingsB (F : FFlow P) : Bool := F.heap.all fun e => noLocalB e.2.2

theorem FFlow.bindingsB_sound {F : FFlow P} (h : F.bindingsB = true) : ∀ s, NoLocal (F.flow.H.bindings s) := by
  intro s
  rcases F.lookup_cases s with ⟨-, hb⟩ | ⟨e, he, rfl, -, hb⟩
  · show NoLocal (F.bindings s); rw [hb]; simp [NoLocal]
  · show NoLocal (F.bindings e.1); rw [hb]; exact noLocalB_sound (List.all_eq_true.mp h e he)

/-- **The marks a frame's checks read, at the marks a flow gives** (proved):
`O` lent, local storage held only by local storage, and, by `bindingsB`,
no binding reaching a local site. -/
theorem FFlow.marks_of_marksFrom {F : FFlow P} (hm : F.MarksFrom) (hF : F.flow.Facts) (hb : F.bindingsB = true) :
    Lendable F.flow.O ∧ LocalHeld F.flow.H ∧ ∀ s, NoLocal (F.flow.H.bindings s) :=
  ⟨F.lendable_of_marksFrom hm, F.localHeld_of_marksFrom hm hF, F.bindingsB_sound hb⟩

/-- **An entry of a member**, decided: every slot of the node `l` of a code
holds what outside code may supply, and the code's returns lie within
`O`. -/
def FFlow.entryB (F : FFlow P) (m : Code) (l : Nat) : Bool :=
  (F.at m entryCx).any fun c =>
    decide (Sub c.ret F.O) && suppliedB F (c.node l).dflt && (c.node l).env.all fun S => suppliedB F S

theorem FFlow.entryB_sound {F : FFlow P} {m : Code} {l : Nat} (h : F.entryB m l = true) :
    ∃ π, F.flow.code m entryCx = some π ∧ (∀ i, Supplied F.flow (π.env l i)) ∧ Sub π.ret F.flow.O := by
  unfold FFlow.entryB at h
  cases hl : F.at m entryCx with
  | none => simp [hl] at h
  | some c =>
    simp only [hl, Option.any_some, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
    obtain ⟨⟨hr, hd⟩, he⟩ := h
    refine ⟨c.flow, by simp [FFlow.flow, hl], fun i => ?_, hr⟩
    show Supplied F.flow ((c.node l).env.getD i (c.node l).dflt)
    rw [Array.getD_eq_getD_getElem?]
    cases hi : (c.node l).env[i]? with
    | none => exact suppliedB_sound F hd
    | some S =>
      obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
      exact suppliedB_sound F (he i hlt)

end Verification.TolerantFrames.ReadOnly
