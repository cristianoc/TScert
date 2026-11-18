import Verification.Paper.TolerantFrames.ReadOnlyComponents

/-! # Read-only handles: the active frame and the roots of outside code

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "Frames
and whose code runs", "What the Lean states"), over the paper model's
reduction (`Step`).

- **The evaluation path** of a term (`path`): the frames on it, innermost
  first, each with its tag and its term with the nested frame on the path
  cut out, and last the top segment, tagged with the code that runs it. A
  step of a term is a step inside the innermost frame on its path
  (`step_path`): that frame's term changes and the frames outside it stay,
  or the frame is popped and its parent's term changes; the frames on the
  path of what the step produces are pushed.
- **The roots of code outside a set of components** are `vals`
  (`ReadOnlyRegion`) at the term: the values held at the positions of the
  frames whose tags run no code of the set, with the values their code
  holds.
- A step whose active frame runs no code of the set changes only locations
  one path step from these roots (`step_reach`), and every value it leaves
  in storage it changes or allocates, from which a path step leaves, is one
  of them (`step_writes`): `OutsideStep.reach` and `OutsideStep.writes` at a
  family's component (`outsideStep_reach`, `outsideStep_writes`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-! ## The evaluation path -/

/-- The term a cut leaves where the nested frame on the path was. -/
def hole : Tm := .undef

/-- Apply `g` to the last element of a list. -/
def mapLast {α : Type} (g : α → α) : List α → List α
  | [] => []
  | [x] => [g x]
  | x :: y :: xs => x :: mapLast g (y :: xs)

/-- Rebuild the term of the last element of a path, keeping its tag. -/
def wrap (g : Tm → Tm) (P : List (ComponentTag × Tm)) : List (ComponentTag × Tm) :=
  mapLast (fun p => (p.1, g p.2)) P

mutual
/-- **The evaluation path** of a term whose top segment runs code tagged
`c`: the frames on it, innermost first, each with its tag and its term with
the nested frame on the path cut out (`hole`), then the top segment. It
follows `Step`'s congruence rules: the first position whose term is not a
value, in their order; into a frame's running term (`frameC`), whose code
is the frame's tag. A `goto` is a frame not yet entered. -/
def path (c : ComponentTag) : Tm → List (ComponentTag × Tm)
  | .invoke f r args =>
    if isVal f = false then wrap (fun s => .invoke s r args) (path c f)
    else if isVal r = false then wrap (fun s => .invoke f s args) (path c r)
    else pathArgs c (.invoke f r) args
  | .construct f args =>
    if isVal f = false then wrap (fun s => .construct s args) (path c f)
    else pathArgs c (.construct f) args
  | .letE a b => if isVal a = false then wrap (fun s => .letE s b) (path c a) else [(c, .letE a b)]
  | .makeAt cc ns xs => pathArgs c (.makeAt cc ns) xs
  | .readAt f a => if isVal a = false then wrap (.readAt f) (path c a) else [(c, .readAt f a)]
  | .indexAt a key =>
    if isVal a = false then wrap (fun s => .indexAt s key) (path c a)
    else if isVal key = false then wrap (.indexAt a) (path c key) else [(c, .indexAt a key)]
  | .writeAt f a b =>
    if isVal a = false then wrap (fun s => .writeAt f s b) (path c a)
    else if isVal b = false then wrap (.writeAt f a) (path c b) else [(c, .writeAt f a b)]
  | .test k a => if isVal a = false then wrap (.test k) (path c a) else [(c, .test k a)]
  | .ite x a b => if isVal x = false then wrap (fun s => .ite s a b) (path c x) else [(c, .ite x a b)]
  | .arith op a b =>
    if isVal a = false then wrap (fun s => .arith op s b) (path c a)
    else if isVal b = false then wrap (.arith op a) (path c b) else [(c, .arith op a b)]
  | .arrLit xs => pathArgs c .arrLit xs
  | .elemAt a i =>
    if isVal a = false then wrap (fun s => .elemAt s i) (path c a)
    else if isVal i = false then wrap (.elemAt a) (path c i) else [(c, .elemAt a i)]
  | .setElem a i v =>
    if isVal a = false then wrap (fun s => .setElem s i v) (path c a)
    else if isVal i = false then wrap (fun s => .setElem a s v) (path c i)
    else if isVal v = false then wrap (.setElem a i) (path c v) else [(c, .setElem a i v)]
  | .lenOf a => if isVal a = false then wrap .lenOf (path c a) else [(c, .lenOf a)]
  | .spread a => if isVal a = false then wrap .spread (path c a) else [(c, .spread a)]
  | .throw a => if isVal a = false then wrap .throw (path c a) else [(c, .throw a)]
  | .merge d a b =>
    if isVal a = false then wrap (fun s => .merge d s b) (path c a)
    else if isVal b = false then wrap (.merge d a) (path c b) else [(c, .merge d a b)]
  | .makeKey k a =>
    if isVal k = false then wrap (fun s => .makeKey s a) (path c k)
    else if isVal a = false then wrap (.makeKey k) (path c a) else [(c, .makeKey k a)]
  | .goto E K l L d comp => [(comp, .goto E K l L d comp), (c, hole)]
  | .frame E K t L d k x comp => wrap (fun s => .frame E K s L d k x comp) (path comp t) ++ [(c, hole)]
  | t => [(c, t)]
termination_by structural t => t

/-- The path through a list of terms evaluated left to right, `k` rebuilding
the term from the list. -/
def pathArgs (c : ComponentTag) (k : List Tm → Tm) : List Tm → List (ComponentTag × Tm)
  | [] => [(c, k [])]
  | a :: as =>
    if isVal a = false then wrap (fun s => k (s :: as)) (path c a)
    else pathArgs c (fun xs => k (a :: xs)) as
termination_by structural xs => xs
end

/-- **The active tag**: the tag of the innermost frame on the path, or of
the top segment when no frame is on it. -/
def activeTag (c : ComponentTag) (t : Tm) : ComponentTag := ((path c t).head?.map Prod.fst).getD c

/-! ### Lists of frames -/

theorem mapLast_cons_cons {α : Type} {g : α → α} {x y : α} {xs : List α} :
    mapLast g (x :: y :: xs) = x :: mapLast g (y :: xs) := rfl

theorem mapLast_cons {α : Type} {g : α → α} {x : α} {ys : List α} (hy : ys ≠ []) :
    mapLast g (x :: ys) = x :: mapLast g ys := by
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hy; rfl

theorem mapLast_append {α : Type} {g : α → α} :
    ∀ {xs ys : List α}, ys ≠ [] → mapLast g (xs ++ ys) = xs ++ mapLast g ys
  | [], _, _ => rfl
  | x :: xs, ys, hy => by
    rw [List.cons_append, mapLast_cons (by simp [hy]), mapLast_append hy, List.cons_append]

theorem wrap_snoc {g : Tm → Tm} {init : List (ComponentTag × Tm)} {c : ComponentTag} {s : Tm} :
    wrap g (init ++ [(c, s)]) = init ++ [(c, g s)] := by
  simp [wrap, mapLast_append]; rfl

theorem mapLast_fst {α β : Type} {g : α × β → α × β} (hg : ∀ p, (g p).1 = p.1) :
    ∀ P : List (α × β), (mapLast g P).map Prod.fst = P.map Prod.fst
  | [] => rfl
  | [x] => by simp [mapLast, hg]
  | x :: y :: xs => by rw [mapLast_cons_cons, List.map_cons, mapLast_fst hg (y :: xs)]; rfl

theorem wrap_fst {g : Tm → Tm} (P : List (ComponentTag × Tm)) : (wrap g P).map Prod.fst = P.map Prod.fst :=
  mapLast_fst (g := fun p => (p.1, g p.2)) (fun _ => rfl) P

theorem wrap_head {g : Tm → Tm} (P : List (ComponentTag × Tm)) :
    (wrap g P).head?.map Prod.fst = P.head?.map Prod.fst := by
  rw [← List.head?_map, ← List.head?_map, wrap_fst]

theorem wrap_ne_nil {g : Tm → Tm} {P : List (ComponentTag × Tm)} (h : P ≠ []) : wrap g P ≠ [] := by
  intro he
  have := congrArg List.length (wrap_fst (g := g) P)
  rw [he] at this
  simp at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)

/-! ### The path's shape -/

theorem wrap_ex {g : Tm → Tm} {c : ComponentTag} {P : List (ComponentTag × Tm)}
    (h : ∃ init s, P = init ++ [(c, s)]) : ∃ init s, wrap g P = init ++ [(c, s)] := by
  obtain ⟨init, s, rfl⟩ := h
  exact ⟨init, g s, wrap_snoc⟩

theorem pathArgs_ex {c : ComponentTag} :
    ∀ {xs : List Tm}, (∀ a ∈ xs, ∀ c, ∃ init s, path c a = init ++ [(c, s)]) →
      ∀ k, ∃ init s, pathArgs c k xs = init ++ [(c, s)]
  | [], _, k => ⟨[], k [], rfl⟩
  | a :: as, h, k => by
    simp only [pathArgs]
    split
    · exact wrap_ex (h a List.mem_cons_self c)
    · exact pathArgs_ex (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

/-- **The path ends at the top segment**, tagged with the code that runs
it. -/
theorem path_last (t : Tm) : ∀ c, ∃ init s, path c t = init ++ [(c, s)] := by
  induction t using Tm.induct
  all_goals intro c
  all_goals simp only [path]
  all_goals repeat' split
  all_goals first
    | exact ⟨[], _, rfl⟩
    | exact ⟨_, _, rfl⟩
    | exact ⟨[_], _, rfl⟩
    | (apply wrap_ex; solve_by_elim)
    | (apply pathArgs_ex; assumption)

theorem path_ne_nil (c : ComponentTag) (t : Tm) : path c t ≠ [] := by
  obtain ⟨init, s, h⟩ := path_last t c
  rw [h]; simp

/-- A value's path is its top segment alone. -/
theorem path_val {c : ComponentTag} {v : Tm} (hv : isVal v = true) : path c v = [(c, v)] := by
  cases v <;> simp_all [isVal, path]

theorem pathArgs_vals {c : ComponentTag} :
    ∀ {xs : List Tm} (k : List Tm → Tm), (∀ a ∈ xs, isVal a = true) → pathArgs c k xs = [(c, k xs)]
  | [], _, _ => rfl
  | a :: as, k, h => by
    simp only [pathArgs, h a List.mem_cons_self]
    exact pathArgs_vals (fun xs => k (a :: xs)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem pathArgs_append {c : ComponentTag} :
    ∀ {pre : List Tm} (xs : List Tm) (k : List Tm → Tm), (∀ a ∈ pre, isVal a = true) →
      pathArgs c k (pre ++ xs) = pathArgs c (fun ys => k (pre ++ ys)) xs
  | [], _, _, _ => rfl
  | a :: as, xs, k, h => by
    simp only [List.cons_append, pathArgs, h a List.mem_cons_self]
    exact pathArgs_append xs (fun ys => k (a :: ys)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The path through a list at its first term that is not a value. -/
theorem pathArgs_at {c : ComponentTag} :
    ∀ {xs : List Tm} {i : Nat} {a : Tm} (k : List Tm → Tm), xs[i]? = some a →
      (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → isVal a = false →
      pathArgs c k xs = wrap (fun s => k (xs.set i s)) (path c a)
  | [], _, _, _, h, _, _ => by simp at h
  | b :: bs, 0, a, k, h, _, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [pathArgs, ha]
  | b :: bs, i + 1, a, k, h, hpre, ha => by
    have hb : isVal b = true := hpre 0 (Nat.succ_pos _) b rfl
    simp only [pathArgs, hb]
    rw [pathArgs_at (fun xs => k (b :: xs)) (by simpa using h)
      (fun j hj w hw => hpre (j + 1) (by omega) w (by simpa using hw)) ha]
    rfl

/-! ### How a step changes the path -/

/-- **A step's change of the path** (the draft, "Frames and whose code
runs"): the innermost frame `F` stays, its term changing to `F'`'s, or it
is popped and its parent `G`'s term changes to `G'`'s; the frames outside
stay; `new` are the frames pushed, those on the path of the term the step
produces. -/
def PathStep (P P' : List (ComponentTag × Tm)) : Prop :=
  (∃ new F F' rest, P = F :: rest ∧ P' = new ++ F' :: rest ∧ F'.1 = F.1) ∨
  (∃ new F G G' rest, P = F :: G :: rest ∧ P' = new ++ G' :: rest ∧ G'.1 = G.1)

theorem PathStep.wrap {P P' : List (ComponentTag × Tm)} (g : Tm → Tm) (h : PathStep P P') :
    PathStep (ReadOnly.wrap g P) (ReadOnly.wrap g P') := by
  rcases h with ⟨new, F, F', rest, rfl, rfl, ht⟩ | ⟨new, F, G, G', rest, rfl, rfl, ht⟩
  · by_cases hr : rest = []
    · subst hr
      refine .inl ⟨new, (F.1, g F.2), (F'.1, g F'.2), [], rfl, ?_, ht⟩
      simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _)]; rfl
    · refine .inl ⟨new, F, F', ReadOnly.wrap g rest, ?_, ?_, ht⟩
      · simp only [ReadOnly.wrap, mapLast_cons hr]
      · simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _), mapLast_cons hr]
  · by_cases hr : rest = []
    · subst hr
      refine .inr ⟨new, F, (G.1, g G.2), (G'.1, g G'.2), [], rfl, ?_, ht⟩
      simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _)]; rfl
    · refine .inr ⟨new, F, G, G', ReadOnly.wrap g rest, ?_, ?_, ht⟩
      · simp only [ReadOnly.wrap, mapLast_cons (List.cons_ne_nil _ _), mapLast_cons hr]
      · simp only [ReadOnly.wrap, mapLast_append (List.cons_ne_nil _ _), mapLast_cons hr]

theorem PathStep.append {P P' : List (ComponentTag × Tm)} (Q : List (ComponentTag × Tm)) (h : PathStep P P') :
    PathStep (P ++ Q) (P' ++ Q) := by
  rcases h with ⟨new, F, F', rest, rfl, rfl, ht⟩ | ⟨new, F, G, G', rest, rfl, rfl, ht⟩
  · exact .inl ⟨new, F, F', rest ++ Q, rfl, by simp, ht⟩
  · exact .inr ⟨new, F, G, G', rest ++ Q, rfl, by simp, ht⟩

/-- **A step inside an evaluation context**: the context's path wraps the
stepped position's, and where the position's new term is a value the
context's evaluation moves on, the top segment changing. -/
theorem PathStep.ctx {c : ComponentTag} {a a' A A' : Tm} {g : Tm → Tm}
    (hrel : PathStep (path c a) (path c a')) (hA : path c A = ReadOnly.wrap g (path c a))
    (hA' : isVal a' = false → path c A' = ReadOnly.wrap g (path c a')) : PathStep (path c A) (path c A') := by
  cases hv : isVal a'
  · rw [hA, hA' hv]; exact hrel.wrap g
  · rw [path_val hv] at hrel
    obtain ⟨init, s, hl⟩ := path_last A' c
    rw [hA, hl]
    rcases hrel with ⟨new, F, F', rest, hP, hP', ht⟩ | ⟨new, F, G, G', rest, hP, hP', ht⟩
    · obtain ⟨rfl, rfl, rfl⟩ : new = [] ∧ F' = (c, a') ∧ rest = [] := by
        cases new with
        | nil => simp at hP'; exact ⟨rfl, hP'.1.symm, hP'.2⟩
        | cons _ _ => simp at hP'
      rw [hP]
      exact .inl ⟨init, (F.1, g F.2), (c, s), [], rfl, by simp, by simp [← ht]⟩
    · obtain ⟨rfl, rfl, rfl⟩ : new = [] ∧ G' = (c, a') ∧ rest = [] := by
        cases new with
        | nil => simp at hP'; exact ⟨rfl, hP'.1.symm, hP'.2⟩
        | cons _ _ => simp at hP'
      rw [hP]
      exact .inr ⟨init, F, (G.1, g G.2), (c, s), [], rfl, by simp, by simp [← ht]⟩

/-- A step of a frame-free redex: its path is the top segment alone. -/
theorem PathStep.base {c : ComponentTag} {t t' : Tm} {x : Tm} (h : path c t = [(c, x)]) :
    PathStep (path c t) (path c t') := by
  obtain ⟨init, s, hl⟩ := path_last t' c
  rw [h, hl]
  exact .inl ⟨init, (c, x), (c, s), [], rfl, rfl, rfl⟩

/-- A step at a frame that keeps it: a node's entry, a branch, a bind. -/
theorem PathStep.stay {P P' new : List (ComponentTag × Tm)} {F F' X : ComponentTag × Tm} (h : P = [F, X])
    (h' : P' = new ++ [F', X]) (ht : F'.1 = F.1) : PathStep P P' :=
  .inl ⟨new, F, F', [X], h, h', ht⟩

/-- A step at a frame that pops it: a return, a throw out of a node
without a handler. -/
theorem PathStep.pop {P P' init : List (ComponentTag × Tm)} {F G G' : ComponentTag × Tm} (h : P = [F, G])
    (h' : P' = init ++ [G']) (ht : G'.1 = G.1) : PathStep P P' :=
  .inr ⟨init, F, G, G', [], h, h', ht⟩

theorem set_self {xs : List Tm} {i : Nat} {a : Tm} (h : xs[i]? = some a) : xs.set i a = xs := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · subst_vars
    obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
    simp [hl, he]
  · rfl

theorem raises_path {t v : Tm} (hr : Raises t v) : ∀ c, path c t = [(c, t)] := by
  induction hr with
  | throwV hv _ => intro c; simp [path, hv]
  | callArg hf hr' ha hpre _ ih =>
    intro c
    have hna := raises_not_val ‹Raises _ _›
    simp only [path, hf, hr']
    rw [pathArgs_at _ ha hpre hna, ih c]; simp [wrap, mapLast, set_self ha]
  | constructArg hf ha hpre _ ih =>
    intro c
    have hna := raises_not_val ‹Raises _ _›
    simp only [path, hf]
    rw [pathArgs_at _ ha hpre hna, ih c]; simp [wrap, mapLast, set_self ha]
  | makeArg ha hpre _ ih =>
    intro c
    have hna := raises_not_val ‹Raises _ _›
    simp only [path]
    rw [pathArgs_at _ ha hpre hna, ih c]; simp [wrap, mapLast, set_self ha]
  | arrArg ha hpre _ ih =>
    intro c
    have hna := raises_not_val ‹Raises _ _›
    simp only [path]
    rw [pathArgs_at _ ha hpre hna, ih c]; simp [wrap, mapLast, set_self ha]
  | _ =>
    rename_i ih
    intro c
    have hna := raises_not_val ‹Raises _ _›
    simp [path, ih c, wrap, mapLast, *]

@[simp] theorem isVal_objAt {fs : List (PropKey × Nat)} {cc : CallCode} {i : Nat} : isVal (.objAt fs cc i) = true := rfl
@[simp] theorem isVal_arr {ls : List (Option Nat)} : isVal (.arr ls) = true := rfl
@[simp] theorem isVal_num {b : UInt64} : isVal (.num b) = true := rfl
@[simp] theorem isVal_tru : isVal .tru = true := rfl
@[simp] theorem isVal_fls : isVal .fls = true := rfl
@[simp] theorem isVal_str {s : String} : isVal (.str s) = true := rfl
@[simp] theorem isVal_spread {a : Tm} : isVal (.spread a) = false := rfl

/-- A frame whose running term is a value or throws: the frame alone above
the top segment. -/
theorem path_frame {c : ComponentTag} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {u : Tm} {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag}
    (hu : path comp u = [(comp, u)]) : path c (.frame E K u L d k x comp) = [(comp, .frame E K u L d k x comp), (c, hole)] := by
  simp [path, hu, wrap, mapLast]

theorem PathStep.framePop {c : ComponentTag} {t t' : Tm} {F : ComponentTag × Tm} (h : path c t = [F, (c, hole)]) :
    PathStep (path c t) (path c t') := by
  obtain ⟨init, s, hl⟩ := path_last t' c
  exact PathStep.pop h hl rfl

theorem PathStep.frameGoto {c : ComponentTag} {t : Tm} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat} {L : List Tm} {d : Tm} {comp : ComponentTag}
    {F : ComponentTag × Tm} (h : path c t = [F, (c, hole)]) (ht : F.1 = comp) :
    PathStep (path c t) (path c (.goto E K l L d comp)) :=
  PathStep.stay (new := []) h rfl ht.symm

theorem PathStep.base' {c : ComponentTag} {t t' : Tm} (h : (path c t).length = 1) :
    PathStep (path c t) (path c t') := by
  obtain ⟨init, s, hl⟩ := path_last t c
  have : init = [] := by
    have := congrArg List.length hl
    rw [h] at this; simpa using this
  subst this
  exact PathStep.base (x := s) (by simpa using hl)

theorem set_at {xs : List Tm} {i : Nat} {a a' : Tm} (ha : xs[i]? = some a) : (xs.set i a')[i]? = some a' := by
  simp [(List.getElem?_eq_some_iff.mp ha).1]

theorem set_pre {xs : List Tm} {i : Nat} {a' : Tm}
    (hpre : ∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) :
    ∀ j, j < i → ∀ w, (xs.set i a')[j]? = some w → isVal w = true := by
  intro j hj w hw
  rw [List.getElem?_set_ne (by omega)] at hw
  exact hpre j hj w hw

/-- The path through a list at a position a step sets. -/
theorem pathArgs_set {c : ComponentTag} {xs : List Tm} {i : Nat} {a a' : Tm} (k : List Tm → Tm)
    (ha : xs[i]? = some a) (hpre : ∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) (hv : isVal a' = false) :
    pathArgs c k (xs.set i a') = wrap (fun s => k (xs.set i s)) (path c a') := by
  rw [pathArgs_at k (set_at ha) (set_pre hpre) hv]
  simp [List.set_set]

/-- **A step is a step inside the innermost frame on the path** (the
draft, "Frames and whose code runs"): that frame's term changes, the
frames outside it unchanged, or it is popped, a return or a throw out of a
node without a handler, and its parent's term changes; the frames on the
path of what the step produces are pushed, a call's run among them. -/
theorem step_path {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') : ∀ c, PathStep (path c t) (path c t') := by
  induction hs
  case callArg hf hr ha hpre hs ih =>
    intro c
    have hna := not_val_of_step hs
    exact PathStep.ctx (ih c) (by simp only [path, hf, hr]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path, hf, hr]; exact pathArgs_set _ ha hpre hv)
  case constructArg hf ha hpre hs ih =>
    intro c
    have hna := not_val_of_step hs
    exact PathStep.ctx (ih c) (by simp only [path, hf]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path, hf]; exact pathArgs_set _ ha hpre hv)
  case makeArg ha hpre hs ih =>
    intro c
    have hna := not_val_of_step hs
    exact PathStep.ctx (ih c) (by simp only [path]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path]; exact pathArgs_set _ ha hpre hv)
  case arrArg ha hpre hs ih =>
    intro c
    have hna := not_val_of_step hs
    exact PathStep.ctx (ih c) (by simp only [path]; exact pathArgs_at _ ha hpre hna)
      (fun hv => by simp only [path]; exact pathArgs_set _ ha hpre hv)
  case frameC ih =>
    intro c
    simp only [path]
    exact ((ih _).wrap _).append _
  all_goals try (
    rename_i ih
    intro c
    have hna := not_val_of_step ‹Step _ _ _ _›
    exact PathStep.ctx (ih c) (by simp [path, *] <;> rfl) (fun hv => by simp [path, *] <;> rfl))
  all_goals intro c
  case gotoEnter E l e K k x _ L d comp _ _ =>
    obtain ⟨init, s, hl⟩ := path_last (instantiate 0 (envOf L d) e) comp
    refine PathStep.stay (new := init) (F := (comp, .goto E K l L d comp))
      (F' := (comp, .frame E K s L d k x comp)) rfl ?_ rfl
    simp only [path, hl, wrap_snoc, List.append_assoc]; rfl
  case frameHandle hr => exact PathStep.frameGoto (path_frame (raises_path hr _)) rfl
  case frameRaise hr => exact PathStep.framePop (path_frame (raises_path hr _))
  case frameRet hv => exact PathStep.framePop (path_frame (path_val hv))
  case frameBind hv => exact PathStep.frameGoto (path_frame (path_val hv)) rfl
  case frameEffect hv => exact PathStep.frameGoto (path_frame (path_val hv)) rfl
  case frameTag hv => exact PathStep.frameGoto (path_frame (path_val hv)) rfl
  case frameYes => exact PathStep.frameGoto (path_frame (path_val rfl)) rfl
  case frameNo => exact PathStep.frameGoto (path_frame (path_val rfl)) rfl
  case frameYesBind => exact PathStep.frameGoto (path_frame (path_val rfl)) rfl
  case frameNoBind => exact PathStep.frameGoto (path_frame (path_val rfl)) rfl
  case arithV hb =>
    obtain ⟨ha, hb', -⟩ := binop_values hb
    exact PathStep.base' (by simp [path, ha, hb'])
  case arithThrow hb =>
    obtain ⟨ha, hb'⟩ := binopThrows_values hb
    exact PathStep.base' (by simp [path, ha, hb'])
  case indexField hk _ _ => exact PathStep.base' (by simp [path, propertyKey_val hk])
  case indexProto hk _ _ _ => exact PathStep.base' (by simp [path, propertyKey_val hk])
  case indexMissing hk _ _ => exact PathStep.base' (by simp [path, propertyKey_val hk])
  case makeKeyV ha hk => exact PathStep.base' (by simp [path, propertyKey_val hk, ha])
  all_goals try (
    apply PathStep.base'
    first
      | (simp [path, *]; done)
      | (simp [path, *] <;> rw [pathArgs_vals _ (by assumption)] <;> simp; done)
      | (subst_vars; simp [path, *] <;> rw [pathArgs_append _ _ (by assumption)] <;>
          simp [pathArgs, path, wrap, mapLast]; done))

/-! ### The active tag -/

theorem activeTag_wrap {c : ComponentTag} {A a : Tm} {g : Tm → Tm} (h : path c A = ReadOnly.wrap g (path c a)) :
    activeTag c A = activeTag c a := by
  simp only [activeTag, h, wrap_head]

theorem activeTag_frame {c : ComponentTag} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {u : Tm} {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} :
    activeTag c (.frame E K u L d k x comp) = activeTag comp u := by
  have hne := path_ne_nil comp u
  have hw := wrap_head (g := fun s => .frame E K s L d k x comp) (path comp u)
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil (wrap_ne_nil (g := fun s => .frame E K s L d k x comp) hne)
  simp only [activeTag, path]
  rw [hp] at hw ⊢
  rw [List.cons_append, List.head?_cons, ← hw]
  rfl

/-! ## The roots of code outside a set of components

The roots of outside code at a term whose top segment runs code tagged `c`
are `vals ofC (!ofC c) t` (`ReadOnlyRegion`): the values at the positions
of frames whose tags `ofC` does not mark. -/

section Roots
variable {ofC : ComponentTag → Bool}

/-- **An inert value**: no path step leaves it, to a location or into its
code. -/
def Inert (ofC : ComponentTag → Bool) (u : Val) : Prop := (∀ a, next u a = none) ∧ codeVals ofC u = []

theorem not_inert_of_next {u : Val} {a : Label} {l : Nat} (hn : next u a = some l) : ¬ Inert ofC u :=
  fun h => by rw [h.1 a] at hn; cases hn

theorem inert_nul : Inert ofC .nul := ⟨fun a => by cases a <;> rfl, rfl⟩

/-- A value a path step leaves is among the roots of a position of outside
code holding it. -/
theorem mem_vals_self {u : Val} (hu : ¬ Inert ofC u) : u ∈ vals ofC true u := by
  cases u
  case objAt fs cc i => rw [vals_objAt]; exact List.mem_cons_self
  case arr ls => simp [vals]
  case viewSpine f cs => simp [vals]
  all_goals exact (hu ⟨fun a => by cases a <;> rfl, rfl⟩).elim

theorem vals_makeAt {o : Bool} {cc : CallCode} {ns : List PropKey} {xs : List Tm} {u : Val}
    (hu : u ∈ valsArgs ofC o xs) : u ∈ vals ofC o (.makeAt cc ns xs) := by
  cases cc <;> simp_all [vals]

end Roots

/-! ## What a step of outside code changes and stores -/

section Steps
variable {ofC : ComponentTag → Bool}

theorem mem_valsArgs {o : Bool} {xs : List Tm} {i : Nat} {a : Tm} {u : Val} (ha : xs[i]? = some a)
    (hu : u ∈ vals ofC o a) : u ∈ valsArgs ofC o xs := by
  rw [valsArgs_eq]; exact List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, hu⟩

theorem mem_valsArgs_set {o : Bool} {xs : List Tm} {i : Nat} {a : Tm} {u : Val}
    (hu : u ∈ valsArgs ofC o (xs.set i a)) : u ∈ valsArgs ofC o xs ∨ u ∈ vals ofC o a := by
  rw [valsArgs_eq] at hu ⊢
  obtain ⟨x, hx, hux⟩ := List.mem_flatMap.mp hu
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact .inl (List.mem_flatMap.mpr ⟨x, hx, hux⟩)
  · exact .inr hux

/-- **A step of outside code changes only what its roots reach in one
step** (the draft, `OutsideStep.reach`): every old location whose contents
a step changes, the step's active frame running no code `ofC` names, is
the slot of an object or the element cell of a spine held at a position of
outside code. -/
theorem step_reach {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    ∀ c, ofC (activeTag c t) = false → ∀ {l : Nat} {v : Val}, h[l]? = some v → h'[l]? ≠ some v →
      ∃ u ∈ vals ofC (!ofC c) t, ∃ a, next u a = some l := by
  induction hs
  all_goals intro c hc l v hv hn
  all_goals try first
    | exact (hn hv).elim
    | exact (hn (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
    | exact (hn (by
        rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
  case callArg hf hr ha hpre hs ih =>
    simp only [activeTag, path, hf, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c hc hv hn
    exact ⟨u, by simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha hu), b, hb⟩
  case constructArg hf ha hpre hs ih =>
    simp only [activeTag, path, hf, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c hc hv hn
    exact ⟨u, by simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha hu), b, hb⟩
  case makeArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c hc hv hn
    exact ⟨u, vals_makeAt (mem_valsArgs ha hu), b, hb⟩
  case arrArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c hc hv hn
    exact ⟨u, by simp only [vals]; exact mem_valsArgs ha hu, b, hb⟩
  case frameC ih =>
    obtain ⟨u, hu, b, hb⟩ := ih _ (by rwa [activeTag_frame] at hc) hv hn
    exact ⟨u, by simp only [vals, List.mem_append]; exact .inr hu, b, hb⟩
  case writeField oid f fs cc l' _ w hw hf _ =>
    have hc' : ofC c = false := by simpa [activeTag, path, hw] using hc
    by_cases he : l = l'
    · subst he
      exact ⟨.objAt fs cc oid, by simp only [vals, List.mem_append]; simp only [hc', Bool.not_false]; exact .inl (mem_vals_self (ofC := ofC)
        (not_inert_of_next (a := .key f) (by simpa [next, fieldsOf] using hf))), .key f, by simpa [next, fieldsOf] using hf⟩
    · exact (hn (by rw [List.getElem?_set_ne (Ne.symm he)]; exact hv)).elim
  case setPresent ls b l' _ w hw hl _ =>
    have hc' : ofC c = false := by simpa [activeTag, path, hw] using hc
    by_cases he : l = l'
    · subst he
      simp only [elemLoc, Option.bind_eq_some_iff] at hl
      obtain ⟨k, -, o, ho, hl⟩ := hl
      cases o with
      | none => cases hl
      | some m =>
        cases hl
        have hn' : next (.arr ls) (.cell k) = some l := by simp [next, spineEntries, ho]
        exact ⟨.arr ls, by simp [vals, hc'], .cell k, hn'⟩
    · exact (hn (by rw [List.getElem?_set_ne (Ne.symm he)]; exact hv)).elim
  all_goals (
    rename_i ih
    have hna := not_val_of_step ‹Step _ _ _ _›
    obtain ⟨u, hu, b, hb⟩ := ih c (by rwa [activeTag_wrap (by simp [path, *] <;> rfl)] at hc) hv hn
    exact ⟨u, by simp [vals, hu], b, hb⟩)

theorem append_new {h xs : Heap} {w : Nat} {u : Val} (hs : ¬ ∃ v, h[w]? = some v ∧ (h ++ xs)[w]? = some v)
    (hu : (h ++ xs)[w]? = some u) : u ∈ xs := by
  by_cases hw : w < h.length
  · rw [List.getElem?_append_left hw] at hu
    exact (hs ⟨u, hu, by rw [List.getElem?_append_left hw]; exact hu⟩).elim
  · rw [List.getElem?_append_right (by omega)] at hu
    exact List.mem_of_getElem? hu

theorem set_new {h : Heap} {l w : Nat} {x u : Val} (hs : ¬ ∃ v, h[w]? = some v ∧ (h.set l x)[w]? = some v)
    (hu : (h.set l x)[w]? = some u) : u = x := by
  by_cases he : w = l
  · subst he
    rw [List.getElem?_set_self'] at hu
    cases hh : h[w]? with
    | none => rw [hh] at hu; cases hu
    | some _ => rw [hh] at hu; simp at hu; exact hu.symm
  · rw [List.getElem?_set_ne (Ne.symm he)] at hu
    exact (hs ⟨u, hu, by rw [List.getElem?_set_ne (Ne.symm he)]; exact hu⟩).elim


/-- **What a step of outside code stores is among its roots** (the draft,
`OutsideStep.writes`): every value a step whose active frame runs no code
`ofC` names leaves in a location it changes or allocates, and from which a
path step reaches a location, is held at a position of outside code: the
value written, or an initializer of the allocation. -/
theorem step_writes {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') :
    ∀ c, ofC (activeTag c t) = false → ∀ {w : Nat} {u : Val}, ¬ (∃ v, h[w]? = some v ∧ h'[w]? = some v) →
      h'[w]? = some u → ¬ Inert ofC u → u ∈ vals ofC (!ofC c) t := by
  induction hs
  all_goals intro c hc w u hsame hu hn
  all_goals try exact (hsame ⟨u, hu, hu⟩).elim
  case callArg hf hr ha hpre hs ih =>
    simp only [activeTag, path, hf, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha (ih c hc hsame hu hn))
  case constructArg hf ha hpre hs ih =>
    simp only [activeTag, path, hf, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha (ih c hc hsame hu hn))
  case makeArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    exact vals_makeAt (mem_valsArgs ha (ih c hc hsame hu hn))
  case arrArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals]; exact mem_valsArgs ha (ih c hc hsame hu hn)
  case frameC ih =>
    simp only [vals, List.mem_append]
    exact .inr (ih _ (by rwa [activeTag_frame] at hc) hsame hu hn)
  case makeFields hvs _ =>
    simp only [activeTag, path] at hc
    rw [pathArgs_vals _ hvs] at hc
    rw [List.append_assoc] at hsame hu
    have hc' : ofC c = false := by simpa using hc
    rcases List.mem_append.mp (append_new hsame hu) with hm | hm
    · exact vals_makeAt (by
        rw [valsArgs_eq, hc', Bool.not_false]; exact List.mem_flatMap.mpr ⟨u, hm, mem_vals_self hn⟩)
    · simp only [List.mem_singleton] at hm; subst hm; exact (hn inert_nul).elim
  case arrAlloc hvs _ =>
    simp only [activeTag, path] at hc
    rw [pathArgs_vals _ hvs] at hc
    have hc' : ofC c = false := by simpa using hc
    have hm := append_new hsame hu
    simp only [vals]; rw [valsArgs_eq, hc', Bool.not_false]; exact List.mem_flatMap.mpr ⟨u, hm, mem_vals_self hn⟩
  case writeField hw _ _ =>
    have hc' : ofC c = false := by simpa [activeTag, path, hw] using hc
    have := set_new hsame hu; subst this
    simp only [vals, List.mem_append]; simp only [hc', Bool.not_false]; exact .inr (mem_vals_self hn)
  case setPresent hw _ _ =>
    have hc' : ofC c = false := by simpa [activeTag, path, hw] using hc
    have := set_new hsame hu; subst this
    simp only [vals, List.mem_append]; simp only [hc', Bool.not_false]; exact .inr (mem_vals_self hn)
  case setGrow hw _ _ =>
    have hc' : ofC c = false := by simpa [activeTag, path, hw] using hc
    have hm := append_new hsame hu
    simp only [List.mem_singleton] at hm; subst hm
    simp only [vals, List.mem_append]; simp only [hc', Bool.not_false]; exact .inr (mem_vals_self hn)
  all_goals try (
    have hm := append_new hsame hu
    simp only [List.mem_singleton] at hm; subst hm; exact (hn inert_nul).elim)
  all_goals (
    rename_i ih
    have hna := not_val_of_step ‹Step _ _ _ _›
    have hu' := ih c (by rwa [activeTag_wrap (by simp [path, *] <;> rfl)] at hc) hsame hu hn
    simp [vals, hu'])

end Steps

/-! ## At a component of a family -/

/-- **`OutsideStep.reach` of a step of the calculus** at the component `C`:
a step whose active frame runs no code of `C` changes only locations one
path step from the roots of outside code. -/
theorem outsideStep_reach {F : Family} {C : Nat} {st st' : St (F.at C)} {c : ComponentTag} {t t' : Tm}
    (hs : Step st.s.h t st'.s.h t') (hact : ¬ F.Runs (activeTag c t) C) (hc : ¬ F.Runs c C)
    (hroots : st.roots = vals (F.ofC C) true t) :
    ∀ l, Changes st st' l → ReachesFrom (F.at C).ofC st.s.h st.roots l := by
  rintro l ⟨v, hv, hn⟩
  obtain ⟨u, hu, a, ha⟩ := step_reach (ofC := F.ofC C) hs c (by simp [Family.ofC, hact]) hv hn
  simp only [Family.ofC, hc, decide_false, Bool.not_false] at hu
  exact ⟨u, hroots ▸ hu, [a], ha⟩

/-- **`OutsideStep.writes` of a step of the calculus** at the component
`C`: what a step whose active frame runs no code of `C` leaves in storage
it changes or allocates references, in one path step, only what the roots
of outside code reach in one. -/
theorem outsideStep_writes {F : Family} {C : Nat} {st st' : St (F.at C)} {c : ComponentTag} {t t' : Tm}
    (hs : Step st.s.h t st'.s.h t') (hact : ¬ F.Runs (activeTag c t) C) (hc : ¬ F.Runs c C)
    (hroots : st.roots = vals (F.ofC C) true t) :
    ∀ (w : Nat) (u : Val), ¬ (∃ v : Val, st.s.h[w]? = some v ∧ st'.s.h[w]? = some v) → st'.s.h[w]? = some u →
      ∀ (a : Label) (l : Nat), next u a = some l →
        ReachesFrom (F.at C).ofC st.s.h st.roots l ∨ st.s.h.length ≤ l := by
  intro _ u hsame hu a _ hn
  have hm := step_writes (ofC := F.ofC C) hs c (by simp [Family.ofC, hact]) hsame hu (not_inert_of_next hn)
  simp only [Family.ofC, hc, decide_false, Bool.not_false] at hm
  exact .inl ⟨u, hroots ▸ hm, [a], hn⟩

/-- **The roots of a valid term are valid** (`RootsValid`). -/
theorem rootsValid_of_term {P : Package} {st : St P} {o : Bool} {t : Tm}
    (hroots : st.roots = vals P.ofC o t) (ht : RefsOk st.s.W t) : RootsValid st := by
  intro u hu
  rw [hroots] at hu
  exact vals_refsOkN (RefsOk.refsOkN ht) hu

end Verification.TolerantFrames.ReadOnly
