import Verification.Semantics.Reach.Values

/-! # What a step reaches and writes

A step of the calculus forges no reference (`step_noForge`): every value
the next term holds was held by the term or reachable from it, or is a
fresh allocation. The locations a step writes are reached from the term
(`step_writes`, `step_reach`). -/

namespace Verification.TolerantFrames.Reach

open Verification Footprints

variable {P : Package}

theorem follows_cons {ofC : ComponentTag → Bool} {h : Heap} {v v₀ : Val} {a : Label} {π : List Label} {l : Nat}
    (hs : Succ ofC h v a v₀) (hf : Follows ofC h v₀ π l) : Follows ofC h v (a :: π) l := by
  cases π with
  | nil => exact hf.elim
  | cons b π => exact ⟨v₀, hs, hf⟩

end Verification.TolerantFrames.Reach

namespace Verification.TolerantFrames.Reach

open Verification Footprints

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
value, in their order; into a frame's running term (`frameC`). A `goto` is
a frame not yet entered. A frame's entry carries its owner (`Realm.own`):
its tag, or for a frame of the realm's code the owner of the frame that
called it where that frame is suspended at a native-call key (`nk`, read by
`rl.native` at the caller's code, tag and node key), the client `none`
otherwise. -/
def path (rl : Realm) (c : ComponentTag) (nk : Bool) : Tm → List (ComponentTag × Tm)
  | .invoke f r args =>
    if isVal f = false then wrap (fun s => .invoke s r args) (path rl c nk f)
    else if isVal r = false then wrap (fun s => .invoke f s args) (path rl c nk r)
    else pathArgs rl c nk (.invoke f r) args
  | .construct f args =>
    if isVal f = false then wrap (fun s => .construct s args) (path rl c nk f)
    else pathArgs rl c nk (.construct f) args
  | .letE a b => if isVal a = false then wrap (fun s => .letE s b) (path rl c nk a) else [(c, .letE a b)]
  | .makeAt cc ns xs => pathArgs rl c nk (.makeAt cc ns) xs
  | .readAt f a => if isVal a = false then wrap (.readAt f) (path rl c nk a) else [(c, .readAt f a)]
  | .indexAt a key =>
    if isVal a = false then wrap (fun s => .indexAt s key) (path rl c nk a)
    else if isVal key = false then wrap (.indexAt a) (path rl c nk key) else [(c, .indexAt a key)]
  | .writeAt f a b =>
    if isVal a = false then wrap (fun s => .writeAt f s b) (path rl c nk a)
    else if isVal b = false then wrap (.writeAt f a) (path rl c nk b) else [(c, .writeAt f a b)]
  | .test k a => if isVal a = false then wrap (.test k) (path rl c nk a) else [(c, .test k a)]
  | .ite x a b => if isVal x = false then wrap (fun s => .ite s a b) (path rl c nk x) else [(c, .ite x a b)]
  | .arith op a b =>
    if isVal a = false then wrap (fun s => .arith op s b) (path rl c nk a)
    else if isVal b = false then wrap (.arith op a) (path rl c nk b) else [(c, .arith op a b)]
  | .arrLit xs => pathArgs rl c nk .arrLit xs
  | .elemAt a i =>
    if isVal a = false then wrap (fun s => .elemAt s i) (path rl c nk a)
    else if isVal i = false then wrap (.elemAt a) (path rl c nk i) else [(c, .elemAt a i)]
  | .setElem a i v =>
    if isVal a = false then wrap (fun s => .setElem s i v) (path rl c nk a)
    else if isVal i = false then wrap (fun s => .setElem a s v) (path rl c nk i)
    else if isVal v = false then wrap (.setElem a i) (path rl c nk v) else [(c, .setElem a i v)]
  | .lenOf a => if isVal a = false then wrap .lenOf (path rl c nk a) else [(c, .lenOf a)]
  | .spread a => if isVal a = false then wrap .spread (path rl c nk a) else [(c, .spread a)]
  | .throw a => if isVal a = false then wrap .throw (path rl c nk a) else [(c, .throw a)]
  | .merge d a b =>
    if isVal a = false then wrap (fun s => .merge d s b) (path rl c nk a)
    else if isVal b = false then wrap (.merge d a) (path rl c nk b) else [(c, .merge d a b)]
  | .makeKey k a =>
    if isVal k = false then wrap (fun s => .makeKey s a) (path rl c nk k)
    else if isVal a = false then wrap (.makeKey k) (path rl c nk a) else [(c, .makeKey k a)]
  | .goto E K l L d comp => [(rl.own c nk comp, .goto E K l L d comp), (c, hole)]
  | .frame E K t L d k x comp =>
    wrap (fun s => .frame E K s L d k x comp) (path rl (rl.own c nk comp) (rl.native ((E, K), comp) (k, x)) t) ++ [(c, hole)]
  | t => [(c, t)]
termination_by structural t => t

/-- The path through a list of terms evaluated left to right, `k` rebuilding
the term from the list. -/
def pathArgs (rl : Realm) (c : ComponentTag) (nk : Bool) (k : List Tm → Tm) : List Tm → List (ComponentTag × Tm)
  | [] => [(c, k [])]
  | a :: as =>
    if isVal a = false then wrap (fun s => k (s :: as)) (path rl c nk a)
    else pathArgs rl c nk (fun xs => k (a :: xs)) as
termination_by structural xs => xs
end

/-- **The active tag**: the owner of the innermost frame on the path, or the
top segment's tag when no frame is on it. -/
def activeTag (rl : Realm) (c : ComponentTag) (nk : Bool) (t : Tm) : ComponentTag :=
  ((path rl c nk t).head?.map Prod.fst).getD c

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

theorem wrap_ex {g : Tm → Tm} {c : ComponentTag} {P : List (ComponentTag × Tm)}
    (h : ∃ init s, P = init ++ [(c, s)]) : ∃ init s, wrap g P = init ++ [(c, s)] := by
  obtain ⟨init, s, rfl⟩ := h
  exact ⟨init, g s, wrap_snoc⟩

theorem pathArgs_ex {c : ComponentTag} :
    ∀ {xs : List Tm}, (∀ a ∈ xs, ∀ c nk, ∃ init s, path rl c nk a = init ++ [(c, s)]) →
      ∀ k, ∃ init s, pathArgs rl c nk k xs = init ++ [(c, s)]
  | [], _, k => ⟨[], k [], rfl⟩
  | a :: as, h, k => by
    simp only [pathArgs]
    split
    · exact wrap_ex (h a List.mem_cons_self c nk)
    · exact pathArgs_ex (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

/-- **The path ends at the top segment**, tagged with the code that runs
it. -/
theorem path_last (t : Tm) : ∀ c nk, ∃ init s, path rl c nk t = init ++ [(c, s)] := by
  induction t using Tm.induct
  all_goals intro c nk
  all_goals simp only [path]
  all_goals repeat' split
  all_goals first
    | exact ⟨[], _, rfl⟩
    | exact ⟨_, _, rfl⟩
    | exact ⟨[_], _, rfl⟩
    | (apply wrap_ex; solve_by_elim)
    | (apply pathArgs_ex; assumption)

theorem path_ne_nil (c : ComponentTag) (t : Tm) : path rl c nk t ≠ [] := by
  obtain ⟨init, s, h⟩ := path_last t c nk
  rw [h]; simp

/-- A value's path is its top segment alone. -/
theorem path_val {c : ComponentTag} {v : Tm} (hv : isVal v = true) : path rl c nk v = [(c, v)] := by
  cases v <;> simp_all [isVal, path]

theorem pathArgs_vals {c : ComponentTag} :
    ∀ {xs : List Tm} (k : List Tm → Tm), (∀ a ∈ xs, isVal a = true) → pathArgs rl c nk k xs = [(c, k xs)]
  | [], _, _ => rfl
  | a :: as, k, h => by
    simp only [pathArgs, h a List.mem_cons_self]
    exact pathArgs_vals (fun xs => k (a :: xs)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem pathArgs_append {c : ComponentTag} :
    ∀ {pre : List Tm} (xs : List Tm) (k : List Tm → Tm), (∀ a ∈ pre, isVal a = true) →
      pathArgs rl c nk k (pre ++ xs) = pathArgs rl c nk (fun ys => k (pre ++ ys)) xs
  | [], _, _, _ => rfl
  | a :: as, xs, k, h => by
    simp only [List.cons_append, pathArgs, h a List.mem_cons_self]
    exact pathArgs_append xs (fun ys => k (a :: ys)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The path through a list at its first term that is not a value. -/
theorem pathArgs_at {c : ComponentTag} :
    ∀ {xs : List Tm} {i : Nat} {a : Tm} (k : List Tm → Tm), xs[i]? = some a →
      (∀ j, j < i → ∀ w, xs[j]? = some w → isVal w = true) → isVal a = false →
      pathArgs rl c nk k xs = wrap (fun s => k (xs.set i s)) (path rl c nk a)
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

theorem set_self {xs : List Tm} {i : Nat} {a : Tm} (h : xs[i]? = some a) : xs.set i a = xs := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · subst_vars
    obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
    simp [hl, he]
  · rfl

theorem raises_path {t v : Tm} (hr : Raises t v) : ∀ c nk, path rl c nk t = [(c, t)] := by
  induction hr with
  | throwV hv _ => intro c nk; simp [path, hv]
  | callArg hf hr' ha hpre _ ih =>
    intro c nk
    have hna := raises_not_val ‹Raises _ _›
    simp only [path, hf, hr']
    rw [pathArgs_at _ ha hpre hna, ih c nk]; simp [wrap, mapLast, set_self ha]
  | constructArg hf ha hpre _ ih =>
    intro c nk
    have hna := raises_not_val ‹Raises _ _›
    simp only [path, hf]
    rw [pathArgs_at _ ha hpre hna, ih c nk]; simp [wrap, mapLast, set_self ha]
  | makeArg ha hpre _ ih =>
    intro c nk
    have hna := raises_not_val ‹Raises _ _›
    simp only [path]
    rw [pathArgs_at _ ha hpre hna, ih c nk]; simp [wrap, mapLast, set_self ha]
  | arrArg ha hpre _ ih =>
    intro c nk
    have hna := raises_not_val ‹Raises _ _›
    simp only [path]
    rw [pathArgs_at _ ha hpre hna, ih c nk]; simp [wrap, mapLast, set_self ha]
  | _ =>
    rename_i ih
    intro c nk
    have hna := raises_not_val ‹Raises _ _›
    simp [path, ih c nk, wrap, mapLast, *]

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
    (hu : path rl (rl.own c nk comp) (rl.native ((E, K), comp) (k, x)) u = [(rl.own c nk comp, u)]) :
    path rl c nk (.frame E K u L d k x comp) = [(rl.own c nk comp, .frame E K u L d k x comp), (c, hole)] := by
  simp [path, hu, wrap, mapLast]

theorem activeTag_wrap {c : ComponentTag} {A a : Tm} {g : Tm → Tm} (h : path rl c nk A = Reach.wrap g (path rl c nk a)) :
    activeTag rl c nk A = activeTag rl c nk a := by
  simp only [activeTag, h, wrap_head]

theorem activeTag_frame {c : ComponentTag} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {u : Tm} {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} {comp : ComponentTag} :
    activeTag rl c nk (.frame E K u L d k x comp) =
      activeTag rl (rl.own c nk comp) (rl.native ((E, K), comp) (k, x)) u := by
  have hne := path_ne_nil (rl := rl) (nk := rl.native ((E, K), comp) (k, x)) (rl.own c nk comp) u
  have hw := wrap_head (g := fun s => .frame E K s L d k x comp)
    (path rl (rl.own c nk comp) (rl.native ((E, K), comp) (k, x)) u)
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil (wrap_ne_nil (g := fun s => .frame E K s L d k x comp) hne)
  simp only [activeTag, path]
  rw [hp] at hw ⊢
  rw [List.cons_append, List.head?_cons, ← hw]
  rfl

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
theorem mem_vals_self {u : Val} (hu : ¬ Inert ofC u) : u ∈ vals ofC rl true nk u := by
  cases u
  case objAt fs cc i => rw [vals_objAt]; exact List.mem_cons_self
  case arr ls => simp [vals]
  case viewSpine f cs => simp [vals]
  all_goals exact (hu ⟨fun a => by cases a <;> rfl, rfl⟩).elim

theorem vals_makeAt {o : Bool} {cc : CallCode} {ns : List PropKey} {xs : List Tm} {u : Val}
    (hu : u ∈ valsArgs ofC rl o nk xs) : u ∈ vals ofC rl o nk (.makeAt cc ns xs) := by
  cases cc <;> simp_all [vals]

end Roots

section Steps

variable {ofC : ComponentTag → Bool}

theorem mem_valsArgs {o : Bool} {xs : List Tm} {i : Nat} {a : Tm} {u : Val} (ha : xs[i]? = some a)
    (hu : u ∈ vals ofC rl o nk a) : u ∈ valsArgs ofC rl o nk xs := by
  rw [valsArgs_eq]; exact List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, hu⟩

theorem mem_valsArgs_of {o : Bool} {xs : List Tm} {a : Tm} {u : Val} (ha : a ∈ xs) (hu : u ∈ vals ofC rl o nk a) :
    u ∈ valsArgs ofC rl o nk xs := by
  rw [valsArgs_eq]; exact List.mem_flatMap.mpr ⟨a, ha, hu⟩

theorem mem_valsArgs_set {o : Bool} {xs : List Tm} {i : Nat} {a : Tm} {u : Val}
    (hu : u ∈ valsArgs ofC rl o nk (xs.set i a)) : u ∈ valsArgs ofC rl o nk xs ∨ u ∈ vals ofC rl o nk a := by
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
    ∀ c nk, ofC (activeTag rl c nk t) = false → ∀ {l : Nat} {v : Val}, h[l]? = some v → h'[l]? ≠ some v →
      ∃ u ∈ vals ofC rl (!ofC c) nk t, ∃ a, next u a = some l := by
  induction hs
  all_goals intro c nk hc l v hv hn
  all_goals try first
    | exact (hn hv).elim
    | exact (hn (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
    | exact (hn (by
        rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv)).elim
  case callArg hf hr ha hpre hs ih =>
    simp only [activeTag, path, hf, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c nk hc hv hn
    exact ⟨u, by simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha hu), b, hb⟩
  case constructArg hf ha hpre hs ih =>
    simp only [activeTag, path, hf, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c nk hc hv hn
    exact ⟨u, by simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha hu), b, hb⟩
  case makeArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c nk hc hv hn
    exact ⟨u, vals_makeAt (mem_valsArgs ha hu), b, hb⟩
  case arrArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    obtain ⟨u, hu, b, hb⟩ := ih c nk hc hv hn
    exact ⟨u, by simp only [vals]; exact mem_valsArgs ha hu, b, hb⟩
  case frameC ih =>
    obtain ⟨u, hu, b, hb⟩ := ih _ _ (by rwa [activeTag_frame] at hc) hv hn
    exact ⟨u, by simp only [vals, List.mem_append, Realm.flag_own rl ofC rfl]; exact .inr hu, b, hb⟩
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
    obtain ⟨u, hu, b, hb⟩ := ih c nk (by rwa [activeTag_wrap (by simp [path, *] <;> rfl)] at hc) hv hn
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
    ∀ c nk, ofC (activeTag rl c nk t) = false → ∀ {w : Nat} {u : Val}, ¬ (∃ v, h[w]? = some v ∧ h'[w]? = some v) →
      h'[w]? = some u → ¬ Inert ofC u → u ∈ vals ofC rl (!ofC c) nk t := by
  induction hs
  all_goals intro c nk hc w u hsame hu hn
  all_goals try exact (hsame ⟨u, hu, hu⟩).elim
  case callArg hf hr ha hpre hs ih =>
    simp only [activeTag, path, hf, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha (ih c nk hc hsame hu hn))
  case constructArg hf ha hpre hs ih =>
    simp only [activeTag, path, hf, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha (ih c nk hc hsame hu hn))
  case makeArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    exact vals_makeAt (mem_valsArgs ha (ih c nk hc hsame hu hn))
  case arrArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals]; exact mem_valsArgs ha (ih c nk hc hsame hu hn)
  case frameC ih =>
    simp only [vals, List.mem_append, Realm.flag_own rl ofC rfl]
    exact .inr (ih _ _ (by rwa [activeTag_frame] at hc) hsame hu hn)
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
    have hu' := ih c nk (by rwa [activeTag_wrap (by simp [path, *] <;> rfl)] at hc) hsame hu hn
    simp [vals, hu'])

end Steps

section NoForge

variable {ofC : ComponentTag → Bool}

/-- **A location the roots `R` reach at `h`, or a fresh one.** -/
def Good (ofC : ComponentTag → Bool) (h : Heap) (R : List Val) (l : Nat) : Prop :=
  ReachesFrom ofC h R l ∨ h.length ≤ l

/-- **A value whose path steps reach only good locations**: every location
one location step reaches from it, or from a value its code holds, is
reached by the roots or fresh. -/
def GV (ofC : ComponentTag → Bool) (h : Heap) (R : List Val) (v : Val) : Prop :=
  ∀ w, CodeReach ofC v w → ∀ a l, next w a = some l → Good ofC h R l

variable {h : Heap} {R : List Val}

theorem GV.of {v : Val} (hn : ∀ a l, next v a = some l → Good ofC h R l)
    (hc : ∀ x ∈ codeVals ofC v, GV ofC h R x) : GV ofC h R v := by
  intro w hw
  cases hw with
  | refl => exact hn
  | step hx hxw => exact hc _ hx _ hxw

theorem GV.code {v x : Val} (hv : GV ofC h R v) (hx : x ∈ codeVals ofC v) : GV ofC h R x :=
  fun w hw => hv w (.step hx hw)

theorem GV.next {v : Val} {a : Label} {l : Nat} (hv : GV ofC h R v) (hn : next v a = some l) :
    Good ofC h R l :=
  hv v (.refl v) a l hn

theorem GV.inert {u : Val} (hu : Inert ofC u) : GV ofC h R u := by
  intro w hw
  cases hw with
  | refl => intro a l hn; rw [hu.1 a] at hn; cases hn
  | step hx _ => rw [hu.2] at hx; cases hx

/-- Two objects with the same fields and descriptor take the same location
steps. -/
theorem GV.same_next {v v' : Val} (hv : GV ofC h R v) (hn : ∀ a, Reach.next v' a = Reach.next v a)
    (hc : ∀ x ∈ codeVals ofC v', GV ofC h R x) : GV ofC h R v' :=
  GV.of (fun a l h' => hv.next (by rw [← hn a]; exact h')) hc

theorem follows_trans {h : Heap} : ∀ {r : Val} {π π' : List Label} {v : Val} {l' l₀ : Nat},
    Follows ofC h r π l₀ → h[l₀]? = some v → Follows ofC h v π' l' → Follows ofC h r (π ++ π') l'
  | _, [], _, _, _, _, hf, _, _ => hf.elim
  | _, [_], _, _, _, _, hf, hl, hf' => follows_cons (.inl ⟨_, hf, hl⟩) hf'
  | _, _ :: _ :: _, _, _, _, _, ⟨_, hs, hf⟩, hl, hf' => follows_cons hs (follows_trans hf hl hf')

/-- **A root's paths reach only what the roots reach.** -/
theorem GV.root {v : Val} (hv : v ∈ R) : GV ofC h R v :=
  fun _ hw _ _ hn => .inl ⟨v, hv, codeReach_reaches hw hn⟩

/-- **The contents of a good location**: its paths extend the roots'. -/
theorem GV.heap {l : Nat} {v : Val} (hg : Good ofC h R l) (hl : h[l]? = some v) : GV ofC h R v := by
  intro w hw a l' hn
  rcases hg with ⟨r, hr, π, hf⟩ | hfresh
  · obtain ⟨π', hf'⟩ := codeReach_reaches (h := h) hw hn
    exact .inl ⟨r, hr, _, follows_trans hf hl hf'⟩
  · rw [List.getElem?_eq_none hfresh] at hl; cases hl

/-- **Paths after a step reach only good locations** where every value
outside code holds after it is good and every location a good location's
new contents reach is good. -/
theorem follows_good {h' : Heap} (hheap : ∀ l u, Good ofC h R l → h'[l]? = some u → GV ofC h R u) :
    ∀ {v : Val} {π : List Label} {l : Nat}, GV ofC h R v → Follows ofC h' v π l → Good ofC h R l
  | _, [], _, _, hf => hf.elim
  | _, [_], _, hv, hf => hv.next hf
  | _, _ :: _ :: _, _, hv, ⟨_, .inl ⟨_, hn, hl⟩, hf⟩ => follows_good hheap (hheap _ _ (hv.next hn) hl) hf
  | _, _ :: _ :: _, _, hv, ⟨_, .inr ⟨_, _, hc⟩, hf⟩ => follows_good hheap (hv.code (List.mem_of_getElem? hc)) hf

theorem vals_mono : ∀ (t : Tm) {rl : Realm} {nk : Bool} {x : Val}, x ∈ vals ofC rl false nk t → x ∈ vals ofC rl true nk t := by
  intro t
  induction t using Tm.induct
  case frame E K u L d k xx comp _ ihu _ _ =>
    intro rl nk x hx
    simp only [vals, List.mem_append] at hx ⊢
    unfold Realm.flag at hx ⊢
    by_cases ht : rl.tags comp = true
    · cases nk
      · simpa [ht] using hx
      · simp only [ht, ↓reduceIte, Bool.false_eq_true, List.not_mem_nil, false_or] at hx
        simp only [ht, ↓reduceIte]
        exact .inr (ihu hx)
    · simpa [ht] using hx
  case goto E K l L d comp _ _ _ =>
    intro rl nk x hx
    simp only [vals] at hx ⊢
    unfold Realm.flag at hx ⊢
    by_cases ht : rl.tags comp = true
    · cases nk
      · simpa [ht] using hx
      · simp [ht] at hx
    · simpa [ht] using hx
  all_goals intro rl nk x hx
  all_goals simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap, Bool.false_eq_true,
    ↓reduceIte, List.not_mem_nil, Bool.false_and] at hx ⊢
  all_goals grind

theorem objAt_next_eq {fs : List (PropKey × Nat)} {i : Nat} {cc cc' : CallCode}
    (h : HeapKnowledge.descriptorSpine (.objAt fs cc i) = HeapKnowledge.descriptorSpine (.objAt fs cc' i)) :
    ∀ a, Reach.next (.objAt fs cc' i) a = Reach.next (.objAt fs cc i) a := by
  intro a; cases a <;> simp_all [Reach.next, fieldsOf, spineEntries]

/-- **Substitution keeps the values good**: the values of `subst j a b` are
`a`'s, or `b`'s with the same location steps and good code. -/
theorem subst_cover {a : Tm} (ha : ∀ x ∈ vals ofC Realm.all true true a, GV ofC h R x) :
    ∀ (b : Tm) (j : Nat) (rl : Realm) (o nk : Bool), (∀ x ∈ vals ofC rl o nk b, GV ofC h R x) →
      ∀ x ∈ vals ofC rl o nk (subst j a b), GV ofC h R x := by
  intro b
  induction b using Tm.induct
  case var i =>
    intro j rl o nk _ x hx
    simp only [subst] at hx
    split at hx
    · exact ha x (vals_all ofC a rl o nk hx)
    · split at hx <;> simp [vals] at hx
  case objBound fs oid t r pre iht ihr ihp =>
    intro j rl o nk hb x hx
    cases o
    · simp [subst, vals] at hx
    · have hself := hb _ (by rw [vals_objAt]; exact List.mem_cons_self)
      have hpart : ∀ y ∈ codeVals ofC (.objAt fs (.bound t r pre) oid), GV ofC h R y :=
        fun y hy => hb y (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hy)
      simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap] at hpart
      have hcode : ∀ y ∈ codeVals ofC (.objAt fs (.bound (subst j a t) (subst j a r) (substArgs j a pre)) oid),
          GV ofC h R y := by
        intro y hy
        simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap, substArgs_eq_map, List.mem_map] at hy
        rcases hy with (hy | hy) | ⟨_, ⟨p, hp, rfl⟩, hy⟩
        · exact iht j Realm.all true true (fun z hz => hpart z (.inl (.inl hz))) y hy
        · exact ihr j Realm.all true true (fun z hz => hpart z (.inl (.inr hz))) y hy
        · exact ihp p hp j Realm.all true true (fun z hz => hpart z (.inr ⟨p, hp, hz⟩)) y hy
      simp only [subst] at hx
      rw [vals_objAt] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hself.same_next (objAt_next_eq rfl) hcode
      · exact hcode x hx
  case objGraph fs oid n E K st caps k r comp ihE ihc =>
    intro j rl o nk hb x hx
    cases o
    · simp [subst, vals] at hx
    · have hself := hb _ (by rw [vals_objAt]; exact List.mem_cons_self)
      have hpart : ∀ y ∈ codeVals ofC (.objAt fs (.graph n E K st caps k r comp) oid), GV ofC h R y :=
        fun y hy => hb y (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hy)
      have hcode : ∀ y ∈ codeVals ofC (.objAt fs (.graph n E K st (substArgs j a caps) k r comp) oid),
          GV ofC h R y := by
        intro y hy
        simp only [codeVals] at hy hpart
        split at hy
        · cases hy
        · rename_i hcomp
          simp only [hcomp, Bool.false_eq_true, ↓reduceIte, List.mem_append, valsArgs_eq, List.mem_flatMap,
            substArgs_eq_map, List.mem_map] at hy hpart
          rcases hy with ⟨e, he, hy⟩ | ⟨_, ⟨p, hp, rfl⟩, hy⟩
          · exact hpart y (.inl ⟨e, he, hy⟩)
          · exact ihc p hp j Realm.all true true (fun z hz => hpart z (.inr ⟨p, hp, hz⟩)) y hy
      simp only [subst] at hx
      rw [vals_objAt] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hself.same_next (objAt_next_eq rfl) hcode
      · exact hcode x hx
  all_goals intro j rl o nk hb x hx
  all_goals simp only [subst, vals, valsArgs_eq, substArgs_eq_map, List.mem_append, List.mem_flatMap,
    List.mem_map] at hx hb
  all_goals (repeat' split at hx) <;> (repeat' split at hb) <;> grind

/-- **Instantiation keeps the values good**: the values of
`instantiate j ρ b` are the environment's, or `b`'s with the same location
steps and good code. -/
theorem instantiate_cover {ρ : Env} (ha : ∀ i, ∀ x ∈ vals ofC Realm.all true true (ρ i), GV ofC h R x) :
    ∀ (b : Tm) (j : Nat) (rl : Realm) (o nk : Bool), (∀ x ∈ vals ofC rl o nk b, GV ofC h R x) →
      ∀ x ∈ vals ofC rl o nk (instantiate j ρ b), GV ofC h R x := by
  intro b
  induction b using Tm.induct
  case var i =>
    intro j rl o nk _ x hx
    simp only [instantiate] at hx
    split at hx
    · simp [vals] at hx
    · exact ha _ x (vals_all ofC _ rl o nk hx)
  case objBound fs oid t r pre iht ihr ihp =>
    intro j rl o nk hb x hx
    cases o
    · simp [instantiate, vals] at hx
    · have hself := hb _ (by rw [vals_objAt]; exact List.mem_cons_self)
      have hpart : ∀ y ∈ codeVals ofC (.objAt fs (.bound t r pre) oid), GV ofC h R y :=
        fun y hy => hb y (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hy)
      simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap] at hpart
      have hcode : ∀ y ∈ codeVals ofC (.objAt fs (.bound (instantiate j ρ t) (instantiate j ρ r) (instantiateArgs j ρ pre)) oid),
          GV ofC h R y := by
        intro y hy
        simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap, instantiateArgs_eq_map, List.mem_map] at hy
        rcases hy with (hy | hy) | ⟨_, ⟨p, hp, rfl⟩, hy⟩
        · exact iht j Realm.all true true (fun z hz => hpart z (.inl (.inl hz))) y hy
        · exact ihr j Realm.all true true (fun z hz => hpart z (.inl (.inr hz))) y hy
        · exact ihp p hp j Realm.all true true (fun z hz => hpart z (.inr ⟨p, hp, hz⟩)) y hy
      simp only [instantiate] at hx
      rw [vals_objAt] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hself.same_next (objAt_next_eq rfl) hcode
      · exact hcode x hx
  case objGraph fs oid n E K st caps k r comp ihE ihc =>
    intro j rl o nk hb x hx
    cases o
    · simp [instantiate, vals] at hx
    · have hself := hb _ (by rw [vals_objAt]; exact List.mem_cons_self)
      have hpart : ∀ y ∈ codeVals ofC (.objAt fs (.graph n E K st caps k r comp) oid), GV ofC h R y :=
        fun y hy => hb y (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hy)
      have hcode : ∀ y ∈ codeVals ofC (.objAt fs (.graph n E K st (instantiateArgs j ρ caps) k r comp) oid),
          GV ofC h R y := by
        intro y hy
        simp only [codeVals] at hy hpart
        split at hy
        · cases hy
        · rename_i hcomp
          simp only [hcomp, Bool.false_eq_true, ↓reduceIte, List.mem_append, valsArgs_eq, List.mem_flatMap,
            instantiateArgs_eq_map, List.mem_map] at hy hpart
          rcases hy with ⟨e, he, hy⟩ | ⟨_, ⟨p, hp, rfl⟩, hy⟩
          · exact hpart y (.inl ⟨e, he, hy⟩)
          · exact ihc p hp j Realm.all true true (fun z hz => hpart z (.inr ⟨p, hp, hz⟩)) y hy
      simp only [instantiate] at hx
      rw [vals_objAt] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hself.same_next (objAt_next_eq rfl) hcode
      · exact hcode x hx
  all_goals intro j rl o nk hb x hx
  all_goals simp only [instantiate, vals, valsArgs_eq, instantiateArgs_eq_map, List.mem_append, List.mem_flatMap,
    List.mem_map] at hx hb
  all_goals (repeat' split at hx) <;> (repeat' split at hb) <;> grind

theorem CodeReach.trans {v x w : Val} (h₁ : CodeReach ofC v x) (h₂ : CodeReach ofC x w) : CodeReach ofC v w := by
  induction h₁ with
  | refl => exact h₂
  | step hx _ ih => exact .step hx (ih h₂)

theorem GV.reach {v x : Val} (hv : GV ofC h R v) (hx : CodeReach ofC v x) : GV ofC h R x :=
  fun w hw => hv w (hx.trans hw)

/-- The values a value holds at a position of outside code are the values
its code steps reach. -/
theorem vals_codeReach {v x : Val} {o : Bool} (hv : isVal v = true) (hx : x ∈ vals ofC rl o nk v) : CodeReach ofC v x := by
  cases v
  case objAt fs cc i =>
    cases o
    · cases cc <;> simp [vals] at hx
    · rw [vals_objAt] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .refl _
      · exact .step hx (.refl _)
  case arr ls => cases o <;> simp [vals] at hx; subst hx; exact .refl _
  case viewSpine f cs => cases o <;> simp [vals] at hx; subst hx; exact .refl _
  all_goals simp [isVal, vals] at hv hx

/-- **A good value holds only good values.** -/
theorem GV.held {v x : Val} {o : Bool} (hv : GV ofC h R v) (hval : isVal v = true) (hx : x ∈ vals ofC rl o nk v) :
    GV ofC h R x :=
  hv.reach (vals_codeReach hval hx)

/-- The contents of a good location, at a heap holding values, hold only
good values. -/
theorem GV.heapHeld {l : Nat} {v x : Val} {o : Bool} (hh : ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true)
    (hg : Good ofC h R l) (hl : h[l]? = some v) (hx : x ∈ vals ofC rl o nk v) : GV ofC h R x :=
  (GV.heap hg hl).held (hh _ _ hl) hx

theorem GV.ofHeapVal {l : Nat} {x : Val} {o : Bool} (hg : Good ofC h R l) (hx : x ∈ vals ofC rl o nk (heapVal h l)) :
    GV ofC h R x := by
  unfold Verification.heapVal at hx
  split at hx
  · split at hx
    · exact (GV.heap hg ‹_›).held ‹_› hx
    · simp [vals] at hx
  · simp [vals] at hx

/-- A value with no reference holds only inert values. -/
theorem noRefs_cover {v x : Val} {o : Bool} (hv : isVal v = true) (hr : refs v = []) (hx : x ∈ vals ofC rl o nk v) :
    GV ofC h R x := by
  cases v
  case objAt fs cc i => cases cc <;> simp [refs, objRefs] at hr
  case arr ls =>
    cases o <;> simp [vals] at hx
    subst hx
    refine GV.inert ⟨fun a => ?_, rfl⟩
    cases a
    case cell i =>
      simp only [Reach.next, spineEntries]
      cases hi : ls[i]? with
      | none => rfl
      | some o =>
        cases o with
        | none => rfl
        | some m =>
          have : Ref.elem m ∈ refs (.arr ls) := by
            simp only [refs, spineRefs, List.mem_filterMap]; exact ⟨some m, List.mem_of_getElem? hi, rfl⟩
          rw [hr] at this; cases this
    all_goals rfl
  case viewSpine f cs =>
    cases o <;> simp [vals] at hx
    subst hx
    have hcs : cs = [] := by simpa [refs] using hr
    subst hcs
    exact GV.inert ⟨fun a => by cases a <;> simp [Reach.next, spineEntries, HeapKnowledge.descriptorSpine, fieldsOf], rfl⟩
  all_goals first | (simp [vals] at hx; done) | (simp [isVal] at hv)

theorem raises_vals {t v : Tm} (hr : Raises t v) : ∀ {o : Bool} {x : Val}, x ∈ vals ofC rl o nk v → x ∈ vals ofC rl o nk t := by
  induction hr
  all_goals intro o x hx
  case throwV => simpa [vals] using hx
  case makeArg ha _ _ ih => exact vals_makeAt (mem_valsArgs ha (ih hx))
  all_goals (simp only [vals, valsArgs_eq, List.mem_append, List.mem_flatMap]; grind [List.mem_of_getElem?])

/-- The elements a spread reads from a good spine are good. -/
theorem readElems_cover (hh : ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) {ls : List (Option Nat)}
    (hls : GV ofC h R (.arr ls)) :
    ∀ {i : Nat} {vs : List Tm}, readElems h (ls.drop i) = some vs → ∀ v ∈ vs, ∀ {o : Bool} {x : Val},
      x ∈ vals ofC rl o nk v → GV ofC h R x := by
  intro i
  induction hd : ls.drop i generalizing i with
  | nil => intro vs he; simp [readElems] at he; subst he; simp
  | cons e es ih =>
    intro vs he v hv o x hx
    have hes : ls.drop (i + 1) = es := by rw [← List.drop_drop, hd]; rfl
    have hget : ls[i]? = some e := by
      have := congrArg List.head? hd
      simpa [List.head?_drop] using this
    cases e with
    | none =>
      simp only [readElems, Option.map_eq_some_iff] at he
      obtain ⟨ws, hws, rfl⟩ := he
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [vals] at hx
      · exact ih hes hws v hv hx
    | some l =>
      simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
      obtain ⟨w, hw, ws, hws, rfl⟩ := he
      rcases List.mem_cons.mp hv with rfl | hv
      · have hn : Reach.next (.arr ls) (.cell i) = some l := by simp [Reach.next, spineEntries, hget]
        exact GV.heapHeld hh (hls.next hn) hw hx
      · exact ih hes hws v hv hx

theorem lookup_cons_eq {β : Type} {k : PropKey} {x : β} {xs : List (PropKey × β)} :
    ((k, x) :: xs).lookup k = some x := by
  simp [List.lookup]

theorem lookup_cons_ne {β : Type} {k k' : PropKey} {x : β} {xs : List (PropKey × β)} (h : k ≠ k') :
    ((k', x) :: xs).lookup k = xs.lookup k := by
  simp only [List.lookup]
  rw [show (k == k') = false from by simpa using h]

theorem firstKeys_lookup {α : Type} : ∀ {ps : List (PropKey × α)} {p : PropKey × α},
    p ∈ firstKeys ps → ps.lookup p.1 = some p.2
  | [], _, hp => by simp [firstKeys] at hp
  | (k, x) :: ps, p, hp => by
    simp only [firstKeys, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
    rcases hp with rfl | ⟨hp, hne⟩
    · exact lookup_cons_eq
    · rw [lookup_cons_ne hne]; exact firstKeys_lookup hp

theorem lookup_map_filter_none {β : Type} {P : PropKey → Bool} {f : Nat → β} {k : PropKey} (hP : ¬ P k = true) :
    ∀ fs : List (PropKey × Nat), ((fs.filter fun q => P q.1).map fun q => (q.1, f q.2)).lookup k = none
  | [] => rfl
  | q :: qs => by
    by_cases hq : P q.1 = true
    · have hqk : k ≠ q.1 := fun he => hP (he ▸ hq)
      simp only [List.filter_cons, hq, ↓reduceIte, List.map_cons]
      rw [lookup_cons_ne hqk]
      exact lookup_map_filter_none hP qs
    · simp only [List.filter_cons, hq, Bool.false_eq_true, ↓reduceIte]
      exact lookup_map_filter_none hP qs

theorem lookup_map_filter {β : Type} {P : PropKey → Bool} {f : Nat → β} :
    ∀ {fs : List (PropKey × Nat)} {k : PropKey} {x : β},
      ((fs.filter fun q => P q.1).map fun q => (q.1, f q.2)).lookup k = some x → ∃ l, fs.lookup k = some l ∧ x = f l
  | [], _, _, hx => by simp at hx
  | (k', l') :: fs, k, x, hx => by
    by_cases hP : P k' = true
    · simp only [List.filter_cons, hP, ↓reduceIte, List.map_cons] at hx
      by_cases hk : k = k'
      · subst hk
        rw [lookup_cons_eq] at hx
        exact ⟨l', lookup_cons_eq, (Option.some.inj hx).symm⟩
      · rw [lookup_cons_ne hk] at hx
        rw [lookup_cons_ne hk]
        exact lookup_map_filter hx
    · simp only [List.filter_cons, hP, Bool.false_eq_true, ↓reduceIte] at hx
      by_cases hk : k = k'
      · subst hk
        rw [lookup_map_filter_none hP fs] at hx; cases hx
      · rw [lookup_cons_ne hk]
        exact lookup_map_filter hx

theorem lookup_append_some {β : Type} : ∀ {xs ys : List (PropKey × β)} {k : PropKey} {x : β},
    (xs ++ ys).lookup k = some x → xs.lookup k = some x ∨ (k, x) ∈ ys
  | [], ys, k, x, h => by
    right
    induction ys with
    | nil => simp at h
    | cons y ys ih =>
      obtain ⟨k', x'⟩ := y
      rw [List.nil_append] at h
      by_cases hk : k = k'
      · subst hk; rw [lookup_cons_eq] at h; cases h; exact List.mem_cons_self
      · rw [lookup_cons_ne hk] at h
        exact List.mem_cons_of_mem _ (ih h)
  | (k', x') :: xs, ys, k, x, h => by
    rw [List.cons_append] at h
    by_cases hk : k = k'
    · subst hk; rw [lookup_cons_eq] at h ⊢; exact .inl h
    · rw [lookup_cons_ne hk] at h ⊢
      exact lookup_append_some h

theorem spineData_mem {hp : Heap} {fs : List (PropKey × Nat)} {e : PropKey × Tm} (he : e ∈ spineData hp fs) :
    ∃ (l : Nat) (ls : List (Option Nat)) (m : Nat), fs.lookup arraySpineKey = some l ∧ hp[l]? = some (.arr ls) ∧
      some m ∈ ls ∧ e.2 = heapVal hp m := by
  unfold spineData at he
  split at he
  · rename_i l hl
    split at he
    · rename_i ls hls
      simp only [List.mem_filterMap] at he
      obtain ⟨⟨o, i⟩, hmem, ho⟩ := he
      cases o with
      | none => cases ho
      | some m =>
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        exact ⟨l, ls, m, hl, hls, List.fst_mem_of_mem_zipIdx hmem, rfl⟩
    · simp at he
  · simp at he

/-- **A copy reads good values**: each value a merge copies is read from a
field of one of its operands, or from an element of the spine a field
holds, or is a string. -/
theorem mergeParts_cover {d : List PropKey} {a b : Tm} {ps : List (PropKey × Tm)}
    (hm : mergeParts h d a b = some ps)
    (hA : ∀ k l, Reach.next a k = some l → Good ofC h R l)
    (hB : ∀ k l, Reach.next b k = some l → Good ofC h R l) :
    ∀ e ∈ ps, ∀ {o : Bool} {x : Val}, x ∈ vals ofC rl o nk e.2 → GV ofC h R x := by
  simp only [mergeParts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
  obtain ⟨p, hp, q, hq, rfl⟩ := hm
  have hfield : ∀ (v : Tm) (fs : List (PropKey × Nat)) (cc : CallCode) (i : Nat),
      (∀ k l, Reach.next v k = some l → Good ofC h R l) → v = .objAt fs cc i →
      ∀ (k : PropKey) (l : Nat), fs.lookup k = some l → Good ofC h R l := by
    intro v fs cc i hv hvv k l hl
    exact hv (.key k) l (by subst hvv; simpa [Reach.next, fieldsOf] using hl)
  intro e he o x hx
  rcases mem_mergeData he with he | he
  · unfold ownAll at hp
    split at hp
    · split at hp
      · cases hp
      · simp only [Option.some.injEq] at hp
        subst hp
        obtain ⟨l, hl, hx'⟩ := lookup_map_filter (P := fun k => k != arraySpineKey) (f := heapVal h)
          (firstKeys_lookup he)
        rw [hx'] at hx
        exact GV.ofHeapVal (hfield _ _ _ _ hA rfl _ _ hl) hx
    · cases hp
  · have he := (List.mem_filter.mp he).1
    unfold ownData at hq
    split at hq
    · split at hq
      · cases hq
      · simp only [Option.some.injEq] at hq
        subst hq
        rename_i fs cc i
        rcases lookup_append_some (firstKeys_lookup he) with he' | he'
        · obtain ⟨l, hl, hx'⟩ := lookup_map_filter (P := copiedKey) (f := heapVal h) he'
          rw [hx'] at hx
          exact GV.ofHeapVal (hfield _ _ _ _ hB rfl _ _ hl) hx
        · obtain ⟨l, ls, m, hl, hls, hm', hx'⟩ := spineData_mem he'
          rw [hx'] at hx
          have hg : Good ofC h R l := hfield _ _ _ _ hB rfl _ _ hl
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hm'
          have hn : Reach.next (.arr ls) (.cell j) = some m := by simp [Reach.next, spineEntries, hj]
          exact GV.ofHeapVal ((GV.heap hg hls).next hn) hx
    · simp only [Option.some.injEq] at hq
      subst hq
      have := mem_firstKeys he
      simp only [stringData, List.mem_map] at this
      obtain ⟨y, -, rfl⟩ := this
      simp [vals] at hx
    all_goals simp_all

theorem slots_lookup_ge : ∀ {base : Nat} {ns : List PropKey} {k : PropKey} {l : Nat},
    (slots base ns).lookup k = some l → base ≤ l
  | _, [], _, _, h => by simp [slots] at h
  | base, n :: ns, k, l, h => by
    simp only [slots] at h
    by_cases hk : k = n
    · subst hk; rw [lookup_cons_eq] at h; cases h; exact Nat.le_refl _
    · rw [lookup_cons_ne hk] at h; have := slots_lookup_ge h; omega

theorem graphEntry_vals {n : Nat} {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {st : Nat} {caps : List Tm} {self : Tm} {rest : Bool} {comp : ComponentTag} {r : Tm} {args : List Tm} {x : Val}
    (hx : x ∈ vals ofC rl true nk (CallArguments.graphEntry n E K st caps self rest comp r args)) :
    (rl.flag ofC true nk comp = true ∧ ((∃ e ∈ E, x ∈ vals ofC Realm.all true true e) ∨
      (∃ y ∈ caps, x ∈ vals ofC Realm.all true true y) ∨ x ∈ vals ofC Realm.all true true self)) ∨
      x ∈ vals ofC Realm.all true true r ∨ ∃ y ∈ args, x ∈ vals ofC Realm.all true true y := by
  have hp : ∀ y ∈ CallArguments.parameters n args, x ∈ vals ofC Realm.all true true y →
      ∃ y ∈ args, x ∈ vals ofC Realm.all true true y := by
    intro y hy hxy
    rcases Kinds.parameters_mem hy with hy | rfl
    · exact ⟨y, hy, hxy⟩
    · simp [vals] at hxy
  cases rest with
  | false =>
    simp only [CallArguments.graphEntry, vals, valsArgs_eq, List.flatMap_cons, List.flatMap_append,
      List.flatMap_nil] at hx
    split at hx
    · rename_i hcomp
      simp only [List.mem_append, List.mem_flatMap, List.append_nil] at hx
      grind
    · simp at hx
  | true =>
    simp only [CallArguments.graphEntry, vals, valsArgs_eq, List.mem_append, List.mem_flatMap] at hx
    have hd : ∀ y ∈ args.drop n, y ∈ args := fun y hy => List.mem_of_mem_drop hy
    have hall : ∀ y {o nk'}, x ∈ vals ofC rl o nk' y → x ∈ vals ofC Realm.all true true y :=
      fun y _ _ hy => vals_all ofC y _ _ _ hy
    split at hx
    · rename_i hcomp
      simp only [List.mem_append, List.mem_flatMap, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, vals,
        List.append_nil] at hx
      grind
    · simp only [List.not_mem_nil, or_false] at hx
      grind

theorem mem_vals_true {o : Bool} {v x : Val} (hx : x ∈ vals ofC rl o nk v) : x ∈ vals ofC rl true nk v := by
  cases o
  · exact vals_mono v hx
  · exact hx

/-- A value's values at a position of outside code are the same at every
realm and key, and include those at any position. -/
theorem mem_vals_val {o : Bool} {v : Tm} {x : Val} (hv : isVal v = true) (rl' : Realm) (nk' : Bool)
    (hx : x ∈ vals ofC rl o nk v) : x ∈ vals ofC rl' true nk' v := by
  rw [vals_val ofC rl' rl true nk' nk hv]; exact mem_vals_true hx

theorem GV.fresh {v : Val} (hn : ∀ a l, Reach.next v a = some l → h.length ≤ l) (hc : codeVals ofC v = []) :
    GV ofC h R v :=
  GV.of (fun a l hl => .inr (hn a l hl)) (by rw [hc]; simp)

theorem makeAt_code {fs : List (PropKey × Nat)} {i : Nat} {cc : CallCode} {ns : List PropKey} {xs : List Tm} {x : Val}
    (hx : x ∈ codeVals ofC (.objAt fs cc i)) : x ∈ vals ofC rl true nk (.makeAt cc ns xs) := by
  cases cc <;> simp [codeVals, vals] at hx ⊢ <;> grind

theorem codeUnitAt_val (s : String) (b : UInt64) : isVal (codeUnitAt s b) = true := by
  unfold codeUnitAt; split <;> rfl

theorem thrown_cover {n : Nat} {o : Bool} {x : Val} (hx : x ∈ vals ofC rl o nk (.throw (thrownError n))) :
    GV ofC h R x := by
  cases o <;> simp [vals, thrownError] at hx
  subst hx
  exact GV.inert ⟨fun a => by cases a <;> rfl, rfl⟩

/-- **A node's next run holds good values** where the frame's code, the
environment it maps and its default are good. -/
theorem goto_cover {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {l : Nat}
    {m : Option (List Nat)} {L₀ : List Tm} {d : Tm} {comp : ComponentTag} {o : Bool}
    (hold : ∀ y, (∃ e ∈ E, y ∈ vals ofC Realm.all true true e) ∨ (∃ y' ∈ L₀, y ∈ vals ofC Realm.all true true y') ∨
      y ∈ vals ofC Realm.all true true d → GV ofC h R y) :
    ∀ x ∈ vals ofC rl o nk (.goto E K l (envMap m L₀ d).1 (envMap m L₀ d).2 comp), GV ofC h R x := by
  intro x hx
  simp only [vals, valsArgs_eq] at hx
  split at hx
  · simp only [List.mem_append, List.mem_flatMap] at hx
    rcases hx with (hx | ⟨y, hy, hx⟩) | hx
    · exact hold x (.inl hx)
    · rcases envMap_mem (.inl hy) with hy | rfl
      · exact hold x (.inr (.inl ⟨y, hy, hx⟩))
      · exact hold x (.inr (.inr hx))
    · rcases envMap_mem (x := (envMap m L₀ d).2) (.inr rfl) with hy | hy
      · exact hold x (.inr (.inl ⟨_, hy, hx⟩))
      · rw [hy] at hx; exact hold x (.inr (.inr hx))
  · cases hx

theorem frame_hold {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {u : Tm}
    {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {xx : Option ControlFlow.Target} {comp : ComponentTag}
    {o : Bool} (hc : rl.flag ofC o nk comp = true)
    (hR : ∀ x ∈ vals ofC rl o nk (.frame E K u L d k xx comp), GV ofC h R x) :
    ∀ y, (∃ e ∈ E, y ∈ vals ofC Realm.all true true e) ∨ (∃ y' ∈ L, y ∈ vals ofC Realm.all true true y') ∨
      y ∈ vals ofC Realm.all true true d ∨ y ∈ vals ofC rl true (rl.native ((E, K), comp) (k, xx)) u → GV ofC h R y := by
  intro y hy
  refine hR y ?_
  simp only [vals, hc, ↓reduceIte, valsArgs_eq, List.mem_append, List.mem_flatMap]
  rcases hy with hy | hy | hy | hy
  · exact .inl (.inl (.inl hy))
  · exact .inl (.inl (.inr hy))
  · exact .inl (.inr hy)
  · exact .inr hy

theorem activeTag_frame_tag {c : ComponentTag} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {u : Tm} {L : List Tm} {d : Tm}
    {k : ControlFlow.Continuation} {xx : Option ControlFlow.Target} {comp : ComponentTag}
    (hu : path rl (rl.own c nk comp) (rl.native ((E, K), comp) (k, xx)) u = [(rl.own c nk comp, u)]) :
    activeTag rl c nk (.frame E K u L d k xx comp) = rl.own c nk comp := by
  simp [activeTag, path_frame hu]

/-- **What outside code holds after a step is good**: every value at a
position of outside code after a step whose active frame runs no code
`ofC` names, from a term whose such values are good, at a heap holding
values, is good. -/
theorem step_cover (hrl : ∀ t, rl.tags t = true → ofC t = false)
    (hh : ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) {h' : Heap} {t t' : Tm}
    (hs : Step h t h' t') :
    ∀ c nk, ofC (activeTag rl c nk t) = false → (∀ x ∈ vals ofC rl (!ofC c) nk t, GV ofC h R x) →
      ∀ x ∈ vals ofC rl (!ofC c) nk t', GV ofC h R x := by
  induction hs
  all_goals intro c nk hc hR x hx
  case callArg hf hr ha hpre hs ih =>
    simp only [activeTag, path, hf, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hR x (by simp only [vals, List.mem_append]; exact .inl (.inl hx))
    · exact hR x (by simp only [vals, List.mem_append]; exact .inl (.inr hx))
    · rcases mem_valsArgs_set hx with hx | hx
      · exact hR x (by simp only [vals, List.mem_append]; exact .inr hx)
      · exact ih hh c nk hc (fun y hy => hR y (by simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha hy))) x hx
  case constructArg hf ha hpre hs ih =>
    simp only [activeTag, path, hf, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hR x (by simp only [vals, List.mem_append]; exact .inl hx)
    · rcases mem_valsArgs_set hx with hx | hx
      · exact hR x (by simp only [vals, List.mem_append]; exact .inr hx)
      · exact ih hh c nk hc (fun y hy => hR y (by simp only [vals, List.mem_append]; exact .inr (mem_valsArgs ha hy))) x hx
  case makeArg cc ns inits i _ _ a a' ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    have hsplit : ∀ {o : Bool} {ys : List Tm} {y : Val}, y ∈ vals ofC rl o nk (.makeAt cc ns ys) →
        y ∈ vals ofC rl o nk (.makeAt cc ns []) ∨ y ∈ valsArgs ofC rl o nk ys := by
      intro o ys y hy
      cases cc <;> simp only [vals, valsArgs_eq, List.mem_append, List.flatMap_nil, List.append_nil] at hy ⊢ <;> grind
    have hjoin : ∀ {o : Bool} {ys : List Tm} {y : Val}, y ∈ vals ofC rl o nk (.makeAt cc ns []) →
        y ∈ vals ofC rl o nk (.makeAt cc ns ys) := by
      intro o ys y hy
      cases cc <;> simp only [vals, valsArgs_eq, List.mem_append, List.flatMap_nil, List.append_nil] at hy ⊢ <;> grind
    rcases hsplit hx with hx | hx
    · exact hR x (hjoin hx)
    · rcases mem_valsArgs_set hx with hx | hx
      · exact hR x (vals_makeAt hx)
      · exact ih hh c nk hc (fun y hy => hR y (vals_makeAt (mem_valsArgs ha hy))) x hx
  case arrArg ha hpre hs ih =>
    simp only [activeTag, path] at hc
    rw [pathArgs_at _ ha hpre (not_val_of_step hs), wrap_head] at hc
    simp only [vals] at hx
    rcases mem_valsArgs_set hx with hx | hx
    · exact hR x (by simp only [vals]; exact hx)
    · exact ih hh c nk hc (fun y hy => hR y (by simp only [vals]; exact mem_valsArgs ha hy)) x hx
  case frameC ih =>
    rw [activeTag_frame] at hc
    simp only [vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hR x (by simp only [vals, List.mem_append]; exact .inl hx)
    · rw [Realm.flag_own rl ofC rfl] at hx
      exact ih hh _ _ hc (fun y hy => hR y (by
        simp only [vals, List.mem_append, Realm.flag_own rl ofC rfl]; exact .inr hy)) x hx
  -- Results that hold no value, or the term's own.
  case testV => split at hx <;> simp [vals] at hx
  case iteT => exact hR x (List.mem_append_left _ (List.mem_append_right _ hx))
  case iteF => exact hR x (List.mem_append_right _ hx)
  case arithV hb => exact noRefs_cover (binop_values hb).2.2 (binop_refs hb) hx
  case elemStr => exact noRefs_cover (codeUnitAt_val _ _) (codeUnitAt_refs _ _) hx
  case setPresent => exact hR x (List.mem_append_left _ (List.mem_append_left _ hx))
  case makeKeyV => exact hR x (List.mem_append_right _ (by simpa [vals] using hx))
  case arrAllocThrow => exact thrown_cover hx
  case lenStrThrow => exact thrown_cover hx
  case arithThrow => exact thrown_cover hx
  -- Copies and allocations.
  case mergeV a b hp d ps ha hb hm =>
    have hc' : ofC c = false := by simpa [activeTag, path, ha, hb] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hA : ∀ k l, Reach.next a k = some l → Good ofC hp R l := fun k l hn =>
      (hR a (List.mem_append_left _ (mem_vals_self (not_inert_of_next hn)))).next hn
    have hB : ∀ k l, Reach.next b k = some l → Good ofC hp R l := fun k l hn =>
      (hR b (List.mem_append_right _ (mem_vals_self (not_inert_of_next hn)))).next hn
    simp only [vals, valsArgs_eq, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨_, ⟨e, he, rfl⟩, hx⟩ := hx
    exact mergeParts_cover hm hA hB e he hx
  case makeFields cc ns vs hp hvs _ =>
    simp only [activeTag, path] at hc
    rw [pathArgs_vals _ hvs] at hc
    have hc' : ofC c = false := by simpa using hc
    simp only [hc', Bool.not_false] at hR hx
    have hcode : ∀ y ∈ codeVals ofC (.objAt (slots hp.length ns) cc (hp.length + vs.length)), GV ofC hp R y :=
      fun y hy => hR y (makeAt_code hy)
    rw [vals_objAt] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine GV.of (fun a l hn => ?_) hcode
      cases a with
      | key k => exact .inr (slots_lookup_ge (by simpa [Reach.next, fieldsOf] using hn))
      | view =>
        cases cc with
        | view s f n =>
          simp only [Reach.next, HeapKnowledge.descriptorSpine, Option.some.injEq] at hn
          subst hn
          exact (hR (.objAt [] (.view s f n) 0) (by simp [vals])).next (a := .view) rfl
        | _ => simp [Reach.next, HeapKnowledge.descriptorSpine] at hn
      | cell => simp [Reach.next, spineEntries] at hn
      | code => cases hn
    · exact hcode x hx
  case arrAlloc vs hp _ _ =>
    simp only [vals] at hx
    split at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      refine GV.fresh (fun a l hn => ?_) rfl
      cases a with
      | cell i =>
        simp only [Reach.next, spineEntries, elemSlots] at hn
        cases hi : ((List.range vs.length).map fun j => some (hp.length + j))[i]? with
        | none => rw [hi] at hn; cases hn
        | some o =>
          rw [hi] at hn
          simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
          obtain ⟨j, -, rfl⟩ := hi
          simp at hn; omega
      | _ => simp [Reach.next, fieldsOf, HeapKnowledge.descriptorSpine] at hn
    · cases hx
  case setGrow ls b k hp v _ _ _ =>
    simp only [vals] at hx
    split at hx
    · rename_i ho
      simp only [List.mem_singleton] at hx
      subst hx
      have harr : GV ofC hp R (.arr ls) := hR _ (List.mem_append_left _ (List.mem_append_left _ (by simp [vals, ho])))
      refine GV.of (fun a l hn => ?_) (by simp [codeVals])
      cases a with
      | cell i =>
        simp only [Reach.next, spineEntries] at hn
        have hm : some l ∈ placeAt ls k hp.length := by
          cases hi : (placeAt ls k hp.length)[i]? with
          | none => rw [hi] at hn; cases hn
          | some o => rw [hi] at hn; cases o <;> simp at hn; subst hn; exact List.mem_of_getElem? hi
        rcases Kinds.mem_placeAt hm with hm | rfl
        · obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
          exact harr.next (a := .cell j) (by simp [Reach.next, spineEntries, hj])
        · exact .inr (Nat.le_refl _)
      | _ => simp [Reach.next, fieldsOf, HeapKnowledge.descriptorSpine] at hn
    · cases hx
  -- Frames.
  case frameRet v _ E K L d xx comp hv =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val hv)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    exact frame_hold hc' hR x (.inr (.inr (.inr (mem_vals_val hv rl _ hx))))
  case frameRaise u v _ E K L d k comp hr =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (raises_path hr _ _)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    exact frame_hold hc' hR x (.inr (.inr (.inr (raises_vals hr (mem_vals_val (raises_val hr) rl _ (by simpa [vals] using hx))))))
  case frameHandle u v _ E K L d k l comp hr =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (raises_path hr _ _)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · exact .inr (.inr (.inr (raises_vals hr (mem_vals_val (raises_val hr) rl _ hy))))
      · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameBind v _ E K L d l xx comp hv =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val hv)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · exact .inr (.inr (.inr (mem_vals_val hv rl _ hy)))
      · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameEffect v _ E K L d l xx comp hv =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val hv)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameYes _ E K L d y n xx comp =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val rfl)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameNo _ E K L d y n xx comp =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val rfl)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameYesBind _ E K L d y n xx comp =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val rfl)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · simp [vals] at hy
      · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameNoBind _ E K L d y n xx comp =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val rfl)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · simp [vals] at hy
      · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  case frameTag v _ E K L d tg y n xx comp hv =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      rw [activeTag_frame_tag (path_val hv)] at hc; simp [Realm.flag_own rl ofC rfl, hc]
    refine goto_cover (fun y hy => frame_hold hc' hR y ?_) x hx
    rcases hy with hy | ⟨y', hy', hy⟩ | hy
    · exact .inl hy
    · rcases List.mem_cons.mp hy' with rfl | hy'
      · exact .inr (.inr (.inr (mem_vals_val hv rl _ hy)))
      · exact .inr (.inl ⟨y', hy', hy⟩)
    · exact .inr (.inr (.inl hy))
  all_goals try (simp [vals] at hx; done)
  -- The heap read at a good location.
  case readField oid f fs cc l _ v hf hv =>
    have hc' : ofC c = false := by simpa [activeTag, path] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs cc oid)
      (by show _ ∈ vals ofC rl true nk (Tm.objAt fs cc oid); rw [vals_objAt]; exact List.mem_cons_self)
    exact GV.heapHeld hh (hobj.next (a := .key f) (by simpa [Reach.next, fieldsOf] using hf)) hv hx
  case readProto oid f fs cc l _ p _ hp hv =>
    have hc' : ofC c = false := by simpa [activeTag, path] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs cc oid)
      (by show _ ∈ vals ofC rl true nk (Tm.objAt fs cc oid); rw [vals_objAt]; exact List.mem_cons_self)
    exact GV.heapHeld hh (hobj.next (a := .key _) (by simpa [Reach.next, fieldsOf] using hp)) hv hx
  case indexField oid key f fs cc l _ v hk hf hv =>
    have hc' : ofC c = false := by simpa [activeTag, path, propertyKey_val hk] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs cc oid) (List.mem_append_left _ (by rw [vals_objAt]; exact List.mem_cons_self))
    exact GV.heapHeld hh (hobj.next (a := .key f) (by simpa [Reach.next, fieldsOf] using hf)) hv hx
  case indexProto oid key f fs cc l _ p hk _ hp hv =>
    have hc' : ofC c = false := by simpa [activeTag, path, propertyKey_val hk] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs cc oid) (List.mem_append_left _ (by rw [vals_objAt]; exact List.mem_cons_self))
    rcases List.mem_append.mp hx with hx | hx
    · exact GV.heapHeld hh (hobj.next (a := .key _) (by simpa [Reach.next, fieldsOf] using hp)) hv hx
    · exact hR x (List.mem_append_right _ hx)
  case elemRead ls b l _ v hl hv =>
    have hc' : ofC c = false := by simpa [activeTag, path] using hc
    simp only [hc', Bool.not_false] at hR hx
    have harr := hR (.arr ls) (List.mem_append_left _ (by simp [vals]))
    simp only [elemLoc, Option.bind_eq_some_iff] at hl
    obtain ⟨k, -, o, ho, hl⟩ := hl
    cases o with
    | none => cases hl
    | some m =>
      cases hl
      exact GV.heapHeld hh (harr.next (a := .cell k) (by simp [Reach.next, spineEntries, ho])) hv hx
  -- Substitution and instantiation.
  case letV ha =>
    have hc' : ofC c = false := by simpa [activeTag, path, ha] using hc
    simp only [hc', Bool.not_false] at hR hx
    exact subst_cover (fun y hy => hR y (List.mem_append_left _ (mem_vals_val ha rl nk hy))) _ 0 rl true nk
      (fun y hy => hR y (List.mem_append_right _ hy)) x hx
  case gotoEnter E l e K k xx hp L d comp he _ =>
    have hc' : rl.flag ofC (!ofC c) nk comp = true := by
      simp only [activeTag, path, List.head?_cons, Option.map_some, Option.getD_some] at hc
      simp [Realm.flag_own rl ofC rfl, hc]
    have hR' : ∀ y, (∃ e ∈ E, y ∈ vals ofC Realm.all true true e) ∨ (∃ y' ∈ L, y ∈ vals ofC Realm.all true true y') ∨
        y ∈ vals ofC Realm.all true true d → GV ofC hp R y := by
      intro y hy
      refine hR y ?_
      simp only [vals, hc', ↓reduceIte, valsArgs_eq, List.mem_append, List.mem_flatMap]
      rcases hy with hy | hy | hy
      · exact .inl (.inl hy)
      · exact .inl (.inr hy)
      · exact .inr hy
    simp only [vals, hc', ↓reduceIte, valsArgs_eq, List.mem_append, List.mem_flatMap] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact hR' x (.inl hx)
    · exact hR' x (.inr (.inl hx))
    · exact hR' x (.inr (.inr hx))
    · refine instantiate_cover (fun i y hy => ?_) e 0 rl true _
        (fun y hy => hR' y (.inl ⟨e, List.mem_of_getElem? he, vals_all ofC e _ _ _ hy⟩)) x hx
      rcases getD_mem_or L i d with hi | hi
      · exact hR' y (.inr (.inl ⟨_, hi, by simp only [envOf] at hy; exact hy⟩))
      · exact hR' y (.inr (.inr (by simp only [envOf] at hy; rw [hi] at hy; exact hy)))
  -- Calls.
  case callBound r args _ fs tt r₀ pre oid hr hargs =>
    simp only [activeTag, path, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_vals _ hargs] at hc
    have hc' : ofC c = false := by simpa using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs (.bound tt r₀ pre) oid)
      (List.mem_append_left _ (List.mem_append_left _ (by rw [vals_objAt]; exact List.mem_cons_self)))
    simp only [vals, valsArgs_eq, List.flatMap_append, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx | hx)
    · exact hobj.code (by simp [codeVals, vals_all ofC _ _ _ _ hx])
    · exact hobj.code (by simp [codeVals, vals_all ofC _ _ _ _ hx])
    · obtain ⟨y, hy, hx⟩ := List.mem_flatMap.mp hx
      exact hobj.code (by simp only [codeVals, valsArgs_eq, List.mem_append, List.mem_flatMap]
                          exact .inr ⟨y, hy, vals_all ofC _ _ _ _ hx⟩)
    · exact hR x (List.mem_append_right _ (by rw [valsArgs_eq]; exact hx))
  case callGraph r args _ fs n E K st caps k rest comp oid hr hargs _ =>
    simp only [activeTag, path, isVal_objAt, hr, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_vals _ hargs] at hc
    have hc' : ofC c = false := by simpa using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs (.graph n E K st caps k rest comp) oid)
      (List.mem_append_left _ (List.mem_append_left _ (by rw [vals_objAt]; exact List.mem_cons_self)))
    rcases graphEntry_vals hx with ⟨hcomp, (hx | hx | hx)⟩ | hx | ⟨y, hy, hx⟩
    · exact hobj.code (by simp only [codeVals, Realm.ofC_of_flag hrl hcomp, Bool.false_eq_true, ↓reduceIte,
        valsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl hx)
    · exact hobj.code (by simp only [codeVals, Realm.ofC_of_flag hrl hcomp, Bool.false_eq_true, ↓reduceIte,
        valsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr hx)
    · exact hobj.held rfl hx
    · exact hR x (List.mem_append_left _ (List.mem_append_right _ (mem_vals_val hr rl nk hx)))
    · exact hR x (List.mem_append_right _ (mem_valsArgs_of hy (mem_vals_val (hargs y hy) rl nk hx)))
  case constructGraph args _ fs n E K st caps rest comp oid hargs =>
    simp only [activeTag, path, isVal_objAt, Bool.true_eq_false, ↓reduceIte] at hc
    rw [pathArgs_vals _ hargs] at hc
    have hc' : ofC c = false := by simpa using hc
    simp only [hc', Bool.not_false] at hR hx
    have hobj := hR (.objAt fs (.graph n E K st caps .construct rest comp) oid)
      (List.mem_append_left _ (by rw [vals_objAt]; exact List.mem_cons_self))
    rcases graphEntry_vals hx with ⟨hcomp, (hx | hx | hx)⟩ | hx | ⟨y, hy, hx⟩
    · exact hobj.code (by simp only [codeVals, Realm.ofC_of_flag hrl hcomp, Bool.false_eq_true, ↓reduceIte,
        valsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl hx)
    · exact hobj.code (by simp only [codeVals, Realm.ofC_of_flag hrl hcomp, Bool.false_eq_true, ↓reduceIte,
        valsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr hx)
    · exact hobj.held rfl hx
    · simp [vals] at hx
    · exact hR x (List.mem_append_right _ (mem_valsArgs_of hy (mem_vals_val (hargs y hy) rl nk hx)))
  -- Spreads.
  case callSpread f r hp args pre post ls vs hf hr hargs hpre he =>
    subst hargs
    have hc' : ofC c = false := by
      simp only [activeTag, path, hf, hr, Bool.true_eq_false, ↓reduceIte] at hc
      rw [pathArgs_append _ _ hpre] at hc
      simpa [pathArgs, path, wrap, mapLast] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hargs : ∀ {y : Val}, y ∈ valsArgs ofC rl true nk (pre ++ .spread (.arr ls) :: post) → GV ofC hp R y :=
      fun hy => hR _ (List.mem_append_right _ hy)
    have harr : GV ofC hp R (.arr ls) := hargs (by simp [vals])
    simp only [vals, valsArgs_eq, List.flatMap_append, List.mem_append] at hx
    rcases hx with ((hx | hx) | (hx | hx) | hx)
    · exact hR x (List.mem_append_left _ (List.mem_append_left _ hx))
    · exact hR x (List.mem_append_left _ (List.mem_append_right _ hx))
    · exact hargs (by rw [valsArgs_eq, List.flatMap_append]; exact List.mem_append_left _ hx)
    · obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hx
      exact readElems_cover hh harr (i := 0) (by simpa using he) v hv hx
    · exact hargs (by simp only [valsArgs_eq, List.flatMap_append, List.flatMap_cons, List.mem_append]; exact .inr (.inr hx))
  case constructSpread f hp args pre post ls vs hf hargs hpre he =>
    subst hargs
    have hc' : ofC c = false := by
      simp only [activeTag, path, hf, Bool.true_eq_false, ↓reduceIte] at hc
      rw [pathArgs_append _ _ hpre] at hc
      simpa [pathArgs, path, wrap, mapLast] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hargs : ∀ {y : Val}, y ∈ valsArgs ofC rl true nk (pre ++ .spread (.arr ls) :: post) → GV ofC hp R y :=
      fun hy => hR _ (List.mem_append_right _ hy)
    have harr : GV ofC hp R (.arr ls) := hargs (by simp [vals])
    simp only [vals, valsArgs_eq, List.flatMap_append, List.mem_append] at hx
    rcases hx with (hx | (hx | hx) | hx)
    · exact hR x (List.mem_append_left _ hx)
    · exact hargs (by rw [valsArgs_eq, List.flatMap_append]; exact List.mem_append_left _ hx)
    · obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hx
      exact readElems_cover hh harr (i := 0) (by simpa using he) v hv hx
    · exact hargs (by simp only [valsArgs_eq, List.flatMap_append, List.flatMap_cons, List.mem_append]; exact .inr (.inr hx))
  case arrSpread inits pre post ls vs hp hargs hpre he =>
    subst hargs
    have hc' : ofC c = false := by
      simp only [activeTag, path] at hc
      rw [pathArgs_append _ _ hpre] at hc
      simpa [pathArgs, path, wrap, mapLast] using hc
    simp only [hc', Bool.not_false] at hR hx
    have hargs : ∀ {y : Val}, y ∈ valsArgs ofC rl true nk (pre ++ .spread (.arr ls) :: post) → GV ofC hp R y :=
      fun hy => hR _ hy
    have harr : GV ofC hp R (.arr ls) := hargs (by simp [vals])
    simp only [vals, valsArgs_eq, List.flatMap_append, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx)
    · exact hargs (by rw [valsArgs_eq, List.flatMap_append]; exact List.mem_append_left _ hx)
    · obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hx
      exact readElems_cover hh harr (i := 0) (by simpa using he) v hv hx
    · exact hargs (by simp only [valsArgs_eq, List.flatMap_append, List.flatMap_cons, List.mem_append]; exact .inr (.inr hx))
  all_goals try (
    rename_i ih
    have hna := not_val_of_step ‹Step _ _ _ _›
    have hc₁ := hc
    rw [activeTag_wrap (by simp [path, *] <;> rfl)] at hc₁
    have ih' := ih hh c nk hc₁ (fun y hy => hR y (by simp [vals, hy]))
    simp only [vals, List.mem_append] at hx hR
    grind)

/-- **`noForge` of a step of the calculus**: after a step whose active
frame runs no code `ofC` names, at a heap holding values, every location
the roots of outside code reach was reached by them before, or is fresh.
A path after the step runs through good values only: the roots after it
are good (`step_cover`), and so are the new contents of every good
location, which the step stored among its roots (`step_writes`) or left
as they were (`GV.heap`). -/
theorem step_noForge (hrl : ∀ t, rl.tags t = true → ofC t = false)
    (hh : ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true) {h' : Heap} {t t' : Tm}
    (hs : Step h t h' t') (c : ComponentTag) (hc : ofC (activeTag rl c nk t) = false) :
    ∀ l, ReachesFrom ofC h' (vals ofC rl (!ofC c) nk t') l →
      ReachesFrom ofC h (vals ofC rl (!ofC c) nk t) l ∨ h.length ≤ l := by
  have hR : ∀ x ∈ vals ofC rl (!ofC c) nk t, GV ofC h (vals ofC rl (!ofC c) nk t) x := fun _ hx => GV.root hx
  have hcover := step_cover (R := vals ofC rl (!ofC c) nk t) hrl hh hs c nk hc hR
  have hheap : ∀ l u, Good ofC h (vals ofC rl (!ofC c) nk t) l → h'[l]? = some u →
      GV ofC h (vals ofC rl (!ofC c) nk t) u := by
    intro l u hg hu
    by_cases hsame : ∃ v, h[l]? = some v ∧ h'[l]? = some v
    · obtain ⟨v, hv, hv'⟩ := hsame
      rw [hu] at hv'; cases hv'
      exact GV.heap hg hv
    · by_cases hi : Inert ofC u
      · exact GV.inert hi
      · exact GV.root (step_writes hs c nk hc hsame hu hi)
  rintro l ⟨v, hv, π, hf⟩
  exact follows_good hheap (hcover v hv) hf

end NoForge

/-- A well-formed heap holds values. -/
theorem heap_isVal {s : IndexedHeap} {l : Nat} {v : Val} (hv : s.h[l]? = some v) : isVal v = true := by
  have hl : l < s.h.length := (List.getElem?_eq_some_iff.mp hv).1
  have hlen : l < (entries s.W).length := by
    have := s.ok.1.1
    simp only [toList, List.length_map] at this
    omega
  obtain ⟨r, hr⟩ := roleAt_some hlen
  obtain ⟨u, hu, hcat, -⟩ := s.ok.2 l r hr
  rw [hv] at hu
  cases hu
  cases r with
  | field | cell | elem => exact sourceVal_isVal hcat
  | identity => subst hcat; rfl
  | spine f =>
    cases f with
    | array => obtain ⟨ls, rfl⟩ := hcat; rfl
    | view => obtain ⟨cs, rfl, -⟩ := hcat; rfl

end Verification.TolerantFrames.Reach
