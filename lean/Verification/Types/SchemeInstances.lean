import Verification.Types.PositiveRules

/-! ## Instances of a scheme row

An instance of a scheme row is named by an instance map `θ`, sending each row a
signature reaches to a type of the graph: a binder to the type it is
instantiated at, a clause row to a clause row whose clauses are its own with
every operand mapped (the substituted copy the graph already holds, such as
`PromiseLike<boolean>` for `PromiseLike<R1>`), a scheme row to a scheme row
with the same binders and its signatures mapped, and any row that does not
depend on a moved binder to itself. Dependence is by free parameter rows,
stated by a checked certificate (`FreeOk`): a row under a scheme binding a
parameter does not depend on it, so a receiver `Promise<number>`, whose `then`
mentions `then`'s own binders, is its own image. -/
namespace Verification.PositiveRules
open PositiveNormalization PositiveGraphs ReferenceConjunctions Tower CallEffects


/-! ### Instance tables

An instance is checked by a finite table of entries `(row, context, image)`.
The context says what each binder in scope stands for: an instance type, or,
under a scheme the instance maps to another, that scheme's binder. Under its
context an entry's row means its image. Binder rows shared between scopes, as
the colouring of generic methods makes them, are told apart by the context. -/

/-- What the binders in scope stand for. -/
abbrev Ctx (ι : Type) := List (ι × List ι)

/-- Entries `(row, context, image)`. -/
abbrev InstTable (ι : Type) := List (ι × Ctx ι × List ι)

@[nospecialize] def entryImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (l : ι) : Option (List ι) :=
  (tbl.find? fun e => e.1 == l && e.2.1 == κ).map (·.2.2)

/-- A type's image: its rows' images, each an entry. -/
@[nospecialize] def tyImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (S : List ι) : Option (List ι) :=
  (S.mapM (entryImg tbl κ)).map List.flatten

@[nospecialize] def sigImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p : Arrow (List ι)) : Option (Arrow (List ι)) := do
  return ⟨← tyImg tbl κ p.receiver, ← p.arguments.mapM (tyImg tbl κ), ← tyImg tbl κ p.result, p.effect⟩

@[nospecialize] def restImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p : RestArrow (List ι)) :
    Option (RestArrow (List ι)) := do
  return ⟨← tyImg tbl κ p.receiver, (← p.arguments.1.mapM (tyImg tbl κ), ← tyImg tbl κ p.arguments.2),
    ← tyImg tbl κ p.result, p.effect⟩

/-- Two label lists with the same members. A type is the union of its labels,
so their order and repetition carry no meaning. -/
@[nospecialize] def sameLabels [DecidableEq ι] (a b : List ι) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

/-- The images of a list of types, each an entry's. -/
@[nospecialize] def tysImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (Ss : List (List ι)) :
    Option (List (List ι)) :=
  Ss.mapM (tyImg tbl κ)

/-- A receiver universe covers the instance's receiver without a substitution. -/
@[nospecialize] def receiverUniverse [DecidableEq ι] (G : NormalGraph ι) (P Q : List ι) : Bool :=
  expand G P == [.top] ||
    (expand G P == [.source] && sourceTy G Q)

/-- The premises under which the scheme signature `p`, read through the
instance's images, covers the target signature `q` (`Inst≤`): the target's
receiver within the image's, unless the scheme's receiver admits every value;
each target argument within the image's; the image's result within the
target's. None where the arities differ, `p`'s effect does not cover `q`'s,
or an operand has no image. -/
@[nospecialize] def sigPremises [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (p q : Arrow (List ι)) : Option (List (List ι × List ι)) :=
  if p.arguments.length == q.arguments.length && p.effect.covers q.effect then
    match tysImg tbl κ p.arguments, tyImg tbl κ p.result with
    | some ps, some r =>
      let body := q.arguments.zip ps ++ [(r, q.result)]
      if receiverUniverse G p.receiver q.receiver then some body
      else (tyImg tbl κ p.receiver).map fun rc => (q.receiver, rc) :: body
    | _, _ => none
  else none

/-- The same, for a variadic signature: its fixed arguments, its rest's
argument lists and its result. -/
@[nospecialize] def restPremises [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (p q : RestArrow (List ι)) : Option (List (List ι × List ι)) :=
  if p.arguments.1.length == q.arguments.1.length && p.effect.covers q.effect then
    match tysImg tbl κ p.arguments.1, tyImg tbl κ p.arguments.2, tyImg tbl κ p.result with
    | some ps, some e, some r =>
      let body := q.arguments.1.zip ps ++ [(q.arguments.2, e), (r, q.result)]
      if receiverUniverse G p.receiver q.receiver then some body
      else (tyImg tbl κ p.receiver).map fun rc => (q.receiver, rc) :: body
    | _, _, _ => none
  else none

/-- The context `κ` on the rows `ps` outside `src`, in the order of `ps`. -/
@[nospecialize] def keep [DecidableEq ι] (κ : Ctx ι) (src ps : List ι) : Ctx ι :=
  ps.filterMap fun p => if src.contains p then none else (κ.lookup p).map (p, ·)

/-- Entering scheme row `i` mapped to another: its binders stand for the
other's, and of the outer context only the free rows of `i` are kept, in the
order `V` lists them. Nothing inside reads another, and the contexts met while
relating recursive types, whose schemes nest without end, are then finitely
many, so their entries recur. -/
@[nospecialize] def enter [DecidableEq ι] (V : FreeMap ι) (i : ι) (κ : Ctx ι) (src tgt : List ι) : Ctx ι :=
  src.zip (tgt.map ([·])) ++ keep κ src (fv V i)

/-- A clause with every operand replaced by its image. -/
@[nospecialize] def clauseImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (c : Clause (List ι)) :
    Clause (List ι) :=
  c.map fun S => (tyImg tbl κ S).getD []

/-- A checked operand image transports a value clause. Both sorts of operands
are required; a value equality alone cannot justify a rest-parameter image. -/
theorem clauseImg_value [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (c : Clause (List ι)) (X Y : List ι → Fam) (P Q : List ι → ArgFam)
    (n : Nat) (W : WorldT n) (v : Val)
    (himg : ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      Agree (X S) (Y T) n ∧ Agree (P S) (Q T) n)
    (he : Agree (X []) (Y []) n) (hp : Agree (P []) (Q []) n) :
    semWithArgs Ξ X P c n W v ↔ semWithArgs Ξ Y Q (clauseImg tbl κ c) n W v := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  unfold clauseImg
  rw [semWithArgs_map, ← hcr, semWithArgs_map, semWithArgs_map]
  have h : ∀ S, Agree (X (r S)) (Y ((tyImg tbl κ (r S)).getD [])) n ∧
      Agree (P (r S)) (Q ((tyImg tbl κ (r S)).getD [])) n := by
    intro S
    by_cases hS : S ∈ c.operands
    · obtain ⟨T, hT, hx, ha⟩ := himg S hS
      simpa [r, hS, hT] using And.intro hx ha
    · simpa [r, hS, tyImg] using And.intro he hp
  exact semWithArgs_congr _ _ _ _ n (fun _ _ _ _ => Iff.rfl) (fun S => (h S).1) (fun S => (h S).2) c W v

/-- A checked operand image transports a clause read in a row: the built-ins'
invariant is the same of a clause and of its image. -/
theorem clauseImg_row [DecidableEq ι] {G : NormalGraph ι} (tbl : InstTable ι) (κ : Ctx ι)
    (c : Clause (List ι)) (A X Y : List ι → Fam) (P Q : List ι → ArgFam)
    (n : Nat) (W : WorldT n) (v : Val)
    (himg : ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      Agree (X S) (Y T) n ∧ Agree (P S) (Q T) n)
    (he : Agree (X []) (Y []) n) (hp : Agree (P []) (Q []) n) :
    rowSem G A X P c n W v ↔ rowSem G A Y Q (clauseImg tbl κ c) n W v := by
  refine and_congr (clauseImg_value tbl κ c X Y P Q n W v himg he hp) ?_
  unfold clauseImg
  rw [builtinInvariant_map]

/-- The list component of the same checked clause image uses element equality
at this level. Requiring only agreement below it would lose object evidence. -/
theorem clauseImg_arguments [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (c : Clause (List ι)) (X Y : List ι → Fam) (n : Nat) (W : WorldT n) (vs : List Val)
    (himg : ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      ∀ v, X S n W v ↔ Y T n W v)
    (he : ∀ v, X [] n W v ↔ Y [] n W v) :
    clauseArguments X c n W vs ↔ clauseArguments Y (clauseImg tbl κ c) n W vs := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  unfold clauseImg
  rw [clauseArguments_map, ← hcr, clauseArguments_map, clauseArguments_map]
  apply clauseArguments_congr _ _ c n W (fun S v => ?_) vs
  by_cases hS : S ∈ c.operands
  · obtain ⟨T, hT, hx⟩ := himg S hS
    simpa [r, hS, hT] using hx v
  · simpa [r, hS, tyImg] using he v

/-- A label list's members, in the order of `U`. -/
@[nospecialize] def canonIn [DecidableEq ι] (U S : List ι) : List ι := U.filter fun l => decide (l ∈ S)

theorem canonIn_same [DecidableEq ι] {U S : List ι} (h : ∀ l ∈ S, l ∈ U) :
    sameLabels (canonIn U S) S = true := by
  simp only [sameLabels, canonIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_filter]
  exact ⟨fun l hl => hl.2, fun l hl => ⟨h l hl, by simpa using hl⟩⟩

/-- Two clause lists that are the same up to each operand's members: compared
with every operand listed in one order of all their labels. -/
@[nospecialize] def sameClauses [DecidableEq ι] (Cs Ds : List (Clause (List ι))) : Bool :=
  let U := (Cs ++ Ds).flatMap fun c => c.operands.flatten
  Cs.map (·.map (canonIn U)) == Ds.map (·.map (canonIn U))

/-- A clause's meaning depends on its operands' members only. -/
theorem semWithArgs_members [DecidableEq ι] {X : List ι → Fam} {P : List ι → ArgFam}
    (hX : ∀ S T, sameLabels S T = true → X S = X T) (hP : ∀ S T, sameLabels S T = true → P S = P T)
    {f : List ι → List ι} {c : Clause (List ι)}
    (hf : ∀ S ∈ c.operands, sameLabels (f S) S = true) (hnil : sameLabels (f []) [] = true) :
    semWithArgs Ξ X P (c.map f) = semWithArgs Ξ X P c := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [semWithArgs_map, ← hcr, semWithArgs_map, semWithArgs_map]
  have hr : ∀ S, sameLabels (f (r S)) (r S) = true := fun S => by
    by_cases hS : S ∈ c.operands
    · simpa [r, hS] using hf S hS
    · simpa [r, hS] using hnil
  have h1 : (fun a => X (f (r a))) = fun a => X (r a) := funext fun a => hX _ _ (hr a)
  have h2 : (fun a => P (f (r a))) = fun a => P (r a) := funext fun a => hP _ _ (hr a)
  rw [h1, h2]

/-- A clause's argument lists depend on its operands' members only. -/
theorem clauseArguments_members [DecidableEq ι] {X : List ι → Fam}
    (hX : ∀ S T, sameLabels S T = true → X S = X T)
    {f : List ι → List ι} {c : Clause (List ι)}
    (hf : ∀ S ∈ c.operands, sameLabels (f S) S = true) (hnil : sameLabels (f []) [] = true) :
    clauseArguments X (c.map f) = clauseArguments X c := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [clauseArguments_map, ← hcr, clauseArguments_map, clauseArguments_map]
  have hr : ∀ S, sameLabels (f (r S)) (r S) = true := fun S => by
    by_cases hS : S ∈ c.operands
    · simpa [r, hS] using hf S hS
    · simpa [r, hS] using hnil
  have h1 : (fun a => X (f (r a))) = fun a => X (r a) := funext fun a => hX _ _ (hr a)
  rw [h1]

/-- Clause lists the same up to operand members hold the same members of any
property that depends on operand members only. -/
theorem sameClauses_iff [DecidableEq ι] {Cs Ds : List (Clause (List ι))}
    (h : sameClauses Cs Ds = true) (Q : Clause (List ι) → Prop)
    (hQ : ∀ (c : Clause (List ι)) (f : List ι → List ι),
      (∀ S ∈ c.operands, sameLabels (f S) S = true) → sameLabels (f []) [] = true →
      (Q (c.map f) ↔ Q c)) :
    (∃ c ∈ Cs, Q c) ↔ (∃ d ∈ Ds, Q d) := by
  unfold sameClauses at h
  have heq := beq_iff_eq.mp h
  have canon : ∀ c ∈ Cs ++ Ds,
      Q (c.map (canonIn ((Cs ++ Ds).flatMap fun c => c.operands.flatten))) ↔ Q c := fun c hc =>
    hQ c _ (fun S hS => canonIn_same fun l hl =>
      List.mem_flatMap.mpr ⟨c, hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩)
      (by simp [sameLabels, canonIn])
  constructor
  · rintro ⟨c, hc, hq⟩
    have hm := List.mem_map_of_mem (f := (·.map (canonIn ((Cs ++ Ds).flatMap fun c => c.operands.flatten)))) hc
    rw [heq] at hm
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hm
    exact ⟨d, hd, (canon d (List.mem_append_right _ hd)).mp
      (hde ▸ (canon c (List.mem_append_left _ hc)).mpr hq)⟩
  · rintro ⟨d, hd, hq⟩
    have hm := List.mem_map_of_mem (f := (·.map (canonIn ((Cs ++ Ds).flatMap fun c => c.operands.flatten)))) hd
    rw [← heq] at hm
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp hm
    exact ⟨c, hc, (canon c (List.mem_append_left _ hc)).mp
      (hce ▸ (canon d (List.mem_append_right _ hd)).mpr hq)⟩

/-- A plain row and its checked clause image agree on argument lists, including
unions and intersections of tuple shapes. The element images are supplied by
the value-row proof at this level, not by a second recursive unfolding. -/
theorem graphArguments_image [DecidableEq ι] (G : NormalGraph ι)
    (tbl : InstTable ι) (κ : Ctx ι) (η θ : MixedAssignment ι)
    (X Y : List ι → Fam) (i j : ι) (hi : G.plain i = true) (hj : G.plain j = true)
    (hrows : sameClauses (G j) ((G i).map (clauseImg tbl κ)) = true)
    (hY : ∀ S T, sameLabels S T = true → Y S = Y T) (n : Nat) (W : WorldT n) (vs : List Val)
    (himg : ∀ c ∈ G i, ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      ∀ v, X S n W v ↔ Y T n W v)
    (he : ∀ v, X [] n W v ↔ Y [] n W v) :
    graphArguments G η X [i] n W vs ↔ graphArguments G θ Y [j] n W vs := by
  have key := sameClauses_iff hrows (fun d => clauseArguments Y d n W vs)
    (fun c f hf hn => by simp only [clauseArguments_members hY hf hn])
  simp only [graphArguments, List.mem_singleton, exists_eq_left,
    NormalGraph.listParam_of_plain hi, NormalGraph.listParam_of_plain hj, Bool.false_eq_true, if_false]
  rw [key]
  simp only [List.mem_map]
  constructor
  · rintro ⟨c, hc, hv⟩
    exact ⟨_, ⟨c, hc, rfl⟩, (clauseImg_arguments tbl κ c X Y n W vs (himg c hc) he).mp hv⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, hv⟩
    exact ⟨c, hc, (clauseImg_arguments tbl κ c X Y n W vs (himg c hc) he).mpr hv⟩

/-- A bound's image: the target binder at the bound binder's position, and the
bound type's image under the outer context (a bound is read at the scheme's
own assignment, not under its binders). -/
@[nospecialize] def boundImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (src tgt : List ι)
    (b : ι × List ι) : Option (ι × List ι) :=
  match (src.zip (tgt.map ([·]))).lookup b.1 with
  | some [q] => (tyImg tbl κ b.2).map (q, ·)
  | _ => none

/-- The image of a parameter must be in its binder's sort (`sortTy`): its
outer sort, the category of its values and its lists' elements. -/
@[nospecialize] def substitutionKind (G : NormalGraph ι) (b : ι) (U : List ι) : Bool :=
  match G.parameterKinds b with
  | some k => PositiveRules.sortTy G k U
  | none => false

/-- One kind check is shared by instantiation and table substitution. -/
@[nospecialize] def instKinds (G : NormalGraph ι) (bs : List ι) (θs : List (List ι)) : Bool :=
  (bs.zip θs).all fun (b, U) => substitutionKind G b U

/-- The context fixes row `i`: it gives each free row of `i` nothing, or that
parameter row itself (inside a scheme matched against itself, its binders
stand for themselves). -/
@[nospecialize] def fixedBy [DecidableEq ι] (G : NormalGraph ι) (κ : Ctx ι) (V : FreeMap ι) (i : ι) : Bool :=
  (fv V i).all fun p => match κ.lookup p with
    | none => true
    | some U => U == [p] && G.params p

/-- The clause lists a meet row's image meets: each parameter's image's
clauses, then the clauses mapped. -/
@[nospecialize] def meetOperands [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (ps : List ι) (cs : List (Clause (List ι))) : List (List (Clause (List ι))) :=
  ps.map (fun p => clausesOf G ((κ.lookup p).getD [])) ++ [cs.map (clauseImg tbl κ)]

/-- A meet of clause lists, left to right: `A ⊓ B ⊓ …`. -/
def meetMany : List (List (Clause α)) → List (Clause α)
  | [] => []
  | A :: rest => rest.foldl meetLists A

/-- A meet row `ps ⊓ cs`'s image under `κ`, row `j`: with `ps` value
parameters, either a meet row whose parameters are the ones `κ` gives `ps`
(each itself where `κ` gives it nothing), with `cs` mapped, or, when `κ` gives
every one of `ps` a type of clause rows, a value clause row holding the meet
of those types' clauses with `cs` mapped, in the order `ps` then `cs`, or the
reverse. -/
@[nospecialize] def meetOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (ps : List ι) (cs : List (Clause (List ι))) (j : ι) : Bool :=
  ps.all (fun p => G.parameterKinds p == some .value) &&
    cs.all (fun c => c.operands.all fun S => (tyImg tbl κ S).isSome) &&
    match G.meets j with
    | some (q, ds) =>
      !G.params j && (G.schemes j).isNone &&
        (q :: G.meetParams j).all (fun r => G.parameterKinds r == some .value) &&
        ps.all (fun p => (q :: G.meetParams j).any fun r => (κ.lookup p).getD [p] == [r]) &&
        (q :: G.meetParams j).all (fun r => ps.any fun p => (κ.lookup p).getD [p] == [r]) &&
        sameClauses ds (cs.map (clauseImg tbl κ))
    | none =>
      ps.all (fun p => (κ.lookup p).isSome) &&
        G.plain j && (ps.map fun p => (κ.lookup p).getD []).all G.plainTy &&
        G.hasKind .value [j] &&
        (sameClauses (G j) (meetMany (meetOperands G tbl κ ps cs)) ||
          sameClauses (G j) (meetMany (meetOperands G tbl κ ps cs).reverse))

/-- One entry. A parameter row's image is what the context gives it, or itself.
A row the context fixes may be its own image. A clause
row's image is a clause row holding its clauses mapped. A meet row's is
`meetOk`'s. A scheme row's image is
a scheme row with as many binders, distinct parameter rows, whose signatures
are its own mapped with its binders standing for them, provided no free row of
the source, nor any row of a free row's image, is one of those binders. -/
@[nospecialize] def entryOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (V : FreeMap ι)
    (e : ι × Ctx ι × List ι) : Bool :=
  if G.params e.1 then
    e.2.2 == (e.2.1.lookup e.1).getD [e.1] && substitutionKind G e.1 e.2.2
  else if e.2.2 == [e.1] && fixedBy G e.2.1 V e.1 then true
  else match G.schemes e.1, e.2.2 with
    | some s, [j] =>
      match G.schemes j with
      | some s2 =>
        !G.params j && decide s2.binders.Nodup && s2.binders.length == s.binders.length &&
          s2.binders.all G.params &&
          (s.binders.zip s2.binders).all (fun (a,b) => G.parameterKinds a == G.parameterKinds b) &&
          (fv V e.1).all (fun p => match e.2.1.lookup p with
            | some U => U.all fun l => (fv V l).all fun q => !s2.binders.contains q
            | none => !s2.binders.contains p) &&
          s.signatures.mapM (sigImg tbl (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.signatures &&
          s.bounds.mapM (boundImg tbl e.2.1 s.binders s2.binders) == some s2.bounds &&
          s.variadic.mapM (restImg tbl (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.variadic && sameShape s s2
      | none => false
    | none, [j] =>
      match G.meets e.1 with
      | some (p, cs) => meetOk G tbl e.2.1 (p :: G.meetParams e.1) cs j
      | none =>
        G.plain e.1 && G.plain j &&
          (G e.1).all (fun c => c.operands.all fun S => (tyImg tbl e.2.1 S).isSome) &&
          sameClauses (G j) ((G e.1).map (clauseImg tbl e.2.1))
    | _, _ => false

/-- The rows a table mentions. -/
@[nospecialize] def tableRows (tbl : InstTable ι) : List ι :=
  tbl.flatMap fun e => e.1 :: e.2.2 ++ e.2.1.flatMap (·.2)

/-- A checked table: its rows lie in a domain with a sound free-variable
certificate, and every entry is one of `entryOk`'s. -/
@[nospecialize] def TableOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (D : List ι)
    (V : FreeMap ι) : Bool :=
  FreeOk G D V && (tableRows tbl).all (D.contains ·) && tbl.all (entryOk G tbl V)

/-! ### The compiled table check

`TableOk` looks every image up in the whole table, so checking a table's
entries is quadratic in its size, and the tables of a recursive generic
interface run to a thousand entries and more. An entry's lookups are all under
one context, or under the one context it enters, so the compiled check groups
the entries by context once and looks each image up among its context's
entries only. `TableOk_eq_fast` proves the two equal; `csimp` makes the
compiler run the grouped one. What is checked is unchanged. -/

/-- The entries under context `κ`. -/
@[nospecialize] def ctxEntries [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) : InstTable ι :=
  tbl.filter (·.2.1 == κ)

theorem entryImg_ctxEntries [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) :
    entryImg (ctxEntries tbl κ) κ = entryImg tbl κ := by
  funext l
  unfold entryImg ctxEntries
  rw [List.find?_filter]
  congr 2
  funext e
  cases e.1 == l <;> cases e.2.1 == κ <;> rfl

/-- The contexts the table uses. -/
@[nospecialize] def ctxsOf [DecidableEq ι] (tbl : InstTable ι) : List (Ctx ι) := (tbl.map (·.2.1)).eraseDups

/-- The entries of each context the table uses, grouped once. -/
@[nospecialize] def ctxGroups [DecidableEq ι] (tbl : InstTable ι) : List (Ctx ι × InstTable ι) :=
  (ctxsOf tbl).map fun κ => (κ, ctxEntries tbl κ)

/-- A table's rows lie in `D`: each entry's row and image, and the rows of each
context once, not once per entry under it. -/
theorem tableRows_all [DecidableEq ι] (tbl : InstTable ι) (D : List ι) :
    (tableRows tbl).all (D.contains ·) =
      (tbl.all (fun e => (e.1 :: e.2.2).all (D.contains ·)) &&
        (ctxsOf tbl).all fun κ => (κ.flatMap (·.2)).all (D.contains ·)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [tableRows, ctxsOf, Bool.and_eq_true, List.all_eq_true, List.mem_flatMap,
    List.mem_cons, List.mem_append, List.mem_eraseDups, List.mem_map, List.contains_iff_mem]
  constructor
  · intro h
    exact ⟨fun e he x hx => h x ⟨e, he, Or.inl hx⟩,
      fun κ ⟨e, he, hκ⟩ x ⟨b, hb, hx⟩ => h x ⟨e, he, Or.inr ⟨b, hκ ▸ hb, hx⟩⟩⟩
  · rintro ⟨h1, h2⟩ x ⟨e, he, hx | ⟨b, hb, hx⟩⟩
    · exact h1 e he x hx
    · exact h2 e.2.1 ⟨e, he, rfl⟩ x ⟨b, hb, hx⟩

/-- The entries to look an image under `κ` up in: its group, or the whole table. -/
@[nospecialize] def ctxTable [DecidableEq ι] (groups : List (Ctx ι × InstTable ι)) (tbl : InstTable ι)
    (κ : Ctx ι) : InstTable ι :=
  match groups.find? (·.1 == κ) with
  | some g => g.2
  | none => tbl

theorem entryImg_ctxTable [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) :
    entryImg (ctxTable (ctxGroups tbl) tbl κ) κ = entryImg tbl κ := by
  unfold ctxTable
  split
  · rename_i g hg
    have hm := List.mem_of_find?_eq_some hg
    have hk := List.find?_some hg
    simp only [beq_iff_eq] at hk
    simp only [ctxGroups, List.mem_map] at hm
    obtain ⟨κ', _, rfl⟩ := hm
    simp only at hk ⊢
    subst hk
    exact entryImg_ctxEntries tbl _
  · rfl

section
variable [DecidableEq ι] {t u : InstTable ι} {κ : Ctx ι}

theorem tyImg_congr (h : entryImg t κ = entryImg u κ) : tyImg t κ = tyImg u κ := by
  funext S; simp only [tyImg, h]

theorem sigImg_congr (h : entryImg t κ = entryImg u κ) : sigImg t κ = sigImg u κ := by
  funext p; simp only [sigImg, tyImg_congr h]

theorem restImg_congr (h : entryImg t κ = entryImg u κ) : restImg t κ = restImg u κ := by
  funext p; simp only [restImg, tyImg_congr h]

theorem clauseImg_congr (h : entryImg t κ = entryImg u κ) : clauseImg t κ = clauseImg u κ := by
  funext c; simp only [clauseImg, tyImg_congr h]

theorem boundImg_congr (h : entryImg t κ = entryImg u κ) : boundImg t κ = boundImg u κ := by
  funext src tgt b; simp only [boundImg, tyImg_congr h]

theorem meetOk_congr (G : NormalGraph ι) (h : entryImg t κ = entryImg u κ) :
    meetOk G t κ = meetOk G u κ := by
  funext ps cs j; simp only [meetOk, meetOperands, tyImg_congr h, clauseImg_congr h]
end

/-- `entryOk`, each lookup under context `κ` made in `look κ`. -/
@[nospecialize] def entryOkIn [DecidableEq ι] (G : NormalGraph ι) (look : Ctx ι → InstTable ι) (V : FreeMap ι)
    (e : ι × Ctx ι × List ι) : Bool :=
  if G.params e.1 then
    e.2.2 == (e.2.1.lookup e.1).getD [e.1] && substitutionKind G e.1 e.2.2
  else if e.2.2 == [e.1] && fixedBy G e.2.1 V e.1 then true
  else match G.schemes e.1, e.2.2 with
    | some s, [j] =>
      match G.schemes j with
      | some s2 =>
        !G.params j && decide s2.binders.Nodup && s2.binders.length == s.binders.length &&
          s2.binders.all G.params &&
          (s.binders.zip s2.binders).all (fun (a,b) => G.parameterKinds a == G.parameterKinds b) &&
          (fv V e.1).all (fun p => match e.2.1.lookup p with
            | some U => U.all fun l => (fv V l).all fun q => !s2.binders.contains q
            | none => !s2.binders.contains p) &&
          s.signatures.mapM (sigImg (look (enter V e.1 e.2.1 s.binders s2.binders))
            (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.signatures &&
          s.bounds.mapM (boundImg (look e.2.1) e.2.1 s.binders s2.binders) == some s2.bounds &&
          s.variadic.mapM (restImg (look (enter V e.1 e.2.1 s.binders s2.binders))
            (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.variadic && sameShape s s2
      | none => false
    | none, [j] =>
      match G.meets e.1 with
      | some (p, cs) => meetOk G (look e.2.1) e.2.1 (p :: G.meetParams e.1) cs j
      | none =>
        G.plain e.1 && G.plain j &&
          (G e.1).all (fun c => c.operands.all fun S => (tyImg (look e.2.1) e.2.1 S).isSome) &&
          sameClauses (G j) ((G e.1).map (clauseImg (look e.2.1) e.2.1))
    | _, _ => false

theorem entryOkIn_eq [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι)
    (look : Ctx ι → InstTable ι) (V : FreeMap ι)
    (h : ∀ κ, entryImg (look κ) κ = entryImg tbl κ) (e : ι × Ctx ι × List ι) :
    entryOkIn G look V e = entryOk G tbl V e := by
  simp only [entryOkIn, entryOk, sigImg_congr (h _), restImg_congr (h _), boundImg_congr (h _),
    meetOk_congr G (h _), tyImg_congr (h _), clauseImg_congr (h _)]

/-- `TableOk`, grouped by context: what the compiler runs. -/
@[nospecialize] def TableOkFast [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (D : List ι)
    (V : FreeMap ι) : Bool :=
  let ctxs := ctxsOf tbl
  let groups := ctxs.map fun κ => (κ, ctxEntries tbl κ)
  FreeOk G D V &&
    (tbl.all (fun e => (e.1 :: e.2.2).all (D.contains ·)) &&
      ctxs.all fun κ => (κ.flatMap (·.2)).all (D.contains ·)) &&
    tbl.all (entryOkIn G (ctxTable groups tbl) V)

@[csimp] theorem TableOk_eq_fast : @TableOk = @TableOkFast := by
  funext ι _ G tbl D V
  simp only [TableOk, TableOkFast, ← tableRows_all,
    show entryOkIn G (ctxTable ((ctxsOf tbl).map fun κ => (κ, ctxEntries tbl κ)) tbl) V =
      entryOk G tbl V from
      funext (entryOkIn_eq G tbl _ V (entryImg_ctxTable tbl))]

/-- A context relates the component a binder actually observes to its image.
The two-component image retains list bounds; the selected parameter side does
not constrain an unused component of a mixed assignment. -/
@[nospecialize] def RelKWith [DecidableEq ι] (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (κ : Ctx ι) (S : List ι) (ηL ηR : ParameterAssignment k ι) : Prop :=
  ∀ p ∈ S, match κ.lookup p with
    | some U => I.parameter p (ηL.1 p) =
        I.bound ηR (setSem fun i => qDenoteWithArgs G I (ηR, i)) U
    | none => I.parameter p (ηL.1 p) = I.parameter p (ηR.1 p)

/-- A mapped pack or value parameter obeys its table relation at both semantic
components. This does not reinterpret a list as a runtime value. -/
theorem mixed_parameter_image [DecidableEq ι] (G : NormalGraph ι) (κ : Ctx ι)
    (η θ : MixedAssignment ι) (p : ι) (kind : ParameterKind) (U : List ι)
    (hp : G.parameterKinds p = some kind) (hU : κ.lookup p = some U)
    (h : RelKWith G (mixedParameters G) κ [p] η θ) :
    mixedMeaning G η [p] = mixedMeaning G θ U := by
  rw [mixedMeaning_parameter G η p kind hp]
  have he := h p (by simp)
  rw [hU] at he
  change selectParameter (G.parameterKinds p) (η.1 p) = mixedMeaning G θ U at he
  rw [hp] at he
  exact he

theorem entryImg_mem [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} {l : ι} {T : List ι}
    (h : entryImg tbl κ l = some T) : (l, κ, T) ∈ tbl := by
  unfold entryImg at h
  cases hf : tbl.find? (fun e => e.1 == l && e.2.1 == κ) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨a, b, c⟩ := e
    simp only at hp h
    rw [← hp.1, ← hp.2, ← h]
    exact hm

/-- A union maps to the union of its rows' images. -/
theorem tyImg_iff [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} {P Q : ι → Prop} :
    ∀ {S S' : List ι}, tyImg tbl κ S = some S' →
      (∀ l ∈ S, ∀ T, entryImg tbl κ l = some T → (P l ↔ ∃ l' ∈ T, Q l')) →
      ((∃ l ∈ S, P l) ↔ ∃ l' ∈ S', Q l')
  | [], S', h, _ => by
    have : S' = [] := by simpa [tyImg] using h.symm
    subst this; simp
  | l :: S, S', h, hper => by
    unfold tyImg at h
    cases hl : entryImg tbl κ l with
    | none => simp [List.mapM_cons, hl] at h
    | some T =>
      cases hs : S.mapM (entryImg tbl κ) with
      | none => simp [List.mapM_cons, hl, hs] at h
      | some Ts =>
        have hS' : S' = T ++ Ts.flatten := by
          simp [List.mapM_cons, hl, hs] at h; exact h.symm
        subst hS'
        have ih := tyImg_iff (S := S) (S' := Ts.flatten) (by simp [tyImg, hs])
          (fun l' hl' T' hT' => hper l' (List.mem_cons_of_mem _ hl') T' hT')
        have hh := hper l List.mem_cons_self T hl
        simp only [List.mem_cons, List.mem_append, exists_eq_or_imp] at ih ⊢
        constructor
        · rintro (h1 | h2)
          · obtain ⟨l', hl', q⟩ := hh.mp h1; exact ⟨l', .inl hl', q⟩
          · obtain ⟨l', hl', q⟩ := ih.mp h2; exact ⟨l', .inr hl', q⟩
        · rintro ⟨l', hl' | hl', q⟩
          · exact .inl (hh.mpr ⟨l', hl', q⟩)
          · exact .inr (ih.mpr ⟨l', hl', q⟩)

theorem mem_of_lookup [DecidableEq ι] {κ : List (ι × β)} {p : ι} {U : β}
    (h : κ.lookup p = some U) : (p, U) ∈ κ := by
  induction κ with
  | nil => simp at h
  | cons e κ ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases ha : p = a
    · subst ha; simp at h; subst h; exact List.mem_cons_self
    · rw [beq_false_of_ne ha] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_append_none [DecidableEq ι] {xs ys : List (ι × β)} {p : ι}
    (h : xs.lookup p = none) : (xs ++ ys).lookup p = ys.lookup p := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases ha : p = a
    · subst ha; simp at h
    · rw [beq_false_of_ne ha] at h
      simp only [List.cons_append, List.lookup_cons]
      rw [beq_false_of_ne ha]; exact ih h

theorem keep_cons [DecidableEq ι] (κ : Ctx ι) (src : List ι) (q : ι) (ps : List ι) :
    keep κ src (q :: ps) = if q ∈ src then keep κ src ps else
      match κ.lookup q with
      | none => keep κ src ps
      | some U => (q, U) :: keep κ src ps := by
  by_cases hq : q ∈ src
  · simp [keep, hq]
  · cases hk : κ.lookup q <;> simp [keep, hq, hk]

theorem lookup_keep [DecidableEq ι] (κ : Ctx ι) {src : List ι} {p : ι} (hp : p ∉ src) :
    ∀ ps : List ι, (keep κ src ps).lookup p = if p ∈ ps then κ.lookup p else none
  | [] => by simp [keep]
  | q :: ps => by
    rw [keep_cons]
    by_cases hq : q ∈ src
    · have hpq : p ≠ q := fun e => hp (e ▸ hq)
      rw [if_pos hq, lookup_keep κ hp ps]
      simp [hpq]
    · rw [if_neg hq]
      by_cases hpq : p = q
      · subst hpq
        cases hk : κ.lookup p with
        | none => simp only; rw [lookup_keep κ hp ps]; simp [hk]
        | some U => simp
      · cases hk : κ.lookup q with
        | none => simp only; rw [lookup_keep κ hp ps]; simp [hpq]
        | some U =>
          simp only [List.lookup_cons, beq_false_of_ne hpq]
          rw [lookup_keep κ hp ps]; simp [hpq]

/-- Outside the binders, entering changes nothing a free row of the scheme
reads. -/
theorem enter_nmem [DecidableEq ι] (V : FreeMap ι) (i : ι) (κ : Ctx ι) {src tgt : List ι} {p : ι}
    (hp : p ∉ src) (hi : p ∈ fv V i) :
    (enter V i κ src tgt).lookup p = κ.lookup p := by
  unfold enter
  rw [lookup_append_none (lookup_zip_none hp), lookup_keep κ hp, if_pos hi]

/-- A binder entered stands for the binder at its position, and both sides are
given the same family there. -/
theorem enter_binder [DecidableEq ι] (ηL ηR : ParameterAssignment k ι) :
    ∀ {src tgt : List ι} {As : List (ParameterFamily k)} {p : ι} {U : List ι},
      tgt.Nodup → src.length = As.length → tgt.length = As.length →
      (src.zip (tgt.map ([·]))).lookup p = some U →
      ∃ q, U = [q] ∧ (assign ηL src As).1 p = (assign ηR tgt As).1 q
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | b :: src, c :: tgt, [], _, _, _, h1, _, _ => by simp at h1
  | b :: src, c :: tgt, A :: As, p, U, hnd, h1, h2, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons] at h
    by_cases hb : p = b
    · subst hb
      simp only [beq_self_eq_true, Option.some.injEq] at h
      refine ⟨c, h.symm, ?_⟩
      rw [assign_cons_head, assign_cons_head]
    · rw [beq_false_of_ne hb] at h
      obtain ⟨q, hq, he⟩ := enter_binder ηL ηR (List.nodup_cons.mp hnd).2
        (by simpa using h1) (by simpa using h2) h
      refine ⟨q, hq, ?_⟩
      have hqt : q ∈ tgt := by
        have hm := (List.of_mem_zip (mem_of_lookup h)).2
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        rw [hq] at hxe
        cases hxe; exact hx
      have hqc : q ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hqt)
      have e1 := assign_cons_ne ηL src A As hb
      have e2 := assign_cons_ne ηR tgt A As hqc
      rw [e1, e2, he]

theorem mapM_some {f : α → Option α} :
    ∀ {xs ys : List α}, xs.mapM f = some ys → ys = xs.map (fun x => (f x).getD x) ∧
      ∀ x ∈ xs, (f x).isSome
  | [], ys, h => by simp at h; subst h; simp
  | x :: xs, ys, h => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some zs =>
        have hys : ys = y :: zs := by simp [List.mapM_cons, hx, hxs] at h; exact h.symm
        subst hys
        obtain ⟨h1, h2⟩ := mapM_some hxs
        refine ⟨by simp [hx, h1], ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · simp [hx]
        · exact h2 z hz

theorem lookup_zip_isSome [DecidableEq ι] {src : List ι} {ys : List β} {p : ι}
    (h : p ∈ src) (hl : src.length = ys.length) : ∃ U, (src.zip ys).lookup p = some U := by
  induction src generalizing ys with
  | nil => cases h
  | cons b src ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      by_cases hb : p = b
      · subst hb; simp
      · rw [beq_false_of_ne hb]
        exact ih ((List.mem_cons.mp h).resolve_left hb) (by simpa using hl)

theorem lookup_append_some [DecidableEq ι] {xs ys : List (ι × β)} {p : ι} {U : β}
    (h : xs.lookup p = some U) : (xs ++ ys).lookup p = some U := by
  induction xs with
  | nil => simp at h
  | cons e xs ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : p = a
    · subst ha; simp only [List.cons_append, List.lookup_cons, beq_self_eq_true] at h ⊢; exact h
    · simp only [List.lookup_cons, beq_false_of_ne ha] at h
      simp only [List.cons_append, List.lookup_cons, beq_false_of_ne ha]; exact ih h

/-- Renaming a bound parameter assigns the same family to both binders, but
the correspondence compares only their common kind. Arbitrary unused
components remain unrestricted, including under nested universal schemes. -/
theorem mixed_enter_binder [DecidableEq ι] (G : NormalGraph ι) (V : FreeMap ι) (i : ι) (κ : Ctx ι)
    (η θ : MixedAssignment ι) {src tgt : List ι} {As : List MixedFamily} {p : ι}
    (hp : p ∈ src) (hnd : tgt.Nodup) (hs : src.length = As.length) (ht : tgt.length = As.length)
    (hk : ∀ p q, (src.zip (tgt.map ([·]))).lookup p = some [q] →
      ∃ kind, G.parameterKinds p = some kind ∧ G.parameterKinds q = some kind) :
    ∃ q ∈ tgt, (enter V i κ src tgt).lookup p = some [q] ∧
      (mixedParameters G).parameter p ((assign η src As).1 p) =
        mixedMeaning G (assign θ tgt As) [q] := by
  obtain ⟨U, hU⟩ := lookup_zip_isSome (ys := tgt.map ([·])) hp (by simp [hs, ht])
  obtain ⟨q, rfl, he⟩ := enter_binder η θ hnd hs ht hU
  obtain ⟨kind, hpk, hqk⟩ := hk p q hU
  have hq : q ∈ tgt := by
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.of_mem_zip (mem_of_lookup hU)).2
    cases hxe; exact hx
  refine ⟨q, hq, ?_, ?_⟩
  · unfold enter
    exact lookup_append_some hU
  · rw [mixedMeaning_parameter G _ q kind hqk]
    change selectParameter (G.parameterKinds p) _ = _
    rw [hpk, he]

theorem sameLabels_exists [DecidableEq ι] {a b : List ι} (h : sameLabels a b = true)
    (P : ι → Prop) : (∃ i ∈ a, P i) ↔ (∃ i ∈ b, P i) := by
  simp only [sameLabels, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  constructor
  · rintro ⟨i, hi, hp⟩; exact ⟨i, h.1 i hi, hp⟩
  · rintro ⟨i, hi, hp⟩; exact ⟨i, h.2 i hi, hp⟩

theorem sameLabels_values [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {a b : List ι} (h : sameLabels a b = true) : mixedValues G η a = mixedValues G η b := by
  funext n W v
  exact propext (sameLabels_exists h _)

theorem sameLabels_arguments [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {X : List ι → Fam} {a b : List ι} (h : sameLabels a b = true) :
    graphArguments G η X a = graphArguments G η X b := by
  funext n W vs
  exact propext (sameLabels_exists h _)

theorem tysImg_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} :
    ∀ {Ss Ts : List (List ι)}, tysImg tbl κ Ss = some Ts →
      Ts.length = Ss.length ∧ ∀ x ∈ Ss.zip Ts, tyImg tbl κ x.1 = some x.2
  | [], Ts, h => by simp [tysImg] at h; subst h; simp
  | S :: Ss, Ts, h => by
    simp only [tysImg, List.mapM_cons] at h
    cases hS : tyImg tbl κ S with
    | none => simp [hS] at h
    | some T =>
      cases hr : Ss.mapM (tyImg tbl κ) with
      | none => simp [hS, hr] at h
      | some Ts' =>
        simp only [hS, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨hl, hz⟩ := tysImg_some (Ss := Ss) (Ts := Ts') hr
        refine ⟨by simp [hl], ?_⟩
        intro x hx
        simp only [List.zip_cons_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hS
        · exact hz x hx

/-- What `sigPremises` read: the images of the arguments and the result, and
of the receiver unless the scheme's receiver admits the target's. -/
theorem sigPremises_some [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {κ : Ctx ι}
    {p q : Arrow (List ι)} {prs : List (List ι × List ι)} (h : sigPremises G tbl κ p q = some prs) :
    p.arguments.length = q.arguments.length ∧ p.effect.covers q.effect = true ∧
    ∃ ps r, tysImg tbl κ p.arguments = some ps ∧ tyImg tbl κ p.result = some r ∧
      (q.arguments.zip ps ++ [(r, q.result)] ⊆ prs) ∧
      (receiverUniverse G p.receiver q.receiver = true ∨
        ∃ rc, tyImg tbl κ p.receiver = some rc ∧ (q.receiver, rc) ∈ prs) := by
  unfold sigPremises at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    split at h
    · rename_i ps r hps hr
      refine ⟨hc.1, hc.2, ps, r, hps, hr, ?_⟩
      split at h
      · rename_i hu
        cases h
        exact ⟨List.Subset.refl _, .inl hu⟩
      · cases hrc : tyImg tbl κ p.receiver with
        | none => simp [hrc] at h
        | some rc =>
          simp only [hrc, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨List.subset_cons_self _ _, .inr ⟨rc, rfl, List.mem_cons_self⟩⟩
    · cases h
  · cases h

/-- What `restPremises` read. -/
theorem restPremises_some [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {κ : Ctx ι}
    {p q : RestArrow (List ι)} {prs : List (List ι × List ι)} (h : restPremises G tbl κ p q = some prs) :
    p.arguments.1.length = q.arguments.1.length ∧ p.effect.covers q.effect = true ∧
    ∃ ps e r, tysImg tbl κ p.arguments.1 = some ps ∧ tyImg tbl κ p.arguments.2 = some e ∧
      tyImg tbl κ p.result = some r ∧
      (q.arguments.1.zip ps ++ [(q.arguments.2, e), (r, q.result)] ⊆ prs) ∧
      (receiverUniverse G p.receiver q.receiver = true ∨
        ∃ rc, tyImg tbl κ p.receiver = some rc ∧ (q.receiver, rc) ∈ prs) := by
  unfold restPremises at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    split at h
    · rename_i ps e r hps he hr
      refine ⟨hc.1, hc.2, ps, e, r, hps, he, hr, ?_⟩
      split at h
      · rename_i hu
        cases h
        exact ⟨List.Subset.refl _, .inl hu⟩
      · cases hrc : tyImg tbl κ p.receiver with
        | none => simp [hrc] at h
        | some rc =>
          simp only [hrc, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨List.subset_cons_self _ _, .inr ⟨rc, rfl, List.mem_cons_self⟩⟩
    · cases h
  · cases h

/-- Positions included pairwise, as values, are pointwise wider. -/
theorem argsLe_of_zip {G : NormalGraph ι} {η : MixedAssignment ι} :
    ∀ {as bs : List (List ι)}, as.length = bs.length →
      (∀ x ∈ as.zip bs, FamLe (mixedMeaning G η x.1) (mixedMeaning G η x.2)) →
      ArgsLe (as.map (mixedValues G η)) (bs.map (mixedValues G η))
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    refine .cons (fun n W v hv => h (a, b) (by simp) n W (.inl v) hv)
      (argsLe_of_zip hl fun x hx => h x (by simp [hx]))

/-- A type whose one clause is `top` holds every closed value. -/
theorem top_row_mixed {G : NormalGraph ι} {η : MixedAssignment ι} {S : List ι}
    (h : expand G S = [.top]) {n W v} (hv : isVal v = true ∧ Scoped 0 v) :
    mixedValues G η S n W v :=
  mixed_of_expand h ⟨hv, builtinInvariant_of_withoutInvariant rfl n W v⟩

/-- A type holding the built-ins' `unknown`: one of its labels is a clause row
with a `source` clause. -/
@[nospecialize] def unknownTy (G : NormalGraph ι) (T : List ι) : Bool :=
  T.any fun t => (G t).any fun c => match c with | .source => true | _ => false

/-- A value of the built-ins' `unknown` is a member of a type holding it. -/
theorem unknownTy_sound {G : NormalGraph ι} {η : MixedAssignment ι} {T : List ι}
    (h : unknownTy G T = true) {n W v} (hv : excOf G n W v) : mixedValues G η T n W v := by
  obtain ⟨t, ht, hp⟩ := List.any_eq_true.mp h
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp hp
  cases c <;> simp only [Bool.false_eq_true] at hs
  exact mixed_expand_mpr ⟨.source, List.mem_flatMap.mpr ⟨t, ht, hc⟩, hv⟩

/-- A type of the built-ins' `unknown` alone: each label a clause row of `source`
clauses only. -/
@[nospecialize] def exactUnknown (G : NormalGraph ι) (U : List ι) : Bool :=
  U.all fun u => G.plain u && (G u).all fun c => match c with | .source => true | _ => false

/-- A member of a type of the built-ins' `unknown` alone is of the exception family. -/
theorem exactUnknown_sound {G : NormalGraph ι} {η : MixedAssignment ι} {U : List ι}
    (h : exactUnknown G U = true) {n W v} (hv : mixedValues G η U n W v) : excOf G n W v := by
  obtain ⟨u, hu, hv⟩ := hv
  have hp := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨c, hc, hrow⟩ := (mixed_unfold_plain η hp.1 n W v).mp hv
  have hs := hp.2 c hc
  cases c <;> simp only [Bool.false_eq_true] at hs
  exact hrow

theorem sigImg_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : Arrow (List ι)} (h : sigImg tbl κ p = some q) :
    tyImg tbl κ p.receiver = some q.receiver ∧ p.arguments.mapM (tyImg tbl κ) = some q.arguments ∧
      tyImg tbl κ p.result = some q.result ∧ p.effect = q.effect := by
  unfold sigImg at h
  cases h1 : tyImg tbl κ p.receiver with
  | none => simp [h1] at h
  | some a =>
    cases h2 : p.arguments.mapM (tyImg tbl κ) with
    | none => simp [h1, h2] at h
    | some b =>
      cases h3 : tyImg tbl κ p.result with
      | none => simp [h1, h2, h3] at h
      | some c =>
        simp [h1, h2, h3] at h
        subst h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem restImg_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : RestArrow (List ι)} (h : restImg tbl κ p = some q) :
    tyImg tbl κ p.receiver = some q.receiver ∧ p.arguments.1.mapM (tyImg tbl κ) = some q.arguments.1 ∧
      tyImg tbl κ p.arguments.2 = some q.arguments.2 ∧ tyImg tbl κ p.result = some q.result ∧ p.effect = q.effect := by
  unfold restImg at h
  cases h1 : tyImg tbl κ p.receiver with
  | none => simp [h1] at h
  | some a =>
    cases h2 : p.arguments.1.mapM (tyImg tbl κ) with
    | none => simp [h1, h2] at h
    | some b =>
      cases h3 : tyImg tbl κ p.arguments.2 with
      | none => simp [h1, h2, h3] at h
      | some c =>
        cases h4 : tyImg tbl κ p.result with
        | none => simp [h1, h2, h3, h4] at h
        | some d =>
          simp [h1, h2, h3, h4] at h
          subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A context fixing a row relates the two assignments on its free rows as
equal parameters. -/
theorem fixedBy_rel [DecidableEq ι] {G : NormalGraph ι} {κ : Ctx ι} {V : FreeMap ι} {i : ι}
    {ηL ηR : MixedAssignment ι} (hfix : fixedBy G κ V i = true)
    (hrel : RelKWith G (mixedParameters G) κ (fv V i) ηL ηR) :
    ∀ p ∈ fv V i, (mixedParameters G).parameter p (ηL.1 p) =
      (mixedParameters G).parameter p (ηR.1 p) := by
  intro p hp
  have hr := hrel p hp
  have hf := List.all_eq_true.mp hfix p hp
  cases hk : κ.lookup p with
  | none => rw [hk] at hr; exact hr
  | some U =>
    rw [hk] at hr hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, hpar⟩ := hf
    obtain ⟨kind, hkind⟩ : ∃ kind, G.parameterKinds p = some kind := by
      simpa [NormalGraph.params, Option.isSome_iff_exists] using hpar
    change selectParameter (G.parameterKinds p) (ηL.1 p) = mixedMeaning G ηR [p] at hr
    rw [mixedMeaning_parameter G ηR p kind hkind] at hr
    change selectParameter (G.parameterKinds p) (ηL.1 p) = selectParameter (G.parameterKinds p) (ηR.1 p)
    rw [hkind]; rw [hkind] at hr; exact hr

/-- A meet row, as a parameter row, has no argument lists. -/
theorem meet_noArguments {G : NormalGraph ι} {σ : MixedAssignment ι} {l : ι}
    {pc : ι × List (Clause (List ι))} (hl : G.params l = false) (hm : G.meets l = some pc)
    {n : Nat} {W : WorldT n} {vs : List Val} : ¬ mixedMeaning G σ [l] n W (.inr vs) := by
  have hk : G.parameterKinds l = none := by simpa [NormalGraph.params] using hl
  simp [mixedMeaning, mixedParameters, graphArguments, hk, NormalGraph.clauses,
    NormalGraph.plain, hm, NormalGraph.listParam]

/-- A meet row's image has no argument lists either. -/
theorem meetOk_noArguments [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι}
    {κ : Ctx ι} {ps : List ι} {cs : List (Clause (List ι))} {j : ι}
    (hok : meetOk G tbl κ ps cs j = true)
    (σ : MixedAssignment ι) {n : Nat} (W : WorldT n) (vs : List Val) :
    ¬ mixedMeaning G σ [j] n W (.inr vs) := by
  unfold meetOk at hok
  cases hmj : G.meets j with
  | some qd =>
    simp only [hmj, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact meet_noArguments hok.2.1.1.1.1.1 hmj
  | none =>
    simp only [hmj, Bool.and_eq_true] at hok
    exact mixedMeaning_noArguments G σ [j] hok.2.1.2 n W vs

/-- A meet of several clause lists holds what each of them holds. -/
theorem meetMany_row (G : NormalGraph ι) (Z X : List ι → Fam) (P : List ι → ArgFam)
    (Ls : List (List (Clause (List ι)))) (hne : Ls ≠ []) (n W v) :
    setSem (rowSem G Z X P) (meetMany Ls) n W v ↔
      ∀ L ∈ Ls, setSem (rowSem G Z X P) L n W v := by
  cases Ls with
  | nil => contradiction
  | cons A rest =>
    induction rest generalizing A with
    | nil => simp [meetMany]
    | cons B rest ih =>
      have h := ih (meetLists A B) (List.cons_ne_nil _ _)
      simp only [meetMany, List.foldl_cons] at h ⊢
      rw [h]
      simp only [List.mem_cons, forall_eq_or_imp, meetLists_row]
      constructor
      · rintro ⟨⟨ha, hb⟩, hr⟩; exact ⟨ha, hb, hr⟩
      · rintro ⟨ha, hb, hr⟩; exact ⟨⟨ha, hb⟩, hr⟩

/-- A meet row's parameter, read at the image its context gives it: itself
where the context gives it nothing. -/
theorem meet_param_image [DecidableEq ι] {G : NormalGraph ι} {κ : Ctx ι} {p : ι}
    {ηL ηR : MixedAssignment ι} {n : Nat} {W : WorldT n} {v : Val}
    (hpk : G.parameterKinds p = some .value)
    (hr : RelKWith G (mixedParameters G) κ [p] ηL ηR) :
    ηL.1 p n W (.inl v) ↔ mixedValues G ηR ((κ.lookup p).getD [p]) n W v := by
  have hsel : ∀ A : WorldFamily ParameterSpace.mixed.Carrier,
      (mixedParameters G).parameter p A n W (.inl v) ↔ A n W (.inl v) := by
    intro A; simp [mixedParameters, selectParameter, hpk]
  have h := hr p (List.mem_singleton_self p)
  cases hU : κ.lookup p with
  | none =>
    rw [hU] at h
    simp only [Option.getD_none]
    rw [← hsel (ηL.1 p), h, hsel]
    change _ ↔ mixedMeaning G ηR [p] n W (.inl v)
    rw [mixedMeaning_parameter G ηR p .value hpk]
    simp [selectParameter]
  | some U =>
    rw [hU] at h
    simp only [Option.getD_some]
    rw [← hsel (ηL.1 p), h]; rfl

/-- **A meet row means its image.** Under a context relating the meet row's
parameters, and with its clauses' images, `ps ⊓ cs` means the meet row of the
parameters' images, or, when the context gives each of `ps` a type of clause
rows, the clause row holding the meet of those types' clauses with the
clauses' images: the value is in each and in the clauses, which
`meetLists_row` makes one clause list. -/
theorem meet_row_value [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {κ : Ctx ι}
    {i j p : ι} {cs : List (Clause (List ι))} {ηL ηR : MixedAssignment ι} {n : Nat}
    {W : WorldT n} {v : Val}
    (hpar : G.params i = false) (hsch : G.schemes i = none) (hm : G.meets i = some (p, cs))
    (hok : meetOk G tbl κ (p :: G.meetParams i) cs j = true)
    (hrel : RelKWith G (mixedParameters G) κ (p :: G.meetParams i) ηL ηR)
    (hcl : ∀ c ∈ cs, mixedSem G ηL c n W v ↔ mixedSem G ηR (clauseImg tbl κ c) n W v) :
    qDenoteWithArgs G (mixedParameters G) (ηL, i) n W v ↔ mixedValues G ηR [j] n W v := by
  unfold meetOk at hok
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hpk, _⟩, hok⟩ := hok
  -- The meet row: each parameter's image, within the clauses' images.
  have hval : ∀ q ∈ p :: G.meetParams i,
      (partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηL q n W v ↔
      mixedValues G ηR ((κ.lookup q).getD [q]) n W v) := by
    intro q hq
    rw [partSemWithArgs_param (by simp [NormalGraph.params, hpk q hq])]
    simp [mixedParameters, hpk q hq, selectParameter]
    exact meet_param_image (hpk q hq) (fun r hr => by
      cases List.mem_singleton.mp hr; exact hrel q hq)
  have hL : qDenoteWithArgs G (mixedParameters G) (ηL, i) n W v ↔
      (∀ q ∈ p :: G.meetParams i, mixedValues G ηR ((κ.lookup q).getD [q]) n W v) ∧
        setSem (mixedSem G ηR) (cs.map (clauseImg tbl κ)) n W v := by
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hpar, hsch, hm, Bool.false_eq_true, ite_false]
    refine and_congr ?_ ⟨?_, ?_⟩
    · rw [List.forall_mem_cons]
      exact and_congr (hval p List.mem_cons_self)
        (forall₂_congr fun q hq => hval q (List.mem_cons_of_mem _ hq))
    · rintro ⟨c, hc, h⟩
      exact ⟨_, List.mem_map_of_mem hc, (hcl c hc).mp h⟩
    · rintro ⟨_, hc', h⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
      exact ⟨c, hc, (hcl c hc).mpr h⟩
  have hsingle : mixedValues G ηR [j] n W v ↔ qDenoteWithArgs G (mixedParameters G) (ηR, j) n W v :=
    ⟨fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h,
     fun h => ⟨j, List.mem_singleton_self j, h⟩⟩
  have members : ∀ {Cs Ds : List (Clause (List ι))}, sameClauses Cs Ds = true →
      (setSem (mixedSem G ηR) Cs n W v ↔ setSem (mixedSem G ηR) Ds n W v) := fun h =>
    sameClauses_iff h (fun d => mixedSem G ηR d n W v) (fun c f hf hn => by
      simp only [rowSem, semWithArgs_members (fun S T h => sameLabels_values h)
        (fun S T h => sameLabels_arguments h) hf hn, builtinInvariant_map])
  rw [hL, hsingle]
  cases hmj : G.meets j with
  | some qd =>
    -- A meet row of the parameters' images.
    obtain ⟨q, ds⟩ := qd
    simp only [hmj, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
      beq_iff_eq, Option.isNone_iff_eq_none] at hok
    obtain ⟨⟨⟨⟨⟨hjp, hjs⟩, hrk⟩, hfwd⟩, hbwd⟩, hds⟩ := hok
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hjp, hjs, hmj, Bool.false_eq_true, ite_false]
    refine and_congr ?_ (members hds).symm
    have hrv : ∀ r ∈ q :: G.meetParams j,
        (mixedValues G ηR [r] n W v ↔ (mixedParameters G).value r (ηR.1 r) n W v) := by
      intro r hr
      simp [mixedParameters, hrk r hr, selectParameter]
      change mixedMeaning G ηR [r] n W (.inl v) ↔ _
      rw [mixedMeaning_parameter G ηR r .value (hrk r hr)]
      simp [selectParameter]
    have hrv : ∀ r ∈ q :: G.meetParams j,
        (mixedValues G ηR [r] n W v ↔
          partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηR r n W v) := by
      intro r hr
      rw [partSemWithArgs_param (by simp [NormalGraph.params, hrk r hr])]
      exact hrv r hr
    have hR : (partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηR q n W v ∧
        ∀ r ∈ G.meetParams j,
          partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηR r n W v) ↔
        ∀ r ∈ q :: G.meetParams j, mixedValues G ηR [r] n W v := by
      rw [List.forall_mem_cons]
      exact and_congr (hrv q List.mem_cons_self).symm
        (forall₂_congr fun r hr => (hrv r (List.mem_cons_of_mem _ hr)).symm)
    rw [hR]
    constructor
    · intro h r hr
      obtain ⟨p', hp', he⟩ := hbwd r hr
      rw [← he]; exact h p' hp'
    · intro h p' hp'
      obtain ⟨r, hr, he⟩ := hfwd p' hp'
      rw [he]; exact h r hr
  | none =>
    -- A clause row holding the meet of the parameters' images with the clauses.
    simp only [hmj, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨hsome, hjplain⟩, hUplain⟩, _⟩, horder⟩ := hok
    have hparts : ∀ q ∈ p :: G.meetParams i,
        (mixedValues G ηR ((κ.lookup q).getD [q]) n W v ↔
          setSem (mixedSem G ηR) (clausesOf G ((κ.lookup q).getD [])) n W v) := by
      intro q hq
      obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (hsome q hq)
      have hpl : G.plainTy U = true := by
        have := hUplain _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
        simpa [hU] using this
      simp only [hU, Option.getD_some]
      rw [mixed_expand ηR hpl n W v, expand_of_plain hpl]
    have hops : (∀ L ∈ meetOperands G tbl κ (p :: G.meetParams i) cs,
        setSem (mixedSem G ηR) L n W v) ↔
        ((∀ q ∈ p :: G.meetParams i, mixedValues G ηR ((κ.lookup q).getD [q]) n W v) ∧
          setSem (mixedSem G ηR) (cs.map (clauseImg tbl κ)) n W v) := by
      simp only [meetOperands, List.mem_append, List.mem_map, List.mem_singleton]
      constructor
      · intro h
        exact ⟨fun q hq => (hparts q hq).mpr (h _ (.inl ⟨q, hq, rfl⟩)), h _ (.inr rfl)⟩
      · rintro ⟨h1, h2⟩ L (⟨q, hq, rfl⟩ | rfl)
        · exact (hparts q hq).mp (h1 q hq)
        · exact h2
    have hne : meetOperands G tbl κ (p :: G.meetParams i) cs ≠ [] := by simp [meetOperands]
    rw [mixed_unfold_plain ηR hjplain n W v]
    rcases horder with h | h
    · rw [members h, meetMany_row G _ _ _ _ hne]
      exact hops.symm
    · rw [members h, meetMany_row G _ _ _ _ (by simpa using hne)]
      simp only [List.mem_reverse]
      exact hops.symm

/-- The argument half of table transport uses the value half at exactly the
same level. It covers every checked entry, including parameters, unchanged
rows and schemes; it does not assume the table contains only tuple rows. -/
theorem table_row_arguments [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι}
    {D : List ι} {V : FreeMap ι} (hok : TableOk G tbl D V = true) (n : Nat)
    (hv : ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) v, qDenoteWithArgs G (mixedParameters G) (η, e.1) n W v ↔
        mixedMeaning G θ e.2.2 n W (.inl v)) :
    ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) vs, mixedMeaning G η [e.1] n W (.inr vs) ↔
        mixedMeaning G θ e.2.2 n W (.inr vs) := by
  simp only [TableOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hF, hrows⟩, hents⟩ := hok
  rintro η θ ⟨i, κ, T⟩ he hrel W vs
  have hiD : i ∈ D := by
    have := hrows i (List.mem_flatMap.mpr ⟨(i, κ, T), he, List.mem_cons_self⟩)
    simpa using this
  have ⟨hself, hreads, _⟩ := freeOk_row hF hiD
  have hrow := hents _ he
  simp only [entryOk] at hrow
  cases hp : G.params i
  · simp only [hp, Bool.false_eq_true, if_false] at hrow
    by_cases hrig : (T == [i] && fixedBy G κ V i) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hrig
      obtain ⟨rfl, hfix⟩ := hrig
      have h := graphArguments_free hF _
        (agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF)) η θ [i]
        (fun l hl => by cases List.mem_singleton.mp hl; exact hiD)
        (fun l hl p hp' => by
          cases List.mem_singleton.mp hl
          exact fixedBy_rel hfix hrel p hp')
      exact iff_of_eq (congrFun (congrFun (congrFun h n) W) vs)
    · have hrigF : (T == [i] && fixedBy G κ V i) = false := by
        simpa using hrig
      simp only [hrigF, Bool.false_eq_true, if_false] at hrow
      cases hs : G.schemes i with
      | some s =>
        cases T with
        | nil => simp [hs] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hs] at hrow
          | nil =>
            cases ht : G.schemes j with
            | none => simp [hs, ht] at hrow
            | some t =>
              have hj : G.params j = false := by
                simp only [hs, ht, Bool.and_eq_true, Bool.not_eq_true'] at hrow
                exact hrow.1.1.1.1.1.1.1.1.1
              have noArgs : ∀ (σ : MixedAssignment ι) l,
                  G.params l = false → G.schemes l ≠ none →
                  ¬ mixedMeaning G σ [l] n W (.inr vs) := by
                intro σ l hl hsch
                have hk : G.parameterKinds l = none := by simpa [NormalGraph.params] using hl
                simp [mixedMeaning, mixedParameters, graphArguments, hk,
                  NormalGraph.clauses, NormalGraph.plain, hsch, NormalGraph.listParam]
              -- A scheme contributes values only, regardless of its binders.
              exact iff_of_false (noArgs η i hp (by simp [hs]))
                (noArgs θ j hj (by simp [ht]))
      | none =>
        cases T with
        | nil => simp [hs] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hs] at hrow
          | nil =>
            cases hm : G.meets i with
            | some pc =>
              simp only [hs, hm] at hrow
              exact iff_of_false (meet_noArguments hp hm) (meetOk_noArguments hrow θ W vs)
            | none =>
            simp only [hs, hm, Bool.and_eq_true, List.all_eq_true] at hrow
            obtain ⟨⟨⟨hip, hjp⟩, hops⟩, hG⟩ := hrow
            apply graphArguments_image G tbl κ η θ _ _ i j hip hjp hG
              (fun S T h => sameLabels_values h) n W vs
            · intro c hc S hS
              obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (hops c hc S hS)
              refine ⟨U, hU, fun v => tyImg_iff hU fun l hl T hT => ?_⟩
              apply hv η θ (l, κ, T) (entryImg_mem hT) _ W v
              intro p hp'
              have hlr : l ∈ reads G i := by
                simp only [reads, hs]
                exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
              rcases (hreads l hlr).2 p hp' with h | ⟨s', hs', _⟩
              · exact hrel p h
              · rw [hs] at hs'; cases hs'
            · intro v; simp [setSem, mixedValues]
  · simp only [hp, if_true, Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨rfl, _⟩ := hrow
    have hr := hrel i (hself hp)
    obtain ⟨kind, hk⟩ : ∃ kind, G.parameterKinds i = some kind := by
      simpa [NormalGraph.params, Option.isSome_iff_exists] using hp
    rw [mixedMeaning_parameter G η i kind hk]
    cases hκ : κ.lookup i with
    | none =>
      rw [hκ] at hr
      simp only [Option.getD_none]
      rw [mixedMeaning_parameter G θ i kind hk]
      change selectParameter (G.parameterKinds i) _ = selectParameter (G.parameterKinds i) _ at hr
      rw [hk] at hr
      rw [hr]
    | some U =>
      rw [hκ] at hr
      simp only [Option.getD_some]
      change selectParameter (G.parameterKinds i) _ = mixedMeaning G θ U at hr
      rw [hk] at hr
      rw [hr]

/-- Closing one level of a mixed table proof needs only its value images:
the argument images follow at that same level. In the recursive proof the
value step may use both components at strictly smaller levels. -/
theorem table_row_mixed_of_values [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι}
    {D : List ι} {V : FreeMap ι} (hok : TableOk G tbl D V = true) (n : Nat)
    (hv : ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) v, qDenoteWithArgs G (mixedParameters G) (η, e.1) n W v ↔
        mixedMeaning G θ e.2.2 n W (.inl v)) :
    ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) x, mixedMeaning G η [e.1] n W x ↔
        mixedMeaning G θ e.2.2 n W x := by
  intro η θ e he hrel W x
  cases x with
  | inl v =>
    change (∃ i ∈ [e.1], qDenoteWithArgs G (mixedParameters G) (η, i) n W v) ↔ _
    simpa only [List.mem_singleton, exists_eq_left] using hv η θ e he hrel W v
  | inr vs => exact table_row_arguments hok n hv η θ e he hrel W vs

private theorem tyImg_mixed_iff [DecidableEq ι] {G : NormalGraph ι}
    {tbl : InstTable ι} {κ : Ctx ι} {S T : List ι} (h : tyImg tbl κ S = some T)
    {η : MixedAssignment ι} {n : Nat} {W : WorldT n} {x : Val ⊕ List Val}
    {P : ι → Prop}
    (hr : ∀ i ∈ S, ∀ U, entryImg tbl κ i = some U →
      (P i ↔ mixedMeaning G η U n W x)) :
    (∃ i ∈ S, P i) ↔ mixedMeaning G η T n W x := by
  rw [mixedMeaning_union]
  exact tyImg_iff h (fun i hi U hU => (hr i hi U hU).trans (mixedMeaning_union G η U n W x))

/-- **Instance tables.** Under its context, an entry's row means its image. -/
theorem table_row_mixed [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {D : List ι}
    {V : FreeMap ι} (hok : TableOk G tbl D V = true) :
    ∀ n, ∀ ηL ηR : MixedAssignment ι, ∀ e ∈ tbl, RelKWith G (mixedParameters G) e.2.1 (fv V e.1) ηL ηR →
      ∀ (W : WorldT n) x, mixedMeaning G ηL [e.1] n W x ↔ mixedMeaning G ηR e.2.2 n W x := by
  have checked := hok
  simp only [TableOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hF, hrowsD⟩, hents⟩ := hok
  have inD : ∀ e ∈ tbl, e.1 ∈ D ∧ (∀ l ∈ e.2.2, l ∈ D) ∧
      ∀ p U, e.2.1.lookup p = some U → ∀ l ∈ U, l ∈ D := by
    intro e he
    have h := fun l hl => by simpa using hrowsD l hl
    refine ⟨h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_self⟩),
      fun l hl => h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _ (List.mem_append_left _ hl)⟩),
      fun p U hU l hl => h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(p, U), mem_of_lookup hU, hl⟩))⟩)⟩
  have singleton : ∀ (η : MixedAssignment ι) (j : ι) m (U : WorldT m) u,
      mixedValues G η [j] m U u ↔ qDenoteWithArgs G (mixedParameters G) (η, j) m U u := fun η j m U u =>
    ⟨fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h,
     fun h => ⟨j, List.mem_singleton_self j, h⟩⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  apply table_row_mixed_of_values checked n
  rintro ηL ηR ⟨i, κ, T⟩ he hrel W v
  change qDenoteWithArgs G (mixedParameters G) (ηL,i) n W v ↔ mixedValues G ηR T n W v
  have hrow := hents _ he
  obtain ⟨hiD, _, hκD⟩ := inD _ he
  have ⟨hself, hreads, hbounds⟩ := freeOk_row hF hiD
  simp only at hrel hiD hκD
  -- A type whose rows have entries under a context, related on their free
  -- rows, means its image below the budget.
  have hty : ∀ (ηL' ηR' : MixedAssignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelKWith G (mixedParameters G) κ' (fv V l) ηL' ηR') →
      Agree (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (ηL', l)) S) (mixedValues G ηR' S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U u
    exact tyImg_iff hS fun l hl T hT => by
      have h := ih m hm ηL' ηR' (l, κ', T) (entryImg_mem hT) (hrl l hl) U (.inl u)
      simpa [mixedMeaning, mixedParameters, setSem] using h
  have hmix : ∀ (ηL' ηR' : MixedAssignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelKWith G (mixedParameters G) κ' (fv V l) ηL' ηR') →
      Agree (mixedMeaning G ηL' S) (mixedMeaning G ηR' S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U x
    rw [mixedMeaning_union]
    exact tyImg_mixed_iff hS fun l hl T hT =>
      ih m hm ηL' ηR' (l, κ', T) (entryImg_mem hT) (hrl l hl) U x
  have hpack : ∀ (ηL' ηR' : MixedAssignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelKWith G (mixedParameters G) κ' (fv V l) ηL' ηR') →
      Agree (graphArguments G ηL' (mixedValues G ηL') S)
        (graphArguments G ηR' (mixedValues G ηR') S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U vs
    exact hmix ηL' ηR' κ' S S' hS hrl m hm U (.inr vs)
  simp only [entryOk] at hrow
  cases hpar : G.params i
  · simp only [hpar, Bool.false_eq_true, if_false] at hrow
    by_cases hrig : (T == [i] && fixedBy G κ V i) = true
    · -- its own image, the context fixing its free rows
      simp only [Bool.and_eq_true, beq_iff_eq] at hrig
      obtain ⟨rfl, hfix⟩ := hrig
      rw [singleton]
      rw [agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF) ηL ηR i hiD
        (fixedBy_rel hfix hrel)]
    · have hrigF : (T == [i] && fixedBy G κ V i) = false := by
        simpa using hrig
      simp only [hrigF, Bool.false_eq_true, if_false] at hrow
      cases hsch : G.schemes i with
      | some s =>
        cases hT : T with
        | nil => simp [hsch, hT] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, hT] at hrow
          | nil =>
            simp only [hsch, hT] at hrow
            cases hs2 : G.schemes j with
            | none => simp [hs2] at hrow
            | some s2 =>
            simp only [hs2, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq,
              List.all_eq_true] at hrow
            obtain ⟨hrow, hord⟩ := hrow
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨hjp, hnd⟩, hlen⟩, hpars⟩, hkinds⟩, hcap⟩, hsigs⟩, hbnds⟩, hrests⟩ := hrow
            rw [singleton, qDenoteWithArgs_unfold, qDenoteWithArgs_unfold]
            simp only [qLayerWithArgs, hpar, hjp, hsch, hs2, Bool.false_eq_true, if_false]
            change boundedSem _ ηL s _ G.domain n W v ↔ boundedSem _ ηR s2 _ G.domain n W v
            refine and_congr (by rw [sameShape_construct hord]) ?_
            rw [hlen]
            refine forall_congr' fun qlevel => forall_congr' fun hlevel => forall_congr' fun As => forall_congr' fun hlA =>
              imp_congr (sameShape_allowed G.domain hord As) (imp_congr ?_ ?_)
            · -- Each bound maps to the target's: the same family on the binders,
              -- and the bound types related at the outer assignments.
              obtain ⟨hbmap, hbsome⟩ := mapM_some hbnds
              unfold Bounded
              rw [hbmap]
              simp only [List.forall_mem_map]
              refine forall_congr' fun b => forall_congr' fun hb => ?_
              obtain ⟨⟨q, B'⟩, hbi⟩ := Option.isSome_iff_exists.mp (hbsome b hb)
              simp only [hbi, Option.getD_some]
              unfold boundImg at hbi
              split at hbi
              · rename_i q' hU
                obtain ⟨B'', hB'', hqB⟩ := Option.map_eq_some_iff.mp hbi
                cases hqB
                obtain ⟨q'', hq'', he⟩ := enter_binder ηL ηR hnd hlA.symm (hlen.trans hlA.symm) hU
                cases hq''
                have hb1 : b.1 ∈ s.binders := (List.of_mem_zip (mem_of_lookup hU)).1
                have hq2 : q ∈ s2.binders := by
                  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.of_mem_zip (mem_of_lookup hU)).2
                  cases hxe; exact hx
                refine imp_congr (iff_of_true hb1 hq2) (forall_congr' fun j => forall_congr' fun hj =>
                  forall_congr' fun U => forall_congr' fun u => imp_congr (by rw [he]) ?_)
                have hbr : ∀ l ∈ b.2, l ∈ reads G i ∧ l ∈ boundReads G i := by
                  intro l hl'
                  refine ⟨?_, ?_⟩
                  · simp only [reads, hsch]
                    exact List.mem_append_left _
                      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hl'⟩))
                  · simp only [boundReads, hsch]
                    exact List.mem_flatMap.mpr ⟨b, hb, hl'⟩
                exact hmix ηL ηR κ b.2 _ hB''
                  (fun l hl p hp => hrel p (hbounds l (hbr l hl).2 p hp)) j (by omega) U u
              · simp at hbi
            have hty := fun a b c d e f g => Agree.mono (hty a b c d e f g) hlevel
            have hpack := fun a b c d e f g => Agree.mono (hpack a b c d e f g) hlevel
            let W := trunc qlevel hlevel W
            let n := qlevel
            -- Inside, the relation holds on each signature row's free rows.
            have hrel' : ∀ l ∈ reads G i, RelKWith G (mixedParameters G) (enter V i κ s.binders s2.binders) (fv V l)
                (assign ηL s.binders As) (assign ηR s2.binders As) := by
              intro l hl p hp
              by_cases hb : p ∈ s.binders
              · have hkindRel : ∀ p q, (s.binders.zip (s2.binders.map ([·]))).lookup p = some [q] →
                    ∃ kind, G.parameterKinds p = some kind ∧ G.parameterKinds q = some kind := by
                  intro p q hlookup
                  have hmem : (p,q) ∈ s.binders.zip s2.binders := by
                    have hmem := mem_of_lookup hlookup
                    rw [List.zip_map_right] at hmem
                    obtain ⟨⟨a,b⟩, hab, heq⟩ := List.mem_map.mp hmem
                    cases heq
                    exact hab
                  have heq := hkinds (p,q) hmem
                  have hqp := hpars q (List.of_mem_zip hmem).2
                  obtain ⟨kind, hkind⟩ : ∃ kind, G.parameterKinds q = some kind := by
                    simpa [NormalGraph.params, Option.isSome_iff_exists] using hqp
                  exact ⟨kind, heq.trans hkind, hkind⟩
                obtain ⟨q, hq, hk, he⟩ := mixed_enter_binder G V i κ ηL ηR hb hnd hlA.symm
                  (hlen.trans hlA.symm) hkindRel
                rw [hk]; exact he
              · have hpi : p ∈ fv V i := by
                  rcases (hreads l hl).2 p hp with h1 | ⟨s', hs', h2⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'; exact absurd h2 hb
                rw [enter_nmem V i κ hb hpi, assign_nmem ηL s.binders As hb]
                have hr := hrel p hpi
                have hc := hcap p hpi
                cases hk : κ.lookup p with
                | none =>
                  rw [hk] at hr hc
                  have : p ∉ s2.binders := by simpa using hc
                  rw [assign_nmem ηR s2.binders As this]; exact hr
                | some U =>
                  rw [hk] at hr
                  simp only [hk, List.all_eq_true, Bool.not_eq_true'] at hc
                  rw [hr]
                  exact (mixed_respectsFree hF).bound _
                    (agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF))
                    ηR (assign ηR s2.binders As) U (hκD p U hk)
                    (fun l hl q hq => by
                      rw [assign_nmem ηR s2.binders As (by simpa using (hc l hl) q hq)])
            simp only [instanceTWithArgs]
            rw [← sameShape_construct hord]
            obtain ⟨hmap, _⟩ := mapM_some hsigs
            obtain ⟨hmap', _⟩ := mapM_some hrests
            unfold instanceSigs instanceRestsWithArgs
            dsimp only [mixedParameters]
            rw [hmap, hmap']
            simp only [List.map_map]
            refine sigsT_congr s.construct s.signatures _ _ s.variadic _ _ (fun _ _ _ _ => Iff.rfl) (by
              intro p hps
              obtain ⟨_, hsome⟩ := mapM_some hsigs
              obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hsome p hps)
              simpa [Function.comp, hq, Arrow.map, Contract.map] using (sigImg_some hq).2.2.2) (fun p hps => ?_) (by
              intro p hps
              obtain ⟨_, hsome⟩ := mapM_some hrests
              obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hsome p hps)
              simpa [Function.comp, hq, RestArrow.mapWith, Contract.map] using (restImg_some hq).2.2.2.2) (fun p hps => ?_) W v
            · have hin : ∀ l ∈ p.receiver ++ p.arguments.flatten ++ p.result, l ∈ reads G i := fun l hl => by
                simp only [reads, hsch]
                exact List.mem_append_left _
                  (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hps, by simpa [Arrow.operands, RestArrow.operands, List.append_assoc] using hl⟩))
              obtain ⟨q, hq⟩ : ∃ q, sigImg tbl (enter V i κ s.binders s2.binders) p = some q := by
                obtain ⟨_, hsome⟩ := mapM_some hsigs
                exact Option.isSome_iff_exists.mp (hsome p hps)
              obtain ⟨h1, h2, h3, heff⟩ := sigImg_some hq
              simp only [Function.comp, hq, Option.getD_some]
              refine ⟨hty _ _ _ _ _ h1 fun l hl => hrel' l (hin l (by simp [hl])), ?_,
                hty _ _ _ _ _ h3 fun l hl => hrel' l (hin l (by simp [hl]))⟩
              have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) = some Ts →
                  (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) →
                  ArgsAgree n (Ss.map (setSem fun l => qDenoteWithArgs G (mixedParameters G) (assign ηL s.binders As, l)))
                    (Ts.map (mixedValues G (assign ηR s2.binders As))) := by
                intro Ss
                induction Ss with
                | nil => intro Ts h _; simp at h; subst h; exact .nil
                | cons S Ss ihs =>
                  intro Ts h hSs
                  cases hS : tyImg tbl (enter V i κ s.binders s2.binders) S with
                  | none => simp [List.mapM_cons, hS] at h
                  | some S' =>
                    cases hr : Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) with
                    | none => simp [List.mapM_cons, hS, hr] at h
                    | some Ts' =>
                      have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
                      subst this
                      exact .cons (hty _ _ _ _ _ hS fun l hl => hrel' l (hSs S List.mem_cons_self l hl))
                        (ihs Ts' hr fun T hT => hSs T (List.mem_cons_of_mem _ hT))
              exact hargs _ _ h2 fun S hS l hl => hin l (by
                simp only [List.mem_append, List.mem_flatten]
                exact .inl (.inr ⟨S, hS, hl⟩))
            · have hin : ∀ l ∈ p.receiver ++ p.arguments.1.flatten ++ p.arguments.2 ++ p.result, l ∈ reads G i :=
                fun l hl => by
                  simp only [reads, hsch]
                  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hps, by simpa [Arrow.operands, RestArrow.operands, List.append_assoc] using hl⟩)
              obtain ⟨q, hq⟩ : ∃ q, restImg tbl (enter V i κ s.binders s2.binders) p = some q := by
                obtain ⟨_, hsome⟩ := mapM_some hrests
                exact Option.isSome_iff_exists.mp (hsome p hps)
              obtain ⟨h1, h2, h3, h4, heff⟩ := restImg_some hq
              simp only [Function.comp, hq, Option.getD_some]
              refine ⟨hty _ _ _ _ _ h1 fun l hl => hrel' l (hin l (by simp [hl])), ?_,
                hpack _ _ _ _ _ h3 fun l hl => hrel' l (hin l (by simp [hl])),
                hty _ _ _ _ _ h4 fun l hl => hrel' l (hin l (by simp [hl]))⟩
              have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) = some Ts →
                  (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) →
                  ArgsAgree n (Ss.map (setSem fun l => qDenoteWithArgs G (mixedParameters G) (assign ηL s.binders As, l)))
                    (Ts.map (mixedValues G (assign ηR s2.binders As))) := by
                intro Ss
                induction Ss with
                | nil => intro Ts h _; simp at h; subst h; exact .nil
                | cons S Ss ihs =>
                  intro Ts h hSs
                  cases hS : tyImg tbl (enter V i κ s.binders s2.binders) S with
                  | none => simp [List.mapM_cons, hS] at h
                  | some S' =>
                    cases hr : Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) with
                    | none => simp [List.mapM_cons, hS, hr] at h
                    | some Ts' =>
                      have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
                      subst this
                      exact .cons (hty _ _ _ _ _ hS fun l hl => hrel' l (hSs S List.mem_cons_self l hl))
                        (ihs Ts' hr fun T hT => hSs T (List.mem_cons_of_mem _ hT))
              exact hargs _ _ h2 fun S hS l hl => hin l (by
                simp only [List.mem_append, List.mem_flatten]
                exact .inl (.inl (.inr ⟨S, hS, hl⟩)))
      | none =>
        cases hT : T with
        | nil => simp [hsch, hT] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, hT] at hrow
          | nil =>
            cases hm : G.meets i with
            | some pc =>
              -- A meet row: its parameters' images within its clauses' images.
              obtain ⟨p, cs⟩ := pc
              simp only [hsch, hT, hm] at hrow
              have hops := hrow
              unfold meetOk at hops
              simp only [Bool.and_eq_true, List.all_eq_true] at hops
              have hkinds := hops.1.1
              have hops := hops.1.2
              apply meet_row_value hpar hsch hm hrow
                (fun q hq => hrel q ((freeOk_meet hF hiD (by rw [meetParts_of hm]; exact hq)).1
                  (by simp [NormalGraph.params, beq_iff_eq.mp (hkinds q hq)])))
              intro c hc
              apply clauseImg_row tbl κ c _ _ _ _ _ n W v
              · intro S hS
                obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp (hops c hc S hS)
                have hrelS : ∀ l ∈ S, RelKWith G (mixedParameters G) κ (fv V l) ηL ηR := by
                  intro l hl q hq
                  apply hrel q
                  have hlr : l ∈ reads G i := by
                    simp only [reads, hsch]
                    exact List.mem_flatMap.mpr ⟨c, List.mem_append_right _ (by simp [meetClauses, hm, hc]),
                      List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
                  rcases (hreads l hlr).2 q hq with h1 | ⟨s', hs', _⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'
                exact ⟨S', hS', hty _ _ _ _ _ hS' hrelS, hpack _ _ _ _ _ hS' hrelS⟩
              · intro m _ U u; simp [mixedValues, setSem]
              · intro m _ U vs; simp [graphArguments]
            | none =>
            simp only [hsch, hT, hm, Bool.and_eq_true, List.all_eq_true] at hrow
            obtain ⟨⟨⟨hip, hjp⟩, hops⟩, hG⟩ := hrow
            rw [singleton, qDenoteWithArgs_unfold, qDenoteWithArgs_unfold]
            have hi := hip
            have hj := hjp
            simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
              Option.isNone_iff_eq_none] at hi hj
            simp only [qLayerWithArgs, hi.1, hj.1, hi.2, hj.2, Bool.false_eq_true, ite_false]
            have key := sameClauses_iff hG (fun d => rowSem G (builtinValues G) (mixedValues G ηR)
                (graphArguments G ηR (mixedValues G ηR)) d n W v)
              (fun c f hf hn => by
                simp only [rowSem, semWithArgs_members (fun S T h => sameLabels_values h)
                  (fun S T h => sameLabels_arguments h) hf hn, builtinInvariant_map])
            simp only [setSem]
            refine Iff.trans ?_ key.symm
            simp only [List.mem_map]
            have clause : ∀ c ∈ G i,
                rowSem G (builtinValues G) (mixedValues G ηL) (graphArguments G ηL (mixedValues G ηL)) c n W v ↔
                  rowSem G (builtinValues G) (mixedValues G ηR) (graphArguments G ηR (mixedValues G ηR))
                    (clauseImg tbl κ c) n W v := by
              intro c hc
              apply clauseImg_row tbl κ c _ _ _ _ _ n W v
              · intro S hS
                obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp (by simpa using hops c hc S hS)
                have hrelS : ∀ l ∈ S, RelKWith G (mixedParameters G) κ (fv V l) ηL ηR := by
                  intro l hl p hp
                  apply hrel p
                  have hlr : l ∈ reads G i := by
                    simp only [reads, hsch]
                    exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
                  rcases (hreads l hlr).2 p hp with h1 | ⟨s', hs', _⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'
                exact ⟨S', hS', hty _ _ _ _ _ hS' hrelS, hpack _ _ _ _ _ hS' hrelS⟩
              · intro m _ U u; simp [mixedValues, setSem]
              · intro m _ U vs; simp [graphArguments]
            constructor
            · rintro ⟨c, hc, h⟩
              exact ⟨_, ⟨c, hc, rfl⟩, (clause c hc).mp h⟩
            · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
              exact ⟨c, hc, (clause c hc).mpr h⟩
  · -- A parameter uses only its declared component on either side.
    simp only [hpar, ite_true, Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨rfl, _⟩ := hrow
    have hr := hrel i (hself hpar)
    obtain ⟨kind, hk⟩ : ∃ kind, G.parameterKinds i = some kind := by
      simpa [NormalGraph.params, Option.isSome_iff_exists] using hpar
    have hsource : qDenoteWithArgs G (mixedParameters G) (ηL,i) n W v ↔
        selectParameter (some kind) (ηL.1 i) n W (.inl v) := by
      rw [qDenoteWithArgs_unfold]
      simp [qLayerWithArgs, hpar, mixedParameters, selectParameter, hk]
    rw [hsource]
    cases hκ : κ.lookup i with
    | none =>
      rw [hκ] at hr
      simp only [Option.getD_none]
      have he := mixedMeaning_parameter G ηR i kind hk
      change selectParameter (G.parameterKinds i) _ = selectParameter (G.parameterKinds i) _ at hr
      rw [hk] at hr
      rw [hr]
      exact (iff_of_eq (congrFun (congrFun (congrFun he n) W) (.inl v))).symm
    | some U =>
      rw [hκ] at hr
      simp only [Option.getD_some]
      change selectParameter (G.parameterKinds i) _ = mixedMeaning G ηR U at hr
      rw [hk] at hr
      rw [hr]
      rfl

theorem assign_zip_map [DecidableEq ι] {k : ParameterSpace} (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k) :
    ∀ {bs : List ι} {θs : List (List ι)} {b : ι} {U : List ι},
      (bs.zip θs).lookup b = some U → (assign η bs (θs.map F)).1 b = (F U).1
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: bs, θ :: θs, b, U, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    by_cases hb : b = c
    · subst hb
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp only [List.map_cons]
      exact assign_cons_head η b bs (F θ) (θs.map F)
    · rw [beq_false_of_ne hb] at h
      simp only [List.map_cons]
      rw [assign_cons_ne η bs (F θ) (θs.map F) hb]
      exact assign_zip_map η F h

/-- Checked substitution meets every binder bound, independently of whether
its arguments denote values or lists. The interpretation is supplied once and
used for both assignment and the bound check. -/
theorem bounded_substitution [DecidableEq ι] {k : ParameterSpace}
    (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k)
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (s : SchemeRow ι) (θs : List (List ι))
    (hlen : θs.length = s.binders.length)
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (F U).1 (D η b.2)) (n : Nat) :
    Bounded D η s (θs.map F) n := by
  intro b hb hbin j _ W u hu
  obtain ⟨θ, hθ⟩ := lookup_zip_isSome (ys := θs) hbin (by omega)
  rw [assign_zip_map η F hθ] at hu
  exact hbnd b hb θ hθ j W u hu

/-- Eliminate a universal callable with one checked substitution. This is the
shared semantic boundary for value and pack instantiation certificates. -/
theorem bounded_substitution_elim [DecidableEq ι] {k : ParameterSpace}
    (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k)
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (s : SchemeRow ι) (θs : List (List ι))
    (body : List (ParameterFamily k) → Fam) (domain : SchemeDomain ι k)
    (hlen : θs.length = s.binders.length)
    (hal : domain.allowed s (θs.map F))
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (F U).1 (D η b.2)) :
    FamLe (boundedSem D η s body domain) (body (θs.map F)) := by
  intro n W v h
  simpa only [trunc_id] using h.2 n (Nat.le_refl n) _ (by simp [hlen]) hal (bounded_substitution η F D s θs hlen hbnd n)

/-- Substituting a complete binder list changes exactly its bound names. -/
theorem assignment_substitution [DecidableEq ι] {k : ParameterSpace}
    (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k)
    (bs : List ι) (θs : List (List ι)) (hlen : θs.length = bs.length) (b : ι) :
    (assign η bs (θs.map F)).1 b =
      match (bs.zip θs).lookup b with
      | some U => (F U).1
      | none => η.1 b := by
  cases hk : (bs.zip θs).lookup b with
  | none =>
    apply assign_nmem
    intro hb
    obtain ⟨U, hU⟩ := lookup_zip_isSome (ys := θs) hb (by omega)
    rw [hU] at hk
    cases hk
  | some U => exact assign_zip_map η F hk

/-- The existing executable kind check makes a mixed substitution satisfy the
selected table relation. Both assigned families come from the graph's single
two-component meaning; no pack contract is reconstructed from a value type. -/
theorem mixed_assignment_substitution [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (bs : List ι) (θs : List (List ι)) (hlen : θs.length = bs.length)
    (hk : instKinds G bs θs = true) (S : List ι) :
    RelKWith G (mixedParameters G) (bs.zip θs) S
      (assign η bs (θs.map fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) η := by
  intro b _
  have he := assignment_substitution η
    (fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩) bs θs hlen b
  cases hU : (bs.zip θs).lookup b with
  | none =>
    rw [hU] at he
    dsimp only
    rw [he]
  | some U =>
    have hkind := List.all_eq_true.mp hk (b, U) (mem_of_lookup hU)
    cases hp : G.parameterKinds b with
    | none => simp [substitutionKind, hp] at hkind
    | some kind =>
      change selectParameter (G.parameterKinds b) _ = mixedMeaning G η U
      rw [hp, he, hU]
      exact mixedMeaning_selected G η U kind (PositiveRules.sortTy_hasKind (by simpa [substitutionKind, hp] using hkind))

/-- The semantic obligation of an instantiation witness: its named type
images mean substitution, for values and argument packs together. Only images
used by the signatures must be named. How their equality is established is
separate: a finite closed table is one implementation, while recursive
equations require a proof covering their application families. -/
@[nospecialize] def InstanceImages [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (bs : List ι) (θs : List (List ι)) (tbl : InstTable ι) : Prop :=
  ∀ S S', tyImg tbl (bs.zip θs) S = some S' →
    mixedMeaning G (assign η bs (θs.map fun U =>
      ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) S = mixedMeaning G η S'

/-- The current finite-table checker discharges the shared image obligation.
The table's closure and free-variable checks remain necessary here; separating
this theorem does not bypass them or accept a finite truncation. -/
theorem table_instanceImages [DecidableEq ι] {G : NormalGraph ι} (η : MixedAssignment ι)
    {bs : List ι} {θs : List (List ι)} {tbl : InstTable ι} {D : List ι} {V : FreeMap ι}
    (hlen : θs.length = bs.length) (hkinds : instKinds G bs θs = true)
    (hok : TableOk G tbl D V = true) : InstanceImages G η bs θs tbl := by
  let As : List MixedFamily := θs.map fun U =>
    ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩
  have hrel : ∀ l, RelKWith G (mixedParameters G) (bs.zip θs) (fv V l)
      (assign η bs As) η := fun l =>
    mixed_assignment_substitution G η bs θs hlen hkinds (fv V l)
  intro S S' hS
  funext m W x
  apply propext
  rw [mixedMeaning_union]
  exact tyImg_mixed_iff hS fun l _ T hT =>
    table_row_mixed hok m _ η (l, _, T) (entryImg_mem hT) (hrel l) W x

/-- **Instantiation by inclusion** (`Inst≤`): a member of a scheme row, at an
instance whose images mean what the substitution means, is in an arrow
contract each of whose signatures one scheme signature's image covers,
receiver and arguments contravariant, result covariant, effect subsuming.
Elimination is at the instance's assignment, transport by the images, and
the covering by the premises' inclusions; a receiver the scheme lets be any
value is weakened to the target's. -/
theorem inst_covers_sound [DecidableEq ι] {G : NormalGraph ι} (η : MixedAssignment ι) {i : ι} {s : SchemeRow ι}
    {tbl : InstTable ι} {θs : List (List ι)} {L : Ops ι}
    {M : List (RestArrow (List ι))}
    (hp : G.params i = false) (hq : G.schemes i = some s) (hcon : s.construct = false)
    (hlen : θs.length = s.binders.length)
    (hal : G.domain.allowed s (θs.map fun U =>
      ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩))
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (mixedMeaning G η U) (mixedMeaning G η b.2))
    (himages : InstanceImages G η s.binders θs tbl)
    (hL : ∀ q ∈ L, ∃ p ∈ s.signatures, ∃ prs, sigPremises G tbl (s.binders.zip θs) p q = some prs ∧
      ∀ x ∈ prs, FamLe (mixedMeaning G η x.1) (mixedMeaning G η x.2))
    (hM : ∀ q ∈ M, ∃ p ∈ s.variadic, ∃ prs, restPremises G tbl (s.binders.zip θs) p q = some prs ∧
      ∀ x ∈ prs, FamLe (mixedMeaning G η x.1) (mixedMeaning G η x.2))
    : FamLe (mixedValues G η [i])
      (semWithArgs (excOf G) (mixedValues G η) (graphArguments G η (mixedValues G η)) (.arrs L M)) := by
  intro n W v hv
  obtain ⟨_, hm, hv⟩ := hv
  cases List.mem_singleton.mp hm
  have hs := (qDenoteWithArgs_unfold G (mixedParameters G) (η, i) n W v).mp hv
  simp only [qLayerWithArgs, hp, hq, Bool.false_eq_true, if_false] at hs
  have hinv : Invocable v := by simpa only [Callee, hcon, Bool.false_eq_true, if_false] using hs.1
  let F : List ι → MixedFamily := fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩
  let As : List MixedFamily := θs.map F
  have hc := bounded_substitution_elim η F
    (fun η' S => mixedMeaning G η' S) s θs
    (fun As => instanceTWithArgs (excOf G)
      (fun η' S => setSem (fun l => qDenoteWithArgs G (mixedParameters G) (η', l)) S) η s As (graphArguments G)) G.domain
    hlen hal hbnd n W v hs
  change instanceTWithArgs (excOf G)
    (fun η' S => setSem (fun l => qDenoteWithArgs G (mixedParameters G) (η', l)) S) η s As (graphArguments G) n W v at hc
  simp only [instanceTWithArgs, sigsT, hcon, Bool.false_eq_true, if_false] at hc
  have himg : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      mixedMeaning G (assign η s.binders As) S = mixedMeaning G η S' := himages
  have hfam : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      mixedValues G (assign η s.binders As) S = mixedValues G η S' := by
    intro S S' hS
    funext m W' v
    exact congrFun (congrFun (congrFun (himg S S' hS) m) W') (.inl v)
  have hpack : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      graphArguments G (assign η s.binders As) (mixedValues G (assign η s.binders As)) S =
        graphArguments G η (mixedValues G η) S' := by
    intro S S' hS
    funext m W' vs
    exact congrFun (congrFun (congrFun (himg S S' hS) m) W') (.inr vs)
  have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (s.binders.zip θs)) = some Ts →
      Ss.map (mixedValues G (assign η s.binders As)) = Ts.map (mixedValues G η) := by
    intro Ss
    induction Ss with
    | nil => intro Ts h; simp at h; subst h; rfl
    | cons S Ss ihs =>
      intro Ts h
      cases hS : tyImg tbl (s.binders.zip θs) S with
      | none => simp [List.mapM_cons, hS] at h
      | some S' =>
        cases hr : Ss.mapM (tyImg tbl (s.binders.zip θs)) with
        | none => simp [List.mapM_cons, hS, hr] at h
        | some Ts' =>
          have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
          subst this
          simp only [List.map_cons, hfam S S' hS, ihs Ts' hr]
  -- A receiver the instance states within a scheme receiver admitting every
  -- value: every receiver is a closed value.
  have anyRecv : ∀ (P Q : List ι), receiverUniverse G P Q = true → ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → ∀ r, mixedValues G η Q j U r →
        mixedValues G (assign η s.binders As) P j U r := by
    intro P Q hP j hj U _ r hr
    simp only [receiverUniverse, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hP
    rcases hP with hP | ⟨hP, hQ⟩
    · obtain ⟨l, _, hl⟩ := hr
      exact top_row_mixed hP (mixedDenote_value G η l hl)
    · exact mixed_of_expand hP (sourceTy_exc hQ η j U r hr)
  refine ⟨⟨hinv, fun q' hq' => ?_⟩, ⟨hinv, fun r' hr' => ?_⟩⟩
  · obtain ⟨q, hqL, rfl⟩ := List.mem_map.mp hq'
    obtain ⟨p, hps, prs, hprs, hle⟩ := hL q hqL
    have hpr := hc.1.2 _ (List.mem_map_of_mem hps)
    change PromiseWith (excOf G) p.effect (ArgsShort (p.arguments.map (mixedValues G (assign η s.binders As))))
      (mixedValues G (assign η s.binders As) p.receiver)
      (mixedValues G (assign η s.binders As) p.result) n W v at hpr
    obtain ⟨hlen', heffect, ps, r, h2, h3, hsub, hrecv⟩ := sigPremises_some hprs
    have e2 := hargs _ _ h2
    have e3 := hfam _ _ h3
    rw [e2, e3] at hpr
    have hpl := (tysImg_some h2).1
    have hargsLe : ArgsLe (q.arguments.map (mixedValues G η)) (ps.map (mixedValues G η)) :=
      argsLe_of_zip (by omega) fun x hx => hle x (hsub (List.mem_append_left _ hx))
    have hres := hle (r, q.result) (hsub (List.mem_append_right _ (List.mem_singleton_self _)))
    rcases hrecv with hu | ⟨rc, h1, hrc⟩
    · exact (hpr.weaken_recv (anyRecv p.receiver q.receiver hu)).weaken
        (Effect.covers_sound heffect) (fun _ _ _ _ h => h)
        (fun _ _ _ _ ha => ArgsShort_mono hargsLe ha) (fun _ _ U u h => hres _ U (.inl u) h)
    · rw [hfam _ _ h1] at hpr
      have hr := hle _ hrc
      exact hpr.weaken (Effect.covers_sound heffect) (fun _ _ U u h => hr _ U (.inl u) h)
        (fun _ _ _ _ ha => ArgsShort_mono hargsLe ha) (fun _ _ U u h => hres _ U (.inl u) h)
  · obtain ⟨q, hqM, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨p, hps, prs, hprs, hle⟩ := hM q hqM
    have hpr := hc.2.2 _ (List.mem_map_of_mem hps)
    change PromiseWith (excOf G) p.effect (ArgsRest (p.arguments.1.map (mixedValues G (assign η s.binders As)))
      (graphArguments G (assign η s.binders As) (mixedValues G (assign η s.binders As)) p.arguments.2))
      (mixedValues G (assign η s.binders As) p.receiver) (mixedValues G (assign η s.binders As) p.result) n W v at hpr
    obtain ⟨hlen', heffect, ps, e, r, h2, h3, h4, hsub, hrecv⟩ := restPremises_some hprs
    have e2 := hargs _ _ h2
    have e3 := hpack _ _ h3
    have e4 := hfam _ _ h4
    rw [e2, e3, e4] at hpr
    have hpl := (tysImg_some h2).1
    have hargsLe : ArgsLe (q.arguments.1.map (mixedValues G η)) (ps.map (mixedValues G η)) :=
      argsLe_of_zip (by omega) fun x hx => hle x (hsub (List.mem_append_left _ hx))
    have hpk := hle (q.arguments.2, e) (hsub (List.mem_append_right _ (by simp)))
    have hres := hle (r, q.result) (hsub (List.mem_append_right _ (by simp)))
    have hacc : ∀ j, j < n → ∀ U args,
        ArgsRest (q.arguments.1.map (mixedValues G η)) (graphArguments G η (mixedValues G η) q.arguments.2) j U args →
        ArgsRest (ps.map (mixedValues G η)) (graphArguments G η (mixedValues G η) e) j U args :=
      fun j _ U _ ha => ArgsRest_mono hargsLe (fun vs hv => hpk j U (.inr vs) hv) ha
    rcases hrecv with hu | ⟨rc, h1, hrc⟩
    · exact (hpr.weaken_recv (anyRecv p.receiver q.receiver hu)).weaken
        (Effect.covers_sound heffect) (fun _ _ _ _ h => h) hacc (fun _ _ U u h => hres _ U (.inl u) h)
    · rw [hfam _ _ h1] at hpr
      have hr := hle _ hrc
      exact hpr.weaken (Effect.covers_sound heffect) (fun _ _ U u h => hr _ U (.inl u) h)
        hacc (fun _ _ U u h => hres _ U (.inl u) h)

end Verification.PositiveRules
