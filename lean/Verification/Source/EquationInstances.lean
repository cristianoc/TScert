import Verification.Source.EquationTrees

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-- A closed tree as a label of `E`, or a located refusal. -/
def closedLabel (E : Equations) (site : String) (t : Tree) : Except String (Label E.signature) :=
  match Label.ofTree? t with
  | some l => .ok l
  | none => .error s!"{site}: {(t.problem E.signature 0 0 .label).getD "not a closed label"}"

def closedUnion (E : Equations) (site : String) (U : Union) : Except String (List (Label E.signature)) :=
  U.mapM (closedLabel E site)

/-! ### Instances by substitution (§4.3, §9.2)

What an equation label proposes for an instance of a scheme row
(`CertificateProducer.Instantiates`): the binders' instances found by
matching the scheme's signatures against the target's trees, and each
operand's image its structural substitution (`Label.substitute`), which
`substitutionTableOk` checks. Untrusted. -/

/-- Whether a tree mentions one of `bs`. -/
partial def mentionsAny (bs : List Tree) (t : Tree) : Bool :=
  bs.contains t || match t with
    | .app _ args | .bound _ args _ => args.toList.any fun ts => ts.toList.any (mentionsAny bs)
    | .meet ps => ps.toList.any (mentionsAny bs)
    | _ => false

/-- A parameter observed through fixed intersection restrictions. Matching
proposes its instance; substitution-image checking retains the restrictions. -/
def viewBinder (bs : List Tree) (t : Tree) : Option Tree :=
  if bs.contains t then some t else match t with
  | .meet ps => match ps.toList.filter (mentionsAny bs ·) with
    | [b] => if bs.contains b then some b else none
    | _ => none
  | _ => none

private def sameSet (a b : List Tree) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-- One step of a label's unfolding, as trees: the clauses the equations
give it. -/
abbrev Unfold := Tree → Option (List (Clause (List Tree)))

/-- How many unfoldings deep two applications of different heads are
compared. -/
def unfoldDepth : Nat := 4

mutual
/-- Extend `θ` so that the union `S`, its binders `bs` read as `θ` gives
them, is `T`. -/
partial def unifyUnion (unfold : Unfold) (fuel : Nat) (bs : List Tree) (θ : List (Tree × List Tree))
    (S T : List Tree) : Option (List (Tree × List Tree)) :=
  match S with
  | [b] =>
    if bs.contains b then
      match θ.lookup b with
      | some U => if sameSet U T then some θ else none
      | none => some (θ ++ [(b, T)])
    else
      let direct := match T with
        | [t] => unifyTree unfold fuel bs θ b t
        | _ => none
      direct.orElse fun _ => match b with
        | .meet ps => match ps.toList.filter (mentionsAny bs ·) with
          | [p] => if bs.contains p then unifyUnion unfold fuel bs θ [p] T else none
          | _ => none
        | _ => none
  | _ =>
    -- The union's labels mentioning no binder are themselves; the one that
    -- does takes the rest of `T`.
    let fixed := S.filter fun t => !mentionsAny bs t
    if !fixed.all (T.contains ·) then none else
    match S.filter (mentionsAny bs ·) with
    | [] => if sameSet S T then some θ else none
    | [x] =>
      match θ.lookup x with
      -- A binder already found: with the fixed labels, its instance is `T`.
      | some U => if bs.contains x && sameSet (fixed ++ U) T then some θ else
          unifyUnion unfold fuel bs θ [x] (T.filter (!fixed.contains ·))
      | none => unifyUnion unfold fuel bs θ [x] (T.filter (!fixed.contains ·))
    | xs => do
      -- A binder beside labels mentioning it (`R | PromiseLike<R>` against
      -- `string | PromiseLike<string>`): each such label is one of `T`'s,
      -- which may find the binder; a binder then found is its instance, and
      -- one still unfound takes the rest of `T`. Several unfound binders
      -- (`T1 | T2` against `string`) are left to the other operands.
      let (θ, img) ← (xs.filter (fun x => (viewBinder bs x).isNone)).foldlM (fun (acc : List (Tree × List Tree) × List Tree) x =>
        T.findSome? fun t => (unifyTree unfold fuel bs acc.1 x t).map fun θ => (θ, acc.2 ++ [t]))
        (θ, fixed)
      let bare := (xs.filterMap (viewBinder bs)).eraseDups
      let img := img ++ (bare.filterMap fun b => θ.lookup b).flatten
      if !img.all (T.contains ·) then none
      match bare.filter (fun b => (θ.lookup b).isNone) with
      | [] => if T.all (img.contains ·) then some θ else none
      | [b] => some (θ ++ [(b, T.filter (!img.contains ·))])
      | _ => some θ
/-- Extend `θ` so that the tree `s` is `t`. Two applications of different
heads are compared by one step of their unfoldings (a literal the target
spells as a row of its own), at most `fuel` steps deep. -/
partial def unifyTree (unfold : Unfold) (fuel : Nat) (bs : List Tree) (θ : List (Tree × List Tree))
    (s t : Tree) : Option (List (Tree × List Tree)) :=
  if !mentionsAny bs s then (if s == t then some θ else none) else
  match s, t with
  | .app h a, .app h' a' =>
    if h == h' && a.toList.length == a'.toList.length then
      (a.toList.zip a'.toList).foldlM (fun θ (x, y) => unifyUnion unfold fuel bs θ x.toList y.toList) θ
    else match fuel, unfold s, unfold t with
      | fuel + 1, some cs, some ds =>
        if cs.length == ds.length && (cs.zip ds).all (fun (c, d) => c.map (fun _ => ()) == d.map (fun _ => ())) then
          (cs.zip ds).foldlM (fun θ (c, d) =>
            (c.operands.zip d.operands).foldlM (fun θ (x, y) => unifyUnion unfold fuel bs θ x y) θ) θ
        else none
      | _, _, _ => none
  | .bound h a _, .bound h' a' _ =>
    if h != h' || a.toList.length != a'.toList.length then none
    else (a.toList.zip a'.toList).foldlM (fun θ (x, y) => unifyUnion unfold fuel bs θ x.toList y.toList) θ
  | .meet ps, _ =>
    let matched := match t with
      | .meet qs =>
        if ps.toList.length != qs.toList.length then none
        else (ps.toList.zip qs.toList).foldlM (fun θ (x, y) => unifyTree unfold fuel bs θ x y) θ
      | .app .. | .bound .. | .local .. | .argument .. | .var .. => none
    matched.orElse fun _ =>
      -- Propose the actual type for a single binder observed through a meet.
      -- The checker retains the other parts in the image and checks the bound.
      match ps.toList.filter (mentionsAny bs ·) with
      | [b] => if bs.contains b then unifyUnion unfold fuel bs θ [b] [t] else none
      | _ => none
  | _, _ => none
end

/-- The binders' instances making a scheme's signatures cover the target
arrows, each target matched against one of the scheme's; unmatched binders
stand for themselves. -/
def unifyScheme (unfold : Unfold) (s : SchemeRow Tree) (L : PositiveRules.Ops Tree) (M : List (RestArrow (List Tree))) :
    Option (List (Tree × List Tree)) := do
  let unifyArrow (relaxed : Bool) (θ : List (Tree × List Tree)) (p q : List (List Tree)) : Option (List (Tree × List Tree)) :=
    if p.length != q.length then none
    else (p.zip q).foldlM (fun θ (x, y) =>
      -- Fixed operands determine no binder. Keep their original images in
      -- the proposal; image equality and signature inclusion check them,
      -- including a target's equivalent spelling of a fixed callback type.
      if relaxed && !x.any (mentionsAny s.binders ·) then some θ
      else unifyUnion unfold unfoldDepth s.binders θ x y) θ
  -- A receiver may determine its own payload binder. Try matching it first;
  -- a receiver admitting every value need not match the target's spelling.
  -- These are proposals: the image and signature checks validate every
  -- receiver, argument, result and bound independently.
  let body (a : Arrow (List Tree)) := a.arguments ++ [a.result]
  let θ ← L.foldlM (fun θ q =>
    let matchOne relaxed := s.signatures.findSome? fun p =>
      if !p.effect.covers q.effect then none else
        (unifyArrow relaxed θ (p.receiver :: body p) (q.receiver :: body q)).orElse fun _ =>
          unifyArrow relaxed θ (body p) (body q)
    -- Preserve exact overload selection before proposing an equivalent
    -- spelling of a fixed operand.
    (matchOne false).orElse fun _ => matchOne true) []
  M.foldlM (fun θ q =>
    let matchOne relaxed := s.variadic.findSome? fun p =>
      if !p.effect.covers q.effect then none
      else
        let body (a : RestArrow (List Tree)) := a.arguments.2 :: a.result :: a.arguments.1
        (unifyArrow relaxed θ (p.receiver :: body p) (q.receiver :: body q)).orElse fun _ =>
          unifyArrow relaxed θ (body p) (body q)
    (matchOne false).orElse fun _ => matchOne true) θ

/-- An equation graph's proposal: instances by matching, images by
structural substitution. -/
def proposeLabels {sig : Signature} (unfold : Unfold) (s : SchemeRow (Label sig)) (L : PositiveRules.Ops (Label sig))
    (M : List (RestArrow (List (Label sig)))) : Option (List (List (Label sig)) × InstTable (Label sig)) := do
  let tree (U : List (Label sig)) : List Tree := U.map (·.1)
  let s' : SchemeRow Tree := ⟨tree s.binders, s.signatures.map (Arrow.map tree),
    s.bounds.map (fun (b, U) => (b.1, tree U)), s.variadic.map (RestArrow.map tree), s.resolution,
    s.construct⟩
  let θ ← unifyScheme unfold s' (L.map (Arrow.map tree)) (M.map (RestArrow.map tree))
  let θs ← s.binders.mapM fun b => ((θ.lookup b.1).getD [b.1]).mapM Label.ofTree?
  let κ : PositiveRules.Ctx (Label sig) := s.binders.zip θs
  let operands := (s.signatures.flatMap Arrow.operands ++ s.variadic.flatMap RestArrow.operands).flatten.eraseDups
  return (θs, operands.map fun l => (l, κ, l.substitute (parameterReplacement κ)))

instance {sig : Signature} : CertificateProducer.Instantiates (Label sig) := ⟨proposeLabels fun _ => none⟩


end Verification.EquationLowering
