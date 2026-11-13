import Verification.Source.SourceClaims
import Verification.Source.SourceFacts
import Verification.Semantics.SafeIntegers

/-! Loop-head proposals of the claims-free front (mode 8): facts a loop's
head is proposed to hold, computed from the fragment's statements alone,
over source names (docs/drafts/single-pass.md, "The claims-free front").
They reach the pass as the producer's facts reach it: as entry claims at the
loop's execution point (`SourceClaims.PointData.entryFacts`), which the
lowering records as the head's candidates (`LoweringFlow.flowNode`), each an
obligation the pass checks on every edge into the head. A wrong proposal
costs a refusal, never an acceptance; the front drops the proposals an edge
refuses and runs the pass again (`FilePlans.passGroupInferred`).

The rules: a
declaration or assignment of a linear value states its equality; a test
states its comparisons on each arm; an increment `x + c` restates each fact
at its shifted bound; a loop's head holds the facts its entry holds over
bindings the loop does not assign (the join of facts both edges define), and of a counter the loop steps by a constant,
its integrality, the bounds its entry states that a step keeps, the bound
the test states shifted by the step, and `2^32 - 1` where the test bounds
it above (the join's candidates `{d, 0, 2^32-1, 2^53-1}`). -/
namespace Verification.SourceExtraction.HeadInference
open Fragment

/-- A linear term over source names: a binding's name, the fields read from
it, and what the term reads (`HeapKnowledge.Term.Kind`). -/
abbrev Key := String × List String × HeapKnowledge.Term.Kind

/-- `Σ c·t ≤ bound`, one coefficient per term, none zero. -/
structure Lin where
  terms : List (Key × Int)
  bound : Int
  deriving BEq, Inhabited

/-- A variable of a quantified fact's body (`SourceClaims.BodyRef`): the
index, the element at it, a projection of the element, or a term over
source names. -/
inductive BodyKey where
  | index
  | elem
  | offset (delta : Nat)
  | project (kind : HeapKnowledge.Term.Kind) (path : List String)
  | term (k : Key)
  deriving BEq, Inhabited

/-- A proposed fact: a linear fact, or a binding's value a safe integer. -/
inductive Fact where
  | lin (l : Lin)
  | int (name : String)
  /-- Unless a guard's path of its binding holds its tag, the arrays two
  paths read are different stores (`IndexFact.storeApart`, guarded). -/
  | apart (guards : List (String × List String × HeapKnowledge.GuardTag)) (a : String) (pa : List String)
      (b : String) (pb : List String)
  /-- Of each index below `stop` of the array the path from `a` reads, the
  body's facts `Σ c·v ≤ d` (`IndexFact.every`, `linear_facts.ml:efact`). -/
  | every (a : String) (pa : List String) (stop : Key) (body : List (List (BodyKey × Int) × Int))
  /-- Unless a guard's path of its binding holds its tag, the linear fact
  (`IndexFact.guarded`, a type invariant's `x.f === null || …`). -/
  | guarded (guards : List (String × List String × HeapKnowledge.GuardTag)) (l : Lin)
  deriving BEq, Inhabited

def Fact.names : Fact → List String
  | .lin l => l.terms.map (·.1.1)
  | .int n => [n]
  | .apart gs a _ b _ => gs.map (·.1) ++ [a, b]
  | .guarded gs l => gs.map (·.1) ++ l.terms.map (·.1.1)
  | .every a _ stop body => a :: stop.1 :: body.flatMap fun (ts, _) => ts.filterMap fun
    | (.term k, _) => some k.1
    | _ => none

/-- The claim the producer would write for the fact. -/
def Fact.claim : Fact → Option SourceClaims.ClauseClaim
  | .lin l => some (.linear [] (l.terms.map fun ((n, p, k), c) => (n, p, k, c)) l.bound)
  | .int n => some (.linear [] [(n, [], .value, 0)] 0)
  | .guarded gs l => some (.linear gs (l.terms.map fun ((n, p, k), c) => (n, p, k, c)) l.bound)
  | .apart .. | .every .. => none

/-- The quantified fact the producer would write for the fact. -/
def Fact.everyClaim : Fact → Option SourceClaims.EveryClaim
  | .every a pa stop body =>
    let ref : BodyKey → SourceClaims.BodyRef := fun
      | .index => .index
      | .elem => .elem
      | .offset d => .offset d
      | .project k p => .project k p
      | .term (n, p, k) => .term n p k
    some ((a, pa), stop, body.map fun (ts, d) => .linear (ts.map fun (v, c) => (ref v, c)) d)
  | _ => none

/-- The store separation the producer would write for the fact. -/
def Fact.storesClaim : Fact → Option SourceClaims.StoresApartClaim
  | .apart gs a pa b pb => some (gs, (a, pa), (b, pb))
  | _ => none

/-- The fact as `@invariant` text. -/
partial def Fact.text : Fact → String
  | .int n => s!"safeInteger({n})"
  | .apart gs a pa b pb =>
    let tag := fun (t : HeapKnowledge.GuardTag) => match t with
      | .null => "null" | .undef => "undefined" | .tru => "true" | .fls => "false"
    let guards := gs.map fun (g, p, t) => s!"{String.intercalate "." (g :: p)} === {tag t} || "
    String.join guards ++ s!"{String.intercalate "." (a :: pa)} !== {String.intercalate "." (b :: pb)}"
  | .guarded gs l =>
    let tag := fun (t : HeapKnowledge.GuardTag) => match t with
      | .null => "null" | .undef => "undefined" | .tru => "true" | .fls => "false"
    String.join (gs.map fun (g, p, t) => s!"{String.intercalate "." (g :: p)} === {tag t} || ") ++ Fact.text (.lin l)
  | .lin l =>
    let term := fun ((n, p, k) : Key) =>
      let path := String.intercalate "." (n :: p)
      match k with
      | .value => path
      | .length | .strLength => path ++ ".length"
      | .view => path ++ ".length"
    let pos := l.terms.filter (·.2 > 0)
    let neg := l.terms.filter (·.2 < 0)
    let side := fun (ts : List (Key × Int)) (c : Int) =>
      let parts := ts.map fun (t, a) => let a := a.natAbs; if a == 1 then term t else s!"{a} * {term t}"
      let parts := if c != 0 || parts.isEmpty then parts ++ [toString c] else parts
      " + ".intercalate parts
    -- `Σpos - Σneg ≤ d` as `Σpos ≤ Σneg + d`, constants on the right.
    s!"{side pos 0} <= {side neg l.bound}"
  | .every a pa (sn, sp, _) body =>
    let arr := String.intercalate "." (a :: pa)
    let v := fun (b : BodyKey) => match b with
      | .index => "i" | .elem => s!"{arr}[i]" | .offset d => s!"{arr}[i + {d}]"
      | .project _ p => String.intercalate "." (s!"{arr}[i]" :: p)
      | .term (n, p, _) => String.intercalate "." (n :: p)
    let clause := fun ((ts, d) : List (BodyKey × Int) × Int) =>
      " + ".intercalate (ts.map fun (b, c) => if c == 1 then v b else s!"{c} * {v b}") ++ s!" <= {d}"
    s!"forall i < {String.intercalate "." (sn :: sp)}.length of {arr}: " ++ " && ".intercalate (body.map clause)

/-- Terms added, coefficients merged, zeros dropped. -/
def addTerms (a b : List (Key × Int)) : List (Key × Int) :=
  let merged := b.foldl (fun acc (k, c) =>
    match acc.find? (·.1 == k) with
    | some _ => acc.map fun (k', c') => if k' == k then (k', c' + c) else (k', c')
    | none => acc ++ [(k, c)]) a
  merged.filter (·.2 != 0)

def scale (c : Int) (ts : List (Key × Int)) : List (Key × Int) := ts.map fun (k, a) => (k, c * a)

/-- The safe integer a literal is. -/
def intLit : Claim.Val → Option Int
  | .vnum b => SafeIntegers.safeIntOfBits b
  | _ => none

/-- A path of named fields from a binding. -/
partial def pathOf : Expr → Option (String × List String)
  | .var _ n => if n.startsWith "%" || n == "this" then none else some (n, [])
  | .read _ (.str f) e => do let (r, p) ← pathOf e; pure (r, p ++ [f])
  | .cast _ _ e => pathOf e
  | _ => none

/-- An expression as a linear form `Σ c·t + k`, where it is one. -/
partial def linOf (K : String → HeapKnowledge.Term.Kind) : Expr → Option (List (Key × Int) × Int)
  | .lit _ v => (intLit v).map ([], ·)
  | .var _ n => if n.startsWith "%" || n == "this" then none else some ([((n, [], .value), 1)], 0)
  | .read _ (.str "length") e => do
    let (r, p) ← pathOf e; pure ([((r, p, if p.isEmpty then K r else .length), 1)], 0)
  | .call _ (.var _ "%ByteLength%") [e] _ _ => do let (r, p) ← pathOf e; pure ([((r, p, .view), 1)], 0)
  | .cast _ _ e => linOf K e
  | .arith _ .add a b => do
    let (ta, ka) ← linOf K a; let (tb, kb) ← linOf K b; pure (addTerms ta tb, ka + kb)
  | .arith _ .sub a b => do
    let (ta, ka) ← linOf K a; let (tb, kb) ← linOf K b; pure (addTerms ta (scale (-1) tb), ka - kb)
  | .arith _ .mul a b => do
    let (ta, ka) ← linOf K a; let (tb, kb) ← linOf K b
    if ta.isEmpty then pure (scale ka tb, ka * kb)
    else if tb.isEmpty then pure (scale kb ta, ka * kb) else none
  | _ => none

/-- `l - r ≤ d` as a fact, where it names a term. -/
def leOf (l r : List (Key × Int) × Int) (d : Int) : List Lin :=
  let ts := addTerms l.1 (scale (-1) r.1)
  if ts.isEmpty then [] else [⟨ts, d - l.2 + r.2⟩]

/-- The comparisons a test's answer `pos` states (`linear_facts.ml:test`):
`<`, `<=`, `>`, `>=` and `===` of linear operands, through `!`, and the
conjuncts of a conjunction holding (of a disjunction failing). -/
partial def atomsOf (K : String → HeapKnowledge.Term.Kind) (e : Expr) (pos : Bool)
    (read : Expr → Bool → List (List (Key × Int) × Int) := fun _ _ => []) : List Lin :=
  -- (an operand no linear form gives: its bound below where it is the
  -- smaller side, above where the larger, `read`)
  let lo := fun (x : Expr) => match linOf K x with | some l => [l] | none => read x false
  let up := fun (x : Expr) => match linOf K x with | some l => [l] | none => read x true
  let le := fun (a b : Expr) (d : Int) => (lo a).flatMap fun l => (up b).flatMap fun r => leOf l r d
  match e with
  | .arith _ op a b => match op, pos with
    | .lt, true => le a b (-1)
    | .lt, false => le b a 0
    | .le, true => le a b 0
    | .le, false => le b a (-1)
    | .gt, true => le b a (-1)
    | .gt, false => le a b 0
    | .ge, true => le b a 0
    | .ge, false => le a b (-1)
    | _, _ => []
  | .equality _ eq a b => if eq != pos then [] else le a b 0 ++ le b a 0
  | .not _ e => atomsOf K e (!pos) read
  | .cast _ _ e => atomsOf K e pos read
  | .logical _ andOp a b => if andOp == pos then atomsOf K a pos read ++ atomsOf K b pos read else []
  | _ => []

/-- The disequalities `l !== r` a test's `true` answer states, conjunct by
conjunct, as the differences `l - r`. -/
partial def neqOf (K : String → HeapKnowledge.Term.Kind) (e : Expr) (pos : Bool) : List (List (Key × Int) × Int) :=
  match e with
  | .equality _ eq a b => if eq == pos then [] else match linOf K a, linOf K b with
    | some l, some r => [(addTerms l.1 (scale (-1) r.1), l.2 - r.2)]
    | _, _ => []
  | .not _ e => neqOf K e (!pos)
  | .cast _ _ e => neqOf K e pos
  | .logical _ andOp a b => if andOp == pos then neqOf K a pos ++ neqOf K b pos else []
  | _ => []

/-- An expression's direct subexpressions, closures' bodies included. -/
partial def kids : Expr → List Expr
  | .var .. | .lit .. => []
  | .lambda _ _ _ _ ds _ _ _ _ _ _ b => ds.map (·.2) ++ [b]
  | .shapeTest _ _ _ e | .tagMember _ _ _ _ _ e | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e => [e]
  | .ctor _ e fs => e :: fs.map (·.2)
  | .construct _ f args _ _ => f :: args
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => es
  | .logical _ _ a b | .coalesce _ a b | .equality _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
  | .elemAt _ a b | .arith _ _ a b | .logicalAssign _ _ a b | .comma _ a b | .inKeys _ a b
  | .withValue _ a b _ _ | .optional _ _ a b | .withObject _ _ a b => [a, b]
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ a b c => [a, b, c]
  | .update _ _ a b _ => a :: b.toList
  | .assign _ _ _ e | .nullishAssign _ _ _ e => [e]
  | .arrayAssign _ targets rest rhs => rhs :: targets.flatMap
      (fun q => q.target :: q.default_.toList) ++ (rest.map (·.2.2.target)).toList
  | .bindWithReceiver _ f r args | .callWithReceiver _ f r args => f :: r :: args
  | .applyWithReceiver _ f r list _ => f :: r :: list.toList
  | .call _ f args _ _ | .invoke _ f args _ _ => f :: args
  | .objectAssign _ t ss => t :: ss
  | .block .. => []

mutual
/-- Every expression of a statement list, nested statements' and closures'
bodies included. -/
partial def exprsOf (ss : List Stmt) : List Expr := ss.flatMap stmtExprs

partial def stmtExprs : Stmt → List Expr
  | .ret _ e | .effect _ e | .throw _ e => allExprs e
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => allExprs b.init
  | .destructure _ _ d init => allExprs init ++ d.toList.flatMap allExprs
  | .ite _ c t e => allExprs c ++ exprsOf t ++ exprsOf (e.getD [])
  | .loop _ c b u _ => allExprs c ++ exprsOf b ++ exprsOf u
  | .block _ _ b => exprsOf b
  | .forOf _ _ _ _ i b => allExprs i ++ exprsOf b
  | .tryStmt _ b h f => exprsOf b ++ exprsOf ((h.map (·.2)).getD []) ++ exprsOf (f.getD [])
  | .closing _ c b => exprsOf c ++ exprsOf b
  | .brk .. | .cont .. => []

/-- An expression and every expression inside it. -/
partial def allExprs (e : Expr) : List Expr :=
  e :: (match e with
    | .block _ ss => exprsOf ss
    | _ => (kids e).flatMap allExprs)
end

/-- How one write changes a binding: by a constant (`x++`, `x += c`,
`x = x + c`, their decrements), or otherwise. -/
def stepOf (name : String) : Expr → Option (Option Int)
  | .update _ op (.var _ n) rhs _ => if n != name then none else some (match op, rhs with
    | .add, none => some 1
    | .sub, none => some (-1)
    | .add, some (.lit _ v) => intLit v
    | .sub, some (.lit _ v) => (intLit v).map (- ·)
    | _, _ => none)
  | .assign _ n _ rhs => if n != name then none else some (match rhs with
    | .arith _ .add (.var _ m) (.lit _ v) | .arith _ .add (.lit _ v) (.var _ m) =>
      if m == name then intLit v else none
    | .arith _ .sub (.var _ m) (.lit _ v) => if m == name then (intLit v).map (- ·) else none
    | _ => none)
  | .nullishAssign _ n _ _ => if n == name then some none else none
  | .logicalAssign _ _ (.var _ n) _ => if n == name then some none else none
  | .arrayAssign .. => some none
  | _ => none

/-- Whether statements assign a binding. -/
def assigns (ss : List Stmt) (n : String) : Bool := ss.any (assignsStmt n)

/-- A counter of a loop: every write of it in the loop a step by one
constant `c ≠ 0` (`some c`), where it has one. -/
def counterStep (ss : List Stmt) (n : String) : Option Int :=
  let steps := (exprsOf ss).filterMap (stepOf n)
  match steps with
  | some c :: rest => if c != 0 && rest.all (· == some c) then some c else none
  | _ => none

/-- Whether a statement list may write the heap or call: any form but
reads, arithmetic, tests and writes of bindings. -/
partial def quiet : Expr → Bool
  | .var .. | .lit .. => true
  | .read _ _ e | .not _ e | .cast _ _ e | .unary _ _ e | .shapeTest _ _ _ e => quiet e
  | .arith _ _ a b | .equality _ _ a b | .logical _ _ a b | .singletonTest _ _ _ _ a b
  | .elemAt _ a b | .coalesce _ a b | .comma _ a b => quiet a && quiet b
  | .ifBody _ a b c => quiet a && quiet b && quiet c
  | .update _ _ (.var ..) rhs _ => (rhs.map quiet).getD true
  | .assign _ _ _ e => quiet e
  -- A typed array's length and element reads (`%ByteLength%`, `%ByteAt%`),
  -- an array's element read (`%ElementAt%`, which writes nothing:
  -- `linear_facts.ml:heap_free`).
  | .call _ (.var _ n) args _ _ => (n == "%ByteLength%" || n == "%ByteAt%" || n == "%ElementAt%") && args.all quiet
  -- An object literal of named fields, an array literal without spreads:
  -- an allocation writing only its own fresh locations
  -- (`linear_facts.ml:heap_free`'s `Alloc` and `ArrayLiteral`).
  | .alloc _ _ es => es.all quiet
  | .arrayLit _ es [] => es.all quiet
  | _ => false

/-- The arrays whose length a statement list may change by name: a
receiver of `push`, `pop`, `shift`, `unshift` or `splice`, or of a
write of `length`. -/
def resized (ss : List Stmt) : List String :=
  (exprsOf ss).filterMap fun
    | .invoke _ (.read _ (.str m) r) _ _ _ =>
      if ["push", "pop", "shift", "unshift", "splice"].contains m then (pathOf r).map (·.1) else none
    | .write _ (.str "length") r _ => (pathOf r).map (·.1)
    | _ => none

/-- Whether a list's last statement leaves it: no statement after it runs. -/
partial def exits : List Stmt → Bool
  | [] => false
  | ss => match ss.getLast? with
    | some (.ret ..) | some (.throw ..) | some (.brk ..) | some (.cont ..) => true
    | some (.ite _ _ t (some e)) => exits t && exits e
    | some (.block _ none b) => exits b
    | _ => false

/-- Whether a loop's body may go back to its head other than by its end: a
`continue` of it (not of a loop nested in it). -/
partial def continues : List Stmt → Bool
  | ss => ss.any fun
    | .cont .. => true
    | .ite _ _ t e => continues t || continues (e.getD [])
    | .block _ _ b => continues b
    | .tryStmt _ b h f => continues b || continues ((h.map (·.2)).getD []) || continues (f.getD [])
    | .closing _ c b => continues c || continues b
    | _ => false

/-- A test with a prefix step of `x` as an operand of its comparison
(`++x >= n`) read with the step done: the operand `x`. -/
def stepped (x : String) (e : Expr) : Expr :=
  let operand := fun (a : Expr) => match a with
    | .update _ _ (.var q n) none false => if n == x then Expr.var q n else a
    | _ => a
  match e with
  | .arith p op a b => .arith p op (operand a) (operand b)
  | .equality p eq a b => .equality p eq (operand a) (operand b)
  | e => e

/-- Whether a loop's body may leave the loop other than by its test: a
`break` of it (not of a loop nested in it), a labeled `break`, or a throw. -/
partial def breaks : List Stmt → Bool
  | ss => ss.any fun
    | .brk .. => true
    | .ite _ _ t e => breaks t || breaks (e.getD [])
    | .block _ _ b => breaks b
    | .tryStmt _ b h f => breaks b || breaks ((h.map (·.2)).getD []) || breaks (f.getD [])
    | .closing _ c b => breaks c || breaks b
    | _ => false

/-- Whether every write of a binding in statements is an assignment of a
linear value or a step by a constant (`linear_facts.ml:linear`'s operands):
a binding written otherwise forgets its integrality. -/
def linearWrites (K : String → HeapKnowledge.Term.Kind) (ss : List Stmt) (x : String) : Bool :=
  let linear : Expr → Bool := fun
    | .ifBody _ _ a b => (linOf K a).isSome && (linOf K b).isSome
    | e => (linOf K e).isSome
  (exprsOf ss).all fun e => match e with
    | .assign _ n _ rhs => n != x || linear rhs
    | .update _ op (.var _ n) rhs _ => n != x || ((op == .add || op == .sub) && (rhs.map linear).getD true)
    | .nullishAssign _ n _ _ => n != x
    | .logicalAssign _ _ (.var _ n) _ => n != x
    | _ => true

/-- Which rules propose (each a commit's rule): `counters`, `carried`. -/
structure Rules where
  /-- The kind of a binding's `length` (`HeapKnowledge.Term.Kind`): an
  array's, a typed array's (`view`) or a string's. -/
  kind : String → HeapKnowledge.Term.Kind := fun _ => .length
  counters : Bool := true
  carried : Bool := true
  /-- Store separations: of a fresh empty array field, carried, copied. -/
  separations : Bool := true
  /-- The bindings that may hold arrays, a fresh field's separations' other side. -/
  arrays : List String := []
  /-- A binding the loop assigns otherwise than by a constant step, an
  integer at entry: its integrality, its entry's lower bounds and
  `2^32 - 1` where the test bounds it above (the join's candidates). -/
  assigned : Bool := true
  /-- A binding the loop steps by `c` at most once an iteration, beside a
  counter its update steps by `c`: its integrality, its entry's lower bound
  and its difference from the counter at entry. -/
  paired : Bool := true
  /-- Forced (`TSCERT_FORCE=head-paired`): each paired binding also stated at
  most `-1`, the adversarial proposal the pass's edge check refuses. -/
  falsePaired : Bool := false
  /-- Forced (`TSCERT_FORCE=head-counters`): each counter also stated at
  most `-1`, the adversarial proposal the pass's edge check refuses. -/
  falseCounters : Bool := false
  /-- Forced (`TSCERT_FORCE=head-carried`): each term of a carried fact also
  stated at most `-1` (`xs.length ≤ -1`), the adversarial proposal the
  pass's edge check refuses. -/
  falseCarried : Bool := false
  /-- Forced (`TSCERT_FORCE=head-separations`): each carried separation's
  first store also stated apart from itself (`x.f !== x.f`), the adversarial
  proposal the pass's edge check refuses. -/
  falseSeparations : Bool := false
  /-- Forced (`TSCERT_FORCE=head-kinds`): each string's or typed array's
  length a proposal names also stated at most `-1`, the adversarial proposal
  the pass's edge check refuses. -/
  falseKinds : Bool := false
  /-- Forced (`TSCERT_FORCE=head-arms`): a binding assigned a choice arm by
  arm (`armsOf`) also stated at most `-1` after it, the adversarial fact a
  loop head it reaches proposes and the pass's edge check refuses. -/
  falseArms : Bool := false
  /-- Forced (`TSCERT_FORCE=head-entails`): a counter one of whose candidates
  the entry does not entail (`Ctx.entails`) also stated at most `-1`, the
  adversarial proposal the pass's edge check refuses. -/
  falseEntails : Bool := false
  /-- Forced (`TSCERT_FORCE=head-every`): each carried quantified fact also
  stated with the body `a[i] ≤ -1`, the adversarial proposal the pass's
  edge check refuses. -/
  falseEvery : Bool := false
  /-- Forced (`TSCERT_FORCE=head-exits`): a counter of a test-free loop
  bounded by an exit test (`headFacts`'s `exited`) also stated at most
  `-1`, the adversarial proposal the pass's edge check refuses. -/
  falseExits : Bool := false
  /-- Forced (`TSCERT_FORCE=head-guards`): of each guarded fact a test
  discharges (`Ctx.unguarded`), its first term also stated at most `-1`,
  the adversarial fact a loop head it reaches proposes and the pass's edge
  check refuses. -/
  falseGuards : Bool := false
  /-- Forced (`TSCERT_FORCE=head-restated`): of each linear fact restated
  through a path's read or an alias (`Fact.restate`), its first term also
  stated at most `-1`, the adversarial fact a loop head it reaches proposes
  and the pass's edge check refuses. -/
  falseRestated : Bool := false
  /-- Forced (`TSCERT_FORCE=head-elements`): a binding an element read bounds
  (`Ctx.elemFacts`) also stated at most `-1`, the adversarial fact a loop head
  it reaches proposes (a counter's too) and the pass's edge check refuses. -/
  falseElements : Bool := false
  /-- Forced (`TSCERT_FORCE=head-called`): of each fact a call in the loop
  gives its actuals' fields (`headFacts`'s `called`), its first term also
  stated at most `-1`, the adversarial proposal the pass's edge check
  refuses. -/
  falseCalled : Bool := false
  /-- Forced (`TSCERT_FORCE=head-eliminated`): of each carried fact a field
  path's entry value rewrites over bindings (`headFacts`'s `eliminated`),
  its first term also stated at most `-1`, the adversarial proposal the
  pass's edge check refuses. -/
  falseEliminated : Bool := false
  /-- Each function's postcondition (`@ensures`) by its name: a call's
  facts of the binding it sets (`callEnsures`). -/
  ensuresOf : String → List HeapKnowledge.IndexFact := fun _ => []
  /-- Forced (`TSCERT_FORCE=head-ensures`): each term of the binding a
  call's postcondition names also stated at most `-1` (`callEnsures`), the
  adversarial fact a loop head it reaches proposes and the pass's edge check
  refuses. -/
  falseEnsures : Bool := false

/-- The typed arrays' constructors: a value one constructs has a view
length (`HeapKnowledge.Term.Kind.view`). -/
def typedArrays : List String :=
  ["Int8Array", "Uint8Array", "Uint8ClampedArray", "Int16Array", "Uint16Array", "Int32Array", "Uint32Array",
    "Float32Array", "Float64Array"]

/-- What the walk knows: the facts it believes hold, over source names. -/
abbrev Ctx := List Fact

def Ctx.kill (ctx : Ctx) (ns : List String) : Ctx := ctx.filter fun f => !f.names.any ns.contains

/-- The bindings whose arrays expressions resize by name: each root of a
resizing method's receiver (`push`, `pop`, `shift`, `unshift`, `splice`), of a
written element's or field's receiver. A callee that resizes an array it is
passed is the pass's to find: the proposal's edge check refuses it. -/
def touched (es : List Expr) : List String :=
  let root := fun (e : Expr) => (pathOf e).map (·.1) |>.toList
  es.flatMap fun
    | .invoke _ (.read _ (.str m) r) _ _ _ =>
      if ["push", "pop", "shift", "unshift", "splice", "fill", "copyWithin"].contains m then root r else []
    | .elemWrite _ r _ _ | .indexWrite _ _ r _ _ | .write _ _ r _ => root r
    | .objectAssign _ t _ => root t
    | _ => []

/-- Whether a fact survives expressions that may write the heap: a fact of
bindings' values and strings' lengths always; of an array's or typed
array's length where no expression may resize it (`touched`); of a field
path where every expression is quiet. -/
partial def Fact.keptAcross (es : List Expr) : Fact → Bool
  | .int _ => true
  -- A separation of stores: kept unless a field its paths read is written
  -- (`linear_facts.ml:skept`, a path's identity changed only by a write).
  | .apart _ _ pa _ pb => !es.any fun
    | .write _ (.str f) _ _ => pa.contains f || pb.contains f
    | .objectAssign .. => !(pa.isEmpty && pb.isEmpty)
    | _ => false
  | .guarded gs l => Fact.keptAcross es (.lin l) && (es.all quiet || gs.all (·.2.1.isEmpty))
  | .lin l =>
    let quietAll := es.all quiet
    let t := touched es
    l.terms.all fun ((n, p, k), _) =>
      if !p.isEmpty then quietAll
      else match k with
        | .value | .strLength => true
        | .length | .view => !t.contains n
  -- A quantified fact: across expressions writing no element and resizing
  -- none of its arrays by name, its array and terms read off bindings
  -- (`linear_facts.ml:estatement`'s kept facts; a write through an alias is
  -- the pass's to refuse).
  | .every a pa stop body =>
    es.all quiet || (pa.isEmpty && !es.any (fun | .elemWrite .. | .indexWrite .. => true | _ => false) &&
      let t := touched es
      let kept := fun ((n, p, k) : Key) => p.isEmpty && (k == .value || k == .strLength || !t.contains n)
      !t.contains a && kept stop && body.all fun (ts, _) => ts.all fun | (.term k, _) => kept k | _ => true)

/-- The guards a test's answer `pos` fails (`x.f !== null` holding: `x.f`
not `null`), through `!` and the conjuncts of a conjunction holding (of a
disjunction failing). -/
partial def failedTags (e : Expr) (pos : Bool) : List (String × List String × HeapKnowledge.GuardTag) :=
  match e with
  | .singletonTest _ tag equal testLeft l r =>
    if equal == pos then [] else
    match pathOf (if testLeft then l else r) with
    | none => []
    | some (n, p) => match tag with
      | .isNul => [(n, p, .null)]
      | .isUndef => [(n, p, .undef)]
      | .isNullish => [(n, p, .null), (n, p, .undef)]
      | _ => []
  | .not _ e => failedTags e (!pos)
  | .cast _ _ e => failedTags e pos
  | .logical _ andOp a b => if andOp == pos then failedTags a pos ++ failedTags b pos else []
  | _ => []

/-- The guarded facts a test's answer `pos` discharges: each guard the test
fails left out, a fact with none left its linear fact (`linear_facts.ml`'s
guarded facts narrowed by a test, ARITHMETIC.md "Guarded clauses"). -/
def Ctx.unguarded (ctx : Ctx) (c : Expr) (pos : Bool) (forced : Bool := false) : List Fact :=
  let failed := failedTags c pos
  if failed.isEmpty then [] else ctx.flatMap fun
    | .guarded gs l =>
      let rest := gs.filter (!failed.contains ·)
      if rest.length == gs.length then [] else
      -- (forced: the fact's first term at most `-1`)
      let false_ := match l.terms with
        | (t, _) :: _ => if forced && rest.isEmpty then [Fact.lin ⟨[(t, 1)], -1⟩] else []
        | [] => []
      (if rest.isEmpty then .lin l else .guarded rest l) :: false_
    | _ => []

/-- The facts that survive expressions (`Fact.keptAcross`). -/
def Ctx.across (ctx : Ctx) (es : List Expr) : Ctx :=
  if es.all quiet then ctx else ctx.filter (Fact.keptAcross es)

def Ctx.add (ctx : Ctx) (fs : List Fact) : Ctx := ctx ++ fs.filter (!ctx.contains ·)

/-- Whether a value term holds a safe integer by the facts: a binding an
integrality states; a path a linear fact names, which holds of a path only
where it reads a safe integer (`linear_facts.ml:is_int` of a path term,
bound-annotations.mts's `safeInteger(p.f)`). -/
def Ctx.integral (ctx : Ctx) : String × List String → Bool
  | (n, []) => ctx.contains (.int n)
  | (n, p) => ctx.any fun
    | .lin l => l.terms.any fun ((m, q, k), _) => m == n && q == p && k == .value
    | _ => false

/-- A binding equal to a linear value: its two bounds, and its integrality
where the value is an integer literal or a length. -/
def Ctx.defines (ctx : Ctx) (l : Lin) : Bool :=
  l.terms.all fun ((n, p, k), _) => k != .value || ctx.integral (n, p)

/-- A test's comparisons whose bindings each hold an integer: an operand is
linear only so (`linear_facts.ml:linear`, an identifier with an
integrality fact). -/
def Ctx.tested (ctx : Ctx) (ls : List Lin) : List Fact := (ls.filter ctx.defines).map .lin

def equalTo (ctx : Ctx) (x : String) (v : List (Key × Int) × Int) : List Fact :=
  if v.1.any (·.1.1 == x) || !ctx.defines ⟨v.1, 0⟩ then [] else
  let le := addTerms [((x, [], .value), 1)] (scale (-1) v.1)
  let integral := v.1.all fun ((n, p, k), _) => k != .value || ctx.integral (n, p)
  [.lin ⟨le, v.2⟩, .lin ⟨scale (-1) le, -v.2⟩] ++ (if integral then [.int x] else [])

/-- A binding a choice `c ? a : b` of linear arms sets (`linear_facts.ml`'s
conditional expressions arm by arm, joined): within both arms from the side
the test picks, `x ≤ a ∧ x ≤ b` where it picks the smaller (`a < b ? a : b`,
`a <= b ? a : b`), `a ≤ x ∧ b ≤ x` where the larger. -/
def choiceBounds (K : String → HeapKnowledge.Term.Kind) (x : String) : Expr → List Fact
  | .ifBody _ c a b => match linOf K a, linOf K b with
    | some va, some vb =>
      let diff := addTerms va.1 (scale (-1) vb.1)
      -- (each answer of the test states the order of the arm it picks: a
      -- comparison's two answers, an equality's false answer none)
      let same := fun (x y : List (Key × Int)) => x.length == y.length && x.all y.contains
      let aBelow := fun (answer : Bool) => (atomsOf K c answer).any fun l => same l.terms diff && l.bound ≤ vb.2 - va.2
      let bBelow := fun (answer : Bool) => (atomsOf K c answer).any fun l => same l.terms (scale (-1) diff) && l.bound ≤ va.2 - vb.2
      let picksSmaller := aBelow true && bBelow false
      let picksLarger := bBelow true && aBelow false
      let xt : List (Key × Int) := [((x, [], .value), 1)]
      let le := fun (v : List (Key × Int) × Int) => Fact.lin ⟨addTerms xt (scale (-1) v.1), v.2⟩
      let ge := fun (v : List (Key × Int) × Int) => Fact.lin ⟨addTerms (scale (-1) xt) v.1, -v.2⟩
      if va.1.any (·.1.1 == x) || vb.1.any (·.1.1 == x) then []
      -- (an arm reading a length: as `valueArms`)
      else if !(va.1 ++ vb.1).all (·.1.2.2 == .value) then []
      else if picksSmaller then [le va, le vb] else if picksLarger then [ge va, ge vb] else []
    | _, _ => []
  | .cast _ _ e => choiceBounds K x e
  | _ => []

/-- A precondition's fact (`Fragment.Fn.requires`, at the function's
positions: `0` the receiver, `i + 1` the `i`-th parameter) over the
parameters' names, where it is a linear fact or an integrality. -/
partial def ofIndexFact (nameAt : Nat → Option String) : HeapKnowledge.IndexFact → Option Fact
  | .int p => (nameAt p).map .int
  | .storeApart a pa b pb => do pure (.apart [] (← nameAt a) pa (← nameAt b) pb)
  | .guarded g p t body => do
    match ← ofIndexFact nameAt body with
    | .apart gs a pa b pb => pure (.apart ((← nameAt g, p, t) :: gs) a pa b pb)
    | .lin l => pure (.guarded [(← nameAt g, p, t)] l)
    | .guarded gs l => pure (.guarded ((← nameAt g, p, t) :: gs) l)
    | _ => none
  | .linear (.le form d) => do
    let ts ← form.mapM fun (t, c) => do pure (((← nameAt t.slot), t.path, t.kind), c)
    let ts := addTerms [] ts
    if ts.isEmpty then none else pure (.lin ⟨ts, d⟩)
  | .every s path stop body => do
    let a ← nameAt s
    let var : HeapKnowledge.Bound → Option BodyKey := fun
      | .index => some .index
      | .elem => some .elem
      | .offset d => some (.offset d)
      | .project k p => some (.project k p)
      | .free t => (nameAt t.slot).map fun n => .term (n, t.path, t.kind)
    let body ← body.mapM fun
      | .atom (.le form d) => do pure (← form.mapM fun (b, c) => do pure (← var b, c), d)
      | .either .. | .atom (.ne ..) => none
    pure (.every a path (← nameAt stop.slot, stop.path, stop.kind) body)
  | _ => none

def ofRequires (params : List String) : HeapKnowledge.IndexFact → Option Fact :=
  ofIndexFact fun p => if p == 0 then none else params[p - 1]?

/-- The fields an object literal of named fields gives the binding `x` it
initializes, `const x = { f: e, … }`: each linear field's value the path's
(`linear_facts.ml:declaration`'s `Alloc`, Lean's `freshLinks`). -/
def allocFields (K : String → HeapKnowledge.Term.Kind) (ctx : Ctx) (x : String) : Expr → List Fact
  | .alloc _ names es => (names.zip es).flatMap fun
    | (.str f, e) => match linOf K e with
      | some v =>
        if v.1.any (·.1.1 == x) || !ctx.defines ⟨v.1, 0⟩ then [] else
        let le := addTerms [((x, [f], .value), 1)] (scale (-1) v.1)
        [.lin ⟨le, v.2⟩, .lin ⟨scale (-1) le, -v.2⟩]
      | none => []
    | _ => []
  | .cast _ _ e => allocFields K ctx x e
  | _ => []

/-- A typed array a binding's initializer constructs at a linear length
(`new Int32Array(n)`): its view length equal to it (the construction's
postcondition, `linear_facts.ml`'s postconditions of constructors). -/
def constructedLength (K : String → HeapKnowledge.Term.Kind) (x : String) : Expr → List Fact
  | .construct _ (.var _ t) [arg] _ _ =>
    if !typedArrays.contains t then [] else match linOf K arg with
    | some v =>
      if v.1.any (·.1.1 == x) then [] else
      let le := addTerms [((x, [], .view), 1)] (scale (-1) v.1)
      [.lin ⟨le, v.2⟩, .lin ⟨scale (-1) le, -v.2⟩]
    | none => []
  | _ => []

/-- The separations a declaration of `x` states (`linear_facts.ml:sstatement`):
an object literal's field holding a fresh empty array (`{ f: [] }`) apart from
every array binding of `arrays` (an array binding's store is never the fresh
one); a copy (`const x = o`) each of `o`'s separations at `x`; a choice of `o`
and `null` (`c ? o : null`) each guarded by `x === null`. -/
def separations (arrays : List String) (ctx : Ctx) (x : String) : Expr → List Fact
  | .alloc _ names es =>
    (names.zip es).flatMap fun (k, e) => match k, e with
      | .str f, .arrayLit _ [] _ => (arrays.filter (· != x)).map fun a => Fact.apart [] x [f] a []
      | _, _ => []
  | .var _ o => copies o []
  | .ifBody _ _ (.var _ o) (.lit _ .vnull) | .ifBody _ _ (.lit _ .vnull) (.var _ o) => copies o [(x, [], .null)]
  | .cast _ _ e => separations arrays ctx x e
  | _ => []
where
  copies (o : String) (guards : List (String × List String × HeapKnowledge.GuardTag)) : List Fact :=
    ctx.filterMap fun
      | .apart [] a pa b pb =>
        if a == o && b != x then some (.apart guards x pa b pb)
        else if b == o && a != x then some (.apart guards a pa x pb) else none
      | _ => none

/-- A binding stepped by `c`: each fact restated at its shifted bound. -/
def Ctx.step (ctx : Ctx) (x : String) (c : Int) : Ctx :=
  ctx.filterMap fun
    | .lin l => match l.terms.find? (·.1 == (x, [], .value)) with
      | some (_, a) => some (.lin { l with bound := l.bound + a * c })
      | none => some (.lin l)
    -- (a quantified fact naming the binding: forgotten)
    | f@(.every ..) => if f.names.contains x then none else some f
    | f => some f

/-- A quantified or linear fact restated where the binding `n` is declared
at the read of the path `path` from `root` (`linear_facts.ml:erestate_read`):
its array, its bound and its terms through the path, of `n`. -/
def Fact.restate (n root : String) (path : List String) : Fact → Option Fact
  | f@(.every a pa stop body) =>
    let through := fun (m : String) (p : List String) =>
      if m == root && path.isPrefixOf p then some (n, p.drop path.length) else none
    let move := fun ((m, p, k) : Key) => match through m p with
      | some (n', p') => (n', p', k)
      | none => (m, p, k)
    let (a', pa') := (through a pa).getD (a, pa)
    let f' := Fact.every a' pa' (move stop) (body.map fun (ts, d) =>
      (ts.map fun | (.term k, c) => (.term (move k), c) | v => v, d))
    if f' == f then none else some f'
  | f@(.lin l) =>
    let move := fun ((m, p, k) : Key) =>
      if m == root && path.isPrefixOf p then (n, p.drop path.length, k) else (m, p, k)
    let f' := Fact.lin { l with terms := addTerms [] (l.terms.map fun (t, c) => (move t, c)) }
    if f' == f then none else some f'
  | f@(.guarded gs l) =>
    let move := fun ((m, p, k) : Key) =>
      if m == root && path.isPrefixOf p then (n, p.drop path.length, k) else (m, p, k)
    let gs' := gs.map fun (g, p, t) => if g == root && path.isPrefixOf p then (n, p.drop path.length, t) else (g, p, t)
    let f' := Fact.guarded gs' { l with terms := addTerms [] (l.terms.map fun (t, c) => (move t, c)) }
    if f' == f then none else some f'
  | _ => none

/-- Whether the facts entail a linear fact (`linear_facts.ml:entails`, with
`term_ranges`): a fact whose terms differ from its by lengths alone, at a
bound that each length's range (`0 ≤ n.length ≤ 2^32 - 1`, a string's
`≤ 2^53 - 1`) keeps at most its own; the empty fact `0 ≤ 0` among them. -/
def Ctx.entails (ctx : Ctx) (l : Lin) : Bool :=
  -- The largest value of lengths' sum, where every term is a length.
  let rangeMax := fun (ts : List (Key × Int)) => ts.foldlM (init := (0 : Int)) fun acc ((_, _, k), c) =>
    match k with
    | .value => none
    | .strLength => some (if c < 0 then acc else acc + c * (2 ^ 53 - 1))
    | _ => some (if c < 0 then acc else acc + c * (2 ^ 32 - 1))
  let via := fun (terms : List (Key × Int)) (b : Int) =>
    match rangeMax (addTerms l.terms (scale (-1) terms)) with
    | some m => b + m ≤ l.bound
    | none => false
  via [] 0 || ctx.any fun
    | .lin l' => via l'.terms l'.bound
    | _ => false

/-- A quantified fact's body fact `c·elem + Σ ≤ d` at the index `k`
(`kt + kc`): where `c` is `1` (`upper`) or `-1`, the linear form the element
is at most or at least. -/
def bodyBound (upper : Bool) (kt : List (Key × Int)) (kc : Int) (ts : List (BodyKey × Int)) (d : Int) :
    Option (List (Key × Int) × Int) := do
  let c ← ts.lookup BodyKey.elem
  if c != (if upper then 1 else -1) then none
  let rest := ts.filter fun (v, _) => v != BodyKey.elem
  let sum ← rest.foldlM (init := (([] : List (Key × Int)), (0 : Int))) fun (acc, ac) (v, c') =>
    match v with
    | .term t => some (addTerms acc [(t, c')], ac)
    | .index => some (addTerms acc (scale c' kt), ac + c' * kc)
    | _ => none
  -- `elem + Σ ≤ d`: at most `d - Σ`; `-elem + Σ ≤ d`: at least `Σ - d`
  if upper then pure (scale (-1) sum.1, d - sum.2) else pure (sum.1, sum.2 - d)

/-- An element read `xs[k]` at an index the facts place in `xs`'s range,
bounded by a quantified fact over `xs`'s whole array: the linear form it is
at most (`upper`) or at least, its body's fact restated at the index `k`
(`linear_facts.ml:element_facts`, `instantiate`). -/
partial def Ctx.elemBound (K : String → HeapKnowledge.Term.Kind) (ctx : Ctx) (upper : Bool) : Expr →
    List (List (Key × Int) × Int)
  | .cast _ _ e => ctx.elemBound K upper e
  | .call _ (.var _ n) [xs, k] _ _ =>
    if n == "%ElementAt%" || n == "%ByteAt%" then ctx.elemBound K upper (.index default none xs k) else []
  | .index _ none (.var _ xs) k => match linOf K k with
    | none => []
    | some (kt, kc) =>
      if !ctx.entails ⟨scale (-1) kt, kc⟩ then [] else
      -- (an index below the fact's stop: its array's length, or a prefix's
      -- bound, `forall i < n of xs`)
      ctx.flatMap fun (f : Fact) => match f with
        | .every b [] stop body =>
          if b != xs || !ctx.entails ⟨addTerms kt [(stop, -1)], -1 - kc⟩ then [] else
          body.filterMap fun (ts, d) => bodyBound upper kt kc ts d
        | _ => []
  | _ => []

/-- The facts a binding `x` an element read sets holds (`Ctx.elemBound`):
its integrality and its bounds. -/
def Ctx.elemFacts (K : String → HeapKnowledge.Term.Kind) (ctx : Ctx) (x : String) (e : Expr) (forced : Bool := false) :
    List Fact :=
  let xt : List (Key × Int) := [((x, [], .value), 1)]
  let up := (ctx.elemBound K true e).filter (fun (ts, _) => !ts.any (·.1.1 == x)) |>.map fun (ts, d) =>
    Fact.lin ⟨addTerms xt (scale (-1) ts), d⟩
  let lo := (ctx.elemBound K false e).filter (fun (ts, _) => !ts.any (·.1.1 == x)) |>.map fun (ts, d) =>
    Fact.lin ⟨addTerms (scale (-1) xt) ts, -d⟩
  let fs := up ++ lo
  -- (forced: the binding also at most `-1`)
  let false_ := if forced then [Fact.lin ⟨[((x, [], .value), 1)], -1⟩] else []
  if fs.isEmpty then [] else .int x :: fs ++ false_

/-- The quantified facts `xs.push(a)` keeps over `xs`'s whole array: each
whose body's facts the facts state of `a` at the index `xs.length`
(`linear_facts.ml:egrown`, `every-push`). -/
def Ctx.pushed (K : String → HeapKnowledge.Term.Kind) (ctx : Ctx) : Expr → List Fact
  | .invoke _ (.read _ (.str "push") (.var _ xs)) [a] _ _ =>
    match linOf K a with
    | none => []
    | some (at_, ac) => ctx.filter fun
      | .every b [] stop body => b == xs && stop == (xs, [], K xs) && body.all fun (ts, d) =>
        let k := ((ts.find? (·.1 == .elem)).map (·.2)).getD 0
        let terms := ts.foldl (init := (some [] : Option (List (Key × Int)))) fun acc (v, c) => do
          let acc ← acc
          match v with
          | .index => pure (addTerms acc [((xs, [], K xs), c)])
          | .elem => pure (addTerms acc (scale c at_))
          | .term t => pure (addTerms acc [(t, c)])
          | _ => none
        match terms with
        | some ts => ctx.entails ⟨ts, d - k * ac⟩
        | none => false
      | _ => false
  | _ => []

/-- Two states joined: each fact of `a` that `b` holds, and each linear fact
of `a` whose terms a linear fact of `b` bounds, at the larger bound. -/
def Ctx.join (a b : Ctx) : Ctx :=
  a.filterMap fun
    | .lin l => (b.filterMap fun
        | .lin l' => if l'.terms == l.terms then some (Fact.lin { l with bound := max l.bound l'.bound }) else none
        | _ => none).head?
    | f => if b.contains f then some f else none

/-- The facts a call of a function stating a postcondition gives the
binding `x` it sets: each of its `@ensures` facts (position `0` its result,
`p + 2` its `p`-th parameter), its result `x` and each parameter the actual
where that is a binding (`linear_facts.ml:call_expression_facts`). -/
def callEnsures (ensures : String → List HeapKnowledge.IndexFact) (x : String) (forced : Bool := false) :
    Expr → List Fact
  | .call _ (.var _ f) args [] _ =>
    let nameAt := fun (p : Nat) => if p == 0 then some x else if p < 2 then none else match args[p - 2]? with
      | some (.var _ a) => if a == x then none else some a
      | _ => none
    let fs := (ensures f).filterMap (ofIndexFact nameAt)
    -- (forced: each term of `x` a fact names at most `-1`)
    let falses : List Fact := if !forced then [] else
      ((fs.flatMap fun | .lin l => l.terms.map (·.1) | _ => []).filter (·.1 == x)).eraseDups.map fun t => .lin ⟨[(t, 1)], -1⟩
    fs ++ falses
  | .cast _ _ e => callEnsures ensures x forced e
  | _ => []

/-- The facts a choice `c ? a : b` gives the binding `x` it sets: on each
arm, under what its answer of `c` states, `x` equal to a linear arm or a
call's postcondition (`callEnsures`), the two joined
(`linear_facts.ml:declaration`'s conditional, arm by arm). -/
def valueArms (K : String → HeapKnowledge.Term.Kind) (ensures : String → List HeapKnowledge.IndexFact)
    (ctx : Ctx) (x : String) (forced : Bool := false) : Expr → List Fact
  | .ifBody _ c a b =>
    -- (an arm reading a length states nothing of the choice's value: the
    -- pass's merge of the arms keeps a fact of the value where each arm
    -- states it of its own, which a length's link does not carry)
    let arm := fun (answer : Bool) (e : Expr) =>
      let ctx' := ctx.add (ctx.tested (atomsOf K c answer))
      match linOf K e with
      | some v => if v.1.all (·.1.2.2 == .value) then equalTo ctx' x v else []
      | none => callEnsures ensures x forced e
    let l := arm true a
    let r := arm false b
    if l.isEmpty || r.isEmpty then [] else (Ctx.join l r).filter fun f => f.names.contains x
  | .cast _ _ e => valueArms K ensures ctx x forced e
  | _ => []

/-- The facts after an expression statement: an assignment of a linear
value states its equality, a step restates, any other write forgets. -/
def Ctx.effectOne (K : String → HeapKnowledge.Term.Kind) (ctx : Ctx) (e : Expr)
    (ensures : String → List HeapKnowledge.IndexFact := fun _ => []) (falseEnsures : Bool := false) : Ctx :=
  let pushed := ctx.pushed K e
  let ctx := (ctx.across (allExprs e)).add pushed
  match e with
  | .assign _ x _ rhs => match stepOf x e with
    | some (some c) => ctx.step x c
    | _ =>
      let ctx := ctx.kill [x]
      match linOf K rhs with
      | some v => ctx.add (equalTo ctx x v)
      | none => ctx.add (choiceBounds K x rhs ++ callEnsures ensures x falseEnsures rhs ++
          valueArms K ensures ctx x falseEnsures rhs)
  | .update _ _ (.var _ x) _ _ => match stepOf x e with
    | some (some c) => ctx.step x c
    | _ => ctx.kill [x]
  | _ =>
    let written := ((allExprs e).filterMap fun
      | .assign _ n _ _ | .nullishAssign _ n _ _ => some n
      | .update _ _ (.var _ n) _ _ | .logicalAssign _ _ (.var _ n) _ => some n
      | _ => none)
    ctx.kill written

/-- An assignment of a choice, `x ± (c ? p : q)` (`x += c ? p : q`, `x = a ±
(c ? p : q)` with `a` a binding or a literal): the assignment of each arm
under the facts its answer of `c` states, the two joined
(`linear_facts.ml:distribute`, `assign_arms`). -/
def armsOf (x : String) : Expr → Option (Expr × Expr × Expr)
  | .update pos op (.var vp n) (some (.ifBody _ c p q)) post =>
    if n == x && (op == .add || op == .sub) && quiet c then
      some (c, .update pos op (.var vp n) (some p) post, .update pos op (.var vp n) (some q) post)
    else none
  | .assign pos n np (.arith ap op a (.ifBody _ c p q)) =>
    let operand := match a with
      | .var _ m => !(allExprs c).any fun | .assign _ k _ _ => k == m | .update _ _ (.var _ k) _ _ => k == m | _ => false
      | .lit .. => true
      | _ => false
    if n == x && (op == .add || op == .sub) && operand && quiet c then
      some (c, .assign pos n np (.arith ap op a p), .assign pos n np (.arith ap op a q))
    else none
  | _ => none

/-- The facts after an expression statement (`Ctx.effectOne`), an assignment
of a choice arm by arm (`armsOf`). -/
def Ctx.effect (K : String → HeapKnowledge.Term.Kind) (ctx : Ctx) (e : Expr) (falseArms : Bool := false)
    (ensures : String → List HeapKnowledge.IndexFact := fun _ => []) (falseEnsures : Bool := false) : Ctx :=
  let x := match e with
    | .update _ _ (.var _ n) _ _ | .assign _ n _ _ => some n
    | _ => none
  match x.bind (armsOf · e) with
  | some (c, p, q) =>
    let x := x.getD ""
    let base := (ctx.across (allExprs e)).kill [x]
    let l := (ctx.add (ctx.tested (atomsOf K c true))).effectOne K p ensures
    let r := (ctx.add (ctx.tested (atomsOf K c false))).effectOne K q ensures
    -- (forced: the binding at most `-1`)
    let forced := if falseArms then [Fact.lin ⟨[((x, [], .value), 1)], -1⟩] else []
    base.add ((l.join r).filter (fun f => f.names.contains x) ++ forced)
  | none => ctx.effectOne K e ensures falseEnsures

/-- The expressions of the loops nested in statements. -/
partial def nestedExprs : List Stmt → List Expr
  | [] => []
  | s :: rest => (match s with
    | .loop _ c b u _ => allExprs c ++ exprsOf b ++ exprsOf u
    | .forOf _ _ _ _ i b => allExprs i ++ exprsOf b
    | .ite _ _ t e => nestedExprs t ++ nestedExprs (e.getD [])
    | .block _ _ b => nestedExprs b
    | .tryStmt _ b h f => nestedExprs b ++ nestedExprs ((h.map (·.2)).getD []) ++ nestedExprs (f.getD [])
    | .closing _ c b => nestedExprs c ++ nestedExprs b
    | _ => []) ++ nestedExprs rest

/-- A binding's constant value where the facts state it (`x ≤ k ∧ -x ≤ -k`). -/
def Ctx.constOf (ctx : Ctx) (x : String) : Option Int :=
  ctx.findSome? fun
    | .lin ⟨[((n, [], .value), 1)], k⟩ =>
      if n == x && ctx.contains (.lin ⟨[((x, [], .value), -1)], -k⟩) then some k else none
    | _ => none

/-- A binding's value as a linear form of others where the facts state it
(`x - Σ ≤ k ∧ Σ - x ≤ -k`): `x = Σ + k`. -/
def Ctx.equalOf (ctx : Ctx) (x : String) : Option (List (Key × Int) × Int) :=
  let xt : Key := (x, [], .value)
  ctx.findSome? fun
    | .lin l =>
      if (l.terms.lookup xt) != some 1 then none else
      let rest := l.terms.filter (·.1 != xt)
      if rest.any (·.1.1 == x) then none else
      if ctx.contains (.lin ⟨addTerms [(xt, -1)] (scale (-1) rest), -l.bound⟩) then some (scale (-1) rest, l.bound) else none
    | _ => none

/-- A fact with the binding `x` replaced by its value where the facts state
it (`Ctx.equalOf`). -/
def Ctx.substitute (ctx : Ctx) (x : String) (l : Lin) : Lin :=
  let xt : Key := (x, [], .value)
  match l.terms.lookup xt, ctx.equalOf x with
  | some a, some (v, k) => ⟨addTerms (l.terms.filter (·.1 != xt)) (scale a v), l.bound - a * k⟩
  | _, _ => l

/-- A loop's head facts (`rules`): over the bindings it does not assign,
the facts its entry holds (`carried`); of each counter (`counters`), its
integrality, its entry's facts a step keeps (a bound below an increasing
counter, above a decreasing one), the test's bound shifted by the step, a
disequality's as a bound, and `2^32 - 1` above an increasing counter the
test bounds, the last three where the entry entails them (`Ctx.entails`). -/
def headFacts (rules : Rules) (ctx : Ctx) (cond : Expr) (loop : List Stmt) (update : List Stmt := []) : List Fact :=
  let K := rules.kind
  let assigned := (ctx.flatMap Fact.names ++ (exprsOf loop ++ allExprs cond).filterMap (fun
      | .assign _ n _ _ | .nullishAssign _ n _ _ => some n
      | .update _ _ (.var _ n) _ _ | .logicalAssign _ _ (.var _ n) _ => some n
      | _ => none)).eraseDups.filter (assigns loop ·)
  let resized := resized loop
  let lengthKept := fun (f : Fact) => match f with
    | .lin l => l.terms.all fun ((n, _, k), _) => k == .value || !resized.contains n
    | _ => true
  -- A field path's length across the loop only where it is quiet
  -- (`linear_facts.ml:term_kept`: a path term is kept where the change
  -- writes no object, a call of no stated footprint writing any).
  let quietLoop := (exprsOf loop ++ allExprs cond).all quiet
  let pathKept := fun (l : Lin) => quietLoop || l.terms.all fun ((_, p, _), _) => p.isEmpty
  -- A test's upper bound below `2^32 - 1`: by arrays' lengths, or by
  -- bindings the entry bounds by arrays' lengths (`linear_facts.ml:join`'s
  -- candidate `2^32 - 1`, which an array's length bounds; a string's
  -- length bounds it by `2^53 - 1` alone).
  let lengthBounded := fun (m : String) => ctx.any fun
    | .lin l => l.bound ≤ 0 && l.terms.any (fun ((n, p, k), c) => n == m && p.isEmpty && k == .value && c > 0) &&
        l.terms.all fun ((n, p, k), c) => (n == m && p.isEmpty && k == .value) || ((k == .length || k == .view) && c < 0)
    | _ => false
  let arrayBound := fun (x : String) (l : Lin) => l.terms.all fun ((n, p, k), c) =>
    (n == x && p.isEmpty && k == .value) || ((k == .length || k == .view) && c < 0) ||
      (k == .value && p.isEmpty && c < 0 && lengthBounded n)
  -- (a quantified fact: where the loop keeps it, `Fact.keptAcross`)
  let loopEs := exprsOf loop ++ allExprs cond
  let everyKept := fun (f : Fact) => match f with
    | .every .. => f.keptAcross loopEs
    | _ => true
  let carried := if rules.carried then
    ctx.filter fun f => !f.names.any assigned.contains && lengthKept f && everyKept f else []
  let tests := (atomsOf K cond true (fun e u => ctx.elemBound K u e)).filter fun l =>
    ctx.defines ⟨l.terms.filter fun ((n, _, _), _) => !assigned.contains n, 0⟩
  -- A test-free loop's (`while (true)`) exit tests: of each statement of
  -- its body from the one holding a counter's last step that leaves the
  -- loop where its test holds (`if (t) return …`, a step in the test read
  -- as done, `++x >= n`), the test's failure, which the back edge carries
  -- where no `continue` goes back earlier (`linear_facts.ml:join` of the back
  -- edge's facts with the entry's at the head's fixpoint).
  let exitTests := fun (x : String) => match cond with
    | .lit _ (.vbool true) =>
      if continues loop then [] else
      match (loop.zipIdx.filter fun ((st : Stmt), (_ : Nat)) => assignsStmt x st).getLast? with
      | some (_, last) => (loop.drop last).flatMap fun (st : Stmt) => match st with
          | .ite _ c t none => if !exits t then [] else (atomsOf K (stepped x c) false).filter fun (l : Lin) =>
              ctx.defines ⟨l.terms.filter fun ((n, _, _), _) => !assigned.contains n, 0⟩
          | _ => []
      | none => []
    | _ => []
  let counters := if !rules.counters then [] else
    (assigned.filterMap fun x => if ctx.contains (.int x) then (counterStep loop x).map (x, ·) else none)
  -- A candidate the join keeps only where the entry entails it, the
  -- binding's entry value substituted (`linear_facts.ml:join`'s `bound` of
  -- the entry's side).
  let atEntry := fun (x : String) (f : Fact) => match f with
    | .lin l => ctx.entails l || ctx.entails (ctx.substitute x l)
    | _ => true
  let counterFacts := counters.flatMap fun (x, c) =>
    let others := fun (l : Lin) => l.terms.all fun ((n, p, _), _) => n == x && p.isEmpty || !assigned.contains n
    let coeff := fun (l : Lin) => ((l.terms.find? (·.1 == (x, [], .value))).map (·.2)).getD 0
    -- A bound a step keeps: below an increasing counter, above a decreasing one.
    let kept := ctx.filterMap fun
      | .lin l => if others l && lengthKept (.lin l) && pathKept l && coeff l * c < 0 then some (Fact.lin l) else none
      | _ => none
    -- The test's bound on the counter, the step taken.
    let shifted := tests.filterMap fun l =>
      if others l && pathKept l && coeff l * c > 0 then some (Fact.lin { l with bound := l.bound + coeff l * c }) else none
    -- A disequality the counter steps towards by one, as the bound it keeps.
    let reached := if c.natAbs != 1 then [] else (neqOf K cond true).filterMap fun (ts, k) =>
      match ts.find? (·.1 == (x, [], .value)) with
      | some (_, a) => if a * c > 0 && ts.all (fun ((n, p, _), _) => n == x && p.isEmpty || !assigned.contains n)
          then some (Fact.lin ⟨ts, -k⟩) else none
      | none => none
    -- An exit test's bound on the counter, after the step: unshifted.
    let exited := (exitTests x).filterMap fun l =>
      if others l && pathKept l && coeff l * c > 0 then some (Fact.lin l) else none
    -- (`x - n ≤ d` stepped by `c` keeps `x ≤ 2^32 - 1` where `d + c ≤ 0`)
    let above := if c > 0 && (tests.any fun l => coeff l == 1 && arrayBound x l && l.bound + c ≤ 0) then
      [Fact.lin ⟨[((x, [], .value), 1)], 2 ^ 32 - 1⟩] else []
    let forced := if rules.falseCounters then [Fact.lin ⟨[((x, [], .value), 1)], -1⟩] else []
    -- (forced: where a candidate is left out, the counter at most `-1`)
    let forced := forced ++ if rules.falseEntails && (shifted ++ reached ++ above).any (!atEntry x ·)
      then [Fact.lin ⟨[((x, [], .value), 1)], -1⟩] else []
    let forced := forced ++ if rules.falseExits && !exited.isEmpty then [Fact.lin ⟨[((x, [], .value), 1)], -1⟩] else []
    let forced := forced ++ if rules.falseElements && ctx.contains (Fact.lin ⟨[((x, [], .value), 1)], -1⟩)
      then [Fact.lin ⟨[((x, [], .value), 1)], -1⟩] else []
    -- A counter the test does not read is bounded by nothing across the
    -- step: no safe integer, so nothing is proposed of it.
    -- So is one the test reads but bounds by no comparison on the step's
    -- side (`while (f(s.charCodeAt(x))) x++`): no safe integer either.
    -- (a disjunction bounds it where each disjunct does)
    let rec boundsStep (e : Expr) (fuel : Nat) : Bool :=
      (atomsOf K e true (fun e u => ctx.elemBound K u e)).any (fun l => coeff l * c > 0) || match fuel, e with
        | n + 1, .logical _ false a b => boundsStep a n && boundsStep b n
        | n + 1, .logical _ true a b => boundsStep a n || boundsStep b n
        | _, _ => false
    let bounded := boundsStep cond 16 || !reached.isEmpty || !exited.isEmpty
    if (!(cond.freeNames.contains x) || !bounded) && exited.isEmpty then forced else
    [Fact.int x] ++ kept ++ (shifted ++ reached ++ above ++ exited).filter (atEntry x) ++ forced
  -- The other bindings it assigns that enter as integers: the join's
  -- candidates, the entry's lower bounds and `2^32 - 1` below a test's bound.
  let joined := if !rules.assigned then [] else
    (assigned.filter fun x => !counters.any (·.1 == x) && ctx.contains (.int x) && linearWrites K loop x).flatMap fun x =>
      let others := fun (l : Lin) => l.terms.all fun ((n, p, _), _) => n == x && p.isEmpty || !assigned.contains n
      let coeff := fun (l : Lin) => ((l.terms.find? (·.1 == (x, [], .value))).map (·.2)).getD 0
      let lower := ctx.filterMap fun
        | .lin l => if others l && lengthKept (.lin l) && coeff l < 0 then some (Fact.lin l) else none
        | _ => none
      let above := if tests.any fun l => coeff l > 0 && arrayBound x l then
        [Fact.lin ⟨[((x, [], .value), 1)], 2 ^ 32 - 1⟩] else []
      [Fact.int x] ++ lower ++ above.filter (atEntry x)
  -- A binding the test does not read, stepped by `c` once at most an
  -- iteration (one step, in no nested loop), beside a counter the update
  -- steps by `c` on every iteration: the difference at entry bounds it
  -- (`x - y ≤ a - b` for `c > 0`), the join's candidate, and its entry value
  -- bounds it on the other side.
  let paired := if !rules.paired then [] else
    (assigned.filter fun x => ctx.contains (.int x) && !cond.freeNames.contains x).flatMap fun x =>
      match counterStep loop x, ctx.equalOf x with
      | some c, some (vx, a) =>
        let steps := (exprsOf loop).filter fun e => (stepOf x e).isSome
        if steps.length != 1 || (nestedExprs loop).any (fun e => (stepOf x e).isSome) then [] else
        -- (stepped by the update, every iteration: the difference is kept exactly)
        let everyIteration := (exprsOf update).any fun e => stepOf x e == some (some c)
        let partners := counters.filter fun (y, c') => c' == c && cond.freeNames.contains y &&
          (exprsOf update).any fun e => stepOf y e == some (some c)
        let xt : Key := (x, [], .value)
        -- `x - y ≤ (vx + a) - (vy + b)` (for `c > 0`), both ways where the update steps both
        let diffs := partners.flatMap fun (y, _) => match ctx.equalOf y with
          | some (vy, b) =>
            let yt : Key := (y, [], .value)
            if (vx ++ vy).any (fun ((n, _, _), _) => assigned.contains n) then [] else
            let form := addTerms (addTerms [(xt, 1), (yt, -1)] (scale (-1) vx)) vy
            let up := Fact.lin ⟨form, a - b⟩
            let down := Fact.lin ⟨scale (-1) form, b - a⟩
            if everyIteration then [up, down] else [if c > 0 then up else down]
          | none => []
        let own := if !vx.isEmpty then [] else [if c > 0 then Fact.lin ⟨[(xt, -1)], -a⟩ else Fact.lin ⟨[(xt, 1)], a⟩]
        let forced := if rules.falsePaired then [Fact.lin ⟨[(xt, 1)], -1⟩] else []
        if diffs.isEmpty then [] else [Fact.int x] ++ own ++ diffs ++ forced
      | _, _ => []
  -- Across a loop that may write a field, a carried fact's field path
  -- replaced by the path-free value an entry equality gives it (`t = e`,
  -- `t` a path's term, `e` over bindings): the fact over bindings alone,
  -- which a write of the field keeps (`segmentCount = prepared.widths.length`
  -- and `segmentFlags.length = prepared.widths.length` give
  -- `segmentCount = segmentFlags.length`).
  let pathFree := fun (ts : List (Key × Int)) => ts.all fun ((_, p, _), _) => p.isEmpty
  let valueOf : List (Key × (List (Key × Int) × Int)) := if quietLoop then [] else ctx.filterMap fun
    | .lin l => if !ctx.contains (.lin ⟨scale (-1) l.terms, -l.bound⟩) then none else
      match l.terms.filter (fun ((_, p, _), c) => !p.isEmpty && c.natAbs == 1) with
      | [(t, c)] =>
        let rest := l.terms.filter (·.1 != t)
        if !pathFree rest || rest.any (fun ((n, _, _), _) => assigned.contains n) then none
        -- (`c·t + rest = b`: `t = c·(b - rest)`)
        else some (t, (scale (-c) rest, c * l.bound))
      | _ => none
    | _ => none
  let eliminated := carried.flatMap fun
    | .lin l => valueOf.filterMap fun (t, (e, k)) =>
      match l.terms.find? (·.1 == t) with
      | some (_, a) =>
        let ts := addTerms (l.terms.filter (·.1 != t)) (scale a e)
        if ts.isEmpty || !pathFree ts then none else some (Fact.lin ⟨ts, l.bound - a * k⟩)
      | none => none
    | _ => []
  -- The facts a call in the loop states of its actuals' fields at its
  -- return (its `@ensures` at positions `p + 2`, a parameter's type
  -- invariant its body keeps among them, ARITHMETIC.md "Type invariants"),
  -- where the entry entails each and the loop assigns no binding it names:
  -- the join's candidates both edges state (`linear_facts.ml:join`).
  let called := (loopEs.flatMap allExprs).flatMap fun
    | .call _ (.var _ g) args [] _ =>
      let nameAt := fun (p : Nat) => if p < 2 then none else match args[p - 2]? with
        | some (.var _ a) => some a
        | _ => none
      (rules.ensuresOf g).filterMap fun F => match ofIndexFact nameAt F with
        | some (.lin l) =>
          if l.terms.all (fun ((n, p, _), _) => !p.isEmpty && !assigned.contains n) && ctx.entails l
          then some (Fact.lin l) else none
        | _ => none
    | _ => []
  let falseEliminated := if !rules.falseEliminated then [] else eliminated.filterMap fun
    | .lin ⟨(t, _) :: _, _⟩ => some (Fact.lin ⟨[(t, 1)], -1⟩)
    | _ => none
  let falseCalled := if !rules.falseCalled then [] else called.filterMap fun
    | .lin ⟨(t, _) :: _, _⟩ => some (Fact.lin ⟨[(t, 1)], -1⟩)
    | _ => none
  let falseCarried := if !rules.falseCarried then [] else carried.flatMap fun
    | .lin l => l.terms.map fun (t, _) => Fact.lin ⟨[(t, 1)], -1⟩
    | _ => []
  let falseEvery := if !rules.falseEvery then [] else carried.filterMap fun
    | .every a pa stop _ => some (Fact.every a pa stop [([(.elem, 1)], -1)])
    | _ => none
  let falseSeparations := if !rules.falseSeparations then [] else carried.filterMap fun
    | .apart _ a pa _ _ => some (Fact.apart [] a pa a pa)
    | _ => none
  -- (a fact once, whatever the order of its terms)
  let same := fun (a b : Fact) => match a, b with
    | .lin l, .lin l' => l.bound == l'.bound && l.terms.length == l'.terms.length && l.terms.all l'.terms.contains
    | _, _ => a == b
  (carried ++ eliminated ++ counterFacts ++ joined ++ paired ++ called ++ falseCarried ++ falseSeparations ++ falseEvery ++
    falseCalled ++ falseEliminated).foldl (fun acc f => if acc.any (same f) then acc else acc ++ [f]) []

mutual
/-- The walk: each loop's head facts by its statement's start, and the facts
after the statements. -/
partial def walk (rules : Rules) (ctx : Ctx) (ss : List Stmt) : StateM (List (Nat × List Fact)) Ctx := do
  let mut ctx := ctx
  for s in ss do
    ctx ← walkStmt rules ctx s
  return ctx

partial def walkStmt (rules : Rules) (ctx : Ctx) : Stmt → StateM (List (Nat × List Fact)) Ctx
    | .constants _ bs | .mutables _ bs => do
      let mut ctx := ctx
      for b in bs do
        ctx := Ctx.kill (ctx.across (allExprs b.init)) [b.name]
        if !b.early then
          -- (a field path's read, `x = o.f`: its value term, where a fact
          -- names it, `linear_facts.ml:linear`'s `Read`)
          let pathRead := match b.init with
            | .read _ (.str f) o => if f == "length" then none else
                (pathOf o).map fun (r, p) => ([((r, p ++ [f], HeapKnowledge.Term.Kind.value), (1 : Int))], (0 : Int))
            | _ => none
          match (linOf rules.kind b.init).orElse fun _ => pathRead with
          | some v => ctx := ctx.add (equalTo ctx b.name v)
          | none => ctx := ctx.add (choiceBounds rules.kind b.name b.init ++ constructedLength rules.kind b.name b.init ++
              allocFields rules.kind ctx b.name b.init ++
              callEnsures rules.ensuresOf b.name rules.falseEnsures b.init ++
              valueArms rules.kind rules.ensuresOf ctx b.name rules.falseEnsures b.init ++
              ctx.elemFacts rules.kind b.name b.init rules.falseElements)
          if rules.separations then ctx := ctx.add (separations rules.arrays ctx b.name b.init)
          -- (a read of a path: its quantified facts restated, `Fact.restate`;
          -- of the empty path, an alias `x = o` or a cast `o as T`, every
          -- fact of `o`'s paths)
          if let some (root, p) := pathOf b.init then
            if root != b.name then
              -- (of an alias, the facts of the object's paths and lengths:
              -- its own value is the equality's, `equalTo`)
              let restated := (ctx.filterMap (Fact.restate b.name root p)).filter fun
                | .lin l => !p.isEmpty || !l.terms.any fun ((n, q, k), _) => n == b.name && q.isEmpty && k == .value
                | _ => true
              -- (forced: each restated linear fact's first term at most `-1`)
              let false_ := if !rules.falseRestated then [] else restated.filterMap fun
                | .lin ⟨(t, _) :: _, _⟩ => some (Fact.lin ⟨[(t, 1)], -1⟩)
                | _ => none
              ctx := ctx.add (restated ++ false_)
      return ctx
    | .effect _ e => pure (ctx.effect rules.kind e rules.falseArms rules.ensuresOf rules.falseEnsures)
    | .ite _ c t e => do
      let tOut ← walk rules (ctx.add (ctx.tested (atomsOf rules.kind c true) ++ ctx.unguarded c true rules.falseGuards)) t
      let eOut ← walk rules (ctx.add (ctx.tested (atomsOf rules.kind c false) ++ ctx.unguarded c false rules.falseGuards)) (e.getD [])
      let both := t ++ e.getD []
      let changed := (ctx.flatMap Fact.names).eraseDups.filter (assigns both ·)
      if exits t && !exits (e.getD []) then return eOut
      if exits (e.getD []) && !exits t then return tOut
      let base := ctx.kill changed
      return base.across (exprsOf both)
    | .loop pos c body update (names, inv) => do
      let all := body ++ update
      -- The written invariant (`@invariant`) holds at the head: its facts
      -- are known there, and none is proposed again.
      let written := inv.filterMap (ofIndexFact (names[·]?))
      let head := (headFacts rules (ctx.add written) c all update).filter (!written.contains ·)
      -- (forced: each string's or typed array's length named at most `-1`)
      let falseKinds : List Fact := if !rules.falseKinds then [] else
        ((head.flatMap fun | .lin l => l.terms.map (·.1) | _ => []).filter fun (_, _, k) =>
          k == .strLength || k == .view).eraseDups.map fun t => .lin ⟨[(t, 1)], -1⟩
      let head := head ++ falseKinds.filter (!head.contains ·)
      modify (· ++ [(pos.1, head)])
      let _ ← walk rules (head ++ written ++ Ctx.tested (head ++ written) (atomsOf rules.kind c true)) body
      let changed := (ctx.flatMap Fact.names).eraseDups.filter (assigns all ·)
      let base := ctx.kill changed
      let base := base.across (exprsOf all ++ allExprs c)
      -- (at the exit, the written invariant too: it holds at the head)
      return if breaks body then base else base.add (written ++ head ++ Ctx.tested (head ++ written) (atomsOf rules.kind c false))
    | .block _ _ body => do
      let _ ← walk rules ctx body
      let changed := (ctx.flatMap Fact.names).eraseDups.filter (assigns body ·)
      let base := ctx.kill changed
      return base.across (exprsOf body)
    | .forOf pos _ _ _ i body => do
      -- A `for...of` head: its iterable once, then the facts of a loop
      -- whose test is its iterator's step.
      let entry := ctx.across (allExprs i)
      let head := headFacts rules entry (.lit pos (.vbool true)) body
      modify (· ++ [(pos.1, head)])
      let _ ← walk rules head body
      let changed := (entry.flatMap Fact.names).eraseDups.filter (assigns body ·)
      return (entry.kill changed).across (exprsOf body)
    | .tryStmt _ b h f => do
      let all := b ++ ((h.map (·.2)).getD []) ++ f.getD []
      let changed := (ctx.flatMap Fact.names).eraseDups.filter (assigns all ·)
      let base := (ctx.kill changed).across (exprsOf all)
      let _ ← walk rules base b
      let _ ← walk rules base ((h.map (·.2)).getD [])
      let _ ← walk rules base (f.getD [])
      return base
    | .closing _ cl b => do
      let all := cl ++ b
      let changed := (ctx.flatMap Fact.names).eraseDups.filter (assigns all ·)
      let base := (ctx.kill changed).across (exprsOf all)
      let _ ← walk rules base b
      return base
    | .destructure _ t _ init =>
      let ctx := Ctx.kill (ctx.across (allExprs init)) t.names
      -- (an object pattern's fields of a path: its quantified facts
      -- restated, each read in turn, `linear_facts.ml:destructure_reads`)
      match t, pathOf init with
      | .object _ props _, some (root, p) =>
        if t.names.contains root then pure ctx else
        pure (props.foldl (init := ctx) fun ctx (f, pt, d) => match pt, d with
          | .name n _, none => ctx.add (ctx.filterMap (Fact.restate n root (p ++ [f])))
          | _, _ => ctx)
      | _, _ => pure ctx
    | .ret .. | .throw .. | .brk .. | .cont .. => pure ctx
end

/-- A unit's loop heads' proposals, by each loop statement's start. -/
def proposals (rules : Rules) (body : List Stmt) (entry : Ctx := []) : List (Nat × List Fact) :=
  ((walk rules entry body).run []).2

/-- The kind of the `length` of a value of a written type (the parser's
type term): an array's or tuple's, a typed array's, a string's; of a union,
its parts' but `null` and `undefined`, where they agree. -/
partial def kindOfType (j : Lean.Json) : Option HeapKnowledge.Term.Kind :=
  match j.getObjValAs? String "k" with
  | .ok "array" | .ok "tuple" => some .length
  | .ok "atom" => if (j.getObjValAs? String "name").toOption == some "string" then some .strLength else none
  | .ok "reference" =>
    let name := ((j.getObjVal? "reference").toOption.bind fun r =>
      ((r.getObjVal? "target").toOption.bind fun t => (t.getObjValAs? String "name").toOption))
    match name with
    | some n => if typedArrays.contains n then some .view
        else if n == "Array" || n == "ReadonlyArray" then some .length else none
    | none => none
  | .ok "union" =>
    let parts := ((j.getObjValAs? (Array Lean.Json) "parts").toOption.getD #[]).toList.filter fun p =>
      !((p.getObjValAs? String "k").toOption == some "atom" &&
        ((p.getObjValAs? String "name").toOption == some "null" || (p.getObjValAs? String "name").toOption == some "undefined"))
    match parts.map kindOfType with
    | some k :: ks => if ks.all (· == some k) then some k else none
    | _ => none
  | _ => none

/-- The kind of the `length` of the value an initializer makes, where its
form says: an array literal's, a typed array's construction's, a string
literal's. -/
partial def kindOfInit : Expr → Option HeapKnowledge.Term.Kind
  | .arrayLit .. => some .length
  | .construct _ (.var _ n) _ _ _ => if typedArrays.contains n then some .view
      else if n == "Array" then some .length else none
  | .lit _ (.vstr _) => some .strLength
  | .cast _ (some a) e => (kindOfType a).orElse fun _ => kindOfInit e
  | .cast _ none e => kindOfInit e
  | _ => none

/-- The declarations' `length` kinds of a statement list (`kindsOf`), an
annotation's read by `ty`. -/
partial def declKinds (ty : Lean.Json → Option HeapKnowledge.Term.Kind := kindOfType) :
    List Stmt → List (String × HeapKnowledge.Term.Kind)
    | [] => []
    | s :: rest => (match s with
      | .constants _ bs | .mutables _ bs => bs.filterMap fun b =>
          ((b.annot.bind ty).orElse fun _ => kindOfInit b.init).map (b.name, ·)
      | .ite _ _ t e => declKinds ty t ++ declKinds ty (e.getD [])
      | .loop _ _ b u _ => declKinds ty b ++ declKinds ty u
      | .block _ _ b | .forOf _ _ _ _ _ b => declKinds ty b
      | .tryStmt _ b h f => declKinds ty b ++ declKinds ty ((h.map (·.2)).getD []) ++ declKinds ty (f.getD [])
      | .closing _ c b => declKinds ty c ++ declKinds ty b
      | _ => []) ++ declKinds ty rest

/-- Each binding's `length` kind in a function: a parameter's by its type
(`param`, by default its written type's), a declaration's by its
annotation, else its initializer; an array's where neither says. -/
def kindsOf (f : Fn) (param : Lean.Json → Option HeapKnowledge.Term.Kind := kindOfType) :
    String → HeapKnowledge.Term.Kind :=
  let params := f.params.filterMap fun p => (param p.ty).map (p.name, ·)
  let all := params ++ declKinds param f.body
  fun n => (all.lookup n).getD .length

/-- The names a statement list's destructurings bind, nested statements' included. -/
partial def destructured : List Stmt → List String
  | [] => []
  | s :: rest => (match s with
    | .destructure _ t _ _ => t.names
    | .ite _ _ t e => destructured t ++ destructured (e.getD [])
    | .loop _ _ b u _ => destructured b ++ destructured u
    | .block _ _ b | .forOf _ _ _ _ _ b => destructured b
    | .tryStmt _ b h f => destructured b ++ destructured ((h.map (·.2)).getD []) ++ destructured (f.getD [])
    | .closing _ c b => destructured c ++ destructured b
    | _ => []) ++ destructured rest

/-- The bindings of a function that may hold arrays: those a parameter's
type (`param`), a written type or an initializer gives an array's or a typed
array's length (`kindsOf`), and those a destructuring binds. -/
def arraysOf (f : Fn) (param : Lean.Json → Option HeapKnowledge.Term.Kind := kindOfType) : List String :=
  let params := f.params.filterMap fun p => match param p.ty with
    | some .length | some .view => some p.name
    | _ => none
  let decls := (declKinds param f.body).filterMap fun (n, k) => if k == .length || k == .view then some n else none
  (params ++ decls ++ destructured f.body).eraseDups

/-- A function's entry facts: its precondition's, over its parameters'
names (`ofRequires`). -/
def entryOf (f : Fn) : Ctx := f.requires.filterMap (ofRequires (f.params.map (·.name)))

end Verification.SourceExtraction.HeadInference
