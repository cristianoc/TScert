import Verification.Source.Fragment

namespace Verification.SourceExtraction
open Fragment

mutual
/-- Storage is selected from source assignments, including writes in nested
closures. Active-name shadowing is rejected by the lowering, so a matching
name cannot silently designate a different binding. Producer claims cannot
choose which parameters are mutable. -/
private partial def assignsExpr (name : String) : Fragment.Expr → Bool
  | .var .. | .lit .. => false
  | .assign _ target _ rhs | .nullishAssign _ target _ rhs => target == name || assignsExpr name rhs
  | .lambda _ _ _ _ defaults _ _ e =>
    defaults.attach.any (fun ⟨d,_⟩ => assignsExpr name d.2) || assignsExpr name e
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e =>
    assignsExpr name e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .optional _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .withValue _ a b _ _ | .index _ _ a b =>
    assignsExpr name a || assignsExpr name b
  | .indexWrite _ _ a b c | .elemWrite _ a b c => assignsExpr name a || assignsExpr name b || assignsExpr name c
  | .arith _ _ a b | .elemAt _ a b | .comma _ a b | .inKeys _ a b => assignsExpr name a || assignsExpr name b
  | .arrayLit _ es _ => es.any (assignsExpr name)
  | .arrayAssign _ targets rest rhs => targets.any (fun q => q.target.targetLocal == some name ||
      q.target.referenceParts.any (assignsExpr name) || (q.default_.map (assignsExpr name)).getD false) ||
      rest.any (fun r => r.2.2.target.targetLocal == some name ||
        r.2.2.target.referenceParts.any (assignsExpr name)) ||
      assignsExpr name rhs
  | .logicalAssign _ _ target rhs =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || assignsExpr name rhs
  | .update _ _ target rhs _ =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || (rhs.map (assignsExpr name)).getD false
  | .alloc _ _ es | .build _ _ es => es.any (assignsExpr name)
  | .call _ f args _ _ | .invoke _ f args _ _ => assignsExpr name f || args.any (assignsExpr name)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    assignsExpr name f || assignsExpr name r || args.any (assignsExpr name)
  | .ctor _ lam fs => assignsExpr name lam || fs.any (assignsExpr name ·.2)
  | .objectAssign _ t ss => assignsExpr name t || ss.any (assignsExpr name)
  | .construct _ f args _ _ => assignsExpr name f || args.any (assignsExpr name)
  | .applyWithReceiver _ f r list =>
    assignsExpr name f || assignsExpr name r || (list.map (assignsExpr name)).getD false
  | .ifBody _ c t e => assignsExpr name c || assignsExpr name t || assignsExpr name e
  | .block _ ss => ss.any (assignsStmt name)

partial def assignsStmt (name : String) : Fragment.Stmt → Bool
  | .ret _ e | .effect _ e | .throw _ e => assignsExpr name e
  | .tryStmt _ b h f => b.any (assignsStmt name) || ((h.map (·.2)).getD []).any (assignsStmt name) ||
    (f.getD []).any (assignsStmt name)
  | .constants _ bs | .mutables _ bs => bs.any fun b => assignsExpr name b.init
  | .destructure _ target d init => assignsExpr name init ||
    (d.toList ++ target.defaults).any (assignsExpr name)
  | .ite _ c t e => assignsExpr name c || t.any (assignsStmt name) ||
    (e.getD []).any (assignsStmt name)
  | .loop _ c b u => assignsExpr name c || b.any (assignsStmt name) || u.any (assignsStmt name)
  | .forOf _ _ _ _ i b => assignsExpr name i || b.any (assignsStmt name)
  | .block _ _ b => b.any (assignsStmt name)
  | .closing _ c b => c.any (assignsStmt name) || b.any (assignsStmt name)
  | .brk .. | .cont .. => false
end

/-! ### Bindings held in cells

A cell shares a binding with the closures that capture it. A mutable binding
is held in a slot of its own activation instead, rebound at each write, when
every closure that mentions it sees the value it held when the closure was
created: no closure writes it, and no write of it follows, in the
activation's evaluation order, the creation of a closure that mentions it.
The walk below follows that order: the parts of an expression left to right,
statements in order, every part of a choice (a conservative superset of
either arm), and a loop's parts twice, so that a write in one iteration is
seen after a closure the iteration before created. Both facts it tracks only
ever change one way, so a second pass reaches their fixpoint.

A write other than a statement's own (a declaration's initialization, or the
assignment or update an expression statement is) also keeps the binding in
a cell: the lowering types the rest of a statement, and joins the arms of an
expression, at the frame the statement entered with, which a slot rebound
within the statement would not fit. -/

/-- One binding's walk: whether a closure mentioning it has been created, and
whether it is still a slot. -/
structure Capture where
  captured : Bool := false
  slot : Bool := true

/-- A write, nested in an expression or the statement's own. -/
private def Capture.write (w : Capture) (nested : Bool) : Capture :=
  if w.captured || nested then { w with slot := false } else w

mutual
private partial def captureExpr (x : String) (c : Bool) (e : Fragment.Expr) (w : Capture) : Capture :=
  let all := fun (es : List Fragment.Expr) (w : Capture) => es.foldl (fun w e => captureExpr x true e w) w
  let arms := all
  let written := fun (n : String) (c : Bool) (w : Capture) => if n == x then w.write c else w
  match e with
  | .lambda .. | .ctor .. =>
    if e.freeNames.contains x then { captured := true, slot := w.slot && !assignsExpr x e } else w
  | .var .. | .lit .. => w
  | .assign _ n _ rhs => written n c (captureExpr x true rhs w)
  | .nullishAssign _ n _ rhs => written n true (arms [rhs] w)
  | .update _ _ target rhs _ =>
    let w := all (target :: rhs.toList) w
    match target with | .var _ n => written n c w | _ => w
  | .logicalAssign _ _ target rhs =>
    let w := arms [rhs] (captureExpr x true target w)
    match target with | .var _ n => written n true w | _ => w
  | .arrayAssign _ targets rest rhs =>
    -- The right side, then each target in turn: its reference's parts, its
    -- default, then its write.
    let target := fun (q : Fragment.ArrayElem Fragment.Expr) (w : Capture) =>
      let w := q.target.referenceParts.foldl (fun w e => captureExpr x true e w) w
      let w := arms q.default_.toList w
      match q.target.targetLocal with | some n => written n c w | none => w
    let w := targets.foldl (fun w q => target q w) (captureExpr x true rhs w)
    rest.toList.foldl (fun w (_, _, q) => target q w) w
  | .logical _ _ a b | .coalesce _ a b | .optional _ _ a b => all [a, b] w
  | .ifBody _ a b d => all [a, b, d] w
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e => captureExpr x true e w
  | .equality _ _ a b | .singletonTest _ _ _ _ a b
  | .write _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b | .comma _ a b
  | .inKeys _ a b | .withValue _ a b _ _ => all [a, b] w
  | .indexWrite _ _ a b d | .elemWrite _ a b d => all [a, b, d] w
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => all es w
  | .call _ f args _ _ | .invoke _ f args _ _ | .construct _ f args _ _ => all (f :: args) w
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args => all (f :: r :: args) w
  | .applyWithReceiver _ f r list => all (f :: r :: list.toList) w
  | .objectAssign _ t ss => all (t :: ss) w
  | .block _ ss => captureStmts x ss w

private partial def captureStmts (x : String) (ss : List Fragment.Stmt) (w : Capture) : Capture :=
  ss.foldl (fun w s => captureStmt x s w) w

private partial def captureStmt (x : String) (s : Fragment.Stmt) (w : Capture) : Capture :=
  let twice := fun (f : Capture → Capture) w => f (f w)
  let expr := fun e w => captureExpr x true e w
  match s with
  | .effect _ e => captureExpr x false e w
  | .ret _ e | .throw _ e => expr e w
  | .constants _ bs => bs.foldl (fun w b => expr b.init w) w
  | .mutables _ bs => bs.foldl (fun w b =>
      let w := expr b.init w
      if b.name == x then w.write false else w) w
  | .destructure _ t d init =>
    (d.toList ++ t.defaults).foldl (fun w e => captureExpr x true e w) (expr init w)
  | .ite _ c t e => captureStmts x (e.getD []) (captureStmts x t (expr c w))
  | .loop _ c b u => twice (fun w => captureStmts x u (captureStmts x b (expr c w))) w
  | .forOf _ _ _ _ i b => twice (captureStmts x b) (expr i w)
  | .block _ _ b => captureStmts x b w
  | .tryStmt _ b h f =>
    captureStmts x (f.getD []) (captureStmts x ((h.map (·.2)).getD []) (captureStmts x b w))
  | .closing _ c b => captureStmts x c (captureStmts x b w)
  | .brk .. | .cont .. => w
end

/-- Whether the binding `x`, whose scope runs through `ss` from its
declaration (a parameter's: the whole body), is held in a cell. -/
def heldInCell (x : String) (ss : List Fragment.Stmt) : Bool :=
  !(captureStmts x ss {}).slot

mutual
/-- The `let` declarations of a statement list held in cells, by name and
declaring statement; each `let`'s scope is the rest of its list. Closures'
bodies are their own. With `all`, every `let` is one. -/
private partial def letCells (all : Bool) : List Fragment.Stmt → List (String × Option Span)
  | [] => []
  | s :: rest =>
    let own := match s with
      | .mutables pos bs =>
        (bs.filter fun b => all || heldInCell b.name (s :: rest)).map fun b => (b.name, some pos)
      | _ => []
    own ++ nestedCells all s ++ letCells all rest

private partial def nestedCells (all : Bool) : Fragment.Stmt → List (String × Option Span)
  | .ite _ _ t e => letCells all t ++ letCells all (e.getD [])
  | .loop _ _ b u => letCells all b ++ letCells all u
  | .forOf _ _ _ _ _ b | .block _ _ b => letCells all b
  | .tryStmt _ b h f => letCells all b ++ letCells all ((h.map (·.2)).getD []) ++ letCells all (f.getD [])
  | .closing _ c b => letCells all b ++ letCells all c
  | _ => []
end

/-- The mutable bindings of a body held in cells: an assigned parameter by
its name alone, a `let` by its name and declaring statement. In a module's
initialization every `let` is one: the module's functions, separate units,
may read it. -/
def cellLocals (params : List String) (body : List Fragment.Stmt) (module : Bool := false) :
    List (String × Option Span) :=
  (params.filter fun p => body.any (assignsStmt p) && heldInCell p body).map (·, none) ++
    letCells module body

/-- Every name a statement's expressions mention, bound or not: a superset of
the module functions its body can reach. -/
partial def stmtNames : Fragment.Stmt → List String
  | .ret _ e | .effect _ e | .throw _ e => e.freeNames
  | .tryStmt _ b h f => b.flatMap stmtNames ++ ((h.map (·.2)).getD []).flatMap stmtNames ++
    (f.getD []).flatMap stmtNames
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => b.init.freeNames
  | .destructure _ target d init => init.freeNames ++
    (d.toList ++ target.defaults).flatMap Fragment.Expr.freeNames ++ target.slices.map (Fragment.restFromName ·.2)
  | .ite _ c t e => c.freeNames ++ t.flatMap stmtNames ++ (e.getD []).flatMap stmtNames
  | .loop _ c b u => c.freeNames ++ b.flatMap stmtNames ++ u.flatMap stmtNames
  | .forOf _ _ _ it i b => it :: i.freeNames ++ b.flatMap stmtNames
  | .block _ _ b => b.flatMap stmtNames
  | .closing _ c b => c.flatMap stmtNames ++ b.flatMap stmtNames
  | .brk .. | .cont .. => []

/-! ### Owned objects

A key-adding write is lowered as a copy (`Tm.merge`, allocation from parts)
of the object with the key added, rebound to every local that holds it. That
is JavaScript's in-place write only where nothing else can observe the object
the copy replaces: a local's own fresh allocation (an object literal, or a
`new` of a class the file declares at its top level, whose constructor reads
no `this` and ends in the instance's allocation), which no reference but the
constants bound to it since (its aliases) has reached. The analysis is
syntactic and decides only which lowering a write gets; the copy is checked
by the merge rule like any other. -/

/-- Whether `n` may reach a place other than the receiver of a member read or
write of `n`: another binding, a field, an argument or `this` of a call, a
result, a capture. Reads, writes, index reads and `in` tests of `n`'s own
members only look at the object. Any other occurrence counts, and every
occurrence inside a closure does, since the closure holds the object. -/
partial def escapesExpr (n : String) : Fragment.Expr → Bool
  | .var _ m => m == n
  | .lit .. => false
  | .read _ _ (.var ..) => false
  | .index _ _ (.var ..) key => escapesExpr n key
  | .write _ _ (.var ..) rhs => escapesExpr n rhs
  | .indexWrite _ _ (.var ..) key rhs => escapesExpr n key || escapesExpr n rhs
  | .inKeys _ key (.var ..) => escapesExpr n key
  | .shapeTest _ (.hasKey _) _ (.var ..) => false
  | .update _ _ (.read _ _ (.var ..)) rhs _ => (rhs.map (escapesExpr n)).getD false
  | .update _ _ (.index _ _ (.var ..) key) rhs _ =>
    escapesExpr n key || (rhs.map (escapesExpr n)).getD false
  | .logicalAssign _ _ (.read _ _ (.var ..)) rhs => escapesExpr n rhs
  | .logicalAssign _ _ (.index _ _ (.var ..) key) rhs => escapesExpr n key || escapesExpr n rhs
  -- `Object.assign(o, …)` copies onto `o`, as a write does; its value is `o`,
  -- which only its statement form, whose value no one reads, lowers.
  | .objectAssign _ (.var ..) ss => ss.any (escapesExpr n)
  -- A method call passes its object as `this`.
  | .invoke _ (.read _ _ (.var _ m)) args _ _ => m == n || args.any (escapesExpr n)
  | .invoke _ (.index _ _ (.var _ m) key) args _ _ =>
    m == n || escapesExpr n key || args.any (escapesExpr n)
  | e@(.lambda ..) | e@(.ctor ..) | e@(.block ..) | e@(.ifBody ..) | e@(.optional ..)
  | e@(.withValue ..) | e@(.arrayAssign ..) | e@(.assign ..) | e@(.nullishAssign ..) =>
    e.freeNames.contains n
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e => escapesExpr n e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .singletonTest _ _ _ _ a b
  | .write _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b | .comma _ a b
  | .inKeys _ a b | .logicalAssign _ _ a b => escapesExpr n a || escapesExpr n b
  | .indexWrite _ _ a b c | .elemWrite _ a b c => escapesExpr n a || escapesExpr n b || escapesExpr n c
  | .update _ _ a b _ => escapesExpr n a || (b.map (escapesExpr n)).getD false
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => es.any (escapesExpr n)
  | .call _ f args _ _ | .invoke _ f args _ _ | .construct _ f args _ _ =>
    escapesExpr n f || args.any (escapesExpr n)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    escapesExpr n f || escapesExpr n r || args.any (escapesExpr n)
  | .applyWithReceiver _ f r list =>
    escapesExpr n f || escapesExpr n r || (list.map (escapesExpr n)).getD false
  | .objectAssign _ t ss => escapesExpr n t || ss.any (escapesExpr n)

/-- The closures' statement bodies an expression creates, where their own
owned objects are found. -/
partial def closureBodies : Fragment.Expr → List (List Fragment.Stmt)
  | .lambda _ _ _ _ ds _ _ b => ds.flatMap (fun d => closureBodies d.2) ++
    (match b with | .block _ ss => [ss] | b => closureBodies b)
  | .ctor _ lam _ => closureBodies lam
  | .var .. | .lit .. => []
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e => closureBodies e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .singletonTest _ _ _ _ a b
  | .write _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b | .comma _ a b
  | .inKeys _ a b | .logicalAssign _ _ a b | .optional _ _ a b
  | .withValue _ a b _ _ => closureBodies a ++ closureBodies b
  | .indexWrite _ _ a b c | .elemWrite _ a b c | .ifBody _ a b c =>
    closureBodies a ++ closureBodies b ++ closureBodies c
  | .update _ _ a b _ => closureBodies a ++ (b.map closureBodies).getD []
  | .alloc _ _ es | .build _ _ es | .arrayLit _ es _ => es.flatMap closureBodies
  | .arrayAssign _ targets rest rhs => closureBodies rhs ++
    targets.flatMap (fun q => q.target.referenceParts.flatMap closureBodies ++
      (q.default_.map closureBodies).getD []) ++
    ((rest.map fun r => r.2.2.target.referenceParts.flatMap closureBodies).getD [])
  | .assign _ _ _ e | .nullishAssign _ _ _ e => closureBodies e
  | .call _ f args _ _ | .invoke _ f args _ _ | .construct _ f args _ _ =>
    closureBodies f ++ args.flatMap closureBodies
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    closureBodies f ++ closureBodies r ++ args.flatMap closureBodies
  | .applyWithReceiver _ f r list =>
    closureBodies f ++ closureBodies r ++ (list.map closureBodies).getD []
  | .objectAssign _ t ss => closureBodies t ++ ss.flatMap closureBodies
  | .block _ ss => [ss]

/-- A local binding: its name and the span of the statement declaring it, as
the lowering's scope describes it. -/
abbrev Holder := String × Span

/-- A key-adding write site: the write's span and the bindings holding its
object there, every one of which the copy is rebound to. -/
structure GrowSite where
  span : Span
  holders : List Holder
  deriving Inhabited, Repr

/-- An owned object: the loop depth of its allocation and the bindings that
hold it, the allocating local and the constants bound to it since. -/
private structure OwnedObject where
  depth : Nat
  holders : List Holder

/-- The analysis state: the owned objects, and the key-adding writes found so
far. -/
private structure Owned where
  objects : List OwnedObject := []
  sites : List GrowSite := []

/-- An initializer that allocates an object no reference holds yet: an object
literal, or a `new` of a class the file declares at its top level (`classes`),
whose constructor reads no `this` and ends in the instance's allocation. -/
private def freshAllocation (classes : List String) : Fragment.Expr → Bool
  | .alloc .. | .build .. => true
  | .construct _ (.var _ c) _ _ _ => classes.contains c
  | _ => false

/-- A binding of `n` makes a holder of that name, out of scope by now, hold
nothing: the parser gives every shadowing local a name of its own, so two
bindings of one name are never both in scope. -/
private def forget (n : String) (s : Owned) : Owned :=
  let held := s.objects.map fun o => { o with holders := o.holders.filter (·.1 != n) }
  { s with objects := held.filter fun o => !o.holders.isEmpty }

/-- The object a local holds, by its name. -/
private def heldBy (s : Owned) (n : String) : Option OwnedObject :=
  s.objects.find? fun o => o.holders.any (·.1 == n)

mutual
/-- An expression runs: every owned object a holder of which it may let
escape stops being owned, and the closures it creates are analysed as bodies
of their own. -/
private partial def ownedExpr (classes : List String) (e : Fragment.Expr) (s : Owned) : Owned :=
  let s := { s with objects := s.objects.filter fun o => !o.holders.any fun (n, _) => escapesExpr n e }
  (closureBodies e).foldl (fun s ss => { s with sites := (ownedStmts classes 0 ss {}).sites ++ s.sites }) s

/-- The statements in order at loop depth `d`. An `o.k = e` statement on a
holder `o` of an owned object allocated at the same depth is a key-adding
site when `e` (and a computed key) lets no holder escape: no reference but
the holders exists before the write, and outside a loop the allocation does
not enclose, the write runs once per allocation. Later escapes are after the
write in every run. -/
private partial def ownedStmts (classes : List String) (d : Nat) : List Fragment.Stmt → Owned → Owned
  | [], s => s
  | st :: rest, s => ownedStmts classes d rest (ownedStmt classes d st s)

private partial def ownedStmt (classes : List String) (d : Nat) (st : Fragment.Stmt) (s : Owned) : Owned :=
  let declare := fun (pos : Span) (s : Owned) (b : Fragment.Binding) =>
    let s := ownedExpr classes b.init s
    let s := forget b.name s
    if freshAllocation classes b.init then
      { s with objects := { depth := d, holders := [(b.name, pos)] } :: s.objects }
    else s
  let escapesAny := fun (o : OwnedObject) (es : List Fragment.Expr) =>
    o.holders.any fun (n, _) => es.any (escapesExpr n)
  let site := fun (n : String) (span : Span) (es : List Fragment.Expr) =>
    match heldBy s n with
    | some o => if o.depth == d && !escapesAny o es then some ({ span, holders := o.holders } : GrowSite)
      else none
    | none => none
  match st with
  | .constants pos bs => bs.foldl (fun s b =>
      match b.init with
      -- A constant bound to a holder is one more holder of its object.
      | .var _ m =>
        match heldBy s m with
        | some o =>
          let s := forget b.name s
          { s with objects := s.objects.map fun o' =>
              if o'.holders == o.holders then { o' with holders := o'.holders ++ [(b.name, pos)] } else o' }
        | none => declare pos s b
      | _ => declare pos s b) s
  | .mutables pos bs => bs.foldl (declare pos) s
  | .effect _ e =>
    let found : Option GrowSite := match e with
      | .write _ _ (.var _ n) rhs => site n e.span [rhs]
      | .indexWrite _ _ (.var _ n) key rhs => site n e.span [key, rhs]
      | .objectAssign _ (.var _ n) ss => site n e.span ss
      | _ => none
    let s := { s with sites := found.toList ++ s.sites }
    ownedExpr classes e s
  | .ret _ e | .throw _ e => ownedExpr classes e s
  | .destructure _ t dflt init =>
    let s := (init :: dflt.toList ++ t.defaults).foldl (fun s e => ownedExpr classes e s) s
    t.names.foldl (fun s n => forget n s) s
  | .ite _ c t e => ownedStmts classes d (e.getD []) (ownedStmts classes d t (ownedExpr classes c s))
  | .loop _ c b u => ownedStmts classes (d + 1) u (ownedStmts classes (d + 1) b (ownedExpr classes c s))
  | .forOf _ n _ _ i b => ownedStmts classes (d + 1) b (forget n (ownedExpr classes i s))
  -- The iterator's `close` runs where the body is left, after what of it ran.
  | .closing _ c b => ownedStmts classes d c (ownedStmts classes d b s)
  | .block _ _ b => ownedStmts classes d b s
  | .tryStmt _ b h f =>
    let s := ownedStmts classes d b s
    let s := match h with
      | some (param, hs) => ownedStmts classes d hs ((param.map fun (n, _) => forget n s).getD s)
      | none => s
    ownedStmts classes d (f.getD []) s
  | .brk .. | .cont .. => s
end

/-- The classes a module declares at its top level: each constant bound to a
class (`ctor`), and each constant bound to one of those. -/
def sourceClasses (init : List Fragment.Stmt) : List String :=
  init.foldl (fun cs st => match st with
    | .constants _ bs => bs.foldl (fun cs b => match b.init with
      | .ctor .. => cs ++ [b.name]
      | .var _ c => if cs.contains c then cs ++ [b.name] else cs
      | _ => cs) cs
    | _ => cs) []

/-- The key-adding write sites of a body (`ownedStmts`), `classes` the
file's top-level classes. In the module's initialization, a top-level
binding is a module value, which the module's functions and classes read: it
is never a holder. -/
def growSites (classes : List String) (ss : List Fragment.Stmt) (module : Bool := false) : List GrowSite :=
  if module then
    (ss.foldl (fun s st =>
      let s := ownedStmt classes 0 st s
      match st with
      | .constants _ bs | .mutables _ bs => bs.foldl (fun s b => forget b.name s) s
      | _ => s) {}).sites
  else (ownedStmts classes 0 ss {}).sites

end Verification.SourceExtraction
