import Verification.Programs.CertificateProducer

/-! Untrusted recipes for the source closure fragment. Recipes fix rule structure
and intermediate types; only coercions invoke subtype search. The ordinary
certificate consumer remains responsible for acceptance. -/
namespace Verification.DirectProof
open PositiveGraphs ProgramTyping ProgramCertificates PositiveNormalization PositiveRules CertificateProducer
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

variable {ι : Type}

inductive Plan (ι : Type) where
  | rule (goal : Sequent ι) (rule : Rule ι) (children : List (Plan ι))
  | cast (goal : Sequent ι) (child : Plan ι)

def Plan.goal : Plan ι → Sequent ι
  | .rule j _ _ | .cast j _ => j

def Plan.term (p : Plan ι) : Tm := p.goal.term
def Plan.type (p : Plan ι) : Ty ι := p.goal.type

def cast (Γ : List (Ty ι)) (A : Ty ι) (p : Plan ι) : Plan ι :=
  .cast ⟨Γ,p.term,A⟩ p

def node (Γ : List (Ty ι)) (t : Tm) (A : Ty ι) (r : Rule ι)
    (ps : List (Plan ι) := []) : Plan ι := .rule ⟨Γ,t,A⟩ r ps

def var (Γ : List (Ty ι)) (i : Nat) (A : Ty ι) : Plan ι := node Γ (.var i) A .var

def letE (Γ : List (Ty ι)) (a b : Plan ι) : Plan ι :=
  node Γ (.letE a.term b.term) b.type .letE [a,b]

/-- A known Boolean still evaluates its condition; only its reachable arm
needs the requested result type. The consumer checks the singleton premise. -/
def ifE [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (A : Ty ι) (c t e : Plan ι) : Plan ι :=
  match expand G c.type with
  | [.boolLit q] => node Γ (.ite c.term t.term e.term) A (.ifKnown q)
      [c, cast Γ A (if q then t else e)]
  | _ => node Γ (.ite c.term t.term e.term) A .ifBool [c,cast Γ A t,cast Γ A e]

/-- Subtype search results already found, by source and target type
(`CertificateProducer.Answered`), and the current render's exhaustion. The
graph and its image checker are fixed for one cache's life, so the two types
are the key. -/
structure SubtypeCache (ι : Type) [BEq ι] [Hashable ι] where
  answers : CertificateProducer.Answered ι := {}
  /-- The first unfinished coercion in the current render only. -/
  active : Option (Exhaustion ι) := none

section
variable [DecidableEq ι] [Hashable ι] [CertificateProducer.Instantiates ι]

/-- Rendering fails, or rebuilds evidence, with the searches done so far. -/
abbrev RenderM (ι : Type) [DecidableEq ι] [Hashable ι] := OptionT (StateM (SubtypeCache ι))

/-- `coerce`, each search done once per cache: the same search again returns
what it did the first time. -/
def coerceM (G : NormalGraph ι) (images : InstanceImageCheck G) (e : Evidence ι) (A : Ty ι) :
    RenderM ι (Evidence ι) := do
  if (claim e).type = A then return e
  let (found, answers) := subtypeUsing G images (claim e).type A (← get).answers
  modify fun c => { c with answers, active := c.active <|> found.exhaustion }
  let some p := found.value | failure
  return .node ⟨(claim e).context, (claim e).term, A⟩ (.sub p) [e]

/-- Rebuild the recipe in the actual context. Variable leaves explicitly coerce
from that context to the planned type. This handles justified changes of supplied
statement environments without assuming the planned context holds. -/
def renderAt (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) :
    Nat → List (Ty ι) → Plan ι → RenderM ι (Evidence ι)
  | 0, _, _ => failure
  | depth+1, Γ, p => do
   match p with
   | .cast j child => coerceM G images (← renderAt G images pool depth Γ child) j.type
   | .rule j r children =>
    match r, j.term, children with
    | .var, .var i, [] =>
      let some A := Γ[i]? | failure
      coerceM G images (.node ⟨Γ,.var i,A⟩ .var []) j.type
    | .letE, .letE _ _, [a,b] =>
      let ea ← renderAt G images pool depth Γ a
      let eb ← renderAt G images pool depth ((claim ea).type :: Γ) b
      pure (.node ⟨Γ,j.term,j.type⟩ .letE [ea,eb])
    -- The member's covering proofs are searched in the actual context.
    | .bindMember _ _ _, .letE (.readAt k (.var i)) _, [] =>
      let some O := Γ[i]? | failure
      let (searched, answers) := memberProofsUsing G images O k j.type (← get).answers
      modify fun c => { c with answers, active := c.active <|> searched.exhaustion }
      let some (ps, rs, vs) := searched.value | failure
      pure (.node ⟨Γ,j.term,j.type⟩ (.bindMember ps rs vs) [])
    | .ifBoolVar T F, .ite (.var i) _ _, [t,e] =>
      let pt ← renderAt G images pool depth (Γ.set i T) t
      let pe ← renderAt G images pool depth (Γ.set i F) e
      pure (.node ⟨Γ,j.term,j.type⟩ (.ifBoolVar T F) [pt,pe])
    | .unionVar i, _, children =>
      -- One child per label the slot holds in the actual context: the
      -- planned label's child. An enclosing split may have left the slot
      -- fewer labels than the recipe planned for (a variable tested twice).
      let some C := Γ[i]? | failure
      let some P := j.context[i]? | failure
      let C := ProgramTyping.members G C
      let P := ProgramTyping.members G P
      if P.length != children.length then failure else do
        let ps ← C.mapM fun a => do
          let some k := P.idxOf? a | failure
          let some p := children[k]? | failure
          renderAt G images pool depth (Γ.set i [a]) p
        pure (.node ⟨Γ,j.term,j.type⟩ (.unionVar i) ps)
    | _, _, _ =>
      let es ← children.attach.mapM fun q => renderAt G images pool depth Γ q.val
      pure (.node ⟨Γ,j.term,j.type⟩ r es)

def Plan.depth : Plan ι → Nat
  | .cast _ p => 1 + p.depth
  | .rule _ _ ps => 1 + (ps.map Plan.depth).foldl max 0

/-- Render with the searches of earlier renders over the same graph and pool. -/
def renderWith (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (Γ : List (Ty ι)) (p : Plan ι)
    (cache : SubtypeCache ι) : CheckResult ι (Evidence ι) × SubtypeCache ι :=
  let (answer, next) := (renderAt G images pool p.depth Γ p).run.run { cache with active := none }
  (⟨answer, if answer.isSome then none else next.active⟩, next)

end
end Verification.DirectProof
