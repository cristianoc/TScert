import Verification.Paper.TolerantFrames.CompilerRoutes

/-! # Generated node origins and routing evidence

This finite certificate describes exact emitted nodes and actual destination
lookups. The compiler generates every premise structurally. No command's
behavior, body specification or safety is assumed by an origin constructor.
-/
namespace Verification.Paper.TolerantFrames.Compiler
open Verification ControlFlow

inductive Origin (nodes : List AnnotatedNode) (bound : Nat) : AnnotatedNode → Prop where
  | primitive {p stack next broken returned thrown} :
      (Command.step p).InFrame bound → Routes nodes bound stack next broken returned thrown →
      Origin nodes bound (annotated (p.operation.symbolic (hostTemplate bound))
        (match p with | .bind x _ => .bind (resultTarget bound next x) | .perform _ => .effect (target next))
        (some thrown) (.step p) stack)
  | choice {test yes no stack next broken returned thrown yesLabel noLabel} :
      test.Scoped (· < bound) → Routes nodes bound stack next broken returned thrown →
      (nodes[yesLabel]?).map AnnotatedNode.site = some (frontSite yes stack) →
      (nodes[noLabel]?).map AnnotatedNode.site = some (frontSite no stack) →
      Origin nodes bound (annotated (test.code 0)
        (.tagBind .truthy ⟨yesLabel, dropMap (width bound)⟩ ⟨noLabel, dropMap (width bound)⟩)
        none (.choice test yes no) stack)
  | loop {body stack next broken returned thrown bodyLabel} :
      Routes nodes bound stack next broken returned thrown →
      (nodes[bodyLabel]?).map AnnotatedNode.site = some (frontSite body (.loop body :: stack)) →
      Origin nodes bound (annotated .undef (.effect (target bodyLabel)) none (.loop body) stack)
  | returned {value stack next broken returned thrown} :
      value.Scoped (· < bound) → Routes nodes bound stack next broken returned thrown →
      Origin nodes bound (annotated (value.code 0) (.bind (payloadTarget bound returned)) none (.return_ value) stack)
  | thrown {value stack next broken returned thrown} :
      value.Scoped (· < bound) → Routes nodes bound stack next broken returned thrown →
      Origin nodes bound (annotated (.throw (value.code 0)) (.effect (target next)) (some thrown) (.throw_ value) stack)
  | broken {stack next broken returned thrown} :
      Routes nodes bound stack next broken returned thrown →
      Origin nodes bound (annotated .undef (.effect (target broken)) none .break_ stack)
  | normal_sink : Origin nodes bound ⟨⟨.undef, .ret, none⟩, .normal⟩
  | break_sink : Origin nodes bound ⟨⟨.undef, .ret, none⟩, .broken⟩
  | return_sink : Origin nodes bound ⟨⟨.var (bound + 3), .ret, none⟩, .returned⟩
  | throw_sink : Origin nodes bound ⟨⟨.throw (.var (bound + 3)), .ret, none⟩, .thrown⟩

/-- Every generated block node carries generated syntax/routing evidence.
The finite-frame condition is derived for every command, not assumed finally. -/
theorem block_origins {nodes : List AnnotatedNode} {bound : Nat} (c : Command) :
    ∀ stack next broken returned thrown offset,
      c.InFrame bound → Routes nodes bound stack next broken returned thrown →
      Segment nodes offset (block bound c stack next broken returned thrown offset) →
      ∀ node ∈ block bound c stack next broken returned thrown offset, Origin nodes bound node := by
  induction c with
  | step p =>
    intros stack next broken returned thrown offset scope routes segment node member
    cases List.mem_singleton.mp member
    exact .primitive scope routes
  | return_ value =>
    intros stack next broken returned thrown offset scope routes segment node member
    cases List.mem_singleton.mp member
    exact .returned scope routes
  | throw_ value =>
    intros stack next broken returned thrown offset scope routes segment node member
    cases List.mem_singleton.mp member
    exact .thrown scope routes
  | break_ =>
    intros stack next broken returned thrown offset scope routes segment node member
    cases List.mem_singleton.mp member
    exact .broken routes
  | seq a b iha ihb =>
    intros stack next broken returned thrown offset scope routes segment node member
    let first := block bound a (.sequence b :: stack) (offset + codeSize a) broken returned thrown offset
    let second := block bound b stack next broken returned thrown (offset + codeSize a)
    have firstSegment : Segment nodes offset first := by
      simpa only [Nat.add_zero] using segment.trans (Segment.left first second)
    have secondSegment : Segment nodes (offset + codeSize a) second := by
      simpa only [first, block_length] using segment.trans (Segment.right first second)
    rcases List.mem_append.mp member with ha | hb
    · exact iha _ _ _ _ _ _ scope.1 (.sequence routes secondSegment.block_entry_site) firstSegment node ha
    · exact ihb _ _ _ _ _ _ scope.2 routes secondSegment node hb
  | handle body name handler ihb ihd =>
    intros stack next broken returned thrown offset scope routes segment node member
    let first := block bound body (.catcher name handler :: stack) next broken returned
      (resultTarget bound (offset + codeSize body) name) offset
    let second := block bound handler stack next broken returned thrown (offset + codeSize body)
    have firstSegment : Segment nodes offset first := by
      simpa only [Nat.add_zero] using segment.trans (Segment.left first second)
    have secondSegment : Segment nodes (offset + codeSize body) second := by
      simpa only [first, block_length] using segment.trans (Segment.right first second)
    rcases List.mem_append.mp member with hb | hd
    · exact ihb _ _ _ _ _ _ scope.1 (.catcher routes scope.2.1 secondSegment.block_entry_site) firstSegment node hb
    · exact ihd _ _ _ _ _ _ scope.2.2 routes secondSegment node hd
  | loop body ih =>
    intros stack next broken returned thrown offset scope routes segment node member
    have bodySegment := segment.tail
    rcases List.mem_cons.mp member with rfl | hb
    · exact .loop routes bodySegment.block_entry_site
    · have header : (nodes[offset]?).map AnnotatedNode.site = some (.command (.loop body) stack) := by
        simpa only [Option.map_some, annotated] using congrArg (Option.map AnnotatedNode.site) segment.head
      exact ih _ _ _ _ _ _ scope (.loop routes header) bodySegment node hb
  | choice test yes no ihy ihn =>
    intros stack next broken returned thrown offset scope routes segment node member
    let first := block bound yes stack next broken returned thrown (offset + 1)
    let second := block bound no stack next broken returned thrown (offset + 1 + codeSize yes)
    have tailSegment := segment.tail
    have firstSegment : Segment nodes (offset + 1) first := by
      simpa only [Nat.add_zero] using tailSegment.trans (Segment.left first second)
    have secondSegment : Segment nodes (offset + 1 + codeSize yes) second := by
      simpa only [first, block_length] using tailSegment.trans (Segment.right first second)
    rcases List.mem_cons.mp member with rfl | hb
    · exact .choice scope.1 routes firstSegment.block_entry_site secondSegment.block_entry_site
    · rcases List.mem_append.mp hb with hy | hn
      · exact ihy _ _ _ _ _ _ scope.2.1 routes firstSegment node hy
      · exact ihn _ _ _ _ _ _ scope.2.2 routes secondSegment node hn

/-- In particular, no external routing/correctness summary is a premise for
the generated graph of any command. -/
theorem compile_origins (c : Command) :
    ∀ node ∈ compile c.frameBound c, Origin (compile c.frameBound c) c.frameBound node := by
  let bound := c.frameBound
  have routes : Routes (compile bound c) bound [] 0 1 2 (payloadTarget bound 3) := .root rfl rfl rfl rfl
  have bodySegment : Segment (compile bound c) 4 (block bound c [] 0 1 2 (payloadTarget bound 3) 4) :=
    Segment.right (sinks bound) _
  intro node member
  rcases List.mem_append.mp member with sink | body
  · simp only [sinks, List.mem_cons, List.not_mem_nil, or_false] at sink
    rcases sink with rfl | rfl | rfl | rfl
    · exact .normal_sink
    · exact .break_sink
    · exact .return_sink
    · exact .throw_sink
  · exact block_origins c _ _ _ _ _ _ c.inFrame routes bodySegment node body

end Verification.Paper.TolerantFrames.Compiler
