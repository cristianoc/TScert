import Verification.Source.SourceRequests

/-! # The evidence document: tables with backward references

An evidence bundle (`SourceExtraction.Bundle`) is written as one document of
typed tables: the types, contexts, links, heap knowledge and derivation nodes
it states, each once, and the responses and obligations naming them by their
positions (REQUEST-PROTOCOL.md, "Evidence document"). A reference names an
entry of the table its position's kind gives; a derivation node names its
premises among the derivation nodes before it, so a document has no cycle.

`decode` reads the tables in order into arrays, each entry built from the
entries it names, already built: an entry named twice is one value, held
once, and the bundle it gives shares it wherever the document names it. The
checker reads that bundle; its meaning is the bundle the references unfold
to (`proofs_unfold`, `unfold_unique`). Interning (`encode`) is the
producer's: untrusted, and the checker assumes nothing of how much a
document shares. -/
namespace Verification.EvidenceWire
open Lean ProgramTyping ProgramCertificates ControlFlow RequestJson SourceExtraction
open PromiseCalls (Implication Yield)
open PointClaims (EdgeEvidence)

/-- A sequent whose context and type are entries of the document's
`contexts` and `types`. -/
structure SequentRef where
  context : Nat
  term : Tm
  type : Nat
  deriving ToJson, FromJson

/-- A derivation node: its sequent, its rule, and its premises, each an
earlier entry of `proofs`. -/
structure ProofEntry (ι : Type) where
  claim : SequentRef
  rule : Rule ι
  premises : List Nat
  deriving ToJson, FromJson

/-- Heap knowledge whose links are entries of `links`. -/
structure KnowledgeEntry where
  cells : HeapFacts.Facts
  values : HeapFacts.Facts
  links : List Nat
  deriving ToJson, FromJson

/-- `OrdinaryEvidence`, its derivation an entry of `proofs`. -/
inductive OrdinaryRef where
  | effect
  | proof (tree : Nat)
  deriving ToJson, FromJson

/-- `StepEvidence`, each proof an entry of `proofs`. -/
inductive StepRef (ι : Type) where
  | ordinary (proof : Nat)
  | pure (proof : Nat)
  | reading (proof : Nat)
  | created (proof : Nat)
  | typedRead (slot : Nat) (proof : Nat)
  | observedRead (slot : Nat) (contents : List HeapFacts.Atom)
  | slicedRead (tag : Tag) (answer : Bool) (slot : Nat) (proof : Nat) (sub : PositiveCertificates.SubtypeChoices ι)
  | knownValue (slot : Nat) (contents : List HeapFacts.Atom)
  | linkedRead (slot value : Nat) (sub : PositiveCertificates.SubtypeChoices ι)
  | allocated (proof : Nat)
  | written (receiver value : Nat) (contents : Option (List HeapFacts.Atom)) (proof : Nat)
  deriving ToJson, FromJson

/-- `NodeEvidence`, its sequent, derivations and knowledge named by
reference. -/
structure NodeRef (ι : Type) where
  ordinary : Option OrdinaryRef
  sequent : Option SequentRef
  edges : List (EdgeEvidence ι)
  knowledge : Nat
  effect : Option (StepRef ι)
  output : Nat
  handler : Option (Ty ι × EdgeEvidence ι)
  implies : List (Implication ι)
  yields : List (Yield ι)
  arguments : List Nat
  promise : Option (Nat × PositiveCertificates.SubtypeChoices ι)
  deriving ToJson, FromJson

/-- `Response`, its nodes by `NodeRef`. -/
structure ResponseRef (ι : Type) where
  certificate : List (NodeRef ι)
  codes : List (List (NodeRef ι)) := []
  readSummaries : List (ReadSummary ι) := []
  deriving ToJson, FromJson

@[nospecialize] private def derivedResponseRefToJson [ToJson ι] : ResponseRef ι → Json := toJson
@[nospecialize] private def derivedResponseRefFromJson [FromJson ι] : Json → Except String (ResponseRef ι) :=
  fromJson?

/-- A response's `codes` and `readSummaries` are left out when empty, as in
`Response`'s spelling. -/
instance (priority := high) [ToJson ι] : ToJson (ResponseRef ι) :=
  ⟨fun r => withoutEmpty "readSummaries" (withoutEmpty "codes" (derivedResponseRefToJson r))⟩
instance (priority := high) [FromJson ι] : FromJson (ResponseRef ι) :=
  ⟨fun j => derivedResponseRefFromJson (withEmpty "readSummaries" (withEmpty "codes" j))⟩

/-- The evidence document: the tables, then the bundle's responses and
obligations over them. -/
structure Document (ι : Type) where
  types : List (Ty ι)
  contexts : List (List Nat)
  links : List HeapLinks.Link
  knowledge : List KnowledgeEntry
  proofs : List (ProofEntry ι)
  functions : List (ResponseRef ι)
  obligations : List (List Nat)
  deriving ToJson, FromJson

/-! ### Resolution -/

section
variable {ι β α : Type}

/-- Entry `k` of the entries a reference may name (for a derivation's
premises, the ones before it), or the refusal naming the reference. -/
@[nospecialize] def entry (kind : String) (table : Array β) (k : Nat) : Except String β :=
  match table[k]? with
  | some b => .ok b
  | none => .error s!"a reference to {kind} {k}, not among the {kind} entries it may name"

/-- The entries a list of references names. -/
@[nospecialize] def entries (kind : String) (table : Array β) : List Nat → Except String (List β)
  | [] => .ok []
  | k :: ks => match entry kind table k, entries kind table ks with
    | .ok b, .ok bs => .ok (b :: bs)
    | .error m, _ => .error m
    | .ok _, .error m => .error m

/-- Each entry built in order, from the ones before it. -/
@[nospecialize] def build (f : Array β → α → Except String β) : List α → Array β → Except String (Array β)
  | [], acc => .ok acc
  | e :: es, acc => match f acc e with
    | .ok b => build f es (acc.push b)
    | .error m => .error m

/-- The tables as values. -/
structure Tables (ι : Type) where
  types : Array (Ty ι)
  contexts : Array (List (Ty ι))
  knowledge : Array HeapKnowledge.Knowledge
  proofs : Array (Evidence ι)

@[nospecialize] def sequent (types : Array (Ty ι)) (contexts : Array (List (Ty ι))) (s : SequentRef) :
    Except String (Sequent ι) :=
  match entry "context" contexts s.context, entry "type" types s.type with
  | .ok Γ, .ok A => .ok ⟨Γ, s.term, A⟩
  | .error m, _ => .error m
  | .ok _, .error m => .error m

/-- A derivation node, its premises among the nodes `earlier`. -/
@[nospecialize] def proof (types : Array (Ty ι)) (contexts : Array (List (Ty ι))) (earlier : Array (Evidence ι))
    (e : ProofEntry ι) : Except String (Evidence ι) :=
  match sequent types contexts e.claim, entries "proof" earlier e.premises with
  | .ok j, .ok premises => .ok (.node j e.rule premises)
  | .error m, _ => .error m
  | .ok _, .error m => .error m

@[nospecialize] def knowledge (links : Array HeapLinks.Link) (e : KnowledgeEntry) : Except String HeapKnowledge.Knowledge := do
  return ⟨e.cells, e.values, ← entries "link" links e.links⟩

@[nospecialize] def tables (d : Document ι) : Except String (Tables ι) := do
  let types := d.types.toArray
  let contexts ← build (fun _ c => entries "type" types c) d.contexts #[]
  let links := d.links.toArray
  let knowledge ← build (fun _ e => knowledge links e) d.knowledge #[]
  let proofs ← build (proof types contexts) d.proofs #[]
  return ⟨types, contexts, knowledge, proofs⟩

@[nospecialize] def step (t : Tables ι) : StepRef ι → Except String (HeapExpressionRules.StepEvidence ι)
  | .ordinary p => return .ordinary (← entry "proof" t.proofs p)
  | .pure p => return .pure (← entry "proof" t.proofs p)
  | .reading p => return .reading (← entry "proof" t.proofs p)
  | .created p => return .created (← entry "proof" t.proofs p)
  | .typedRead slot p => return .typedRead slot (← entry "proof" t.proofs p)
  | .observedRead slot contents => return .observedRead slot contents
  | .slicedRead tag answer slot p sub => return .slicedRead tag answer slot (← entry "proof" t.proofs p) sub
  | .knownValue slot contents => return .knownValue slot contents
  | .linkedRead slot value sub => return .linkedRead slot value sub
  | .allocated p => return .allocated (← entry "proof" t.proofs p)
  | .written receiver value contents p => return .written receiver value contents (← entry "proof" t.proofs p)

@[nospecialize] def ordinary (t : Tables ι) : OrdinaryRef → Except String (OrdinaryEvidence ι)
  | .effect => return .effect
  | .proof p => return .proof (← entry "proof" t.proofs p)

/-- A node, in its one spelling (`NodeEvidence.wellFormed`). Every field is
given positionally, so a field added to `NodeEvidence` is a field this
reads. -/
@[nospecialize] def node (t : Tables ι) (n : NodeRef ι) : Except String (NodeEvidence ι) := do
  let c : NodeEvidence ι := ⟨← n.ordinary.mapM (ordinary t), ← n.sequent.mapM (sequent t.types t.contexts),
    n.edges, ← entry "knowledge" t.knowledge n.knowledge, ← n.effect.mapM (step t),
    ← entry "knowledge" t.knowledge n.output, n.handler, n.implies, n.yields, n.arguments, n.promise⟩
  unless c.wellFormed do
    throw "a node states its sequent once, by its ordinary derivation, its step's proof or itself, and has an ordinary derivation without step evidence"
  return c

@[nospecialize] def response (t : Tables ι) (r : ResponseRef ι) : Except String (Response ι) := do
  return ⟨← r.certificate.mapM (node t), ← r.codes.mapM (·.mapM (node t)), r.readSummaries⟩

/-- The bundle a document states. -/
@[nospecialize] def Document.resolve (d : Document ι) : Except String (Bundle ι) := do
  let t ← tables d
  return ⟨← d.functions.mapM (response t), ← d.obligations.mapM (entries "proof" t.proofs)⟩

/-- **The evidence decoder.** The document's exact shape (`decodeStrict`),
then its references resolved. -/
@[nospecialize] def decode [ToJson ι] [FromJson ι] (j : Json) : Except String (Bundle ι) := do
  let d : Document ι ← decodeStrict j
  d.resolve

/-! ### Resolution is unfolding

A `proofs` table means the derivations its references unfold to: entry `k`
is the node of its sequent and rule over the derivations its premises name,
each an earlier entry. The table resolution builds satisfies these equations
(`proofs_unfold`), and two tables satisfying them agree (`unfold_unique`), so
the table `decode` builds, sharing each entry wherever it is named, is the
table of the unfolded derivations. -/

/-- The unfolding equations of a `proofs` table: each entry the node of its
claim and rule over the earlier entries its premises name. -/
def Unfolds (types : Array (Ty ι)) (contexts : Array (List (Ty ι))) (es : List (ProofEntry ι))
    (a : Array (Evidence ι)) : Prop :=
  a.size = es.length ∧ ∀ k, k < a.size → ∃ e j premises, es[k]? = some e ∧
    sequent types contexts e.claim = .ok j ∧ entries "proof" a e.premises = .ok premises ∧
    (∀ p ∈ e.premises, p < k) ∧ a[k]? = some (.node j e.rule premises)

theorem entry_lt {table : Array β} {k : Nat} {b : β} (h : entry kind table k = .ok b) : k < table.size := by
  unfold entry at h
  split at h
  · next b' hk => exact (Array.getElem?_eq_some_iff.mp hk).1
  · cases h

theorem entries_lt {table : Array β} : ∀ {ks : List Nat} {bs : List β},
    entries kind table ks = .ok bs → ∀ k ∈ ks, k < table.size
  | [], _, _ => by intro k hk; cases hk
  | k :: ks, bs, h => by
    unfold entries at h
    split at h
    · next b rest hb hr =>
      intro k' hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · exact entry_lt hb
      · exact entries_lt hr k' hk'
    · cases h
    · cases h

/-- References read the same entries in two tables agreeing at them. -/
theorem entries_congr {a b : Array β} : ∀ {ks : List Nat}, (∀ k ∈ ks, a[k]? = b[k]?) →
    entries kind a ks = entries kind b ks
  | [], _ => rfl
  | k :: ks, h => by
    have hk : entry kind a k = entry kind b k := by
      unfold entry; rw [h k (List.mem_cons_self ..)]
    simp only [entries, hk, entries_congr (fun k' h' => h k' (List.mem_cons_of_mem _ h'))]

theorem build_spec {f : Array β → α → Except String β} : ∀ {es : List α} {acc out : Array β},
    build f es acc = .ok out →
      out.size = acc.size + es.length ∧ (∀ i, i < acc.size → out[i]? = acc[i]?) ∧
      ∀ k, k < es.length → ∃ e b, es[k]? = some e ∧ out[acc.size + k]? = some b ∧
        ∃ pre : Array β, pre.size = acc.size + k ∧ (∀ i, i < pre.size → out[i]? = pre[i]?) ∧ f pre e = .ok b
  | [], acc, out, h => by
    simp only [build] at h; cases h
    exact ⟨by simp, fun _ _ => rfl, fun k hk => absurd hk (by simp)⟩
  | e :: es, acc, out, h => by
    unfold build at h
    split at h
    · next b hb =>
      obtain ⟨hsize, hpre, hentries⟩ := build_spec h
      have hpush : (acc.push b).size = acc.size + 1 := Array.size_push ..
      have hacc : ∀ i, i < acc.size → out[i]? = acc[i]? := fun i hi => by
        rw [hpre i (by omega), Array.getElem?_push]
        simp only [show i ≠ acc.size by omega, if_false]
      refine ⟨by simp only [List.length_cons]; omega, hacc, ?_⟩
      intro k hk
      cases k with
      | zero =>
        refine ⟨e, b, rfl, ?_, acc, rfl, hacc, hb⟩
        rw [Nat.add_zero, hpre acc.size (by omega), Array.getElem?_push]
        simp
      | succ k =>
        obtain ⟨e', b', he', hb', pre, hsz, hpre', hf⟩ := hentries k (by simp only [List.length_cons] at hk; omega)
        refine ⟨e', b', by simpa using he', ?_, pre, by omega, hpre', hf⟩
        rw [show acc.size + (k + 1) = (acc.push b).size + k by omega]
        exact hb'
    · cases h

/-- **Resolution satisfies the unfolding equations.** -/
theorem proofs_unfold {types : Array (Ty ι)} {contexts : Array (List (Ty ι))} {es : List (ProofEntry ι)}
    {a : Array (Evidence ι)} (h : build (proof types contexts) es #[] = .ok a) :
    Unfolds types contexts es a := by
  obtain ⟨hsize, -, hentries⟩ := build_spec h
  simp only [Array.size_empty, Nat.zero_add] at hsize hentries
  refine ⟨hsize, fun k hk => ?_⟩
  obtain ⟨e, b, he, hb, pre, hsz, hpre, hf⟩ := hentries k (by omega)
  unfold proof at hf
  split at hf
  · next j premises hj hps =>
    cases hf
    have hlt : ∀ p ∈ e.premises, p < k := fun p hp => by
      have := entries_lt hps p hp; omega
    refine ⟨e, j, premises, he, hj, ?_, hlt, hb⟩
    rw [← hps]
    exact entries_congr fun p hp => hpre p (by have := hlt p hp; omega)
  · cases hf
  · cases hf

/-- **The unfolding equations have one solution.** -/
theorem unfold_unique {types : Array (Ty ι)} {contexts : Array (List (Ty ι))} {es : List (ProofEntry ι)}
    {a b : Array (Evidence ι)} (ha : Unfolds types contexts es a) (hb : Unfolds types contexts es b) :
    a = b := by
  have key : ∀ n k : Nat, k < n → a[k]? = b[k]? := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih =>
      intro k hk
      by_cases h1 : k < a.size
      · obtain ⟨e, j, ps, he, hj, hps, hlt, hak⟩ := ha.2 k h1
        obtain ⟨e', j', ps', he', hj', hps', -, hbk⟩ := hb.2 k (by have := ha.1; have := hb.1; omega)
        rw [he] at he'; cases he'
        rw [hj] at hj'; cases hj'
        rw [entries_congr (fun p hp => ih p (by have := hlt p hp; omega)), hps'] at hps
        cases hps
        rw [hak, hbk]
      · have h2 : ¬ k < b.size := by have := ha.1; have := hb.1; omega
        simp [Array.getElem?_eq_none (Nat.le_of_not_lt h1), Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
  exact Array.ext_getElem? fun k => key (k + 1) k (by omega)

end

/-! ### Interning: the producer's

Search writes its bundle as a document: each type, context, link, heap
knowledge and derivation node once, by its value. A table maps an entry's
key to its position; keys equal under a hash are compared in full, so a
collision never merges two entries. Untrusted: the decoder accepts any
document whose references point back, however much it shares. -/

section
variable {ι : Type} [BEq ι] [Hashable ι] [ToJson ι]

/-- One table being interned: positions by key, and the entries in order. -/
structure Interned (κ α : Type) [BEq κ] [Hashable κ] where
  positions : Std.HashMap κ Nat := {}
  entries : Array α := #[]

/-- The position of `key`'s entry, added as `value` where it is new. -/
@[nospecialize] def Interned.add [BEq κ] [Hashable κ] (t : Interned κ α) (key : κ) (value : α) : Nat × Interned κ α :=
  match t.positions[key]? with
  | some k => (k, t)
  | none => (t.entries.size, ⟨t.positions.insert key t.entries.size, t.entries.push value⟩)

structure Interner (ι : Type) [BEq ι] [Hashable ι] where
  types : Interned (Ty ι) (Ty ι) := {}
  contexts : Interned (List Nat) (List Nat) := {}
  links : Interned HeapLinks.Link HeapLinks.Link := {}
  /-- Knowledge by its facts' JSON text and its link positions. -/
  knowledge : Interned (String × String × List Nat) KnowledgeEntry := {}
  /-- Derivation nodes by their JSON text, whose premises are positions. -/
  proofs : Interned String (ProofEntry ι) := {}

abbrev InternM (ι : Type) [BEq ι] [Hashable ι] := StateM (Interner ι)

@[nospecialize] def internType (A : Ty ι) : InternM ι Nat := modifyGet fun s =>
  let (k, t) := s.types.add A A
  (k, { s with types := t })

@[nospecialize] def internContext (Γ : List (Ty ι)) : InternM ι Nat := do
  let ks ← Γ.mapM internType
  modifyGet fun s =>
    let (k, t) := s.contexts.add ks ks
    (k, { s with contexts := t })

@[nospecialize] def internLink (l : HeapLinks.Link) : InternM ι Nat := modifyGet fun s =>
  let (k, t) := s.links.add l l
  (k, { s with links := t })

@[nospecialize] def internKnowledge (k : HeapKnowledge.Knowledge) : InternM ι Nat := do
  let ls ← k.links.mapM internLink
  let key := ((toJson k.cells).compress, (toJson k.values).compress, ls)
  modifyGet fun s =>
    let (i, t) := s.knowledge.add key ⟨k.cells, k.values, ls⟩
    (i, { s with knowledge := t })

@[nospecialize] def internSequent (j : Sequent ι) : InternM ι SequentRef := do
  return ⟨← internContext j.context, j.term, ← internType j.type⟩

@[nospecialize] partial def internProof : Evidence ι → InternM ι Nat
  | .node j rule premises => do
    let e : ProofEntry ι := ⟨← internSequent j, rule, ← premises.mapM internProof⟩
    modifyGet fun s =>
      let (k, t) := s.proofs.add (toJson e).compress e
      (k, { s with proofs := t })

@[nospecialize] def internStep : HeapExpressionRules.StepEvidence ι → InternM ι (StepRef ι)
  | .ordinary p => return .ordinary (← internProof p)
  | .pure p => return .pure (← internProof p)
  | .reading p => return .reading (← internProof p)
  | .created p => return .created (← internProof p)
  | .typedRead slot p => return .typedRead slot (← internProof p)
  | .observedRead slot contents => return .observedRead slot contents
  | .slicedRead tag answer slot p sub => return .slicedRead tag answer slot (← internProof p) sub
  | .knownValue slot contents => return .knownValue slot contents
  | .linkedRead slot value sub => return .linkedRead slot value sub
  | .allocated p => return .allocated (← internProof p)
  | .written receiver value contents p => return .written receiver value contents (← internProof p)

@[nospecialize] def internOrdinary : OrdinaryEvidence ι → InternM ι OrdinaryRef
  | .effect => return .effect
  | .proof p => return .proof (← internProof p)

@[nospecialize] def internNode (n : NodeEvidence ι) : InternM ι (NodeRef ι) := do
  return ⟨← n.ordinary.mapM internOrdinary, ← n.sequent.mapM internSequent, n.edges,
    ← internKnowledge n.knowledge, ← n.effect.mapM internStep, ← internKnowledge n.output, n.handler,
    n.implies, n.yields, n.arguments, n.promise⟩

@[nospecialize] def internResponse (r : Response ι) : InternM ι (ResponseRef ι) := do
  return ⟨← r.certificate.mapM internNode, ← r.codes.mapM (·.mapM internNode), r.readSummaries⟩

/-- The document a bundle is written as. -/
@[nospecialize] def encode (b : Bundle ι) : Json :=
  let run : InternM ι (List (ResponseRef ι) × List (List Nat)) := do
    return (← b.functions.mapM internResponse, ← b.obligations.mapM (·.mapM internProof))
  let ((functions, obligations), s) := run.run {}
  let d : Document ι := ⟨s.types.entries.toList, s.contexts.entries.toList, s.links.entries.toList,
    s.knowledge.entries.toList, s.proofs.entries.toList, functions, obligations⟩
  toJson d

end

end Verification.EvidenceWire
