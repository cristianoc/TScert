import Verification.Programs.TolerantFramesDriverWalk

/-! # Tolerant frames: each written assertion at its label

`runWalk` refuses a request whose written assertions are at two equal
labels (`(assertions.map (·.1)).eraseDups.length != xssertions.length`) and
reads them by label (`byLabel`, the first at each label). Proved:
`nodup_of_eraseDups` (a list xs long xs its `eraseDups` has no repeated
element) and `byLabel_of_nodup` (with distinct labels, every assertion at a
label below the program's size is the one `byLabel` gives there), and
(`assertionsLabelled_of_checked`) `LabelsChecked` (every accepted call's
written assertions at distinct labels, the check `runWalk`'s setup makes)
⟹ `AssertionsLabelled`, and `labelsChecked` (the setup's check:
`setup_labels`, `setup_of_walk`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules LabelStore

section Labels

/-- **A list xs long xs its `eraseDups` has no repeated element.** -/
theorem nodup_of_eraseDups {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.length = l.length → l.Nodup
  | [], _ => List.nodup_nil
  | a :: xs, h => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons] at h
    have hle : (xs.filter fun b => !b == a).eraseDups.length ≤ (xs.filter fun b => !b == a).length :=
      eraseDups_length_le _
    have hf : (xs.filter fun b => !b == a).length = xs.length :=
      Nat.le_antisymm (List.length_filter_le _ _) (by omega)
    have hall : ∀ b ∈ xs, (!b == a) = true := List.length_filter_eq_length_iff.mp hf
    have heq : (xs.filter fun b => !b == a) = xs := List.filter_eq_self.mpr hall
    rw [heq] at h
    refine List.nodup_cons.mpr ⟨fun hm => by simpa using hall a hm, nodup_of_eraseDups xs (by omega)⟩
termination_by l => l.length
where
  eraseDups_length_le : ∀ (l : List α), l.eraseDups.length ≤ l.length
    | [] => Nat.le_refl _
    | a :: xs => by
      rw [List.eraseDups_cons, List.length_cons, List.length_cons]
      have := eraseDups_length_le (xs.filter fun b => !b == a)
      have := List.length_filter_le (fun b => !b == a) xs
      omega
  termination_by l => l.length
  decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- `byLabel`'s array has the program's size. -/
theorem byLabel_size {α : Type} (n : Nat) (xs : List (Nat × α)) : (CertificateProducer.byLabel n xs).size = n := by
  unfold CertificateProducer.byLabel
  rw [List.foldl_reverse]
  induction xs with
  | nil => simp
  | cons p xs ih =>
    obtain ⟨l, v⟩ := p
    simp only [List.foldr_cons]
    split <;> simp_all

theorem byLabel_cons {α : Type} (n l : Nat) (v : α) (xs : List (Nat × α)) :
    CertificateProducer.byLabel n ((l, v) :: xs) =
      if l < n then (CertificateProducer.byLabel n xs).set! l (some v) else CertificateProducer.byLabel n xs := by
  unfold CertificateProducer.byLabel
  rw [List.foldl_reverse, List.foldl_reverse]
  rfl

/-- **With distinct labels, each assertion is the one `byLabel` gives at
its label**, where the label is below the program's size. -/
theorem byLabel_of_nodup {α : Type} {n : Nat} :
    ∀ {xs : List (Nat × α)}, (xs.map (·.1)).Nodup → ∀ {l : Nat} {k : α}, (l, k) ∈ xs → l < n →
      (CertificateProducer.byLabel n xs)[l]? = some (some k)
  | [], _, _, _, hm, _ => by simp at hm
  | (l', v) :: xs, hnd, l, k, hm, hl => by
    have hnd' : l' ∉ xs.map (·.1) ∧ (xs.map (·.1)).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hsz := byLabel_size n xs
    rw [byLabel_cons]
    rcases List.mem_cons.mp hm with he | hm'
    · cases he
      rw [if_pos hl]
      simp [Array.set!, hsz, hl]
    · have hne : l ≠ l' := fun he => hnd'.1 (by subst he; exact List.mem_map.mpr ⟨_, hm', rfl⟩)
      have ih := byLabel_of_nodup hnd'.2 hm' hl
      split
      · simp [Array.set!, Ne.symm hne, ih]
      · exact ih

end Labels

section Called
variable {ι : Type} [Labels ι]

variable (ι) in
/-- **An accepted call's written assertions are at distinct labels**: the
check `runWalk`'s setup makes before the walk (`a label with two written
assertions`); proved (`labelsChecked`). -/
def LabelsChecked : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) (after : Answered G),
    c.Accepts after → (c.assertions.map (·.1)).eraseDups.length = c.assertions.length

/-- **Every assertion of an accepted call is the written assertion at its
visited label** (`AssertionsLabelled`): the labels distinct
(`LabelsChecked`, `nodup_of_eraseDups`), the record's table `byLabel`'s
(`RunWalkA.stated_eq`), a visited label a node of the program
(`NodeChecked.hP`), so below its size (`byLabel_of_nodup`). -/
theorem assertionsLabelled_of_checked (h : LabelsChecked ι) : AssertionsLabelled ι := by
  intro G I c after admits hp r l k hm hv
  have hnd := nodup_of_eraseDups (c.assertions.map (·.1)) ((h G I c after hp.1).trans (List.length_map _).symm)
  have hlt : l < c.P.toArray.size := by
    have := (r.node l hv).hP
    simp only [List.size_toArray]
    exact (List.getElem?_eq_some_iff.mp this).1
  rw [r.stated_eq l, byLabel_of_nodup hnd hm hlt]
  rfl

/-- **The setup returns only where the written assertions are at distinct
labels** (its check "a label with two written assertions"). -/
theorem setup_labels {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I} {p}
    (h : SinglePass.setup G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional = .ok p) :
    (c.assertions.map (·.1)).eraseDups.length = c.assertions.length := by
  refine Classical.byContradiction fun hne => ?_
  have hb : ((c.assertions.map (·.1)).eraseDups.length != c.assertions.length) = true := by simp [hne]
  unfold SinglePass.setup at h
  by_cases hcl : (c.claims.toArray.size != c.P.toArray.size) = true
  · rw [if_pos hcl] at h
    cases h
  · rw [if_neg hcl] at h
    simp only [hb, if_true] at h
    repeat' split at h
    all_goals cases h

/-- **A walk that returned was set up.** -/
theorem setup_of_walk {G : NormalGraph ι} {I : InstanceImageCheck G} {c : Target.RunCall G I} {q}
    (h : RunCall.walk c = .ok q) :
    ∃ p, SinglePass.setup G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
      c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
      c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
      c.observeEntry c.regional = .ok p := by
  unfold RunCall.walk SinglePass.runWalk at h
  cases hs : SinglePass.setup G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
      c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
      c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
      c.observeEntry c.regional with
  | error e => rw [hs] at h; cases h
  | ok p => exact ⟨p, rfl⟩

/-- **(`labelsChecked`) An accepted call's written assertions are at
distinct labels** (`LabelsChecked`): its walk returned
(`walk_of_accepts`), so its setup did (`setup_of_walk`), which refuses a
repeated label (`setup_labels`). -/
theorem labelsChecked : LabelsChecked ι := fun _ _ _ _ hacc =>
  have ⟨_, _, hw, _⟩ := walk_of_accepts walkStopsRefuse hacc
  have ⟨_, hs⟩ := setup_of_walk hw
  setup_labels hs

end Called

end Verification.TolerantFrames
