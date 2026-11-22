import Verification.Source.Claims.CallbackPrivateFrame

namespace Verification.SourceClaimJson.CallbackInferencePlan
open TolerantFrames TolerantFrames.ReadOnly Footprints

private abbrev AgreeOn (ρ τ : Env) (slots : List Nat) := ∀ i ∈ slots, ρ i = τ i
private abbrev Closes (ρ τ : Env) (t : Tm) := ∀ d slots, SinglePass.mentioned d t = some slots →
  AgreeOn ρ τ slots → instantiate d ρ t = instantiate d τ t

private theorem closesArgs {ρ τ : Env} {args : List Tm} (each : ∀ t ∈ args, Closes ρ τ t) :
    ∀ d slots, SinglePass.mentionedAll d args = some slots → AgreeOn ρ τ slots →
      instantiateArgs d ρ args = instantiateArgs d τ args := by
  induction args with
  | nil => intros; rfl
  | cons t rest ih =>
    intro d slots reads agree
    simp only [SinglePass.mentionedAll,Option.bind_eq_bind,Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at reads
    obtain ⟨a,ha,b,hb,rfl⟩ := reads
    simp only [instantiateArgs]
    rw [each t (by simp) d a ha (fun i hi => agree i (by simp [hi])),
      ih (fun u hu => each u (by simp [hu])) d b hb (fun i hi => agree i (by simp [hi]))]

theorem mentioned_closes {ρ τ : Env} (t : Tm) : Closes ρ τ t := by
  induction t using Tm.induct
  all_goals intro d slots reads agree
  all_goals simp only [SinglePass.mentioned, Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
    Option.some.injEq,reduceCtorEq] at reads
  all_goals try contradiction
  all_goals try rfl
  case var i =>
    simp only [instantiate]
    split
    · rfl
    · apply agree
      have hdi : d ≤ i := by omega
      simp only [hdi, ↓reduceIte] at reads
      subst slots
      simp
  case invoke f r xs F R X =>
    obtain ⟨s0,h0,s1,h1,s2,h2,rfl⟩ := reads
    simp only [instantiate]
    rw [F d s0 h0 (fun i hi => agree i (by simp [hi])),
      R d s1 h1 (fun i hi => agree i (by simp [hi])),
      closesArgs X d s2 h2 (fun i hi => agree i (by simp [hi]))]
  case construct f xs F X =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [F d s0 h0 (fun i hi => agree i (by simp [hi])),
      closesArgs X d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case letE a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B (d+1) s1 h1 (fun i hi => agree i (by simp [hi]))]
  case objBound fs oid t r pre T R X =>
    obtain ⟨s0,h0,s1,h1,s2,h2,rfl⟩ := reads
    simp only [instantiate]
    rw [T d s0 h0 (fun i hi => agree i (by simp [hi])),
      R d s1 h1 (fun i hi => agree i (by simp [hi])),
      closesArgs X d s2 h2 (fun i hi => agree i (by simp [hi]))]
  case makeBound t r pre ns args T R X Y =>
    obtain ⟨s0,h0,s1,h1,s2,h2,s3,h3,rfl⟩ := reads
    simp only [instantiate]
    rw [T d s0 h0 (fun i hi => agree i (by simp [hi])),
      R d s1 h1 (fun i hi => agree i (by simp [hi])),
      closesArgs X d s2 h2 (fun i hi => agree i (by simp [hi])),
      closesArgs Y d s3 h3 (fun i hi => agree i (by simp [hi]))]
  case alloc ns args X =>
    simp only [instantiate]
    rw [closesArgs X d slots reads agree]
  case objGraph fs oid ar es ks st caps kd rs comp E X =>
    simp only [instantiate]
    rw [closesArgs X d slots reads agree]
  case makeGraph ar es ks st caps kd rs comp ns args E X Y =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [closesArgs X d s0 h0 (fun i hi => agree i (by simp [hi])),
      closesArgs Y d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case read f a A =>
    simp only [instantiate]
    rw [A d slots reads agree]
  case index a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case write f a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case test k a A =>
    simp only [instantiate]
    rw [A d slots reads agree]
  case ite a b c A B C =>
    obtain ⟨s0,h0,s1,h1,s2,h2,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi])),
      C d s2 h2 (fun i hi => agree i (by simp [hi]))]
  case arith op a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case arrLit xs X =>
    simp only [instantiate]
    rw [closesArgs X d slots reads agree]
  case elemAt a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case setElem a b c A B C =>
    obtain ⟨s0,h0,s1,h1,s2,h2,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi])),
      C d s2 h2 (fun i hi => agree i (by simp [hi]))]
  case lenOf a A =>
    simp only [instantiate]
    rw [A d slots reads agree]
  case spread a A =>
    simp only [instantiate]
    rw [A d slots reads agree]
  case throw a A =>
    simp only [instantiate]
    rw [A d slots reads agree]
  case merge z a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi]))]
  case makeKey a b A B =>
    obtain ⟨s0,h0,s1,h1,rfl⟩ := reads
    simp only [instantiate]
    rw [A d s0 h0 (fun i hi => agree i (by simp [hi])),
      B d s1 h1 (fun i hi => agree i (by simp [hi]))]

private theorem sourceArgs_all (xs : List Tm) : ObjectCoherence.sourceArgs xs = true ↔
    ∀ t ∈ xs, ObjectCoherence.sourceTerm t = true := by
  induction xs <;> simp [ObjectCoherence.sourceArgs, *]

private theorem source_no_roots {t : Tm} (source : ObjectCoherence.sourceTerm t = true) :
    ∀ rl o nk, vals allC rl o nk t = [] := by
  revert source
  induction t using Tm.induct
  all_goals intro src rl o nk
  all_goals simp only [ObjectCoherence.sourceTerm,Bool.and_eq_true,sourceArgs_all,Bool.false_eq_true] at src
  all_goals try contradiction
  all_goals simp only [vals,valsArgs_eq,List.flatMap_eq_nil_iff,List.append_eq_nil_iff] at *
  all_goals try grind
  case makeGraph =>
    cases o <;> simp only [allC,Bool.not_false,Bool.and_true,Bool.false_eq_true,ite_false,ite_true,List.append_eq_nil_iff,List.flatMap_eq_nil_iff] <;> grind

/-- Only the slots enumerated by the same scan can expose a private field
to evaluation. Source terms carry no raw heap locations. -/
theorem mentioned_hidden {d slots t ρ h l} (reads : SinglePass.mentioned d t = some slots)
    (source : ObjectCoherence.sourceTerm t = true) (old : l < h.length) (heap : hiddenInHeap h l)
    (clean : ∀ i ∈ slots, ¬Leaves allC (ρ i) l ∧ isVal (ρ i) = true) :
    ¬ReachesFrom allC h (vals allC Realm.empty true false (instantiate d ρ t)) l := by
  let env : Env := fun i => if i ∈ slots then ρ i else .undef
  let roots := slots.map ρ
  have envCover : ∀ i x, x ∈ vals allC Realm.all true true (env i) → GV allC h roots x := by
    intro i x hx
    by_cases hi : i ∈ slots
    · simp only [env,hi,↓reduceIte] at hx
      exact (GV.root (List.mem_map.mpr ⟨i,hi,rfl⟩)).held (clean i hi).2 hx
    · simp [env,hi,vals] at hx
  have agree : instantiate d ρ t = instantiate d env t :=
    mentioned_closes t d slots reads (fun i hi => by simp [env,hi])
  rw [agree]
  rintro ⟨v,hv,path,follow⟩
  have cover := instantiate_cover envCover t d Realm.empty true false
    (fun x hx => by simp [source_no_roots source] at hx) _ hv
  rcases follows_good (fun _ _ good read => GV.heap good read) cover follow with ⟨u,hu,reaches⟩ | fresh
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
    exact noPathOfHidden heap (clean i hi).1 reaches
  · omega

end Verification.SourceClaimJson.CallbackInferencePlan
