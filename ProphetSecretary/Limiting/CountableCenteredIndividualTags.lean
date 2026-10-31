import ProphetSecretary.Limiting.CountableIndividualPayloadDisplacement
import ProphetSecretary.Limiting.CountableAuxiliarySplit
import ProphetSecretary.Limiting.CountableOccurrenceStability

/-!
# Centered selected tags of one individual

A bounded tag assignment is zero below a positive level. The canonical base
rule ignores the independent tag. Pointwise centering over that tag makes its
canonical selected expectation zero; selected-occurrence stability controls
the expectation for every nearly optimal tag-observable policy.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance
variable {Seed T : Type*}

noncomputable def payloadPerturbationTag (i : ℕ) (A : ℝ × T → ℝ) : CountableTags (Seed × T) :=
  fun v k => if k=candidateEnumeration (Sum.inl i) then A (v.2.1 i,v.2.2.2.2) else 0

lemma CountableRule.selectedTag_payloadPerturbation (π : CountableRule (Seed × T))
    (i : ℕ) (A : ℝ × T → ℝ) (v : CompleteWorld (Seed × T)) :
    π.selectedTag (payloadPerturbationTag i A) v=
      π.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2) := by
  rw [CountableRule.individualSelectionIndicator_eq_code]
  unfold CountableRule.selectedTag FirstAcceptance.reward
  cases hs : FirstAcceptance.selectedCode π.codeAccepted codeTime v with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one,Nat.add_right_cancel_iff,payloadPerturbationTag]
    split_ifs <;> simp

variable [MeasurableSpace Seed] [MeasurableSpace T]

lemma payloadPerturbationTag_measurable (i : ℕ) {A : ℝ × T → ℝ} (hA : Measurable A) :
    (payloadPerturbationTag (Seed := Seed) i A).IsMeasurable := by
  intro k
  by_cases hk : k=candidateEnumeration (Sum.inl i)
  · have hm : Measurable (fun v : CompleteWorld (Seed × T) => A (v.2.1 i,v.2.2.2.2)) := by fun_prop
    simpa only [payloadPerturbationTag,if_pos hk] using hm
  · simpa only [payloadPerturbationTag,if_neg hk] using (measurable_const : Measurable (fun _ : CompleteWorld (Seed × T) => (0 : ℝ)))

omit [MeasurableSpace Seed] [MeasurableSpace T] in
lemma payloadPerturbationTag_bound (i : ℕ) {A : ℝ × T → ℝ} {D : ℝ}
    (hD : 0≤D) (hBound : ∀ z, |A z|≤D) (v : CompleteWorld (Seed × T)) (k : ℕ) :
    |payloadPerturbationTag i A v k|≤D := by
  unfold payloadPerturbationTag
  split_ifs
  · exact hBound _
  · simpa only [abs_zero] using hD

omit [MeasurableSpace Seed] [MeasurableSpace T] in
lemma payloadPerturbationTag_vanish (i : ℕ) {A : ℝ × T → ℝ} {b : ℝ}
    (hZero : ∀ z, z.1<b → A z=0) (v : CompleteWorld (Seed × T)) (k : ℕ) (hk : codeValue v k<b) :
    payloadPerturbationTag i A v k=0 := by
  by_cases hi : k=candidateEnumeration (Sum.inl i)
  · subst k
    simp only [codeValue,codePoint,Equiv.symm_apply_apply,candidatePoint] at hk
    exact (if_pos rfl).trans (hZero _ hk)
  · exact if_neg hi

lemma canonical_payloadPerturbation_mean_zero (B : CountableInstance) {w c : ℝ} (hw : 0≤w) (hc : 0≤c)
    (i : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν] (κ : Measure T) [IsProbabilityMeasure κ]
    (A : ℝ × T → ℝ) (hA : Measurable A) {D : ℝ} (_hD : 0≤D) (hBound : ∀ z, |A z|≤D)
    (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) :
    (∫ v : CompleteWorld (Seed × T), (B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,v.2.2.2.2)
      ∂B.completeWorldLaw (ν.prod κ))=0 := by
  let f := fun z : CompleteWorld Seed × T =>
    (B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed z.1)*A (z.1.2.1 i,z.2)
  have hErase := (B.eraseCompleteSeed_measurePreserving ν).measurable
  have hCan := (B.valueRule w c).measurable_individualSelectionIndicator (B.valueRule_isMeasurable hw hc) i
  have hMeas : Measurable f := by
    exact ((hCan.comp hErase).comp measurable_fst).mul (hA.comp
      ((((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).comp measurable_fst).prodMk measurable_snd))
  have hInt : Integrable f ((B.completeWorldLaw ν).prod κ) := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable D
    exact Eventually.of_forall (fun z => by
      change ‖(B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed z.1)*A (z.1.2.1 i,z.2)‖≤D
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((B.valueRule w c).individualSelectionIndicator_mem_unit i _).1]
      exact (mul_le_mul ((B.valueRule w c).individualSelectionIndicator_mem_unit i _).2 (hBound _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hMP := B.splitCompleteAuxiliary_measurePreserving ν κ
  have hMean := hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable
  change (∫ v : CompleteWorld (Seed × T), (B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,v.2.2.2.2)
    ∂B.completeWorldLaw (ν.prod κ))=∫ z, f z ∂(B.completeWorldLaw ν).prod κ at hMean
  rw [hMean,integral_prod _ hInt]
  have hInner (v : CompleteWorld Seed) : (∫ t, f (v,t) ∂κ)=0 := by
    change (∫ t, (B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,t) ∂κ)=0
    rw [integral_const_mul,hCentered,mul_zero]
  simp_rw [hInner]
  exact integral_zero _ _

end CountableInstance
namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

noncomputable def payloadPerturbationMean (π : RandomizedIndividualTaggedPolicy B i κ) (A : ℝ × T → ℝ) : ℝ :=
  ∫ v : CompleteWorld (π.Seed × T), π.rule.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2)
    ∂B.completeWorldLaw (π.seedLaw.prod κ)

lemma integrable_payloadPerturbation (π : RandomizedIndividualTaggedPolicy B i κ)
    (A : ℝ × T → ℝ) (hA : Measurable A) {D : ℝ} (hBound : ∀ z, |A z|≤D) :
    Integrable (fun v : CompleteWorld (π.Seed × T) => π.rule.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2))
      (B.completeWorldLaw (π.seedLaw.prod κ)) := by
  have hMeas : Measurable (fun v : CompleteWorld (π.Seed × T) => A (v.2.1 i,v.2.2.2.2)) := by fun_prop
  apply (π.rule.integrable_individualSelectionIndicator π.measurable_rule B (π.seedLaw.prod κ) i).mul_bdd hMeas.aestronglyMeasurable
  exact Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact hBound _)

lemma payloadPerturbationMean_abs_le_tagError (π : RandomizedIndividualTaggedPolicy B i κ)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) (A : ℝ × T → ℝ) (hA : Measurable A) {D : ℝ}
    (hD : 0≤D) (hBound : ∀ z, |A z|≤D) (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) :
    |π.payloadPerturbationMean A|≤π.toBasePolicy.expectedSelectedTagError w c (payloadPerturbationTag i A) := by
  let F := fun v : CompleteWorld (π.Seed × T) =>
    (B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,v.2.2.2.2)
  have hErase := (B.eraseCompleteSeed_measurePreserving (π.seedLaw.prod κ)).measurable
  have hCan := (B.valueRule w c).measurable_individualSelectionIndicator (B.valueRule_isMeasurable hw hc) i
  have hMeasA : Measurable (fun v : CompleteWorld (π.Seed × T) => A (v.2.1 i,v.2.2.2.2)) := by fun_prop
  have hFm : Measurable F := (hCan.comp hErase).mul hMeasA
  have hFI : Integrable F (B.completeWorldLaw (π.seedLaw.prod κ)) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable D
    exact Eventually.of_forall (fun v => by
      change ‖(B.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,v.2.2.2.2)‖≤D
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((B.valueRule w c).individualSelectionIndicator_mem_unit i _).1]
      exact (mul_le_mul ((B.valueRule w c).individualSelectionIndicator_mem_unit i _).2 (hBound _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hZero : (∫ v, F v ∂B.completeWorldLaw (π.seedLaw.prod κ))=0 :=
    B.canonical_payloadPerturbation_mean_zero hw hc i π.seedLaw κ A hA hD hBound hCentered
  have hDiff : π.payloadPerturbationMean A=∫ v,
      π.rule.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2)-F v ∂B.completeWorldLaw (π.seedLaw.prod κ) := by
    rw [integral_sub (π.integrable_payloadPerturbation A hA hBound) hFI,hZero,sub_zero]
    rfl
  rw [hDiff]
  have h := norm_integral_le_integral_norm (μ := B.completeWorldLaw (π.seedLaw.prod κ))
    (fun v => π.rule.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2)-F v)
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    change ‖_‖=_
    rw [Real.norm_eq_abs]
    change _=|π.rule.selectedTag (payloadPerturbationTag i A) v-
      ((B.valueRule w c).comapSeed (fun _ : π.Seed × T => ())).selectedTag (payloadPerturbationTag i A) v|
    rw [CountableRule.selectedTag_payloadPerturbation,CountableRule.selectedTag_payloadPerturbation]
    rfl)

end RandomizedIndividualTaggedPolicy

lemma CountableInstance.centered_payloadPerturbation_stability (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) {T : Type} [MeasurableSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) :
    ∃ ψ : ℝ → ℝ, (∀ r, 0≤ψ r) ∧ Monotone ψ ∧ ψ 0=0 ∧ Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ π : RandomizedIndividualTaggedPolicy B i κ,
        |π.payloadPerturbationMean A|≤ψ (B.optimalScalarValue w c-π.toBasePolicy.scalarObjective w c) := by
  obtain ⟨ψ,hψ,hMono,hψZero,hLimit,hError⟩ := countable_selectedOccurrence_stability_fixed_weights
    (fun _ : Unit => B) B.cap.property hw hc hD hb (fun _ => hZero) (fun _ => le_rfl)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ _ => le_rfl)
  refine ⟨ψ,hψ,hMono,hψZero,hLimit,?_⟩
  intro π
  exact (π.payloadPerturbationMean_abs_le_tagError hw.le hc.le A hA hD hBound hCentered).trans
    (hError () π.toBasePolicy (payloadPerturbationTag i A) (payloadPerturbationTag_measurable i hA)
      (Eventually.of_forall (fun v k => payloadPerturbationTag_bound i hD hBound v k))
      (Eventually.of_forall (fun v k => payloadPerturbationTag_vanish i hVanish v k)))

end ProphetSecretary.Limiting
