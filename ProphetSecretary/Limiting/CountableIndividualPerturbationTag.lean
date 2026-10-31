import ProphetSecretary.Limiting.CountableIndividualDisplacement
import ProphetSecretary.Limiting.CountableOccurrenceStability
import ProphetSecretary.Limiting.CountableCanonicalLimit

/-!
# The selected response of one individual value perturbation

The tag is zero on every other occurrence. Its stability follows from the
proved selected-occurrence comparison for arbitrary competing policies.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance

noncomputable def individualPerturbationTag {Seed : Type*} (i : ℕ) (φ : ℝ → ℝ) : CountableTags Seed :=
  fun v k => if k=candidateEnumeration (Sum.inl i) then φ (v.2.1 i) else 0

lemma individualPerturbationTag_measurable {Seed : Type*} [MeasurableSpace Seed]
    (i : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    (individualPerturbationTag (Seed := Seed) i φ).IsMeasurable := by
  intro k
  by_cases hk : k=candidateEnumeration (Sum.inl i)
  · simpa only [individualPerturbationTag,if_pos hk] using measurable_individualScore i hφ
  · simpa only [individualPerturbationTag,if_neg hk] using (measurable_const : Measurable (fun _ : CompleteWorld Seed => (0 : ℝ)))

lemma individualPerturbationTag_bound {Seed : Type*} (i : ℕ) {φ : ℝ → ℝ} {D : ℝ}
    (hD : 0≤D) (hBound : ∀ x, |φ x|≤D) (v : CompleteWorld Seed) (k : ℕ) :
    |individualPerturbationTag i φ v k|≤D := by
  unfold individualPerturbationTag
  split_ifs
  · exact hBound _
  · simpa only [abs_zero] using hD

lemma individualPerturbationTag_vanish {Seed : Type*} (i : ℕ) {φ : ℝ → ℝ} {b : ℝ}
    (hZero : ∀ x, x<b → φ x=0) (v : CompleteWorld Seed) (k : ℕ) (hk : codeValue v k<b) :
    individualPerturbationTag i φ v k=0 := by
  by_cases hi : k=candidateEnumeration (Sum.inl i)
  · subst k
    simp only [codeValue,codePoint,Equiv.symm_apply_apply,candidatePoint] at hk
    exact (if_pos rfl).trans (hZero _ hk)
  · exact if_neg hi

lemma CountableRule.selectedTag_individualPerturbation {Seed : Type*} (π : CountableRule Seed)
    (i : ℕ) (φ : ℝ → ℝ) (v : CompleteWorld Seed) :
    π.selectedTag (individualPerturbationTag i φ) v=π.individualSelectionIndicator i v*φ (v.2.1 i) := by
  rw [CountableRule.individualSelectionIndicator_eq_code]
  unfold CountableRule.selectedTag FirstAcceptance.reward
  cases hs : FirstAcceptance.selectedCode π.codeAccepted codeTime v with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one,Nat.add_right_cancel_iff,individualPerturbationTag]
    split_ifs <;> simp

end CountableInstance

namespace RandomizedCountablePolicy
variable {B : CountableInstance}

noncomputable def individualPerturbationMean (π : RandomizedCountablePolicy B) (i : ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∫ v, π.rule.individualSelectionIndicator i v*φ (v.2.1 i) ∂B.completeWorldLaw π.seedLaw

lemma integrable_individualPerturbation (π : RandomizedCountablePolicy B) (i : ℕ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {D : ℝ} (hBound : ∀ x, |φ x|≤D) :
    Integrable (fun v => π.rule.individualSelectionIndicator i v*φ (v.2.1 i)) (B.completeWorldLaw π.seedLaw) :=
  (π.rule.integrable_individualSelectionIndicator π.measurable_rule B π.seedLaw i).mul_bdd
    (measurable_individualScore i hφ).aestronglyMeasurable
    (Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact hBound _))

lemma individualPerturbationMean_difference_le (π : RandomizedCountablePolicy B) (i : ℕ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {D : ℝ} (hBound : ∀ x, |φ x|≤D) {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    |π.individualPerturbationMean i φ-(B.valuePolicy hw hc).individualPerturbationMean i φ|≤
      π.expectedSelectedTagError w c (individualPerturbationTag i φ) := by
  let π₀ := B.valuePolicy hw hc
  let F := fun v : CompleteWorld Unit => π₀.rule.individualSelectionIndicator i v*φ (v.2.1 i)
  have hF : Measurable F := (π₀.rule.measurable_individualSelectionIndicator π₀.measurable_rule i).mul (measurable_individualScore i hφ)
  have hFI : Integrable F (B.completeWorldLaw (Measure.dirac ())) := π₀.integrable_individualPerturbation i hφ hBound
  have hSeed := B.eraseCompleteSeed_measurePreserving π.seedLaw
  have hMean := hSeed.hasLaw.integral_comp hF.aestronglyMeasurable
  change (∫ v, F (eraseCompleteSeed v) ∂B.completeWorldLaw π.seedLaw)=π₀.individualPerturbationMean i φ at hMean
  have hOldI := π.integrable_individualPerturbation i hφ hBound
  have hBaseI : Integrable (fun v => F (eraseCompleteSeed v)) (B.completeWorldLaw π.seedLaw) :=
    hSeed.integrable_comp_of_integrable hFI
  have hDiff : π.individualPerturbationMean i φ-π₀.individualPerturbationMean i φ=
      ∫ v, π.rule.individualSelectionIndicator i v*φ (v.2.1 i)-F (eraseCompleteSeed v) ∂B.completeWorldLaw π.seedLaw := by
    rw [integral_sub hOldI hBaseI,hMean]
    rfl
  rw [hDiff]
  have h := norm_integral_le_integral_norm (μ := B.completeWorldLaw π.seedLaw)
    (fun v => π.rule.individualSelectionIndicator i v*φ (v.2.1 i)-F (eraseCompleteSeed v))
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    change ‖_‖=_
    rw [Real.norm_eq_abs]
    change _=|π.rule.selectedTag (individualPerturbationTag i φ) v-
      (B.valueRule w c).selectedTag (individualPerturbationTag i φ) (eraseCompleteSeed v)|
    rw [CountableRule.selectedTag_individualPerturbation,CountableRule.selectedTag_individualPerturbation]
    rfl)

end RandomizedCountablePolicy

lemma CountableInstance.individualPerturbationMean_stability (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) :
    ∃ ψ : ℝ → ℝ, (∀ r, 0≤ψ r) ∧ Monotone ψ ∧ ψ 0=0 ∧ Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ π : RandomizedCountablePolicy B,
        |π.individualPerturbationMean i φ-(B.valuePolicy hw hc).individualPerturbationMean i φ|≤
          ψ (B.optimalScalarValue w c-π.scalarObjective w c) := by
  obtain ⟨ψ,hψ,hMono,hψZero,hLimit,hError⟩ := countable_selectedOccurrence_stability_fixed_weights
    (fun _ : Unit => B) B.cap.property hw hc hD hb (fun _ => hZero) (fun _ => le_rfl)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ _ => le_rfl)
  refine ⟨ψ,hψ,hMono,hψZero,hLimit,?_⟩
  intro π
  exact (π.individualPerturbationMean_difference_le i hφ hBound hw hc).trans
    (hError () π (individualPerturbationTag i φ) (individualPerturbationTag_measurable i hφ)
      (Eventually.of_forall (fun v k => individualPerturbationTag_bound i hD hBound v k))
      (Eventually.of_forall (fun v k => individualPerturbationTag_vanish i hVanish v k)))

end ProphetSecretary.Limiting
