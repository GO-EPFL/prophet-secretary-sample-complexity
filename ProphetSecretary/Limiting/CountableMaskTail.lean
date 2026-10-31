import ProphetSecretary.Limiting.CountableMaskLaw

/-!
# A uniform omitted-individual bound over all unseen masks

The actual masked product-law pushforward and pointwise maximum comparison
show that zero masks cannot increase the omitted excess maximum. Intensity
rescaling does not affect this individual-value bound.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

lemma maskOffer_le_self (keep : Bool) {x : ℝ} (hx : 0 ≤ x) : maskOffer keep x ≤ x := by
  change (if keep = true then x else 0) ≤ x
  split_ifs
  · exact le_rfl
  · exact hx

lemma CountableInstance.individualTailExcessMaximum_mask_le (B : CountableInstance) (keep : IndividualMask)
    (N : ℕ) (x : ℕ → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) B.cap) :
    (B.maskIndividuals keep).individualTailExcessMaximum N (maskIndividualValues keep x) ≤
      B.individualTailExcessMaximum N x := by
  let f : ℕ → ℝ := fun k => Model.excessValueMap B.terminal (maskIndividualValues keep x (k+N))
  let g : ℕ → ℝ := fun k => Model.excessValueMap B.terminal (x (k+N))
  have hg (k : ℕ) : g k ≤ (B.cap : ℝ) :=
    (Model.excessValueMap_le_self B.terminal.property _).trans (hx (k+N)).2
  have hfg (k : ℕ) : f k ≤ g k :=
    Model.excessValueMap_monotone B.terminal.property (maskOffer_le_self (keep (k+N)) (hx (k+N)).1)
  have hBound : BddAbove (range (prefixMaximum 0 g)) :=
    ⟨B.cap,fun _ ⟨M,hM⟩ => hM ▸ prefixMaximum_le B.cap.property B.cap.property g hg M⟩
  change (⨆ M, prefixMaximum 0 f M) ≤ ⨆ M, prefixMaximum 0 g M
  apply ciSup_mono hBound
  intro M
  unfold prefixMaximum
  apply max_le (le_max_left _ _)
  apply Model.Instance.maximum_le _ ((Model.Instance.maximum_nonnegative _).trans (le_max_right _ _))
  intro i
  exact (hfg i.val).trans ((Model.Instance.le_maximum (fun j : Fin M => g j.val) i).trans (le_max_right _ _))

lemma CountableInstance.expectedIndividualTailExcessMaximum_mask_le (B : CountableInstance)
    (keep : IndividualMask) (N : ℕ) :
    (B.maskIndividuals keep).expectedIndividualTailExcessMaximum N ≤ B.expectedIndividualTailExcessMaximum N := by
  have hMP := B.maskValues_measurePreserving keep
  have he : (B.maskIndividuals keep).expectedIndividualTailExcessMaximum N =
      ∫ x, (B.maskIndividuals keep).individualTailExcessMaximum N (maskIndividualValues keep x) ∂B.individualValuesLaw := by
    have h := integral_map (μ := B.individualValuesLaw) hMP.measurable.aemeasurable
      ((B.maskIndividuals keep).measurable_individualTailExcessMaximum N).aestronglyMeasurable
    rw [hMP.map_eq] at h
    exact h
  have hI := hMP.integrable_comp_of_integrable ((B.maskIndividuals keep).integrable_individualTailExcessMaximum N)
  have h := integral_mono_ae hI (B.integrable_individualTailExcessMaximum N)
    (B.individual_values_supported.mono (fun x hx => B.individualTailExcessMaximum_mask_le keep N x hx))
  exact he.le.trans h

lemma CountableInstance.expectedIndividualTailExcessMaximum_remainingState_le (B : CountableInstance)
    (keep : IndividualMask) (u : ℝ≥0) (N : ℕ) :
    (B.remainingState keep u).expectedIndividualTailExcessMaximum N ≤ B.expectedIndividualTailExcessMaximum N :=
  B.expectedIndividualTailExcessMaximum_mask_le keep N

end ProphetSecretary.Limiting
