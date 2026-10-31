import ProphetSecretary.Limiting.HybridMaximumDistribution
import ProphetSecretary.Limiting.HybridExcessState
import ProphetSecretary.Model.ExcessPositiveTail

/-!
# Reserve shift of the actual hybrid prophet benchmark

The Poisson intensity is pushed forward and restricted to positive marks. The
proof compares actual maximum laws through void probabilities, independently
of the scalar-value approximation.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

lemma excessIntensity_positiveTail (μ : FiniteMeasure ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (excessIntensity μ a : Measure ℝ) (Ioi b) = (μ : Measure ℝ) (Ioi (a+b)) := by
  change (Model.excessLaw (μ : Measure ℝ) a).restrict (Ioi 0) (Ioi b) = _
  rw [Measure.restrict_apply measurableSet_Ioi]
  have hi : Ioi b ∩ Ioi (0 : ℝ) = Ioi b := inter_eq_left.mpr (fun _ hx => hb.trans_lt hx)
  rw [hi,Model.excessLaw_positiveTail _ ha hb]

lemma excessLaw_Iic (κ : Measure ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Model.excessLaw κ a (Iic b) = κ (Iic (a+b)) := by
  rw [Model.excessLaw,Measure.map_apply (Model.measurable_excessValueMap a) measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage,mem_Iic]
  exact (not_lt.symm.trans (not_congr (Model.excessValueMap_gt_iff ha hb))).trans not_lt

variable {n : ℕ}

lemma FiniteIntensityHybridInstance.maximum_reserveShift_law (B : FiniteIntensityHybridInstance n) :
    (hybridValueLaw B.individuals B.intensity).map (hybridMaximum B.terminal) =
      (hybridValueLaw (B.excessState B.terminal).individuals (B.excessState B.terminal).intensity).map
        (fun v => (B.terminal : ℝ) + hybridMaximum 0 v) := by
  let C := B.excessState B.terminal
  have hm : Measurable (fun v : Configuration × (Fin n → ℝ) => (B.terminal : ℝ) + hybridMaximum 0 v) :=
    measurable_const.add (measurable_hybridMaximum 0)
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_hybridMaximum B.terminal) measurableSet_Iic,
    Measure.map_apply hm measurableSet_Iic]
  by_cases hat : (B.terminal : ℝ) ≤ t
  · have ht : 0 ≤ t := B.terminal.property.trans hat
    have hb : 0 ≤ t - (B.terminal : ℝ) := sub_nonneg.mpr hat
    have he : {v : Configuration × (Fin n → ℝ) | (B.terminal : ℝ) + hybridMaximum 0 v ≤ t} =
        {v | hybridMaximum 0 v ≤ t - (B.terminal : ℝ)} := by
      ext v
      change (B.terminal : ℝ) + hybridMaximum 0 v ≤ t ↔ hybridMaximum 0 v ≤ t - (B.terminal : ℝ)
      constructor <;> intro h <;> linarith
    change hybridValueLaw B.individuals B.intensity {v | hybridMaximum B.terminal v ≤ t} =
      hybridValueLaw C.individuals C.intensity {v | (B.terminal : ℝ) + hybridMaximum 0 v ≤ t}
    rw [he,hybridMaximum_probability_Iic B.individuals B.intensity ht hat,
      hybridMaximum_probability_Iic C.individuals C.intensity hb hb]
    have htail : (C.intensity : Measure ℝ) (Ioi (t-(B.terminal : ℝ))) =
        (B.intensity : Measure ℝ) (Ioi t) := by
      dsimp [C,FiniteIntensityHybridInstance.excessState]
      exact (excessIntensity_positiveTail B.intensity B.terminal.property hb).trans
        (congrArg (fun z : ℝ => (B.intensity : Measure ℝ) (Ioi z)) (add_sub_cancel (B.terminal : ℝ) t))
    have hind (i : Fin n) : C.individuals.law i (Iic (t-(B.terminal : ℝ))) = B.individuals.law i (Iic t) := by
      change Model.excessLaw (B.individuals.law i) B.terminal (Iic (t-(B.terminal : ℝ))) = _
      exact (excessLaw_Iic (B.individuals.law i) B.terminal.property hb).trans
        (congrArg (fun z : ℝ => B.individuals.law i (Iic z)) (add_sub_cancel (B.terminal : ℝ) t))
    simp only [Measure.real,htail,hind]
  · have hleft : (hybridMaximum (n := n) B.terminal) ⁻¹' Iic t = ∅ := by
      ext v
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((lt_of_not_ge hat).trans_le (le_max_left _ _))
    have hright : (fun v : Configuration × (Fin n → ℝ) => (B.terminal : ℝ) + hybridMaximum 0 v) ⁻¹' Iic t = ∅ := by
      ext v
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((lt_of_not_ge hat).trans_le (le_add_of_nonneg_right (hybridMaximum_nonnegative 0 v)))
    rw [hleft,hright,measure_empty,measure_empty]

lemma FiniteIntensityHybridInstance.expectedMaximum_reserveShift (B : FiniteIntensityHybridInstance n) :
    B.expectedMaximum = (B.terminal : ℝ) + (B.excessState B.terminal).expectedMaximum := by
  let C := B.excessState B.terminal
  have hm : Measurable (fun v : Configuration × (Fin n → ℝ) => (B.terminal : ℝ) + hybridMaximum 0 v) :=
    measurable_const.add (measurable_hybridMaximum 0)
  have hL := integral_map (μ := hybridValueLaw B.individuals B.intensity)
    (measurable_hybridMaximum B.terminal).aemeasurable aestronglyMeasurable_id
  have hR := integral_map (μ := hybridValueLaw C.individuals C.intensity) hm.aemeasurable aestronglyMeasurable_id
  rw [B.maximum_reserveShift_law] at hL
  change _ = (∫ v, (B.terminal : ℝ) + hybridMaximum 0 v ∂hybridValueLaw C.individuals C.intensity) at hR
  have hi : Integrable (hybridMaximum (n := n) 0) (hybridValueLaw C.individuals C.intensity) := C.integrable_maximum
  rw [integral_add (integrable_const _) hi,integral_const] at hR
  simp only [probReal_univ,one_smul] at hR
  exact hL.symm.trans hR

end ProphetSecretary.Limiting
