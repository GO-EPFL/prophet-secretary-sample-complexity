import ProphetSecretary.Limiting.CountableFiniteMask
import ProphetSecretary.Limiting.HybridRewardTail

/-!
# Positive-level tail masses of countable remaining states

The total individual probability mass and anonymous intensity are finite above
any level strictly above the reserve. Every finite masked truncation is bounded
by this same tail mass, independently of its retained dimension and cutoff.
-/

open MeasureTheory Set
open scoped Topology Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

lemma maskedProbabilityLaw_tail_le (q : ProbabilityMeasure ℝ) (keep : Bool) {b : ℝ} (hb : 0 ≤ b) :
    (maskedProbabilityLaw q keep : Measure ℝ) (Ioi b) ≤ (q : Measure ℝ) (Ioi b) := by
  by_cases hk : keep = true
  · have he : maskedProbabilityLaw q keep = q := if_pos hk
    exact (congrArg (fun p : ProbabilityMeasure ℝ => (p : Measure ℝ) (Ioi b)) he).le
  · have he : maskedProbabilityLaw q keep = (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := if_neg hk
    calc
      _ = Measure.dirac (0 : ℝ) (Ioi b) := congrArg (fun p : ProbabilityMeasure ℝ => (p : Measure ℝ) (Ioi b)) he
      _ = 0 := by simp [Measure.dirac_apply',not_lt.mpr hb]
      _ ≤ _ := bot_le

noncomputable def CountableInstance.totalTailMass (B : CountableInstance) (b : ℝ) : ENNReal :=
  (∑' i, (B.individuals i : Measure ℝ) (Ioi b))+B.intensity (Ioi b)

lemma CountableInstance.totalTailMass_finite (B : CountableInstance) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    B.totalTailMass b < ⊤ := ENNReal.add_lt_top.mpr ⟨B.individual_tail_finite b hb,B.intensity_tail_finite b hb⟩

noncomputable def CountableInstance.positiveTailCount (B : CountableInstance) (b : ℝ)
    (_hb : (B.terminal : ℝ) < b) : ℝ := (B.totalTailMass b).toReal

lemma CountableInstance.positiveTailCount_eq (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ) < b) :
    B.positiveTailCount b hb = (∑' i, (B.individuals i : Measure ℝ) (Ioi b)).toReal+B.intensity.real (Ioi b) :=
  ENNReal.toReal_add (B.individual_tail_finite b hb).ne (B.intensity_tail_finite b hb).ne

lemma CountableInstance.positiveTailCount_nonnegative (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ) < b) :
    0 ≤ B.positiveTailCount b hb := ENNReal.toReal_nonneg

lemma CountableInstance.finiteMaskState_tailCount_le (B : CountableInstance) (N : ℕ) (cut : ℝ)
    (hcut : (B.terminal : ℝ) < cut) (keep : Fin N → Bool) (b : ℝ) (hb : (B.terminal : ℝ) < b) :
    (B.finiteMaskState N cut hcut keep).tailCount b ≤ B.positiveTailCount b hb := by
  have hb0 : 0 ≤ b := B.terminal.property.trans hb.le
  have hSum : (∑ i : Fin N, (maskedProbabilityLaw (B.individuals i.val) (keep i) : Measure ℝ) (Ioi b)) ≤
      ∑' i, (B.individuals i : Measure ℝ) (Ioi b) := by
    calc
      _ ≤ ∑ i : Fin N, (B.individuals i.val : Measure ℝ) (Ioi b) := Finset.sum_le_sum (fun i _ => maskedProbabilityLaw_tail_le _ _ hb0)
      _ = ∑ i ∈ Finset.range N, (B.individuals i : Measure ℝ) (Ioi b) := Fin.sum_univ_eq_sum_range (fun i : ℕ => (B.individuals i : Measure ℝ) (Ioi b)) N
      _ ≤ _ := ENNReal.sum_le_tsum (Finset.range N)
  have hInd := ENNReal.toReal_mono (B.individual_tail_finite b hb).ne hSum
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at hInd
  have hIndividuals : (B.finiteMaskState N cut hcut keep).individuals.tailCount b ≤
      (∑' i, (B.individuals i : Measure ℝ) (Ioi b)).toReal := by
    change (∑ i : Fin N, ((maskedProbabilityLaw (B.individuals i.val)
      (extendIndividualMask keep i.val) : Measure ℝ) (Ioi b)).toReal) ≤ _
    simp only [extendIndividualMask_at_prefix]
    exact hInd
  have hIntensity : ((B.finiteMaskState N cut hcut keep).intensity : Measure ℝ).real (Ioi b) ≤
      B.intensity.real (Ioi b) := by
    change ((B.intensity.restrict (Ioi cut)) (Ioi b)).toReal ≤ (B.intensity (Ioi b)).toReal
    rw [Measure.restrict_apply measurableSet_Ioi]
    exact ENNReal.toReal_mono (B.intensity_tail_finite b hb).ne (measure_mono inter_subset_left)
  change (B.finiteMaskState N cut hcut keep).individuals.tailCount b+
    ((B.finiteMaskState N cut hcut keep).intensity : Measure ℝ).real (Ioi b) ≤ _
  rw [B.positiveTailCount_eq b hb]
  exact add_le_add hIndividuals hIntensity

end ProphetSecretary.Limiting
