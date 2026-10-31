import ProphetSecretary.Model.ValueTransportLipschitz
import ProphetSecretary.Model.MappedBellmanLoss
import ProphetSecretary.Model.BellmanLossProbability
import ProphetSecretary.Model.DurationLower
import ProphetSecretary.Analysis.StoppingDecisionLoss

/-!
# Statewise value transport and local decision loss

Coordinate maps commute with restriction to unseen identities. The resulting
continuation bound applies to every remaining horizon. The old canonical action
then incurs mapped loss at most 2wh, and only within its original gap band of
radius 2wh. Paper correspondence: `upmom:transport`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.mapValues_restrictTo (P : Instance n) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    (A : Finset (Fin n)) :
    (P.mapValues f hf hnn).restrictTo A =
      (P.restrictTo A).mapValues (fun j => f (stateEmbedding A j))
        (fun j => hf (stateEmbedding A j)) (fun j => hnn (stateEmbedding A j)) := by
  apply Instance.eq_of_law_eq
  funext j
  rfl

theorem Instance.continuationValue_mapValues_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c u : ℝ} (hh : 0 ≤ h) (hw : 0 ≤ w) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) (A : Finset (Fin n)) :
    |(P.mapValues f hf hnn).continuationValue A u w c - P.continuationValue A u w c| ≤ w * h := by
  unfold continuationValue
  rw [P.mapValues_restrictTo f hf hnn A]
  exact (P.restrictTo A).optimalScalarValue_mapValues_lipschitz
    (P.restrictTo_integrable_maximum A hP) _ _ _ hh hw (mul_nonneg hc hu)
    (fun j => hdispl (stateEmbedding A j))

lemma Instance.mapped_arrival_gap_difference_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (x u : Fin n → ℝ) (i : Fin n) :
    |(w * f i (x i) - (P.mapValues f hf hnn).continuationAtArrival w c x u i) -
      (w * x i - P.continuationAtArrival w c x u i)| ≤ 2 * w * h := by
  have hV := P.continuationValue_mapValues_lipschitz hP f hf hnn hh hw hc
    (le_max_left (0 : ℝ) (1 - u i)) (fun j => Eventually.of_forall (hdispl j))
    ((unseen (history Finset.univ x u (u i))).erase i)
  change |(P.mapValues f hf hnn).continuationAtArrival w c x u i -
    P.continuationAtArrival w c x u i| ≤ w * h at hV
  have hR : |w * f i (x i) - w * x i| ≤ w * h := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (hdispl i (x i)) hw
  calc
    _ = |(w * f i (x i) - w * x i) -
        ((P.mapValues f hf hnn).continuationAtArrival w c x u i - P.continuationAtArrival w c x u i)| := by
      congr 1
      ring
    _ ≤ |w * f i (x i) - w * x i| +
        |(P.mapValues f hf hnn).continuationAtArrival w c x u i - P.continuationAtArrival w c x u i| := abs_sub _ _
    _ ≤ 2 * w * h := by linarith only [hR, hV]

theorem Instance.canonical_mappedLoss_band (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (x u : Fin n → ℝ) (i : Fin n) :
    let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
    π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x u i ≤ 2 * w * h ∧
      (2 * w * h < |w * x i - P.continuationAtArrival w c x u i| →
        π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x u i = 0) := by
  let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
  have hzero : ProphetSecretary.Analysis.gapLoss (π.action () Finset.univ x u i)
      (w * x i - P.continuationAtArrival w c x u i) = 0 := by
    rw [ProphetSecretary.Analysis.gapLoss_eq_decisionLoss]
    exact P.valueThreshold_arrivalLoss_zero hw c x u i
  have hgap := P.mapped_arrival_gap_difference_le hP f hf hnn hh hw.le hc hdispl x u i
  have heq : ProphetSecretary.Analysis.gapLoss (π.action () Finset.univ x u i)
      (w * f i (x i) - (P.mapValues f hf hnn).continuationAtArrival w c x u i) =
      π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x u i := by
    rw [ProphetSecretary.Analysis.gapLoss_eq_decisionLoss]
    rfl
  constructor
  · rw [← heq]
    exact ProphetSecretary.Analysis.gapLoss_perturbation_bound hzero hgap
  · intro hout
    rw [← heq]
    exact ProphetSecretary.Analysis.gapLoss_vanishes_outside_band hzero hgap hout

/-- A zero-preserving perturbation incurs no mapped loss at a zero offer before
the terminal instant. Its arrival identity is still retained in the history. -/
lemma Instance.canonical_mappedLoss_zero_offer (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (hfzero : ∀ i, f i 0 = 0)
    (x u : Fin n → ℝ) (i : Fin n) (hi : x i = 0) (hut : u i < 1) :
    (P.valuePolicy hP hw.le hc.le).rule.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x u i = 0 := by
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn
    (fun j => Eventually.of_forall (hdispl j))
  have hact := P.valueThreshold_rejects_zero hP hw hc x u i hut hi
  have hv := (P.mapValues f hf hnn).continuationAtArrival_nonnegative hQ hw.le hc.le x u i
  dsimp only [Instance.valuePolicy]
  unfold Policy.mappedArrivalLoss
  rw [hi, hfzero, mul_zero, hact]
  simp only [Bool.false_eq_true, if_false, max_eq_right hv, sub_self]

end ProphetSecretary.Model
