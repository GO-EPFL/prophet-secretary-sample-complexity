import ProphetSecretary.Statistics.EmpiricalSlopeEnvelopeMeasurability

/-!
# Dependence of the complete residual envelope on the scalar

The suffix maximum is a finite maximum. Its change between two scalar weights is
bounded by the suffix envelope of their normalized residual difference, and the
actual Bellman continuation values give continuity on nonnegative coefficients.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics

variable {n : ℕ}

lemma abs_suffixEnvelope_sub_le_normalized (u f g : Fin n → ℝ) {d : ℝ} (hd : 0 < d) :
    |suffixEnvelope u f - suffixEnvelope u g| ≤ d * suffixEnvelope u (fun i => (f i - g i) / d) := by
  have hdiff (j : Option (Fin n)) : |suffixSum u f j - suffixSum u g j| ≤
      d * suffixEnvelope u (fun i => (f i - g i) / d) := by
    have h := le_suffixEnvelope u (fun i => (f i - g i) / d) j
    rw [suffixSum_sub_div, abs_div, abs_of_pos hd] at h
    exact (div_le_iff₀ hd).mp h |>.trans_eq (mul_comm _ _)
  have hfg : suffixEnvelope u f ≤ suffixEnvelope u g + d * suffixEnvelope u (fun i => (f i - g i) / d) := by
    apply Finset.sup'_le
    intro j _
    have h := abs_sub_abs_le_abs_sub (suffixSum u f j) (suffixSum u g j)
    nlinarith [le_suffixEnvelope u g j, hdiff j]
  have hgf : suffixEnvelope u g ≤ suffixEnvelope u f + d * suffixEnvelope u (fun i => (f i - g i) / d) := by
    apply Finset.sup'_le
    intro j _
    have h := abs_sub_abs_le_abs_sub (suffixSum u g j) (suffixSum u f j)
    rw [abs_sub_comm] at h
    nlinarith [le_suffixEnvelope u f j, hdiff j]
  rw [abs_le]
  constructor <;> linarith

lemma continuous_suffixEnvelope {f : ℝ → Fin n → ℝ} (u : Fin n → ℝ)
    (hf : ∀ i, Continuous fun z => f z i) : Continuous (fun z => suffixEnvelope u (f z)) := by
  unfold suffixEnvelope
  apply Continuous.finset_sup'_apply ⟨none, Finset.mem_univ _⟩
  intro j _
  cases j with
  | none => exact (continuous_finsetSum _ (fun i _ => hf i)).abs
  | some j =>
    apply Continuous.abs
    apply continuous_finsetSum
    intro i _
    split_ifs
    · exact hf i
    · exact continuous_const

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.abs_residualSuffixEnvelope_sub_le_increment (Q P : Instance n)
    {z z' : ℝ} (hzz : z < z') (u : Fin n → ℝ) :
    |Q.residualSuffixEnvelope P 1 z u - Q.residualSuffixEnvelope P 1 z' u| ≤
      (z' - z) * Q.residualSlopeSuffixEnvelope P z z' u :=
  ProphetSecretary.Statistics.abs_suffixEnvelope_sub_le_normalized u _ _ (sub_pos.mpr hzz)

lemma Instance.continuous_clampedContinuationAtArrival (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (x u : Fin n → ℝ) (i : Fin n) :
    Continuous (fun z : ℝ => Q.continuationAtArrival 1 (max 0 z) x u i) := by
  let A := (unseen (history Finset.univ x u (u i))).erase i
  have hp : Continuous (fun z : ℝ => ((1 : ℝ), max 0 z * max 0 (1 - u i))) :=
    continuous_const.prodMk ((continuous_const.max continuous_id).mul continuous_const)
  have h := ((Q.restrictTo A).continuous_clampedScalarValue (Q.restrictTo_integrable_maximum A hQ)).comp hp
  convert h using 1
  funext z
  change optimalScalarValue (Q.restrictTo A) 1 (max 0 z * max 0 (1 - u i)) =
    optimalScalarValue (Q.restrictTo A) (max 0 (1 : ℝ)) (max 0 (max 0 z * max 0 (1 - u i)))
  rw [max_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
    max_eq_right (mul_nonneg (le_max_left (0 : ℝ) z) (le_max_left (0 : ℝ) (1 - u i)))]

lemma Instance.continuous_clampedResidualSuffixEnvelope (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (u : Fin n → ℝ) : Continuous (fun z : ℝ => Q.residualSuffixEnvelope P 1 (max 0 z) u) := by
  apply ProphetSecretary.Statistics.continuous_suffixEnvelope
  intro i
  exact ((positivePremium_continuous (Q.law i) (Q.integrable_maximum_iff.mp hQ i) 1).comp
    (Q.continuous_clampedContinuationAtArrival hQ (fun _ => 0) u i)).sub
    ((positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) 1).comp
    (Q.continuous_clampedContinuationAtArrival hQ (fun _ => 0) u i))

end ProphetSecretary.Model
