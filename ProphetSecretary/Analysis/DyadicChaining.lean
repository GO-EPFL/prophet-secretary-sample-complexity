import ProphetSecretary.Analysis.DyadicSupremum
import ProphetSecretary.Analysis.DyadicWeights

/-! # Dyadic moment chaining for continuous scalar processes
The finite bound uses Jensen weights `1,1,(3/4)^j`; their sum is at most six.
Level cardinalities and increment distances leave a summable ratio at most
`2/3`. The explicit moment constant is `3·6^(p−1)`, independent of the process
bound used to establish integrability.
-/
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
namespace ProphetSecretary.Analysis
open ProphetSecretary.Reach.EmpiricalChaining
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def dyadicChainingConstant (p : ℕ) : ℝ := 3 * (6 : ℝ) ^ (p - 1)

@[simp] lemma dyadicChainingConstant_two : dyadicChainingConstant 2 = 18 := by norm_num [dyadicChainingConstant]
@[simp] lemma dyadicChainingConstant_six : dyadicChainingConstant 6 = 23328 := by norm_num [dyadicChainingConstant]

lemma integral_lifted_gridMaximum_pow_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D)
    (p : ℕ) (hp : 2 ≤ p)
    (hMoment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ ω, |f ω s - f ω t| ^ p ∂μ) ≤ B * |s - t| ^ p) (J : ℕ) :
    (∫ ω, gridMaximum (liftProcess f) J ω ^ p ∂μ) ≤
      dyadicChainingConstant p * ((∫ ω, |f ω 0| ^ p ∂μ) + (∫ ω, |f ω 1| ^ p ∂μ) + B) := by
  have hp0 : 0 < p := by omega
  have hE0 : Integrable (fun ω ↦ |f ω 0| ^ p) μ :=
    integrable_nonnegative_pow_of_bound μ (hf 0 |>.norm) (fun _ ↦ abs_nonneg _)
      (hBound.mono (fun _ hω ↦ hω 0 ⟨le_rfl, zero_le_one⟩)) p
  have hE1 : Integrable (fun ω ↦ |f ω 1| ^ p) μ :=
    integrable_nonnegative_pow_of_bound μ (hf 1 |>.norm) (fun _ ↦ abs_nonneg _)
      (hBound.mono (fun _ hω ↦ hω 1 ⟨zero_le_one, le_rfl⟩)) p
  have hIj (j : ℕ) : Integrable (fun ω ↦ levelMaximum (liftProcess f) j ω ^ p / ((3 / 4 : ℝ) ^ j) ^ (p - 1)) μ :=
    (integrable_lifted_levelMaximum_pow μ hf hD hBound j p).div_const _
  have hPoint (ω : Ω) : gridMaximum (liftProcess f) J ω ^ p ≤ (6 : ℝ) ^ (p - 1) *
      (|f ω 0| ^ p + |f ω 1| ^ p + ∑ j ∈ Finset.range J,
        levelMaximum (liftProcess f) j ω ^ p / ((3 / 4 : ℝ) ^ j) ^ (p - 1)) := by
    have hChain := lifted_gridMaximum_le_chain f ω J
    have hW := dyadic_chain_pow_le |f ω 0| |f ω 1| (fun j : Fin J ↦ levelMaximum (liftProcess f) j ω)
      (abs_nonneg _) (abs_nonneg _) (fun _ ↦ maxAbs_nonnegative _ _) p hp0
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ levelMaximum (liftProcess f) j ω),
      Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ levelMaximum (liftProcess f) j ω ^ p /
        ((3 / 4 : ℝ) ^ j) ^ (p - 1))] at hW
    exact (pow_le_pow_left₀ (maxAbs_nonnegative _ _) hChain p).trans hW
  have hInt := integral_mono (integrable_lifted_gridMaximum_pow μ hf hD hBound J p)
    (((hE0.add hE1).add (integrable_finsetSum _ (fun j _ ↦ hIj j))).const_mul ((6 : ℝ) ^ (p - 1))) hPoint
  simp only [Pi.add_apply] at hInt
  rw [integral_const_mul,
    integral_add (f := fun ω ↦ |f ω 0| ^ p + |f ω 1| ^ p) (g := fun ω ↦ ∑ j ∈ Finset.range J,
      levelMaximum (liftProcess f) j ω ^ p / ((3 / 4 : ℝ) ^ j) ^ (p - 1))
      (hE0.add hE1) (integrable_finsetSum _ (fun j _ ↦ hIj j)),
    integral_add hE0 hE1, integral_finsetSum _ (fun j _ ↦ hIj j)] at hInt
  simp_rw [integral_div] at hInt
  have hLevels : (∑ j ∈ Finset.range J, (∫ ω, levelMaximum (liftProcess f) j ω ^ p ∂μ) /
      ((3 / 4 : ℝ) ^ j) ^ (p - 1)) ≤ 3 * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (B * (2 : ℝ) ^ j * (1 / (2 : ℝ) ^ (j + 1)) ^ p) /
          ((3 / 4 : ℝ) ^ j) ^ (p - 1) := Finset.sum_le_sum (fun j _ ↦ div_le_div_of_nonneg_right
            (integral_lifted_levelMaximum_pow_le μ hf hD hBound p hp0 hMoment j) (by positivity))
      _ = B * ∑ j ∈ Finset.range J, (2 : ℝ) ^ j * (1 / (2 : ℝ) ^ (j + 1)) ^ p /
          ((3 / 4 : ℝ) ^ j) ^ (p - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ B * 3 := mul_le_mul_of_nonneg_left (dyadic_weighted_factor_sum_le p J hp) hB
      _ = _ := by ring
  have h6 : 0 ≤ (6 : ℝ) ^ (p - 1) := by positivity
  apply hInt.trans
  apply le_trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hLevels) h6)
  have hA0 : 0 ≤ ∫ ω, |f ω 0| ^ p ∂μ := integral_nonneg (fun _ ↦ pow_nonneg (abs_nonneg _) p)
  have hA1 : 0 ≤ ∫ ω, |f ω 1| ^ p ∂μ := integral_nonneg (fun _ ↦ pow_nonneg (abs_nonneg _) p)
  have hExtra := mul_nonneg h6 (add_nonneg hA0 hA1)
  unfold dyadicChainingConstant
  nlinarith

/-- The quantitative bound concerns the constructed countable supremum and
needs no path continuity. Continuity is used only to identify the full supremum. -/
theorem integral_dyadicSupremum_pow_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D)
    (p : ℕ) (hp : 2 ≤ p)
    (hMoment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ ω, |f ω s - f ω t| ^ p ∂μ) ≤ B * |s - t| ^ p) :
    (∫ ω, dyadicSupremum f ω ^ p ∂μ) ≤ dyadicChainingConstant p *
      ((∫ ω, |f ω 0| ^ p ∂μ) + (∫ ω, |f ω 1| ^ p ∂μ) + B) := by
  exact le_of_tendsto (integral_lifted_gridMaximum_pow_tendsto μ hf hD hBound p)
    (Filter.Eventually.of_forall (fun J ↦ integral_lifted_gridMaximum_pow_le μ hf hD hB hBound p hp hMoment J))

/-- Measurable full-interval supremum and moment estimate for every `p≥2`. -/
theorem continuous_dyadic_chaining (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D)
    (hCont : ∀ᵐ ω ∂μ, ContinuousOn (f ω) (Icc (0 : ℝ) 1)) (p : ℕ) (hp : 2 ≤ p)
    (hMoment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ ω, |f ω s - f ω t| ^ p ∂μ) ≤ B * |s - t| ^ p) :
    Measurable (dyadicSupremum f) ∧
      (∀ᵐ ω ∂μ, dyadicSupremum f ω = sSup {y : ℝ | ∃ t ∈ Icc (0 : ℝ) 1, y = |f ω t|}) ∧
      Integrable (fun ω ↦ dyadicSupremum f ω ^ p) μ ∧
      (∫ ω, dyadicSupremum f ω ^ p ∂μ) ≤ dyadicChainingConstant p *
        ((∫ ω, |f ω 0| ^ p ∂μ) + (∫ ω, |f ω 1| ^ p ∂μ) + B) := by
  refine ⟨measurable_dyadicSupremum hf, ?_, integrable_dyadicSupremum_pow μ hf hD hBound p,
    integral_dyadicSupremum_pow_le μ hf hD hB hBound p hp hMoment⟩
  filter_upwards [hBound, hCont] with ω hω hc
  exact dyadicSupremum_eq_intervalSup hD ω hω hc

end ProphetSecretary.Analysis
