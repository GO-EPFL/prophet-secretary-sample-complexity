import ProphetSecretary.Statistics.ProductEmpiricalVariance
import ProphetSecretary.Probability.CenteredValueScore

/-!
# The empirical expected maximum: unbiasedness and variance bound

For arbitrary independent offers capped by H, the actual product-empirical
expected maximum is unbiased and has variance at most Var(max X)/k. For cap1
this is at most M/k, uniformly in the number of distributions. These are the
inequalities of `eq:bayes-maximum-variance`; the separate exact Hoeffding
component expansion is not asserted by this argument.
-/
open MeasureTheory ProbabilityTheory Set Filter BoundedContinuousFunction
open scoped Topology BigOperators Classical NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Statistics ProphetSecretary.Probability
variable {n k : ℕ} [NeZero k]

noncomputable def empiricalExpectedMaximum (y : (Fin n × Fin k) → ℝ) : ℝ :=
  (totalEmpiricalInstance (reservoirCoordinates.symm y)).expectedMaximum
noncomputable def boundedMaximum (H : ℝ≥0) (x : Fin n → ℝ) : ℝ :=
  boundedOfferValue H (Instance.maximum x)

lemma measurable_boundedMaximum (H : ℝ≥0) : Measurable (boundedMaximum (n := n) H) :=
  (boundedOfferValue H).continuous.measurable.comp Instance.measurable_maximum
lemma boundedMaximum_abs_le (H : ℝ≥0) (x : Fin n → ℝ) : |boundedMaximum H x| ≤ H := by
  unfold boundedMaximum
  rw [abs_of_nonneg (boundedOfferValue_mem_range H _).1]
  exact (boundedOfferValue_mem_range H _).2

lemma Instance.maximum_max_zero (x : Fin n → ℝ) :
    Instance.maximum (fun i => max 0 (x i)) = Instance.maximum x := by
  apply le_antisymm
  · exact Instance.maximum_le _ (Instance.maximum_nonnegative x)
      (fun i => max_le (Instance.maximum_nonnegative x) (Instance.le_maximum x i))
  · apply Instance.maximum_le x (Instance.maximum_nonnegative _)
    intro i
    exact (le_max_right (0 : ℝ) (x i)).trans (Instance.le_maximum (fun j => max 0 (x j)) i)

lemma measurable_empiricalExpectedMaximum : Measurable (@empiricalExpectedMaximum n k _) := by
  exact measurable_totalEmpirical_expectedMaximum
    (fun i j => measurable_pi_apply (i,j))

lemma empiricalExpectedMaximum_eq_productAverage_of_cap (H : ℝ≥0)
    (y : (Fin n × Fin k) → ℝ) (hy : ∀ q, y q ≤ (H : ℝ)) :
    empiricalExpectedMaximum y = empiricalProductAverage (boundedMaximum H) y := by
  rw [empiricalExpectedMaximum,totalEmpiricalInstance_expectedMaximum_eq]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => by
    change Instance.maximum (fun i => max 0 (y (i,a i))) = boundedOfferValue H (Instance.maximum (fun i => y (i,a i)))
    rw [Instance.maximum_max_zero,boundedOfferValue_eq H
      ⟨Instance.maximum_nonnegative _,Instance.maximum_le _ H.coe_nonneg (fun i => hy (i,a i))⟩]

omit [NeZero k] in
lemma Instance.training_array_cap_ae (P : Instance n) {H : ℝ}
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ᵐ y : (Fin n × Fin k) → ℝ ∂P.trainingCoordinateLaw k, ∀ q, y q ≤ H := by
  apply ae_all_iff.mpr
  intro q
  exact (measurePreserving_eval (fun q : Fin n × Fin k => P.law q.1) q).quasiMeasurePreserving.ae (hcap q.1)

lemma Instance.boundedMaximum_eq_maximum_ae (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    boundedMaximum H =ᵐ[P.valuesLaw] Instance.maximum := by
  have hvals : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ (H : ℝ) :=
    ae_all_iff.mpr fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)
  filter_upwards [hvals] with x hx
  exact boundedOfferValue_eq H ⟨Instance.maximum_nonnegative x,Instance.maximum_le x H.coe_nonneg hx⟩

lemma Instance.empiricalExpectedMaximum_eq_productAverage_ae (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    empiricalExpectedMaximum (n := n) (k := k) =ᵐ[P.trainingCoordinateLaw k] empiricalProductAverage (boundedMaximum H) :=
  (P.training_array_cap_ae (k := k) hcap).mono fun y hy => empiricalExpectedMaximum_eq_productAverage_of_cap H y hy

lemma Instance.empiricalExpectedMaximum_abs_le_ae (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    ∀ᵐ y ∂P.trainingCoordinateLaw k, |empiricalExpectedMaximum (k := k) y| ≤ (H : ℝ) := by
  filter_upwards [P.empiricalExpectedMaximum_eq_productAverage_ae (k := k) H hcap] with y hy
  rw [hy]
  exact empiricalProductAverage_abs_le H (boundedMaximum_abs_le H) y

lemma Instance.memLp_empiricalExpectedMaximum (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) (p : ENNReal) :
    MemLp (empiricalExpectedMaximum (k := k)) p (P.trainingCoordinateLaw k) := by
  apply MemLp.of_bound measurable_empiricalExpectedMaximum.aestronglyMeasurable H
  exact (P.empiricalExpectedMaximum_abs_le_ae H hcap).mono fun y hy => by
    simpa only [Real.norm_eq_abs] using hy

/-- The empirical expectation of the maximum is exactly unbiased. -/
theorem Instance.integral_empiricalExpectedMaximum (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    (∫ y, empiricalExpectedMaximum (k := k) y ∂P.trainingCoordinateLaw k) = P.expectedMaximum := by
  rw [integral_congr_ae (P.empiricalExpectedMaximum_eq_productAverage_ae H hcap),
    integral_empiricalProductAverage P (measurable_boundedMaximum H) H (boundedMaximum_abs_le H)]
  exact integral_congr_ae (P.boundedMaximum_eq_maximum_ae H hcap)

/-- The variance bound in `eq:bayes-maximum-variance`, before the cap1
simplification. No Hoeffding identity is assumed in its dependency chain. -/
theorem Instance.variance_empiricalExpectedMaximum_le (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k) ≤ variance Instance.maximum P.valuesLaw/(k : ℝ) := by
  rw [variance_congr (P.empiricalExpectedMaximum_eq_productAverage_ae H hcap)]
  have h := variance_empiricalProductAverage_le (k := k) P (measurable_boundedMaximum H) H (boundedMaximum_abs_le H)
  rw [variance_congr (P.boundedMaximum_eq_maximum_ae H hcap)] at h
  exact h

lemma Instance.variance_maximum_le_expectedMaximum (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) :
    variance Instance.maximum P.valuesLaw ≤ P.expectedMaximum := by
  have hvals : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ (1 : ℝ) :=
    ae_all_iff.mpr fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)
  have hmaxBound : ∀ᵐ x ∂P.valuesLaw, |Instance.maximum x| ≤ 1 := hvals.mono fun x hx => by
    rw [abs_of_nonneg (Instance.maximum_nonnegative x)]
    exact Instance.maximum_le x zero_le_one hx
  have hI2 := ProphetSecretary.Probability.integrable_pow_of_bound Instance.measurable_maximum zero_le_one hmaxBound 2
  apply (variance_le_expectation_sq Instance.measurable_maximum.aestronglyMeasurable).trans
  apply integral_mono_ae hI2 (P.integrable_maximum_of_bounded hcap)
  filter_upwards [hvals] with x hx
  have h0 := Instance.maximum_nonnegative x
  have h1 := Instance.maximum_le x zero_le_one hx
  change Instance.maximum x ^ 2 ≤ Instance.maximum x
  nlinarith

/-- Uniformly in finite instance size, with zero expected maximum allowed. -/
theorem Instance.variance_empiricalExpectedMaximum_le_mean_div_samples (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) :
    variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k) ≤ P.expectedMaximum/(k : ℝ) :=
  (P.variance_empiricalExpectedMaximum_le 1 hcap).trans
    (div_le_div_of_nonneg_right (P.variance_maximum_le_expectedMaximum hcap) (Nat.cast_nonneg k))

end ProphetSecretary.Model
